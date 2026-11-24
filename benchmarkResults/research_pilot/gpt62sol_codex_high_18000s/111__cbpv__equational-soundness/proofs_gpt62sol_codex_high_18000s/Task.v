Set Implicit Arguments.
From CBPV Require Import ObservationalEquivalence StrongReduction AbstractReductionSystems.

Definition Equiv {n: nat} := equiv (@sstep n).

Import CommaNotation.

(* Substitution equations, stated pointwise to avoid extensionality axioms. *)
Local Ltac syntax_induction :=
  match goal with
  | |- ?L /\ ?R =>
    let P := lazymatch L with forall (n : nat), @?P n => P end in
    let Q := lazymatch R with forall (n : nat), @?Q n => Q end in
    let aux := fresh "aux" in
    assert (aux : forall (n : nat), (P n /\ Q n));
    [ rapply mutind_val_comp; intros;
      cbn [ren_value ren_comp subst_value subst_comp];
      f_equal; eauto 8
    | let n := fresh "n" in split; intro n; [apply (proj1 (aux n)) | apply (proj2 (aux n))] ]
  end.

Lemma ren_compose :
  (forall n (v : value n) m k (r : ren n m) (s : ren m k) (t : ren n k),
    (forall i, s (r i) = t i) -> ren_value s (ren_value r v) = ren_value t v) /\
  (forall n (c : comp n) m k (r : ren n m) (s : ren m k) (t : ren n k),
    (forall i, s (r i) = t i) -> ren_comp s (ren_comp r c) = ren_comp t c).
Proof.
  assert (lift : forall n m k (r : ren n m) (s : ren m k) (t : ren n k),
    (forall i, s (r i) = t i) ->
    forall i, upRen_value_value s (upRen_value_value r i) = upRen_value_value t i).
  { intros n m k r s t H [i|]; [|reflexivity].
    change (Some (s (r i)) = Some (t i)). now rewrite H. }
  syntax_induction.
Qed.

Lemma subst_after_ren :
  (forall n (v : value n) m k (r : ren n m) (s : fin m -> value k) t,
    (forall i, s (r i) = t i) -> subst_value s (ren_value r v) = subst_value t v) /\
  (forall n (c : comp n) m k (r : ren n m) (s : fin m -> value k) t,
    (forall i, s (r i) = t i) -> subst_comp s (ren_comp r c) = subst_comp t c).
Proof.
  assert (lift : forall n m k (r : ren n m) (s : fin m -> value k) t,
    (forall i, s (r i) = t i) -> forall i,
    up_value_value s (upRen_value_value r i) = up_value_value t i).
  { intros n m k r s t H [i|].
    - change (ren_value shift (s (r i)) = ren_value shift (t i)). now rewrite H.
    - reflexivity. }
  syntax_induction.
Qed.

Lemma ren_after_subst :
  (forall n (v : value n) m k (s : fin n -> value m) (r : ren m k) t,
    (forall i, ren_value r (s i) = t i) -> ren_value r (subst_value s v) = subst_value t v) /\
  (forall n (c : comp n) m k (s : fin n -> value m) (r : ren m k) t,
    (forall i, ren_value r (s i) = t i) -> ren_comp r (subst_comp s c) = subst_comp t c).
Proof.
  assert (lift : forall n m k (s : fin n -> value m) (r : ren m k) t,
    (forall i, ren_value r (s i) = t i) -> forall i,
    ren_value (upRen_value_value r) (up_value_value s i) = up_value_value t i).
  { intros n m k s r t H [i|]; [|reflexivity].
    change (ren_value (upRen_value_value r) (ren_value shift (s i)) =
      ren_value shift (t i)).
    rewrite <- H. rewrite (proj1 ren_compose _ (s i) _ _ shift (upRen_value_value r)
      (fun j => Some (r j))) by reflexivity.
    symmetry. apply (proj1 ren_compose). reflexivity. }
  syntax_induction.
Qed.

Lemma subst_compose :
  (forall n (v : value n) m k (s : fin n -> value m) (r : fin m -> value k) t,
    (forall i, subst_value r (s i) = t i) -> subst_value r (subst_value s v) = subst_value t v) /\
  (forall n (c : comp n) m k (s : fin n -> value m) (r : fin m -> value k) t,
    (forall i, subst_value r (s i) = t i) -> subst_comp r (subst_comp s c) = subst_comp t c).
Proof.
  assert (lift : forall n m k (s : fin n -> value m) (r : fin m -> value k) t,
    (forall i, subst_value r (s i) = t i) -> forall i,
    subst_value (up_value_value r) (up_value_value s i) = up_value_value t i).
  { intros n m k s r t H [i|]; [|reflexivity].
    change (subst_value (up_value_value r) (ren_value shift (s i)) =
      ren_value shift (t i)).
    rewrite <- H. rewrite (proj1 subst_after_ren _ (s i) _ _ shift (up_value_value r)
      (fun j => ren_value shift (r j))) by reflexivity.
    symmetry. apply (proj1 ren_after_subst). reflexivity. }
  syntax_induction.
Qed.

Lemma subst_identity :
  (forall n (v : value n) (s : fin n -> value n),
    (forall i, s i = var_value i) -> subst_value s v = v) /\
  (forall n (c : comp n) (s : fin n -> value n),
    (forall i, s i = var_value i) -> subst_comp s c = c).
Proof.
  assert (lift : forall n (s : fin n -> value n),
    (forall i, s i = var_value i) ->
    forall i, up_value_value s i = var_value i).
  { intros n s H [i|]; [|reflexivity].
    change (ren_value shift (s i) = @var_value (S n) (Some i)). now rewrite H. }
  syntax_induction.
Qed.

Lemma instantiate_one n m (c : comp (S n)) (s : fin n -> value m) (v : value m) :
  (subst_comp (up_value_value s) c)[v..] = subst_comp (v .: s) c.
Proof.
  apply (proj2 subst_compose). intros [i|]; cbn [scons up_value_value funcomp]; auto.
  etransitivity; [apply (proj1 subst_after_ren) with (t := @var_value m); reflexivity|].
  apply (proj1 subst_identity). reflexivity.
Qed.

Lemma instantiate_two n m (c : comp (S (S n))) (s : fin n -> value m) (v w : value m) :
  (subst_comp (up_value_value (up_value_value s)) c)[w,v..] = subst_comp (w,v,s) c.
Proof.
  apply (proj2 subst_compose). intros [j|]; [destruct j as [i|] |]; cbn [scons up_value_value funcomp]; auto.
  change (subst_value (w,v,@var_value m) (ren_value shift (ren_value shift (s i))) = s i).
  rewrite (proj1 subst_after_ren _ (ren_value shift (s i)) _ _ shift (w,v,@var_value m)
    (v .: @var_value m)) by reflexivity.
  etransitivity; [apply (proj1 subst_after_ren) with (t := @var_value m); reflexivity|].
  apply (proj1 subst_identity). reflexivity.
Qed.

Lemma subst_beta_one n m (c : comp (S n)) (s : fin n -> value m) (v : value n) :
  subst_comp s (c[v..]) = (subst_comp (up_value_value s) c)[(subst_value s v)..].
Proof.
  rewrite instantiate_one. apply (proj2 subst_compose). intros [i|]; reflexivity.
Qed.

Lemma subst_beta_two n m (c : comp (S (S n))) (s : fin n -> value m) (v w : value n) :
  subst_comp s (c[w,v..]) =
    (subst_comp (up_value_value (up_value_value s)) c)[subst_value s w,(subst_value s v)..].
Proof.
  rewrite instantiate_two. apply (proj2 subst_compose). intros [j|]; [destruct j as [i|] |]; reflexivity.
Qed.

Lemma ren_beta_one n m (c : comp (S n)) (r : ren n m) (v : value n) :
  ren_comp r (c[v..]) = (ren_comp (upRen_value_value r) c)[(ren_value r v)..].
Proof.
  transitivity (subst_comp (ren_value r v .: fun i => var_value (r i)) c).
  - apply (proj2 ren_after_subst). intros [i|]; reflexivity.
  - symmetry. apply (proj2 subst_after_ren). intros [i|]; reflexivity.
Qed.

Lemma ren_beta_two n m (c : comp (S (S n))) (r : ren n m) (v w : value n) :
  ren_comp r (c[w,v..]) =
    (ren_comp (upRen_value_value (upRen_value_value r)) c)[ren_value r w,(ren_value r v)..].
Proof.
  transitivity (subst_comp (ren_value r w,ren_value r v,fun i => var_value (r i)) c).
  - apply (proj2 ren_after_subst). intros [j|]; [destruct j as [i|] |]; reflexivity.
  - symmetry. apply (proj2 subst_after_ren). intros [j|]; [destruct j as [i|] |]; reflexivity.
Qed.

(* Parallel reduction contracts a redex while reducing its components. *)
Inductive par_v {n : nat} : value n -> value n -> Prop :=
| pv_var i : par_v (var_value i) (var_value i)
| pv_unit : par_v u u
| pv_pair v w v' w' : par_v v v' -> par_v w w' -> par_v (pair v w) (pair v' w')
| pv_inj b v v' : par_v v v' -> par_v (inj b v) (inj b v')
| pv_thunk c c' : par_c c c' -> par_v (thunk c) (thunk c')
with par_c {n : nat} : comp n -> comp n -> Prop :=
| pc_unit : par_c cu cu
| pc_force v v' : par_v v v' -> par_c (force v) (force v')
| pc_lambda c c' : par_c c c' -> par_c (lambda c) (lambda c')
| pc_app c c' v v' : par_c c c' -> par_v v v' -> par_c (app c v) (app c' v')
| pc_tuple c d c' d' : par_c c c' -> par_c d d' -> par_c (tuple c d) (tuple c' d')
| pc_ret v v' : par_v v v' -> par_c (ret v) (ret v')
| pc_let c c' d d' : par_c c c' -> par_c d d' -> par_c (letin c d) (letin c' d')
| pc_proj b c c' : par_c c c' -> par_c (proj b c) (proj b c')
| pc_caseZ v v' : par_v v v' -> par_c (caseZ v) (caseZ v')
| pc_caseS v v' c c' d d' :
    par_v v v' -> par_c c c' -> par_c d d' -> par_c (caseS v c d) (caseS v' c' d')
| pc_caseP v v' c c' : par_v v v' -> par_c c c' -> par_c (caseP v c) (caseP v' c')
| pc_beta_force c c' : par_c c c' -> par_c (force (thunk c)) c'
| pc_beta_app c c' v v' : par_c c c' -> par_v v v' -> par_c (app (lambda c) v) (c'[v'..])
| pc_beta_let v v' c c' : par_v v v' -> par_c c c' -> par_c (letin (ret v) c) (c'[v'..])
| pc_beta_proj b c c' d d' : par_c c c' -> par_c d d' ->
    par_c (proj b (tuple c d)) (if b then c' else d')
| pc_beta_caseS b v v' c c' d d' : par_v v v' -> par_c c c' -> par_c d d' ->
    par_c (caseS (inj b v) c d) ((if b then c' else d')[v'..])
| pc_beta_caseP v v' w w' c c' : par_v v v' -> par_v w w' -> par_c c c' ->
    par_c (caseP (pair v w) c) (c'[w',v'..]).

Scheme par_v_induction := Induction for par_v Sort Prop
  with par_c_induction := Induction for par_c Sort Prop.
Combined Scheme par_induction from par_v_induction, par_c_induction.

Create HintDb parallel.
#[local] Hint Constructors par_v par_c : parallel.

Lemma par_reflexive n :
  (forall (v : value n), par_v v v) /\ (forall (c : comp n), par_c c c).
Proof.
  apply (mutind_val_comp (fun n v => @par_v n v v) (fun n c => @par_c n c c));
    eauto with parallel.
Qed.

Lemma par_v_refl n (v : value n) : par_v v v.
Proof. apply (proj1 (par_reflexive n)). Qed.

Lemma par_c_refl n (c : comp n) : par_c c c.
Proof. apply (proj2 (par_reflexive n)). Qed.
#[local] Hint Resolve par_v_refl par_c_refl : parallel.

Lemma par_ren n :
  (forall (v w : value n), par_v v w -> forall m (r : ren n m),
    par_v (ren_value r v) (ren_value r w)) /\
  (forall (c d : comp n), par_c c d -> forall m (r : ren n m),
    par_c (ren_comp r c) (ren_comp r d)).
Proof.
  apply (par_induction
    (fun n v w _ => forall m (r : ren n m), par_v (ren_value r v) (ren_value r w))
    (fun n c d _ => forall m (r : ren n m), par_c (ren_comp r c) (ren_comp r d)));
    intros; cbn [ren_value ren_comp];
    try rewrite ren_beta_one; try rewrite ren_beta_two;
    eauto with parallel.
  - destruct b; exact (pc_beta_proj _ (H m r) (H0 m r)).
  - replace (ren_comp (upRen_value_value r) (if b then c' else d'))
      with (if b then ren_comp (upRen_value_value r) c' else ren_comp (upRen_value_value r) d')
      by (destruct b; reflexivity).
    eauto with parallel.
Qed.

Lemma par_subst n :
  (forall (v w : value n), par_v v w -> forall m (s t : fin n -> value m),
    (forall i, par_v (s i) (t i)) -> par_v (subst_value s v) (subst_value t w)) /\
  (forall (c d : comp n), par_c c d -> forall m (s t : fin n -> value m),
    (forall i, par_v (s i) (t i)) -> par_c (subst_comp s c) (subst_comp t d)).
Proof.
  assert (lift : forall n m (s t : fin n -> value m),
    (forall i, par_v (s i) (t i)) ->
    forall i, par_v (up_value_value s i) (up_value_value t i)).
  { intros k m s t H [i|].
    - change (par_v (ren_value shift (s i)) (ren_value shift (t i))).
      apply (proj1 (par_ren m)), H.
    - constructor. }
  apply (par_induction
    (fun n v w _ => forall m (s t : fin n -> value m),
      (forall i, par_v (s i) (t i)) -> par_v (subst_value s v) (subst_value t w))
    (fun n c d _ => forall m (s t : fin n -> value m),
      (forall i, par_v (s i) (t i)) -> par_c (subst_comp s c) (subst_comp t d)));
    intros; cbn [subst_value subst_comp];
    try rewrite subst_beta_one; try rewrite subst_beta_two;
    eauto 8 with parallel.
  - destruct b; exact (pc_beta_proj _ (H m s t H1) (H0 m s t H1)).
  - replace (subst_comp (up_value_value t) (if b then c' else d'))
      with (if b then subst_comp (up_value_value t) c' else subst_comp (up_value_value t) d')
      by (destruct b; reflexivity).
    eapply pc_beta_caseS; eauto 8 with parallel.
Qed.

Lemma par_instantiate_one n (c d : comp (S n)) (v w : value n) :
  par_c c d -> par_v v w -> par_c (c[v..]) (d[w..]).
Proof.
  intros Hc Hv. apply (proj2 (par_subst (S n))); [exact Hc|].
  intros [i|]; eauto with parallel.
Qed.

Lemma par_instantiate_two n (c d : comp (S (S n))) (v v' w w' : value n) :
  par_c c d -> par_v v v' -> par_v w w' -> par_c (c[w,v..]) (d[w',v'..]).
Proof.
  intros Hc Hv Hw. apply (proj2 (par_subst (S (S n)))); [exact Hc|].
  intros [j|]; [destruct j as [i|] |]; eauto with parallel.
Qed.

Fixpoint develop_v n (v : value n) : value n :=
  match v with
  | var_value i => var_value i
  | u => u
  | pair v w => pair (develop_v v) (develop_v w)
  | inj b v => inj b (develop_v v)
  | thunk c => thunk (develop_c c)
  end
with develop_c n (c : comp n) : comp n :=
  match c with
  | cu => cu
  | force v =>
      match v with
      | thunk d => develop_c d
      | _ => force (develop_v v)
      end
  | lambda d => lambda (develop_c d)
  | app d v =>
      match d with
      | lambda e => (develop_c e)[(develop_v v)..]
      | _ => app (develop_c d) (develop_v v)
      end
  | tuple d e => tuple (develop_c d) (develop_c e)
  | ret v => ret (develop_v v)
  | letin d e =>
      match d with
      | ret v => (develop_c e)[(develop_v v)..]
      | _ => letin (develop_c d) (develop_c e)
      end
  | proj b d =>
      match d with
      | tuple e f => if b then develop_c e else develop_c f
      | _ => proj b (develop_c d)
      end
  | caseZ v => caseZ (develop_v v)
  | caseS v d e =>
      match v with
      | inj b w => (if b then develop_c d else develop_c e)[(develop_v w)..]
      | _ => caseS (develop_v v) (develop_c d) (develop_c e)
      end
  | caseP v d =>
      match v with
      | pair w x => (develop_c d)[develop_v x,(develop_v w)..]
      | _ => caseP (develop_v v) (develop_c d)
      end
  end.

(* A parallel reduct can always reach the complete development in one round. *)
Lemma par_develop n :
  (forall (v w : value n), par_v v w -> par_v w (develop_v v)) /\
  (forall (c d : comp n), par_c c d -> par_c d (develop_c c)).
Proof.
  apply (par_induction
    (fun n v w _ => par_v w (develop_v v))
    (fun n c d _ => par_c d (develop_c c)));
    intros; cbn [develop_c develop_v]; eauto with parallel.
  - destruct v; cbn [develop_v develop_c]; eauto with parallel.
    inversion p; subst. inversion H; subst. now apply pc_beta_force.
  - destruct c; cbn [develop_v develop_c]; eauto with parallel.
    inversion p; subst. inversion H; subst. now apply pc_beta_app.
  - destruct c; cbn [develop_v develop_c]; eauto with parallel.
    inversion p; subst. inversion H; subst. now apply pc_beta_let.
  - destruct c; cbn [develop_v develop_c]; eauto with parallel.
    inversion p; subst. inversion H; subst. now apply pc_beta_proj.
  - destruct v; cbn [develop_v develop_c]; eauto with parallel.
    inversion p; subst. inversion H; subst. now apply pc_beta_caseS.
  - destruct v; cbn [develop_v develop_c]; eauto with parallel.
    inversion p; subst. inversion H; subst. now apply pc_beta_caseP.
  - now apply par_instantiate_one.
  - now apply par_instantiate_one.
  - destruct b; assumption.
  - apply par_instantiate_one; [destruct b |]; assumption.
  - now apply par_instantiate_two.
Qed.

Lemma primitive_parallel n (c d : comp n) : c ≽ d -> par_c c d.
Proof. intros H; destruct H; subst; eauto with parallel. Qed.

Lemma strong_parallel n :
  (forall (c d : comp n), c ↪ d -> par_c c d) /\
  (forall (v w : value n), v ↪ᵥ w -> par_v v w).
Proof.
  apply (mutind_sstep (fun n v w _ => @par_v n v w) (fun n c d _ => @par_c n c d));
    eauto using primitive_parallel with parallel.
Qed.

Lemma weak_parallel n (c d : comp n) : c > d -> par_c c d.
Proof. intros H; induction H; eauto using primitive_parallel with parallel. Qed.

Definition par_hole (t : bool) (n : nat) :
  (if t then value n else comp n) -> (if t then value n else comp n) -> Prop :=
  if t as b return
    (if b then value n else comp n) -> (if b then value n else comp n) -> Prop
  then @par_v n else @par_c n.

Lemma fill_parallel t m :
  (forall n (C : vctx t m n) x y,
    @par_hole t n x y -> par_v (fillv C x) (fillv C y)) /\
  (forall n (C : cctx t m n) x y,
    @par_hole t n x y -> par_c (fillc C x) (fillc C y)).
Proof.
  apply (mutind_vctx_cctx
    (fun m n C => forall x y, @par_hole t n x y -> par_v (@fillv m n t C x) (fillv C y))
    (fun m n C => forall x y, @par_hole t n x y -> par_c (@fillc m n t C x) (fillc C y)));
    intros; cbn [fillv fillc]; eauto with parallel.
  all: destruct t; cbn in *; contradiction || assumption.
Qed.

Lemma star_transitive X (R : X -> X -> Prop) (x y z : X) :
  star R x y -> star R y z -> star R x z.
Proof. intros H; induction H; eauto using starStep. Qed.

Lemma star_map X Y (R : X -> X -> Prop) (S : Y -> Y -> Prop) (f : X -> Y) :
  (forall x y, R x y -> S (f x) (f y)) ->
  forall x y, star R x y -> star S (f x) (f y).
Proof. intros H x y D; induction D; eauto using starRefl, starStep. Qed.

Lemma diamond_strip X (R : X -> X -> Prop) :
  diamond R -> forall x y z, star R x y -> R x z ->
    exists2 w, R y w & star R z w.
Proof.
  intros D x y z H. revert z.
  induction H as [x|x u y Hxu Huy IH]; intros z Hxz.
  - exists z; [exact Hxz | apply starRefl].
  - destruct (D _ _ _ Hxu Hxz) as [v Huv Hzv].
    destruct (IH _ Huv) as [w Hyw Hvw].
    exists w; eauto using starStep.
Qed.

Lemma diamond_confluent X (R : X -> X -> Prop) : diamond R -> confluent R.
Proof.
  intros D x y z H. revert z.
  induction H as [x|x u y Hxu Huy IH]; intros z Hxz.
  - exists z; [exact Hxz | apply starRefl].
  - destruct (@diamond_strip X R D x z u Hxz Hxu) as [v Hzv Huv].
    destruct (IH _ Huv) as [w Hyw Hvw].
    exists w; eauto using starStep.
Qed.

Lemma parallel_confluent n : confluent (@par_c n).
Proof.
  apply diamond_confluent. intros x y z Hxy Hxz.
  exists (develop_c x); now apply (proj2 (par_develop n)).
Qed.

Lemma parallel_join n (x y : comp n) :
  equiv (@par_c n) x y -> joinable (star (@par_c n)) x y.
Proof.
  intros H; induction H as [x|x u y Hxu Huy IH].
  - exists x; apply starRefl.
  - destruct IH as [z Huz Hyz].
    destruct Hxu as [x u Hxu|x u Hux].
    + exists z; eauto using starStep.
    + assert (Hux' : star par_c u x) by eauto using starStep, starRefl.
      destruct (@parallel_confluent n u x z Hux' Huz) as [w Hxw Hzw].
      exists w; eauto using star_transitive.
Qed.

Lemma fill_equiv m n (C : cctx false m n) (c d : comp n) :
  Equiv c d -> equiv (@par_c m) (fillc C c) (fillc C d).
Proof.
  unfold Equiv, equiv. apply star_map.
  intros x y H; destruct H as [x y H|x y H]; [apply symId | apply symInv];
    apply (proj2 (fill_parallel false m)); now apply (proj1 (strong_parallel n)).
Qed.

Definition hole_typing (t : bool) n (Gamma : ctx n) :
  (if t then value n else comp n) -> (if t then valtype else comptype) -> Type :=
  if t as b return
    (if b then value n else comp n) -> (if b then valtype else comptype) -> Type
  then value_typing Gamma else computation_typing Gamma.

Lemma fill_typing t m (Gamma : ctx m) :
  (forall n (Delta : ctx n) (C : vctx t m n) A T,
    Gamma [[Delta]] ⊩ C : A; T ->
    forall x, @hole_typing t n Delta x T -> inhab (Gamma ⊩ fillv C x : A)) /\
  (forall n (Delta : ctx n) (C : cctx t m n) B T,
    Gamma [[Delta]] ⊢ C : B; T ->
    forall x, @hole_typing t n Delta x T -> inhab (Gamma ⊢ fillc C x : B)).
Proof.
  apply (mutind_vctx_cctx_typing
    (fun m t Gamma n Delta C A T => forall x,
      @hole_typing t n Delta x T -> inhab (Gamma ⊩ fillv C x : A))
    (fun m t Gamma n Delta C B T => forall x,
      @hole_typing t n Delta x T -> inhab (Gamma ⊢ fillc C x : B)));
    intros; cbn [fillv fillc].
  all: try match goal with
    | IH : (forall x, @hole_typing _ _ _ x _ -> inhab _) |- _ =>
      match goal with
      | H : @hole_typing _ _ _ _ _ |- _ => destruct (IH _ H)
      end
    end.
  all: try solve [constructor; eauto using
      typePair, typeSum, typeThunk, typeLambda, typeForce, typeApp, typeTuple,
      typeRet, typeLetin, typeProj, typeCaseZ, typeCaseS, typeCaseP].
  all: match goal with b : bool |- _ => destruct b end; cbn in *; contradiction || (constructor; assumption).
Qed.

(* Reducibility supplies a weak evaluation at return types and restricts the
   returned values to canonical forms at ground types. *)
Fixpoint reducible_v (A : valtype) (v : value 0) : Prop :=
  match A with
  | zero => False
  | one => v = u
  | U B => exists c, v = thunk c /\ reducible_c B c
  | Sigma A B => exists b w, v = inj b w /\
      (if b then reducible_v A w else reducible_v B w)
  | cross A B => exists w x, v = pair w x /\ reducible_v A w /\ reducible_v B x
  end
with reducible_c (B : comptype) (c : comp 0) : Prop :=
  match B with
  | cone => c >* cu
  | F A => exists v, c >* ret v /\ reducible_v A v
  | Pi B D => reducible_c B (proj true c) /\ reducible_c D (proj false c)
  | arrow A B => forall v, reducible_v A v -> reducible_c B (app c v)
  end.

Lemma reducible_backwards B (c d : comp 0) :
  c >* d -> reducible_c B d -> reducible_c B c.
Proof.
  revert c d. induction B; intros c d H Hr; cbn [reducible_c] in *.
  - eauto using star_transitive.
  - destruct Hr as [w [Hdv Hv ] ]. exists w; eauto using star_transitive.
  - destruct Hr as [H1 H2]. split.
    + eapply IHB1; [|exact H1]. eapply star_map; eauto using stepProj.
    + eapply IHB2; [|exact H2]. eapply star_map; eauto using stepProj.
  - intros w Hw. eapply IHB with (d := app d w); [|exact (Hr w Hw)].
    eapply star_map with (f := fun e => app e w); eauto using stepApp.
Qed.

Lemma reducible_primitive B (c d : comp 0) :
  c ≽ d -> reducible_c B d -> reducible_c B c.
Proof. eauto using reducible_backwards, starStep, starRefl, stepPrimitive. Qed.

Definition reducible_subst n (Gamma : ctx n) (s : fin n -> value 0) :=
  forall i, reducible_v (Gamma i) (s i).

Lemma reducible_extend n (Gamma : ctx n) s A v :
  reducible_subst Gamma s -> reducible_v A v ->
  reducible_subst (A .: Gamma) (v .: s).
Proof. intros Hs Hv [i|]; [apply Hs | exact Hv]. Qed.

Lemma reducibility n (Gamma : ctx n) :
  (forall v A, Gamma ⊩ v : A -> forall s,
    reducible_subst Gamma s -> reducible_v A (subst_value s v)) /\
  (forall c B, Gamma ⊢ c : B -> forall s,
    reducible_subst Gamma s -> reducible_c B (subst_comp s c)).
Proof.
  apply (mutind_value_computation_typing
    (fun n Gamma v A => forall s, reducible_subst Gamma s ->
      reducible_v A (subst_value s v))
    (fun n Gamma c B => forall s, reducible_subst Gamma s ->
      reducible_c B (subst_comp s c)));
    intros; cbn [reducible_v reducible_c subst_value subst_comp] in *.
  - apply H.
  - reflexivity.
  - exists (subst_value s v1), (subst_value s v2). repeat split; eauto.
  - exists b, (subst_value s v). split; [reflexivity|].
    destruct b; eauto.
  - exists (subst_comp s c). split; eauto.
  - apply starRefl.
  - intros v Hv. eapply reducible_primitive.
    + apply pstepApp. reflexivity.
    + rewrite instantiate_one. eauto using reducible_extend.
  - specialize (H s H1). destruct H as [v [He Hv ] ].
    eapply reducible_backwards.
    + eapply star_map with (f := fun e => letin e (subst_comp (up_value_value s) c2));
        eauto using stepLetin.
    + eapply reducible_primitive.
      * apply pstepLetin. reflexivity.
      * rewrite instantiate_one. eauto using reducible_extend.
  - exists (subst_value s v). split; eauto using starRefl.
  - eauto.
  - split.
    + eapply reducible_primitive; [apply pstepProj; reflexivity | eauto].
    + eapply reducible_primitive; [apply pstepProj; reflexivity | eauto].
  - specialize (H s H0). destruct b; tauto.
  - destruct (H s H0) as [d [He Hd ] ]. rewrite He.
    eapply reducible_primitive; [apply pstepForce | exact Hd].
  - exact (False_rect _ (H s H0)).
  - destruct (H s H2) as [b [w [He Hw ]  ] ]. rewrite He.
    eapply reducible_primitive; [apply pstepCaseS; reflexivity |].
    destruct b; rewrite instantiate_one; eauto using reducible_extend.
  - destruct (H s H1) as [w [x [He [Hw Hx ] ] ] ]. rewrite He.
    eapply reducible_primitive; [apply pstepCaseP; reflexivity |].
    rewrite instantiate_two. eauto using reducible_extend.
Qed.

Definition par_normal {X} (R : X -> X -> Prop) (x : X) :=
  forall y, R x y -> y = x.

Lemma ground_value_normal (G : groundtype) (v : value 0) :
  reducible_v G v -> par_normal par_v v.
Proof.
  unfold par_normal. revert v. induction G; intros v Hv; cbn [to_valtype reducible_v] in Hv.
  - subst v. intros w H. now inversion H.
  - destruct Hv as [b [x [He Hx] ] ]. subst v.
    intros w H. inversion H; subst. f_equal.
    destruct b; eauto.
  - destruct Hv as [x [y [He [Hx Hy] ] ] ]. subst v.
    intros w H. inversion H; subst. f_equal; eauto.
Qed.

Lemma closed_ground_result (G : groundtype) (c : comp 0) (H : null ⊢ c : F G) :
  exists v, c >* ret v /\ par_normal par_c (ret v).
Proof.
  assert (Hs : reducible_subst null (@var_value 0)) by (intros i; destruct i).
  pose proof (proj2 (reducibility (n := 0) null) c (F G) H _ Hs) as Hr.
  rewrite (proj2 subst_identity 0 c (@var_value 0)) in Hr by reflexivity.
  destruct Hr as [v [He Hv] ]. exists v. split; [exact He|].
  intros d Hd. inversion Hd; subst.
  f_equal. eapply (ground_value_normal G); eauto.
Qed.

Lemma weak_normal_stuck n (c d : comp n) : nf c -> c > d -> False.
Proof.
  intros Hn H; destruct Hn; inversion H; subst;
    match goal with Hp : pstep _ _ |- _ => inversion Hp end.
Qed.

Lemma weak_deterministic n : functional (@step n).
Proof.
  intros c d e H. revert e.
  induction H; intros e He; inversion He; subst.
  all: try solve [f_equal; eauto].
  all: repeat match goal with H : pstep _ _ |- _ => inversion H; subst; clear H end.
  all: try reflexivity.
  all: exfalso; eapply weak_normal_stuck; [constructor | eassumption].
Qed.

Lemma weak_return_unique n (c : comp n) (v w : value n) :
  c >* ret v -> c >* ret w -> v = w.
Proof.
  intros Hv. remember (ret v) as r eqn:Hret in Hv.
  induction Hv as [c|c d r Hcd Hdr IH]; intros Hw.
  - subst c. inversion Hw; subst.
    + reflexivity.
    + exfalso. eapply weak_normal_stuck; [apply nfRet | eassumption].
  - inversion Hw; subst.
    + exfalso. eapply weak_normal_stuck; [apply nfRet | eassumption].
    + assert (d = x') by (eapply weak_deterministic; eassumption).
      subst. eauto.
Qed.

Lemma par_normal_star X (R : X -> X -> Prop) (x y : X) :
  star R x y -> par_normal R x -> y = x.
Proof.
  intros H. induction H as [x|x u y Hxu Huy IH]; intros Hn.
  - reflexivity.
  - specialize (Hn _ Hxu) as He. subst u. now apply IH.
Qed.

Lemma confluent_fixed_results X (R : X -> X -> Prop) (c d x y : X) :
  confluent R -> joinable (star R) c d ->
  star R c x -> star R d y -> par_normal R x -> par_normal R y -> x = y.
Proof.
  intros HC [q Hcq Hdq] Hcx Hdy Hx Hy.
  destruct (HC _ _ _ Hcq Hcx) as [r Hqr Hxr].
  assert (r = x) by (eapply par_normal_star; eassumption). subst r.
  pose proof (star_transitive Hdq Hqr) as Hdx.
  destruct (HC _ _ _ Hdx Hdy) as [r Hxr' Hyr].
  assert (r = x) by (eapply par_normal_star; eassumption).
  assert (r = y) by (eapply par_normal_star; eassumption).
  congruence.
Qed.

Lemma weak_star_parallel n (c d : comp n) : c >* d -> star par_c c d.
Proof. intros H; induction H; eauto using weak_parallel, starRefl, starStep. Qed.

Theorem equiv_soundness_CBPV n (Gamma: ctx n) A (M N: CBPVc Gamma A):
  Equiv M N -> M ≃ N.
Proof.
  intros HE G C HC v.
  destruct (@fill_typing false 0 null) as [_ Hplug].
  destruct (Hplug n Gamma C (F G) A HC M (CBPVc_H M)) as [HM].
  destruct (Hplug n Gamma C (F G) A HC N (CBPVc_H N)) as [HN].
  destruct (closed_ground_result G HM) as [m [Hm Hm_normal] ].
  destruct (closed_ground_result G HN) as [k [Hk Hk_normal] ].
  (* Congruence and confluence identify the two canonical ground results. *)
  assert (ret m = ret k) as He.
  { eapply confluent_fixed_results with (c := fillc C M) (d := fillc C N).
    - apply parallel_confluent.
    - apply parallel_join. now apply fill_equiv.
    - exact (weak_star_parallel Hm).
    - exact (weak_star_parallel Hk).
    - exact Hm_normal.
    - exact Hk_normal. }
  injection He as He. subst k.
  split; intro H.
  - pose proof (weak_return_unique H Hm) as ->. exact Hk.
  - pose proof (weak_return_unique H Hk) as ->. exact Hm.
Qed.
