Require Import Utf8.

Require Import Lang.FOmegaEq.Types Lang.FOmegaEq.Kinds Lang.FOmegaEq.Syntax Lang.FOmegaEq.OpSemantics Lang.FOmegaEq.Typing.

Import Binding.Intrinsic (Ctx, dom, extC, Build_Ctx, mtC).

Require Import Binding.Lib Binding.Env.

Import kindEqDec.

Require Import Coq.Relations.Relation_Operators Coq.Relations.Operators_Properties.

Local Open Scope syn_scope.

Require Import List.
From Stdlib Require Import Classes.RelationClasses Arith.PeanoNat.

Local Open Scope typ_scope.
Local Open Scope bind_scope.
Import ListNotations.

Scheme type_ind' := Induction for type Sort Prop
with constr_ind' := Induction for constr Sort Prop.
Combined Scheme type_constr_ind from type_ind', constr_ind'.

(* Finite observations of higher-kinded types. An observation of a function
   records a finite set of input observations sufficient for one output. *)
Inductive type_head :=
| h_unit | h_void | h_arr | h_sum | h_prod
| h_all (k : kind) | h_xist (k : kind) | h_rec (k : kind)
| h_carr | h_cprod | h_constraint (k : kind).

Definition ctor_head k (c : tctor k) : type_head :=
  match c with
  | tc_unit => h_unit | tc_void => h_void | tc_arr => h_arr
  | tc_sum => h_sum | tc_prod => h_prod
  | tc_all k => h_all k | tc_xist k => h_xist k | tc_rec k => h_rec k
  end.

Inductive observation :=
| o_head (h : type_head)
| o_left (p : observation)
| o_right (p : observation)
| o_arrow (xs : list observation) (y : observation).

Fixpoint obs (k : kind) : Type :=
  match k with
  | ⋆ => observation
  | a ⇒ b => (list (obs a) * obs b)%type
  end.

Fixpoint encode (k : kind) : obs k -> observation :=
  match k with
  | ⋆ => fun x => x
  | a ⇒ b => fun '(xs, y) => o_arrow (map (encode a) xs) (encode b y)
  end.

Lemma map_injective {A B} (f : A -> B) :
  (forall x y, f x = f y -> x = y) ->
  forall xs ys, map f xs = map f ys -> xs = ys.
Proof.
  intros H xs. induction xs as [|x xs IH]; intros [|y ys] E;
    inversion E; subst; f_equal; auto.
Qed.

Lemma encode_injective k (x y : obs k) : encode k x = encode k y -> x = y.
Proof.
  induction k as [|a IHa b IHb]; simpl; auto.
  destruct x as [xs x], y as [ys y]. simpl.
  intros H. assert (E : map (encode a) xs = map (encode a) ys) by congruence.
  assert (F : encode b x = encode b y) by congruence.
  rewrite (map_injective _ IHa _ _ E), (IHb _ _ F). reflexivity.
Qed.

Definition den k := obs k -> Prop.
Definition den_le {k} (P Q : den k) := forall x, P x -> Q x.
Definition den_eq {k} (P Q : den k) := forall x, P x <-> Q x.

Fixpoint obs_le (k : kind) : obs k -> obs k -> Prop :=
  match k with
  | ⋆ => eq
  | a ⇒ b => fun '(xs, x) '(ys, y) =>
      (forall z, In z ys -> exists w, In w xs /\ obs_le a z w) /\ obs_le b x y
  end.

Lemma obs_le_refl k (x : obs k) : obs_le k x x.
Proof.
  induction k as [|a IHa b IHb]; simpl; auto.
  destruct x as [xs x]. split; eauto.
Qed.

Lemma obs_le_trans k (x y z : obs k) :
  obs_le k x y -> obs_le k y z -> obs_le k x z.
Proof.
  induction k as [|a IHa b IHb]; simpl in *; [congruence|].
  destruct x as [xs x], y as [ys y], z as [zs z].
  intros [Hxy Hout] [Hyz Hout']. split; [|eauto].
  intros v Hv. destruct (Hyz _ Hv) as [w [Hw Hvw]].
  destruct (Hxy _ Hw) as [u [Hu Hwu]]. eauto.
Qed.

Definition valid {k} (P : den k) :=
  forall x y, obs_le k x y -> P y -> P x.
Definition down k (xs : list (obs k)) : den k :=
  fun x => exists y, In y xs /\ obs_le k x y.
Definition empty_den k : den k := fun _ => False.

Lemma down_valid k xs : valid (down k xs).
Proof. intros x y H [z [Hz Hyz]]. exists z. eauto using obs_le_trans. Qed.

Lemma down_in k xs x : In x xs -> down k xs x.
Proof. intros H. exists x. auto using obs_le_refl. Qed.

Lemma down_le k xs ys :
  (forall x, In x xs -> down k ys x) -> den_le (down k xs) (down k ys).
Proof. intros H x [y [Hy Hxy]]. eapply down_valid; eauto. Qed.

Lemma down_bound k xs (P : den k) :
  valid P -> (forall x, In x xs -> P x) -> den_le (down k xs) P.
Proof. intros Hv H x [y [Hy Hxy]]. eauto. Qed.

Definition dapp {a b} (P : den (a ⇒ b)) (Q : den a) : den b :=
  fun y => exists xs, (forall x, In x xs -> Q x) /\ P (xs, y).

Lemma dapp_mono a b (P P' : den (a ⇒ b)) (Q Q' : den a) :
  den_le P P' -> den_le Q Q' -> den_le (dapp P Q) (dapp P' Q').
Proof. intros HP HQ y [xs [Hx Hy]]. exists xs. eauto. Qed.

Lemma dapp_eq a b (P P' : den (a ⇒ b)) (Q Q' : den a) :
  den_eq P P' -> den_eq Q Q' -> den_eq (dapp P Q) (dapp P' Q').
Proof. intros HP HQ y. split; apply dapp_mono; firstorder. Qed.

Lemma dapp_valid a b (P : den (a ⇒ b)) (Q : den a) :
  valid P -> valid (dapp P Q).
Proof.
  intros HP y z Hyz [xs [Hx Hz]]. exists xs. split; auto.
  apply (HP (xs,y) (xs,z)); [|exact Hz]. simpl. split; [intros w Hw; exists w; auto using obs_le_refl|exact Hyz].
Qed.

Lemma dapp_down a b (P : den (a ⇒ b)) xs y :
  valid P -> (dapp P (down a xs) y <-> P (xs,y)).
Proof.
  intros Hv. split.
  - intros [ys [Hy HP]]. apply (Hv (xs,y) (ys,y)); auto.
    simpl. split; auto using obs_le_refl.
  - intros HP. exists xs. auto using down_in.
Qed.

Definition tagged (h : type_head) (P : den ⋆) : den ⋆ :=
  fun x => x = o_head h \/ exists y, x = o_left y /\ P y.
Definition paired {k} (P : den ⋆) (Q : den k) : den ⋆ :=
  fun x => (exists y, x = o_left y /\ P y) \/
           (exists y, x = o_right (encode k y) /\ Q y).

Lemma tagged_mono h P Q : den_le P Q -> den_le (tagged h P) (tagged h Q).
Proof. unfold den_le, tagged. firstorder. Qed.

Lemma paired_mono k P P' (Q Q' : den k) :
  den_le P P' -> den_le Q Q' -> den_le (paired P Q) (paired P' Q').
Proof. unfold den_le, paired. firstorder. Qed.

Lemma tagged_inj h h' P Q :
  den_eq (tagged h P) (tagged h' Q) -> h = h' /\ den_eq P Q.
Proof.
  intros H. split.
  - specialize (proj1 (H (o_head h)) (or_introl eq_refl)) as [E|[y [E _]]];
      congruence.
  - intro x. specialize (H (o_left x)). unfold tagged in H.
    split; intro Hx.
    + destruct (proj1 H (or_intror (ex_intro _ x (conj eq_refl Hx))))
        as [E|[y [E Hy]]]; congruence.
    + destruct (proj2 H (or_intror (ex_intro _ x (conj eq_refl Hx))))
        as [E|[y [E Hy]]]; congruence.
Qed.

Lemma paired_inj k P P' (Q Q' : den k) :
  den_eq (paired P Q) (paired P' Q') -> den_eq P P' /\ den_eq Q Q'.
Proof.
  intros H. assert (HL : forall x, paired P Q (o_left x) <-> P x).
  { unfold paired. split; [intros [[y [E Hy]]|[y [E Hy]]]; congruence|eauto]. }
  assert (HL' : forall x, paired P' Q' (o_left x) <-> P' x).
  { unfold paired. split; [intros [[y [E Hy]]|[y [E Hy]]]; congruence|eauto]. }
  assert (HR : forall (R : den ⋆) (S : den k) x,
             paired R S (o_right (encode k x)) <-> S x).
  { unfold paired. split; [|eauto].
    intros [[y [E Hy]]|[y [E Hy]]]; [discriminate|].
    injection E as E. apply encode_injective in E. now subst. }
  split; intro x.
  - rewrite <- HL, <- HL'. apply H.
  - rewrite <- (HR P Q), <- (HR P' Q'). apply H.
Qed.

(* The constructor tag and its arguments can be recovered even from a
   partially applied constructor. Each application records one more argument. *)
Fixpoint rigid k (h : type_head) (P : den ⋆) : den k :=
  match k with
  | ⋆ => tagged h P
  | a ⇒ b => fun '(xs, y) => rigid b h (paired P (down a xs)) y
  end.

Lemma rigid_mono k h P Q : den_le P Q -> den_le (rigid k h P) (rigid k h Q).
Proof.
  revert P Q. induction k as [|a IHa b IHb]; simpl.
  - apply tagged_mono.
  - intros P Q H [xs x]. apply IHb, paired_mono; firstorder.
Qed.

Lemma rigid_valid k h P : valid (rigid k h P).
Proof.
  revert P. induction k as [|a IHa b IHb]; intros P x y H Hy.
  - simpl in H. now subst.
  - destruct x as [xs x], y as [ys y]. destruct H as [Hin Hout].
    apply (IHb (paired P (down a xs)) x y Hout).
    eapply rigid_mono; [|exact Hy].
    apply paired_mono; [firstorder|now apply down_le].
Qed.

Definition covers {I k} (P : den k) (F : I -> den k) :=
  forall x, P x -> exists i, F i x.

Lemma tagged_cover {I : Type} (i : I) h P (F : I -> den ⋆) :
  covers P F -> covers (tagged h P) (fun j => tagged h (F j)).
Proof. unfold covers, tagged. firstorder. Qed.

Lemma paired_cover {I : Type} k P F (Q : den k) G :
  covers P F -> covers Q G ->
  covers (paired P Q) (fun i : I => paired (F i) (G i)).
Proof. unfold covers, paired. firstorder. Qed.

Lemma rigid_cover {I : Type} (i : I) k h P (F : I -> den ⋆) :
  covers P F -> covers (rigid k h P) (fun j => rigid k h (F j)).
Proof.
  revert P F. induction k as [|a IHa b IHb]; simpl.
  - now apply tagged_cover.
  - intros P F HF [xs y]. apply IHb, paired_cover; [exact HF|].
    intros x Hx. now exists i.
Qed.

Lemma rigid_app a b h P (Q : den a) :
  valid Q -> den_eq (dapp (rigid (a ⇒ b) h P) Q) (rigid b h (paired P Q)).
Proof.
  intros Hv y. split.
  - intros [xs [Hin Hy]]. eapply rigid_mono; [|exact Hy].
    apply paired_mono; [firstorder|eauto using down_bound].
  - set (I := {xs : list (obs a) | forall x, In x xs -> Q x}).
    assert (i : I) by (exists nil; intros x []).
    assert (Hcov : covers (paired P Q)
       (fun j : I => paired P (down a (proj1_sig j)))).
    { apply paired_cover; [intros x Hx; now exists i|].
      intros x Hx.
      assert (Hsingle : forall z, In z [x] -> Q z) by (intros z [<-|[]]; exact Hx).
      exists (exist _ [x] Hsingle). apply down_in. now left. }
    intros Hy. destruct (rigid_cover i _ h _ _ Hcov y Hy) as [[xs Hxs] H].
    now exists xs.
Qed.

Lemma rigid_inj k h h' P Q :
  den_eq (rigid k h P) (rigid k h' Q) -> h = h' /\ den_eq P Q.
Proof.
  revert P Q. induction k as [|a IHa b IHb]; simpl; [apply tagged_inj|].
  intros P Q H. assert (E : den_eq (rigid b h (paired P (down a [])))
                                (rigid b h' (paired Q (down a [])))).
  { intro y. apply (H ([],y)). }
  destruct (IHb _ _ E) as [-> E']. apply paired_inj in E'. tauto.
Qed.

Definition tenv (D : Ctx kind) :=
  forall k (x : dom D), Intrinsic.arr D x = k -> den k.

Definition cast_den {a b} (E : a = b) (P : den a) : den b :=
  match E with eq_refl => P end.

Definition tenv_ext {D k} (r : tenv D) (P : den k) : tenv (extC k D) :=
  fun l x =>
    match x as z return Intrinsic.arr (extC k D) z = l -> den l with
    | VZ => fun E => cast_den E P
    | VS x => r l x
    end.

Definition env_le {D} (r s : tenv D) :=
  forall k x E, den_le (r k x E) (s k x E).
Definition env_cover {I D} (r : tenv D) (F : I -> tenv D) :=
  forall k x E, covers (r k x E) (fun i => F i k x E).
Definition env_valid {D} (r : tenv D) := forall k x E, valid (r k x E).

Lemma tenv_ext_le D k (r s : tenv D) P Q :
  env_le r s -> den_le P Q -> env_le (@tenv_ext D k r P) (tenv_ext s Q).
Proof. intros Hr HP l [|x] E; simpl; [destruct E|]; auto. Qed.

Lemma tenv_ext_valid D k (r : tenv D) (P : den k) :
  env_valid r -> valid P -> env_valid (tenv_ext r P).
Proof. intros Hr HP l [|x] E; simpl; [destruct E|]; auto. Qed.

Lemma tenv_ext_cover {I : Type} D k (r : tenv D) (F : I -> tenv D)
  (P : den k) (G : I -> den k) :
  env_cover r F -> covers P G ->
  env_cover (tenv_ext r P) (fun i => tenv_ext (F i) (G i)).
Proof. intros Hr HP l [|x] E; simpl; [destruct E|]; auto. Qed.

Definition constraint_den k (P Q : den k) : den ⋆ :=
  tagged (h_constraint k) (paired (paired (empty_den ⋆) P) Q).

Fixpoint eval_type {D k} (t : typ k D) : tenv D -> den k :=
  match t in type _ k return tenv D -> den k with
  | t_var k x E => fun r => r k x E
  | @t_lam _ a b t => fun r '(xs,y) => eval_type t (tenv_ext r (down a xs)) y
  | t_app s t => fun r => dapp (eval_type s r) (eval_type t r)
  | @t_ctor _ k c => fun _ => rigid k (ctor_head k c) (empty_den ⋆)
  | t_carr c t => fun r => tagged h_carr (paired (eval_constr c r) (eval_type t r))
  | t_cprod c t => fun r => tagged h_cprod (paired (eval_constr c r) (eval_type t r))
  end
with eval_constr {D} (c : constr D) : tenv D -> den ⋆ :=
  match c with c_eq k s t => fun r => constraint_den k (eval_type s r) (eval_type t r) end.

Lemma eval_mono :
  (forall D k (t : typ k D) r s, env_le r s ->
       den_le (eval_type t r) (eval_type t s)) /\
  (forall D (c : constr D) r s, env_le r s ->
       den_le (eval_constr c r) (eval_constr c s)).
Proof.
  enough (H : forall D,
    (forall k (t : typ k D) r s, env_le r s -> den_le (eval_type t r) (eval_type t s)) /\
    (forall (c : constr D) r s, env_le r s -> den_le (eval_constr c r) (eval_constr c s)))
    by (split; intros D; [apply (proj1 (H D))|apply (proj2 (H D))]).
  intro D.
  apply (type_constr_ind
    (fun D k t => forall r s : tenv D, env_le r s -> den_le (eval_type t r) (eval_type t s))
    (fun D c => forall r s : tenv D, env_le r s -> den_le (eval_constr c r) (eval_constr c s))).
  all: intros; simpl.
  - apply H.
  - intros [xs y]. apply H. apply tenv_ext_le; [assumption|firstorder].
  - apply dapp_mono; auto.
  - firstorder.
  - apply tagged_mono, paired_mono; auto.
  - apply tagged_mono, paired_mono; auto.
  - apply tagged_mono, paired_mono; auto.
    apply paired_mono; [firstorder|auto].
Qed.

Lemma eval_valid D k (t : typ k D) r :
  env_valid r -> valid (eval_type t r).
Proof.
  revert r. induction t; intros r Hr; simpl; try solve
    [apply Hr | apply dapp_valid; auto | apply rigid_valid |
     intros x y E Hy; simpl in E; now subst].
  intros [xs x] [ys y] [Hin Hout] H.
  eapply IHt; [apply tenv_ext_valid; auto using down_valid|exact Hout|].
  eapply (proj1 eval_mono); [|exact H].
  apply tenv_ext_le; [firstorder|now apply down_le].
Qed.

Lemma dapp_cover {I : Type} (i0 : I) (merge : I -> I -> I)
  a b (P : den (a ⇒ b)) (Q : den a) F G :
  (forall i j, den_le (F i) (F (merge i j))) ->
  (forall i j, den_le (G i) (G (merge i j)) /\ den_le (G j) (G (merge i j))) ->
  covers P F -> covers Q G -> covers (dapp P Q) (fun i => dapp (F i) (G i)).
Proof.
  intros HF HG HP HQ y [xs [Hin Hy]].
  assert (Hxs : forall zs, (forall x, In x zs -> Q x) ->
                   exists j, forall x, In x zs -> G j x).
  { induction zs as [|z zs IH]; intros Hz.
    - exists i0. intros x [].
    - destruct (HQ z (Hz z (or_introl eq_refl))) as [i Hi].
      destruct (IH (fun x Hx => Hz x (or_intror Hx))) as [j Hj].
      exists (merge i j). intros x [<-|Hx].
      + apply (proj1 (HG i j)), Hi.
      + exact (proj2 (HG i j) _ (Hj x Hx)). }
  destruct (HP _ Hy) as [i Hi]. destruct (Hxs _ Hin) as [j Hj].
  exists (merge i j), xs. split; [|exact (HF i j _ Hi)].
  intros x Hx. exact (proj2 (HG i j) _ (Hj x Hx)).
Qed.

(* Evaluation preserves directed unions of environments. This provides the
   finite input witness required by application in the beta rule. *)
Section DirectedEvaluation.
  Context {I : Type} (i0 : I) (merge : I -> I -> I).
  Definition directed {D} (F : I -> tenv D) :=
    forall i j, env_le (F i) (F (merge i j)) /\ env_le (F j) (F (merge i j)).

  Lemma tenv_ext_directed D k (F : I -> tenv D) (P : den k) :
    directed F -> directed (fun i => tenv_ext (F i) P).
  Proof. intros HF i j. destruct (HF i j). split; apply tenv_ext_le; firstorder. Qed.

  Lemma eval_cover :
    (forall D k (t : typ k D) r (F : I -> tenv D),
      directed F -> env_cover r F -> covers (eval_type t r) (fun i => eval_type t (F i))) /\
    (forall D (c : constr D) r (F : I -> tenv D),
      directed F -> env_cover r F -> covers (eval_constr c r) (fun i => eval_constr c (F i))).
  Proof.
    enough (H : forall D,
      (forall k (t : typ k D) r (F : I -> tenv D), directed F -> env_cover r F ->
        covers (eval_type t r) (fun i => eval_type t (F i))) /\
      (forall (c : constr D) r (F : I -> tenv D), directed F -> env_cover r F ->
        covers (eval_constr c r) (fun i => eval_constr c (F i))))
      by (split; intros D; [apply (proj1 (H D))|apply (proj2 (H D))]).
    intro D.
    apply (type_constr_ind
      (fun D k t => forall r (F : I -> tenv D), directed F -> env_cover r F ->
         covers (eval_type t r) (fun i => eval_type t (F i)))
      (fun D c => forall r (F : I -> tenv D), directed F -> env_cover r F ->
         covers (eval_constr c r) (fun i => eval_constr c (F i)))).
    all: intros; simpl.
    - now apply H0.
    - intros [xs y]. apply H; auto using tenv_ext_directed.
      apply tenv_ext_cover; auto. intros z Hz. now exists i0.
    - eapply (dapp_cover i0 merge); eauto.
      + intros i j. apply (proj1 eval_mono), H1.
      + intros i j. destruct (H1 i j). split; now apply (proj1 eval_mono).
    - intros x Hx. now exists i0.
    - apply (tagged_cover i0), paired_cover; auto.
    - apply (tagged_cover i0), paired_cover; auto.
    - apply (tagged_cover i0), paired_cover; auto.
      apply paired_cover; auto. intros x [].
  Qed.
End DirectedEvaluation.

Lemma eval_beta D a b (t : typ b (extC a D)) (r : tenv D) Q :
  valid Q ->
  den_eq (dapp (eval_type (t_lam t) r) Q) (eval_type t (tenv_ext r Q)).
Proof.
  intros Hv y. split.
  - intros [xs [Hxs Hy]]. eapply (proj1 eval_mono); [|exact Hy].
    apply tenv_ext_le; [firstorder|now apply down_bound].
  - set (I := {xs : list (obs a) | forall x, In x xs -> Q x}).
    assert (nil_I : I) by (exists nil; intros x []).
    pose (merge_I :=
      fun i j : I => exist (fun xs => forall x, In x xs -> Q x) (proj1_sig i ++ proj1_sig j)
        (fun x Hx => match in_app_or _ _ _ Hx with
                     | or_introl H => proj2_sig i x H
                     | or_intror H => proj2_sig j x H
                     end)).
    set (F := fun i : I => tenv_ext r (down a (proj1_sig i))).
    assert (Hd : directed merge_I F).
    { intros [xs Hxs] [ys Hys]. split; apply tenv_ext_le;
        try solve [firstorder]; apply down_le; intros z Hz;
        apply down_in, in_or_app; auto. }
    assert (Hc : env_cover (tenv_ext r Q) F).
    { apply tenv_ext_cover.
      - intros k x E z Hz. now exists nil_I.
      - intros x Hx. assert (Hsingle : forall z, In z [x] -> Q z)
          by (intros z [<-|[]]; exact Hx).
        exists (exist _ [x] Hsingle). apply down_in. now left. }
    intros Hy.
    destruct (proj1 (eval_cover nil_I merge_I) _ _ t _ _ Hd Hc y Hy)
      as [[xs Hxs] H]. now exists xs.
Qed.

Definition env_eq {D} (r s : tenv D) := forall k x E, den_eq (r k x E) (s k x E).

Lemma eval_type_env D k (t : typ k D) r s :
  env_eq r s -> den_eq (eval_type t r) (eval_type t s).
Proof.
  intros H x. split; apply (proj1 eval_mono); intros l z E y Hy;
    [apply (proj1 (H l z E y))|apply (proj2 (H l z E y))]; exact Hy.
Qed.

Lemma eval_constr_env D (c : constr D) r s :
  env_eq r s -> den_eq (eval_constr c r) (eval_constr c s).
Proof.
  intros H x. split; apply (proj2 eval_mono); intros l z E y Hy;
    [apply (proj1 (H l z E y))|apply (proj2 (H l z E y))]; exact Hy.
Qed.

Local Instance den_equiv k : Equivalence (@den_eq k).
Proof. split; unfold Reflexive, Symmetric, Transitive, den_eq; firstorder. Qed.

Lemma tagged_eq h P Q : den_eq P Q -> den_eq (tagged h P) (tagged h Q).
Proof. intros H x. split; apply tagged_mono; firstorder. Qed.

Lemma paired_eq k P P' (Q Q' : den k) :
  den_eq P P' -> den_eq Q Q' -> den_eq (paired P Q) (paired P' Q').
Proof. intros H H' x. split; apply paired_mono; firstorder. Qed.

Lemma rigid_eq k h P Q : den_eq P Q -> den_eq (rigid k h P) (rigid k h Q).
Proof. intros H x. split; apply rigid_mono; firstorder. Qed.

Definition rename_env {D E} (f : Intrinsic.Arr D E) (r : tenv E) : tenv D :=
  fun k x H => r k (Intrinsic.apply_arr f x) (eq_trans (Intrinsic.arr_hom f x) H).

Lemma rename_env_lift D E k (f : Intrinsic.Arr D E) (r : tenv E) P :
  env_eq (rename_env (f ↑) (@tenv_ext E k r P)) (tenv_ext (rename_env f r) P).
Proof.
  intros l [|x] H; cbn [rename_env tenv_ext lift Intrinsic.ALiftableCore_ext
      Intrinsic.extFun Intrinsic.apply_arr Intrinsic.arr_hom inc_map].
  - destruct H. reflexivity.
  - reflexivity.
Qed.

Lemma eval_rename D :
  (forall k (t : typ k D) E (f : Intrinsic.Arr D E) r,
    den_eq (eval_type (tmap f t) r) (eval_type t (rename_env f r))) /\
  (forall (c : constr D) E (f : Intrinsic.Arr D E) r,
    den_eq (eval_constr (cmap f c) r) (eval_constr c (rename_env f r))).
Proof.
  apply (type_constr_ind
    (fun D k t => forall E (f : Intrinsic.Arr D E) r,
        den_eq (eval_type (tmap f t) r) (eval_type t (rename_env f r)))
    (fun D c => forall E (f : Intrinsic.Arr D E) r,
        den_eq (eval_constr (cmap f c) r) (eval_constr c (rename_env f r)))).
  all: intros; simpl; try solve
    [reflexivity | apply dapp_eq; auto |
     apply tagged_eq, paired_eq; auto |
     apply tagged_eq, paired_eq; [apply paired_eq; auto; reflexivity|auto]].
  intros [xs y]. etransitivity; [apply H|].
  apply eval_type_env, rename_env_lift.
Qed.

Lemma rename_shift D k (r : tenv D) P :
  env_eq (@rename_env D (extC k D) mk_shift (tenv_ext r P)) r.
Proof.
  intros l x H.
  change (den_eq (r l x (eq_trans (Intrinsic.ShiftableCore_ext_obligation_1 k D x) H))
                 (r l x H)).
  assert (E : eq_trans (Intrinsic.ShiftableCore_ext_obligation_1 k D x) H = H)
    by apply UIP.
  now rewrite E.
Qed.

Lemma eval_shift D a k (t : typ k D) r (P : den a) :
  den_eq (eval_type (shift t) (tenv_ext r P)) (eval_type t r).
Proof.
  etransitivity; [apply (proj1 (eval_rename D))|].
  apply eval_type_env, rename_shift.
Qed.

Lemma eval_cshift D a (c : constr D) r (P : den a) :
  den_eq (eval_constr (shift c) (tenv_ext r P)) (eval_constr c r).
Proof.
  etransitivity; [apply (proj2 (eval_rename D))|].
  apply eval_constr_env, rename_shift.
Qed.

Definition bind_env {D E}
  (f : @Intrinsic.Sub kind typ IPC_typ D E) (r : tenv E) : tenv D :=
  fun k x H => eval_type (Intrinsic.apply_sub f k x H) r.

Lemma bind_env_lift D E k (f : @Intrinsic.Sub kind typ IPC_typ D E) (r : tenv E) P :
  env_eq (bind_env (f ↑) (@tenv_ext E k r P)) (tenv_ext (bind_env f r) P).
Proof.
  intros l [|x] H.
  - destruct H. reflexivity.
  - apply eval_shift.
Qed.

Lemma eval_bind D :
  (forall k (t : typ k D) E (f : @Intrinsic.Sub kind typ IPC_typ D E) r,
    den_eq (eval_type (tbind f t) r) (eval_type t (bind_env f r))) /\
  (forall (c : constr D) E (f : @Intrinsic.Sub kind typ IPC_typ D E) r,
    den_eq (eval_constr (cbind f c) r) (eval_constr c (bind_env f r))).
Proof.
  apply (type_constr_ind
    (fun D k t => forall E (f : @Intrinsic.Sub kind typ IPC_typ D E) r,
        den_eq (eval_type (tbind f t) r) (eval_type t (bind_env f r)))
    (fun D c => forall E (f : @Intrinsic.Sub kind typ IPC_typ D E) r,
        den_eq (eval_constr (cbind f c) r) (eval_constr c (bind_env f r)))).
  all: intros; simpl; try solve
    [reflexivity | apply dapp_eq; auto |
     apply tagged_eq, paired_eq; auto |
     apply tagged_eq, paired_eq; [apply paired_eq; auto; reflexivity|auto]].
  intros [xs y]. etransitivity; [apply H|].
  apply eval_type_env, bind_env_lift.
Qed.

Lemma eval_subst D a b (t : typ b (extC a D)) (s : typ a D) r :
  den_eq (eval_type (subst t s) r) (eval_type t (tenv_ext r (eval_type s r))).
Proof.
  transitivity (eval_type t (bind_env (mk_subst s) r)).
  - apply (proj1 (eval_bind _)).
  - apply eval_type_env. intros k [|x] E; [destruct E|]; reflexivity.
Qed.

Lemma eval_eta D a b (t : typ (a ⇒ b) D) r :
  env_valid r ->
  den_eq (eval_type t r) (eval_type (t_lam (t_app (shift t) 0ᵛ)) r).
Proof.
  intros Hr [xs y]. simpl. symmetry.
  transitivity (dapp (eval_type t r) (down a xs) y).
  - apply dapp_eq; [apply eval_shift|reflexivity].
  - apply dapp_down, eval_valid, Hr.
Qed.

Lemma eval_tctd D k (t : typ k D) l (c : tctor l) r :
  env_valid r -> tctd t c ->
  exists P, den_eq (eval_type t r) (rigid k (ctor_head l c) P).
Proof.
  intros Hr H. induction H.
  - exists (empty_den ⋆). reflexivity.
  - destruct IHtctd as [P HP]. exists (paired P (eval_type τ r)).
    simpl. etransitivity; [apply dapp_eq; [exact HP|reflexivity]|].
    apply rigid_app, eval_valid, Hr.
Qed.

Definition holds {D} (r : tenv D) (c : constr D) :=
  match c with c_eq _ s t => den_eq (eval_type s r) (eval_type t r) end.

Lemma constraint_den_inj k l (P Q : den k) (R S : den l) :
  den_eq (constraint_den k P Q) (constraint_den l R S) ->
  den_eq P Q -> den_eq R S.
Proof.
  intros H HP. apply tagged_inj in H as [E H]. injection E as E. subst l.
  apply paired_inj in H as [H Hout]. apply paired_inj in H as [_ Hin].
  now transitivity P; [symmetry|transitivity Q].
Qed.

Lemma holds_eq D E (r : tenv D) (s : tenv E) c d :
  den_eq (eval_constr c r) (eval_constr d s) -> holds r c -> holds s d.
Proof. destruct c, d; apply constraint_den_inj. Qed.

Lemma holds_shift D k (r : tenv D) P (c : constr D) :
  holds r c -> holds (@tenv_ext D k r P) (shift c).
Proof. apply holds_eq. symmetry. apply eval_cshift. Qed.

Lemma eval_ctor_app_inj D a b k (c : tctor k)
  (s s' : typ (a ⇒ b) D) (t t' : typ a D) r :
  env_valid r -> tctd s c -> tctd s' c ->
  den_eq (eval_type (s t) r) (eval_type (s' t') r) ->
  den_eq (eval_type s r) (eval_type s' r) /\ den_eq (eval_type t r) (eval_type t' r).
Proof.
  intros Hr Hs Hs' E.
  destruct (eval_tctd _ _ _ _ _ r Hr Hs) as [P HP].
  destruct (eval_tctd _ _ _ _ _ r Hr Hs') as [Q HQ].
  assert (H : den_eq (rigid b (ctor_head k c) (paired P (eval_type t r)))
                     (rigid b (ctor_head k c) (paired Q (eval_type t' r)))).
  { transitivity (eval_type (s t) r).
    - symmetry. cbn [eval_type]. etransitivity.
      + apply dapp_eq; [exact HP|reflexivity].
      + apply rigid_app, eval_valid, Hr.
    - etransitivity; [exact E|]. cbn [eval_type]. etransitivity.
      + apply dapp_eq; [exact HQ|reflexivity].
      + apply rigid_app, eval_valid, Hr. }
  apply rigid_inj in H as [_ H]. apply paired_inj in H as [H1 H2].
  split; [|exact H2].
  etransitivity; [exact HP|]. etransitivity; [exact (rigid_eq _ _ _ _ H1)|].
  symmetry. exact HQ.
Qed.

(* A constraint denotes equality of its two interpretations. An enclosing
   constrained type records both interpretations, so injectivity can transfer
   evidence for the constraint even when its syntax changes. *)
Lemma proves_valid D (Psi : list (constr D)) c :
  Psi ⊩ c ->
  forall r, env_valid r -> (forall d, In d Psi -> holds r d) -> holds r c.
Proof.
  intro H. induction H; intros r Hr Ha; simpl in *.
  - now apply Ha.
  - replace EQ₂ with EQ₁ by apply UIP. reflexivity.
  - intros [xs y]. apply IHtproves_i.
    + apply tenv_ext_valid; auto using down_valid.
    + intros d Hd. apply in_map_iff in Hd as [c [<- Hc]].
      apply holds_shift, Ha, Hc.
  - apply dapp_eq; auto.
  - reflexivity.
  - apply tagged_eq, paired_eq; [reflexivity|auto].
  - apply tagged_eq, paired_eq; [reflexivity|auto].
  - symmetry. auto.
  - etransitivity; eauto.
  - now apply eval_eta.
  - etransitivity; [apply eval_beta, eval_valid, Hr|].
    symmetry. apply eval_subst.
  - exact (proj2 (eval_ctor_app_inj _ _ _ _ _ _ _ _ _ r Hr HI₁ HI₂
                    (IHtproves_i r Hr Ha))).
  - exact (proj1 (eval_ctor_app_inj _ _ _ _ _ _ _ _ _ r Hr HI₁ HI₂
                    (IHtproves_i r Hr Ha))).
  - specialize (IHtproves_i r Hr Ha). apply tagged_inj in IHtproves_i as [_ E].
    apply paired_inj in E. tauto.
  - specialize (IHtproves_i r Hr Ha). apply tagged_inj in IHtproves_i as [_ E].
    apply paired_inj in E. tauto.
  - specialize (IHtproves_i1 r Hr Ha). apply tagged_inj in IHtproves_i1 as [_ E].
    apply paired_inj in E as [E _]. eapply holds_eq; eauto.
  - specialize (IHtproves_i1 r Hr Ha). apply tagged_inj in IHtproves_i1 as [_ E].
    apply paired_inj in E as [E _]. eapply holds_eq; eauto.
Qed.

Lemma cdiscr_self k (c : tctor k) : ~ cdiscrK c c.
Proof.
  unfold cdiscrK. destruct (kindEqDec.eq_dec k k) as [E|NE].
  - replace E with (@eq_refl kind k) by apply UIP. simpl.
    intro H. inversion H.
  - contradiction.
Qed.

Lemma cdiscr_heads k l (c : tctor k) (d : tctor l) :
  cdiscrK c d -> ctor_head k c <> ctor_head l d.
Proof.
  destruct c, d; intros H E; simpl in E; try discriminate;
    try (injection E as E; subst); eapply cdiscr_self; exact H.
Qed.

Lemma discr_invalid D (c : constr D) r :
  env_valid r -> tdiscr c -> ~ holds r c.
Proof.
  intros Hr H. destruct H; simpl; intro E.
  { destruct (eval_tctd _ _ _ _ _ r Hr HI₁) as [P HP].
    destruct (eval_tctd _ _ _ _ _ r Hr HI₂) as [Q HQ].
    assert (F : den_eq (rigid κ (ctor_head κ₁ c₁) P) (rigid κ (ctor_head κ₂ c₂) Q)).
    { transitivity (eval_type τ₁ r); [symmetry; exact HP|].
      transitivity (eval_type τ₂ r); [exact E|exact HQ]. }
    apply rigid_inj in F as [F _]. exact (cdiscr_heads _ _ _ _ HD F). }
  all: try match goal with
       | H : tctd ?t ?c |- _ =>
           destruct (eval_tctd _ _ _ _ _ r Hr H) as [P HP];
           cbn [rigid] in HP;
           first [assert (F : den_eq (tagged h_carr _) (tagged _ P))
               by (etransitivity; [exact E|exact HP])
           | assert (F : den_eq (tagged _ P) (tagged h_carr _))
               by (etransitivity; [symmetry; exact HP|exact E])
           | assert (F : den_eq (tagged h_cprod _) (tagged _ P))
               by (etransitivity; [exact E|exact HP])
           | assert (F : den_eq (tagged _ P) (tagged h_cprod _))
               by (etransitivity; [symmetry; exact HP|exact E])];
           apply tagged_inj in F as [F _]; destruct c; discriminate
       end.
  all: apply tagged_inj in E as [E _]; discriminate.
Qed.

(* Substitution into an erased term commutes with extending its closing environment. *)
Scheme expr_ind' := Induction for expr Sort Prop
with value_ind' := Induction for value Sort Prop.
Combined Scheme expr_value_ind from expr_ind', value_ind'.

Definition ren {A B : Set} (f : A -> B) : Binding.Set.Arr A B :=
  {| Binding.Set.apply_arr := f |}.
Definition sub_val {A B : Set} (f : A -> value B) : @Binding.Set.Sub value SPC_val A B :=
  {| Binding.Set.apply_sub := f |}.
Definition up_ren {A B : Set} (f : A -> B) : inc A -> inc B := inc_map f.
Definition up_val {A B : Set} (f : A -> value B) : inc A -> value (inc B) :=
  fun x => match x with VZ => v_var VZ | VS x => vmap (ren VS) (f x) end.

Lemma term_rename_comp A :
  (forall e : expr A, forall (B C : Set) (f : B -> C) (g : A -> B),
    emap (ren f) (emap (ren g) e) = emap (ren (fun x => f (g x))) e) /\
  (forall v : value A, forall (B C : Set) (f : B -> C) (g : A -> B),
    vmap (ren f) (vmap (ren g) v) = vmap (ren (fun x => f (g x))) v).
Proof.
  (* Pointwise equal renamings also agree below binders. *)
  enough (H : forall A,
    (forall e : expr A, forall (B C : Set) (f : B -> C) (g : A -> B) h,
      (forall x, f (g x) = h x) ->
      emap (ren f) (emap (ren g) e) = emap (ren h) e) /\
    (forall v : value A, forall (B C : Set) (f : B -> C) (g : A -> B) h,
      (forall x, f (g x) = h x) ->
      vmap (ren f) (vmap (ren g) v) = vmap (ren h) v)).
  { split; intros; [eapply (proj1 (H A))|eapply (proj2 (H A))]; reflexivity. }
  intro X.
  apply (expr_value_ind
    (fun A e => forall (B C : Set) (f : B -> C) (g : A -> B) h,
      (forall x, f (g x) = h x) ->
      emap (ren f) (emap (ren g) e) = emap (ren h) e)
    (fun A v => forall (B C : Set) (f : B -> C) (g : A -> B) h,
      (forall x, f (g x) = h x) ->
      vmap (ren f) (vmap (ren g) v) = vmap (ren h) v)).
  all: intros; cbn [emap vmap]; try reflexivity;
    f_equal; try solve [auto | eapply H | eapply H0 | eapply H1].
  all: first [eapply H | eapply H0 | eapply H1];
    intros x; repeat (destruct x as [|x]; [reflexivity|]); cbn [fmap Binding.Set.IncMap Binding.Set.incFun inc_map lift Binding.Set.ALiftableCore_inc Binding.Set.apply_arr ren]; repeat f_equal; auto.
Qed.

Lemma term_bind_rename A :
  (forall e : expr A, forall (B C : Set) (f : B -> value C) (g : A -> B) h,
    (forall x, f (g x) = h x) ->
    ebind (sub_val f) (emap (ren g) e) = ebind (sub_val h) e) /\
  (forall v : value A, forall (B C : Set) (f : B -> value C) (g : A -> B) h,
    (forall x, f (g x) = h x) ->
    vbind (sub_val f) (vmap (ren g) v) = vbind (sub_val h) v).
Proof.
  apply (expr_value_ind
    (fun A e => forall (B C : Set) (f : B -> value C) (g : A -> B) h,
      (forall x, f (g x) = h x) ->
      ebind (sub_val f) (emap (ren g) e) = ebind (sub_val h) e)
    (fun A v => forall (B C : Set) (f : B -> value C) (g : A -> B) h,
      (forall x, f (g x) = h x) ->
      vbind (sub_val f) (vmap (ren g) v) = vbind (sub_val h) v)).
  all: intros; cbn [emap vmap ebind vbind]; try reflexivity;
    try solve [f_equal; auto];
    f_equal; eauto 6 using f_equal.
  all: first [eapply H | eapply H0 | eapply H1];
    intros x; repeat (destruct x as [|x]; [reflexivity|]); cbn [fmap Binding.Set.IncMap Binding.Set.incFun inc_map lift Binding.Set.ALiftableCore_inc Binding.Set.apply_arr ren Binding.Set.SLiftableCore_inc Binding.Set.apply_sub sub_val]; repeat f_equal; auto.
Qed.

Lemma term_rename_bind A :
  (forall e : expr A, forall (B C : Set) (f : B -> C) (g : A -> value B) h,
    (forall x, vmap (ren f) (g x) = h x) ->
    emap (ren f) (ebind (sub_val g) e) = ebind (sub_val h) e) /\
  (forall v : value A, forall (B C : Set) (f : B -> C) (g : A -> value B) h,
    (forall x, vmap (ren f) (g x) = h x) ->
    vmap (ren f) (vbind (sub_val g) v) = vbind (sub_val h) v).
Proof.
  assert (Hlift : forall (A B C : Set) (f : B -> C) (g : A -> value B) h,
      (forall x, vmap (ren f) (g x) = h x) ->
      forall x, vmap (ren (up_ren f)) (up_val g x) = up_val h x).
  { intros X B C f g h H [|x]; [reflexivity|].
    cbn [up_val]. rewrite <- H. rewrite !(proj2 (term_rename_comp _)).
    reflexivity. }
  apply (expr_value_ind
    (fun A e => forall (B C : Set) (f : B -> C) (g : A -> value B) h,
      (forall x, vmap (ren f) (g x) = h x) ->
      emap (ren f) (ebind (sub_val g) e) = ebind (sub_val h) e)
    (fun A v => forall (B C : Set) (f : B -> C) (g : A -> value B) h,
      (forall x, vmap (ren f) (g x) = h x) ->
      vmap (ren f) (vbind (sub_val g) v) = vbind (sub_val h) v)).
  all: intros; cbn [emap vmap ebind vbind]; try reflexivity;
    try solve [f_equal; auto].
  all: f_equal; first [eapply H | eapply H0 | eapply H1]; eauto using Hlift.
  all: change (forall x, vmap (ren (up_ren (up_ren f))) (up_val (up_val g) x) =
                        up_val (up_val h) x).
  all: apply Hlift, Hlift, H0.
Qed.

Lemma term_bind_comp A :
  (forall e : expr A, forall (B C : Set) (f : B -> value C) (g : A -> value B) h,
    (forall x, vbind (sub_val f) (g x) = h x) ->
    ebind (sub_val f) (ebind (sub_val g) e) = ebind (sub_val h) e) /\
  (forall v : value A, forall (B C : Set) (f : B -> value C) (g : A -> value B) h,
    (forall x, vbind (sub_val f) (g x) = h x) ->
    vbind (sub_val f) (vbind (sub_val g) v) = vbind (sub_val h) v).
Proof.
  assert (Hlift : forall (A B C : Set) (f : B -> value C) (g : A -> value B) h,
      (forall x, vbind (sub_val f) (g x) = h x) ->
      forall x, vbind (sub_val (up_val f)) (up_val g x) = up_val h x).
  { intros X B C f g h H [|x]; [reflexivity|].
    cbn [up_val]. rewrite <- H.
    transitivity (vbind (sub_val (fun z => vmap (ren VS) (f z))) (g x)).
    - apply (proj2 (term_bind_rename _)). reflexivity.
    - symmetry. apply (proj2 (term_rename_bind _)). reflexivity. }
  apply (expr_value_ind
    (fun A e => forall (B C : Set) (f : B -> value C) (g : A -> value B) h,
      (forall x, vbind (sub_val f) (g x) = h x) ->
      ebind (sub_val f) (ebind (sub_val g) e) = ebind (sub_val h) e)
    (fun A v => forall (B C : Set) (f : B -> value C) (g : A -> value B) h,
      (forall x, vbind (sub_val f) (g x) = h x) ->
      vbind (sub_val f) (vbind (sub_val g) v) = vbind (sub_val h) v)).
  all: intros; cbn [emap vmap ebind vbind]; try reflexivity;
    try solve [f_equal; auto].
  all: f_equal; first [eapply H | eapply H0 | eapply H1]; eauto using Hlift.
  all: change (forall x, vbind (sub_val (up_val (up_val f))) (up_val (up_val g) x) =
                        up_val (up_val h) x).
  all: apply Hlift, Hlift, H0.
Qed.

Lemma term_bind_id A :
  (forall e : expr A, forall f : A -> value A, (forall x, f x = v_var x) ->
    ebind (sub_val f) e = e) /\
  (forall v : value A, forall f : A -> value A, (forall x, f x = v_var x) ->
    vbind (sub_val f) v = v).
Proof.
  assert (Hlift : forall (A : Set) (f : A -> value A), (forall x, f x = v_var x) ->
         forall x, up_val f x = v_var x).
  { intros X f H [|x]; cbn [up_val]; [reflexivity|now rewrite H]. }
  apply (expr_value_ind
    (fun A e => forall f : A -> value A, (forall x, f x = v_var x) ->
      ebind (sub_val f) e = e)
    (fun A v => forall f : A -> value A, (forall x, f x = v_var x) ->
      vbind (sub_val f) v = v)).
  all: intros; cbn [ebind vbind]; try reflexivity; f_equal; eauto using Hlift.
  apply (H (up_val (up_val f))), Hlift, Hlift, H0.
Qed.

Lemma subst_shift_value {B : Set} (v w : value B) :
  vbind (mk_subst (Inc := inc) w) (shift v) = v.
Proof.
  transitivity (vbind (sub_val (@v_var B)) v).
  - apply (proj2 (term_bind_rename _)). reflexivity.
  - apply (proj2 (term_bind_id _)). reflexivity.
Qed.

Lemma closing_subst {A B : Set} (e : expr (inc A)) (f : A -> value B) v :
  subst (Inc := inc) (ebind ((sub_val f) ↑) e) v =
  ebind (sub_val (f ▹ v)) e.
Proof.
  apply (proj1 (term_bind_comp _)). intros [|x]; [reflexivity|].
  apply subst_shift_value.
Qed.

Lemma closing_subst_rec {A : Set} (e : expr (inc (inc A)))
  (f : A -> value ∅) (self v : value ∅) :
  subst (Inc := inc) (subst (Inc := inc) (ebind (((sub_val f) ↑) ↑) e)
    (shift v)) self = ebind (sub_val (f ▹ self ▹ v)) e.
Proof.
  change (subst (Inc := inc) (subst (Inc := inc)
    (ebind (sub_val (up_val f) ↑) e) (shift v)) self =
    ebind (sub_val (f ▹ self ▹ v)) e).
  rewrite (closing_subst e (up_val f) (shift v)).
  apply (proj1 (term_bind_comp _)).
  intros [|[|x]]; [apply subst_shift_value|reflexivity|apply subst_shift_value].
Qed.

Definition ty_bin (h : type_head) (A B : den ⋆) : den ⋆ :=
  tagged h (paired (paired (empty_den ⋆) A) B).
Definition ty_quant k (h : type_head) (F : den (k ⇒ ⋆)) : den ⋆ :=
  tagged h (paired (empty_den ⋆) F).

Lemma eval_bin D r h (c : tctor (⋆ ⇒ ⋆ ⇒ ⋆)) (A B : typ ⋆ D) :
  ctor_head _ c = h -> env_valid r ->
  den_eq (eval_type (c A B) r) (ty_bin h (eval_type A r) (eval_type B r)).
Proof.
  intros <- Hr. cbn [eval_type]. etransitivity.
  - apply dapp_eq; [apply rigid_app, eval_valid, Hr|reflexivity].
  - apply rigid_app, eval_valid, Hr.
Qed.

Lemma eval_quant D k r h (c : tctor ((k ⇒ ⋆) ⇒ ⋆)) (t : typ ⋆ (extC k D)) :
  ctor_head _ c = h -> env_valid r ->
  den_eq (eval_type (c (t_lam t)) r) (ty_quant k h (eval_type (t_lam t) r)).
Proof. intros <- Hr. apply rigid_app. exact (eval_valid D (k ⇒ ⋆) (t_lam t) r Hr). Qed.

Lemma ty_bin_inj h A B A' B' :
  den_eq (ty_bin h A B) (ty_bin h A' B') -> den_eq A A' /\ den_eq B B'.
Proof.
  intros E. apply tagged_inj in E as [_ E]. apply paired_inj in E as [E H].
  apply paired_inj in E as [_ E]. auto.
Qed.

(* A recursive constructor can have a higher result kind. The spine
   applies the same arguments before and after unfolding its body. *)
Fixpoint spine (k : kind) : Type :=
  match k with ⋆ => unit | a ⇒ b => (den a * spine b)%type end.

Fixpoint spine_valid (k : kind) : spine k -> Prop :=
  match k with ⋆ => fun _ => True | a ⇒ b => fun '(P,tail) => valid P /\ spine_valid b tail end.

Fixpoint spine_eq (k : kind) : spine k -> spine k -> Prop :=
  match k with
  | ⋆ => fun _ _ => True
  | a ⇒ b => fun '(P,tail) '(Q,T) => den_eq P Q /\ spine_eq b tail T
  end.

Fixpoint spine_app (k : kind) : den k -> spine k -> den ⋆ :=
  match k with
  | ⋆ => fun P _ => P
  | a ⇒ b => fun P '(Q,tail) => spine_app b (dapp P Q) tail
  end.

Fixpoint rigid_spine (k : kind) (h : type_head) (P : den ⋆) : spine k -> den ⋆ :=
  match k with
  | ⋆ => fun _ => tagged h P
  | a ⇒ b => fun '(Q,tail) => rigid_spine b h (paired P Q) tail
  end.

Lemma spine_app_eq k (P Q : den k) (S T : spine k) :
  den_eq P Q -> spine_eq k S T -> den_eq (spine_app k P S) (spine_app k Q T).
Proof.
  induction k as [|a IHa b IHb]; simpl; auto.
  destruct S as [R S], T as [R' T]. intros E [ER ES]. apply IHb; auto using dapp_eq.
Qed.

Lemma spine_eq_refl k (S : spine k) : spine_eq k S S.
Proof.
  induction k as [|a IHa b IHb]; simpl; [exact I|].
  destruct S. split; [reflexivity|apply IHb].
Qed.

Lemma rigid_spine_app k h P S :
  spine_valid k S -> den_eq (spine_app k (rigid k h P) S) (rigid_spine k h P S).
Proof.
  revert P S. induction k as [|a IHa b IHb]; simpl; [reflexivity|].
  intros P [Q S] [Hv Hs]. etransitivity.
  - apply spine_app_eq; [now apply rigid_app|apply spine_eq_refl].
  - now apply IHb.
Qed.

Lemma rigid_spine_elim k h P S :
  exists Q, den_eq (rigid_spine k h P S) (tagged h Q).
Proof.
  revert P S. induction k as [|a IHa b IHb]; simpl.
  - intros. eexists. reflexivity.
  - intros P [Q S]. apply IHb.
Qed.

Lemma rigid_spine_inj k h P Q S T :
  den_eq (rigid_spine k h P S) (rigid_spine k h Q T) ->
  den_eq P Q /\ spine_eq k S T.
Proof.
  revert P Q S T. induction k as [|a IHa b IHb]; simpl.
  - intros P Q S T H. apply tagged_inj in H. tauto.
  - intros P Q [R S] [R' T] H. apply IHb in H as [H ES].
    apply paired_inj in H. tauto.
Qed.

Definition roll_head k (F : den (k ⇒ k)) : den k :=
  rigid k (h_rec k) (paired (empty_den ⋆) F).
Definition roll_type k (F : den (k ⇒ k)) (S : spine k) : den ⋆ :=
  rigid_spine k (h_rec k) (paired (empty_den ⋆) F) S.
Definition roll_body k (F : den (k ⇒ k)) (S : spine k) : den ⋆ :=
  spine_app k (dapp F (roll_head k F)) S.

Lemma roll_inj k l (F : den (k ⇒ k)) (G : den (l ⇒ l)) S T :
  den_eq (roll_type k F S) (roll_type l G T) ->
  den_eq (roll_body k F S) (roll_body l G T).
Proof.
  intro H. assert (k = l) as ->.
  { destruct (rigid_spine_elim k (h_rec k) (paired (empty_den ⋆) F) S) as [P HP].
    destruct (rigid_spine_elim l (h_rec l) (paired (empty_den ⋆) G) T) as [Q HQ].
    assert (E : den_eq (tagged (h_rec k) P) (tagged (h_rec l) Q)).
    { transitivity (roll_type k F S); [symmetry; exact HP|].
      etransitivity; [exact H|exact HQ]. }
    apply tagged_inj in E as [E _]. now injection E. }
  apply rigid_spine_inj in H as [H HS]. apply paired_inj in H as [_ HF].
  apply spine_app_eq; [|exact HS].
  apply dapp_eq; [exact HF|]. apply rigid_eq, paired_eq; [reflexivity|exact HF].
Qed.

Lemma eval_rel_app D k (P Q : typ k D) l s t :
  rel_app k P Q l s t ->
  forall r, env_valid r ->
  forall tail : spine l, spine_valid l tail ->
  exists S : spine k, spine_valid k S /\
    den_eq (spine_app l (eval_type s r) tail) (spine_app k (eval_type P r) S) /\
    den_eq (spine_app l (eval_type t r) tail) (spine_app k (eval_type Q r) S).
Proof.
  intro H. induction H; intros r Hr tail Htail.
  - exists tail. split; [exact Htail|split; reflexivity].
  - apply (IHrel_app r Hr (eval_type τ r, tail)).
    split; auto using eval_valid.
Qed.

Lemma eval_roll D k (t : typ k (extC k D)) s u :
  rel_app k (rec_type D k t) (subst t (rec_type D k t)) ⋆ s u ->
  forall r, env_valid r ->
  exists S : spine k,
    den_eq (eval_type s r) (roll_type k (eval_type (t_lam t) r) S) /\
    den_eq (eval_type u r) (roll_body k (eval_type (t_lam t) r) S).
Proof.
  intros H r Hr. pose proof (eval_rel_app _ _ _ _ _ _ _ H r Hr tt I)
    as [S [HS [Hs Hu]]]. exists S.
  assert (E : den_eq (eval_type (rec_type D k t) r) (roll_head k (eval_type (t_lam t) r))).
  { apply rigid_app. exact (eval_valid D (k ⇒ k) (t_lam t) r Hr). }
  split.
  - etransitivity; [exact Hs|]. etransitivity; [apply spine_app_eq; [exact E|apply spine_eq_refl]|].
    now apply rigid_spine_app.
  - etransitivity; [exact Hu|]. apply spine_app_eq; [|apply spine_eq_refl].
    etransitivity; [apply eval_subst|].
    symmetry. transitivity (dapp (eval_type (t_lam t) r) (eval_type (rec_type D k t) r)).
    + apply dapp_eq; [reflexivity|symmetry; exact E].
    + apply eval_beta, eval_valid, Hr.
Qed.

(* The index bounds the number of reductions that must remain possible.
   A value retains its obligations from all smaller indices. *)
Definition val_pred := den ⋆ -> value ∅ -> Prop.
Definition expr_pred := den ⋆ -> expr ∅ -> Prop.
Definition ty_unit := tagged h_unit (empty_den ⋆).
Definition ty_void := tagged h_void (empty_den ⋆).
Definition ty_constrained h C B := tagged h (paired C (B : den ⋆)).

Definition value_clause (V : val_pred) (E : expr_pred) : val_pred :=
  fun T v =>
    match v with
    | v_var x => match x with end
    | v_unit => den_eq T ty_unit
    | v_lam e => exists A B, den_eq T (ty_bin h_arr A B) /\
                 forall w, V A w -> E B (subst (Inc := inc) e w)
    | v_fix e => exists A B, den_eq T (ty_bin h_arr A B) /\
                 forall w, V A w ->
                 E B (subst (Inc := inc) (subst (Inc := inc) e (shift w)) (v_fix e))
    | v_pair v w => exists A B, den_eq T (ty_bin h_prod A B) /\ V A v /\ V B w
    | v_inj a v => exists A B, den_eq T (ty_bin h_sum A B) /\
                 V (match a with L => A | R => B end) v
    | v_tlam e => exists k F, den_eq T (ty_quant k (h_all k) F) /\
                 forall Q, valid Q -> E (dapp F Q) e
    | v_pack v => exists k F (Q : den k), den_eq T (ty_quant k (h_xist k) F) /\
                 valid Q /\ V (dapp F Q) v
    | v_roll v => exists k F S, den_eq T (roll_type k F S) /\ V (roll_body k F S) v
    | v_lamC e => exists k (P Q : den k) B,
                 den_eq T (ty_constrained h_carr (constraint_den k P Q) B) /\
                 (den_eq P Q -> E B e)
    | v_withC v => exists k (P Q : den k) B,
                 den_eq T (ty_constrained h_cprod (constraint_den k P Q) B) /\
                 den_eq P Q /\ V B v
    end.

Fixpoint relations n : val_pred * expr_pred :=
  match n with
  | 0 => (fun _ _ => True, fun _ _ => True)
  | S m =>
      let V := fst (relations m) in
      let E := snd (relations m) in
      let W := fun T v => V T v /\ value_clause V E T v in
      (W, fun T e => (exists v, e = e_val v /\ W T v) \/
                     (exists e', e ↦ e' /\ E T e'))
  end.

Definition rel_v n := fst (relations n).
Definition rel_e n := snd (relations n).

Lemma rel_v_intro n T v :
  rel_v n T v -> value_clause (rel_v n) (rel_e n) T v -> rel_v (S n) T v.
Proof. now split. Qed.

Lemma rel_v_clause n T v :
  rel_v (S n) T v -> value_clause (rel_v n) (rel_e n) T v.
Proof. intros [_ H]. exact H. Qed.

Lemma rel_v_prev n T v : rel_v (S n) T v -> rel_v n T v.
Proof. intros [H _]. exact H. Qed.

Lemma rel_e_val n T v : rel_v n T v -> rel_e n T (e_val v).
Proof. destruct n; [exact (fun _ => I)|]. intro H. left. now exists v. Qed.

Lemma rel_e_step n T e e' : e ↦ e' -> rel_e n T e' -> rel_e (S n) T e.
Proof. intros H E. right. now exists e'. Qed.

Lemma rel_v_le n m T v : m <= n -> rel_v n T v -> rel_v m T v.
Proof. induction 1; auto using rel_v_prev. Qed.

Lemma rel_v_eq n T U v : den_eq T U -> rel_v n T v -> rel_v n U v.
Proof.
  intros EQ. induction n; [trivial|].
  intros [HV HC]. apply rel_v_intro; [now apply IHn|].
  destruct v; cbn [value_clause] in *; try (destruct x).
  all: unfold value_clause;
    repeat match type of HC with exists _, _ => destruct HC as [? HC]; eexists end;
    try destruct HC as [HC Hrest]; try (split; [|exact Hrest]);
    etransitivity; [symmetry; exact EQ|exact HC].
Qed.

Lemma rel_e_eq n T U e : den_eq T U -> rel_e n T e -> rel_e n U e.
Proof.
  intros EQ. revert e. induction n; [trivial|].
  intros e [[v [-> H]]|[e' [H E]]].
  - apply rel_e_val. eauto using rel_v_eq.
  - eapply rel_e_step; eauto.
Qed.

Lemma roll_matches_head k (F : den (k ⇒ k)) S :
  exists P, den_eq (roll_type k F S) (tagged (h_rec k) P).
Proof. apply rigid_spine_elim. Qed.

Lemma different_head h h' P Q :
  den_eq (tagged h P) (tagged h' Q) -> h <> h' -> False.
Proof. intros H Hd. apply tagged_inj in H. tauto. Qed.

Local Ltac inspect_related_value H :=
  apply rel_v_clause in H;
  match type of H with
  | value_clause _ _ _ ?v => destruct v
  end;
  cbn [value_clause] in H;
  try solve [match goal with x : ∅ |- _ => destruct x end];
  repeat match type of H with exists _, _ => destruct H as [? H] end;
  try (destruct H as [H ?]);
  try solve
    [exfalso; eapply different_head; [exact H|discriminate]
    | match type of H with den_eq _ (roll_type ?k ?F ?S) =>
        destruct (roll_matches_head k F S) as [? ?];
        exfalso; eapply different_head;
          [etransitivity; [exact H|eassumption]|discriminate]
      end
    | match type of H with den_eq (roll_type ?k ?F ?S) _ =>
        destruct (roll_matches_head k F S) as [? ?];
        exfalso; eapply different_head;
          [etransitivity; [symmetry; eassumption|exact H]|discriminate]
      end].

Lemma rel_app n A B v w :
  rel_v (S n) (ty_bin h_arr A B) v ->
  rel_v n A w -> rel_e (S n) B (v w).
Proof.
  intros H Hw. inspect_related_value H; apply ty_bin_inj in H as [HA HB].
  - eapply rel_e_step; [apply LamBetaE|].
    eapply rel_e_eq; [symmetry; exact HB|].
    eauto using rel_v_eq.
  - eapply rel_e_step; [apply LamBetaRec|].
    eapply rel_e_eq; [symmetry; exact HB|].
    eauto using rel_v_eq.
Qed.

Lemma rel_tapp n k F Q v :
  valid Q -> rel_v (S n) (ty_quant k (h_all k) F) v ->
  rel_e (S n) (dapp F Q) (e_tapp v).
Proof.
  intros Hv H. inspect_related_value H.
  apply tagged_inj in H as [E H]. injection E as E. subst.
  apply paired_inj in H as [_ H].
  eapply rel_e_step; [apply LamBetaT|].
  eapply rel_e_eq; [apply dapp_eq; [symmetry; exact H|reflexivity]|eauto].
Qed.

Lemma rel_proj n A B v a :
  rel_v (S n) (ty_bin h_prod A B) v ->
  rel_e (S n) (match a with L => A | R => B end) (e_proj a v).
Proof.
  intros H. inspect_related_value H. apply ty_bin_inj in H as [HA HB].
  match goal with K : _ /\ _ |- _ => destruct K end.
  destruct a.
  - eapply rel_e_step; [apply ProjLE|]. apply rel_e_val. eapply rel_v_eq; eauto. now symmetry.
  - eapply rel_e_step; [apply ProjRE|]. apply rel_e_val. eapply rel_v_eq; eauto. now symmetry.
Qed.

Lemma rel_void n v : ~ rel_v (S n) ty_void v.
Proof. intro H. inspect_related_value H. Qed.

Lemma rel_case n A B T v e1 e2 :
  rel_v (S n) (ty_bin h_sum A B) v ->
  (forall w, rel_v n A w -> rel_e n T (subst (Inc := inc) e1 w)) ->
  (forall w, rel_v n B w -> rel_e n T (subst (Inc := inc) e2 w)) ->
  rel_e (S n) T (e_case v e1 e2).
Proof.
  intros H H1 H2. inspect_related_value H. apply ty_bin_inj in H as [HA HB].
  destruct a; simpl in *.
  - eapply rel_e_step; [apply CaseLE|]. apply H1. eapply rel_v_eq; eauto. now symmetry.
  - eapply rel_e_step; [apply CaseRE|]. apply H2. eapply rel_v_eq; eauto. now symmetry.
Qed.

Lemma rel_unpack n k F T v e :
  rel_v (S n) (ty_quant k (h_xist k) F) v ->
  (forall Q, valid Q -> forall w, rel_v n (dapp F Q) w ->
     rel_e n T (subst (Inc := inc) e w)) ->
  rel_e (S n) T (e_unpack v e).
Proof.
  intros H He. inspect_related_value H.
  apply tagged_inj in H as [E H]. injection E as E. subst.
  apply paired_inj in H as [_ H].
  match goal with K : _ /\ _ |- _ => destruct K end.
  eapply rel_e_step; [apply UnpackE|].
  eapply He; [eassumption|]. eapply rel_v_eq; [apply dapp_eq; [symmetry; exact H|reflexivity]|eassumption].
Qed.

Lemma rel_unroll n k F args v :
  rel_v (S n) (roll_type k F args) v -> rel_e (S n) (roll_body k F args) (e_unroll v).
Proof.
  intros H. inspect_related_value H. apply roll_inj in H.
  eapply rel_e_step; [apply UnrollE|]. apply rel_e_val.
  eapply rel_v_eq; [symmetry; exact H|eassumption].
Qed.

Lemma rel_capp n k (P Q : den k) B v :
  den_eq P Q ->
  rel_v (S n) (ty_constrained h_carr (constraint_den k P Q) B) v ->
  rel_e (S n) B (e_capp v).
Proof.
  intros HQ H. inspect_related_value H.
  apply tagged_inj in H as [_ H]. apply paired_inj in H as [HC HB].
  eapply rel_e_step; [apply LamBetaC|].
  eapply rel_e_eq; [symmetry; exact HB|].
  eauto using constraint_den_inj.
Qed.

Lemma rel_lwith n k (P Q : den k) A B v e :
  rel_v (S n) (ty_constrained h_cprod (constraint_den k P Q) A) v ->
  (den_eq P Q -> forall w, rel_v n A w -> rel_e n B (subst (Inc := inc) e w)) ->
  rel_e (S n) B (e_lwith v e).
Proof.
  intros H He. inspect_related_value H.
  apply tagged_inj in H as [_ H]. apply paired_inj in H as [HC HA].
  match goal with K : _ /\ _ |- _ => destruct K end.
  eapply rel_e_step; [apply WithE|]. apply He.
  - eapply constraint_den_inj; [symmetry; exact HC|eassumption].
  - eapply rel_v_eq; [symmetry; exact HA|eassumption].
Qed.

Lemma rel_bind n A B e body :
  rel_e n A e ->
  (forall m, m <= n -> forall v, rel_v m A v -> rel_e m B (subst (Inc := inc) body v)) ->
  rel_e n B (e >>= body).
Proof.
  revert e. induction n; [intros; exact I|].
  intros e [[v [-> HV]]|[e' [Hs HE]]] Hbody.
  - eapply rel_e_step; [apply BindE|]. apply Hbody; auto using Nat.le_succ_diag_r, rel_v_prev.
  - eapply rel_e_step; [apply BindE', Hs|].
    eapply IHn; [exact HE|]. intros m Hm. apply Hbody. now apply le_S.
Qed.

Lemma rel_v_all n T v :
  (forall m, m < n -> value_clause (rel_v m) (rel_e m) T v) -> rel_v n T v.
Proof.
  induction n; [intros; exact I|].
  intro H. apply rel_v_intro.
  - apply IHn. intros m Hm. apply H. auto using le_S.
  - apply H. apply le_n.
Qed.

Definition assumptions_hold {D} (r : tenv D) (P : list (constr D)) :=
  forall c, In c P -> holds r c.
Definition env_related {V : Set} {D} n (r : tenv D) (G : V -> typ ⋆ D)
  (f : V -> value ∅) := forall x, rel_v n (eval_type (G x) r) (f x).

Lemma assumptions_shift D k (r : tenv D) P (Q : den k) :
  assumptions_hold r P -> assumptions_hold (tenv_ext r Q) (map shift P).
Proof.
  intros H c Hc. apply in_map_iff in Hc as [c' [<- Hc]].
  now apply holds_shift, H.
Qed.

Lemma assumptions_extend D (r : tenv D) P c :
  assumptions_hold r P -> holds r c -> assumptions_hold r (c :: P).
Proof. intros H Hc d [<-|Hd]; auto. Qed.

Lemma related_shift (V : Set) D k n (r : tenv D) (G : V -> typ ⋆ D) f (Q : den k) :
  env_related n r G f -> env_related n (tenv_ext r Q) (shift • G) f.
Proof. intros H x. eapply rel_v_eq; [symmetry; apply eval_shift|apply H]. Qed.

Lemma related_extend (V : Set) D n (r : tenv D) (G : V -> typ ⋆ D) f A w :
  env_related n r G f -> rel_v n (eval_type A r) w -> env_related n r (G ▹ A) (f ▹ w).
Proof. intros H Hw [|x]; [exact Hw|exact (H x)]. Qed.

Lemma related_le (V : Set) D n m (r : tenv D) (G : V -> typ ⋆ D) f :
  m <= n -> env_related n r G f -> env_related m r G f.
Proof. intros H Hf x. eauto using rel_v_le. Qed.

Lemma eval_instantiate D a b (t : typ b (extC a D)) (s : typ a D) r :
  env_valid r ->
  den_eq (dapp (eval_type (t_lam t) r) (eval_type s r)) (eval_type (subst t s) r).
Proof.
  intro Hr. etransitivity; [apply eval_beta, eval_valid, Hr|].
  symmetry. apply eval_subst.
Qed.

Scheme typing_expr_ind' := Induction for typing_expr Sort Prop
with typing_val_ind' := Induction for typing_val Sort Prop.
Combined Scheme typing_ind' from typing_expr_ind', typing_val_ind'.

Definition expr_interp {V : Set} {D} P (G : V -> typ ⋆ D) e A :=
  forall n r f, env_valid r -> assumptions_hold r P -> env_related n r G f ->
    rel_e n (eval_type A r) (ebind (sub_val f) e).
Definition val_interp {V : Set} {D} P (G : V -> typ ⋆ D) v A :=
  forall n r f, env_valid r -> assumptions_hold r P -> env_related n r G f ->
    rel_v n (eval_type A r) (vbind (sub_val f) v).

(* The fundamental lemma interprets typing under a closing substitution
   and a type environment satisfying the local equality assumptions. *)
Lemma typing_interpreted (V : Set) D P (G : V -> typ ⋆ D) :
  (forall e A, D ∣ P ∣ G ⊢ₑ e : A -> expr_interp P G e A) /\
  (forall v A, D ∣ P ∣ G ⊢ᵥ v : A -> val_interp P G v A).
Proof.
  apply (typing_ind'
    (fun V D P G e A _ => @expr_interp V D P G e A)
    (fun V D P G v A _ => @val_interp V D P G v A)).
  all: clear V D P G; intros V D P G.
  all: unfold expr_interp, val_interp.
  - intros A v H IH n r f Hr Hp Hf. apply rel_e_val. auto.
  - intros A B e body H IH Hb IHb n r f Hr Hp Hf.
    cbn [ebind]. eapply rel_bind.
    + exact (IH n r f Hr Hp Hf).
    + intros m Hm w Hw. rewrite (closing_subst body f w).
      apply (IHb m r (f ▹ w)); eauto using related_extend, related_le.
  - intros A B e Hc H IH n r f Hr Hp Hf.
    eapply rel_e_eq; [exact (proves_valid _ _ _ Hc r Hr Hp)|exact (IH n r f Hr Hp Hf)].
  - intros A B v w Hv IHv Hw IHw [|n] r f Hr Hp Hf; [exact I|].
    cbn [ebind]. apply (rel_app n (eval_type A r) (eval_type B r)).
    + eapply rel_v_eq; [exact (eval_bin D r h_arr tc_arr A B eq_refl Hr)|exact (IHv (S n) r f Hr Hp Hf)].
    + apply (IHw n r f Hr Hp). eauto using related_le, Nat.le_succ_diag_r.
  - intros k A B v Hv IH [|n] r f Hr Hp Hf; [exact I|].
    cbn [ebind]. eapply rel_e_eq; [exact (eval_instantiate D k ⋆ A B r Hr)|].
    apply (rel_tapp n k (eval_type (t_lam A) r) (eval_type B r)).
    + exact (eval_valid D k B r Hr).
    + eapply rel_v_eq; [exact (eval_quant D k r (h_all k) (tc_all k) A eq_refl Hr)|
        exact (IH (S n) r f Hr Hp Hf)].
  - intros A B v H IH [|n] r f Hr Hp Hf; [exact I|].
    cbn [ebind]. eapply (rel_proj n (eval_type A r) (eval_type B r) _ L).
    eapply rel_v_eq; [exact (eval_bin D r h_prod tc_prod A B eq_refl Hr)|exact (IH (S n) r f Hr Hp Hf)].
  - intros A B v H IH [|n] r f Hr Hp Hf; [exact I|].
    cbn [ebind]. eapply (rel_proj n (eval_type A r) (eval_type B r) _ R).
    eapply rel_v_eq; [exact (eval_bin D r h_prod tc_prod A B eq_refl Hr)|exact (IH (S n) r f Hr Hp Hf)].
  - intros A v Hv IH [|n] r f Hr Hp Hf; [exact I|].
    exfalso. eapply (rel_void n). exact (IH (S n) r f Hr Hp Hf).
  - intros A B T v e1 e2 H1 IH1 H2 IH2 Hv IHv [|n] r f Hr Hp Hf; [exact I|].
    cbn [ebind]. apply (rel_case n (eval_type A r) (eval_type B r)).
    + eapply rel_v_eq; [exact (eval_bin D r h_sum tc_sum A B eq_refl Hr)|exact (IHv (S n) r f Hr Hp Hf)].
    + intros w Hw. rewrite (closing_subst e1 f w). apply (IH1 n r (f ▹ w)); eauto using related_extend,
          related_le, Nat.le_succ_diag_r.
    + intros w Hw. rewrite (closing_subst e2 f w). apply (IH2 n r (f ▹ w)); eauto using related_extend,
          related_le, Nat.le_succ_diag_r.
  - intros k A B v e Hv IHv He IHe [|n] r f Hr Hp Hf; [exact I|].
    cbn [ebind]. apply (rel_unpack n k (eval_type (t_lam A) r)).
    + eapply rel_v_eq; [exact (eval_quant D k r (h_xist k) (tc_xist k) A eq_refl Hr)|
        exact (IHv (S n) r f Hr Hp Hf)].
    + intros Q HQ w Hw. rewrite (closing_subst e f w).
      eapply rel_e_eq; [exact (eval_shift D k ⋆ B r Q)|].
      apply (IHe n (tenv_ext r Q) (f ▹ w)); auto using tenv_ext_valid, assumptions_shift.
      apply related_extend.
      * apply related_shift. eauto using related_le, Nat.le_succ_diag_r.
      * eapply rel_v_eq; [exact (eval_beta D k ⋆ A r Q HQ)|exact Hw].
  - intros k A s u HF v Hv IH [|n] r f Hr Hp Hf; [exact I|].
    destruct (eval_roll _ _ _ _ _ HF r Hr) as [S [Hs Hu]].
    cbn [ebind]. eapply rel_e_eq; [symmetry; exact Hu|].
    apply rel_unroll. eapply rel_v_eq; [exact Hs|exact (IH (Datatypes.S n) r f Hr Hp Hf)].
  - intros A c Hc Hd n r f Hr Hp Hf. exfalso.
    eapply discr_invalid; eauto using proves_valid.
  - intros c A v Hc Hv IH [|n] r f Hr Hp Hf; [exact I|].
    pose proof (proves_valid _ _ _ Hc r Hr Hp) as Hholds.
    specialize (IH (S n) r f Hr Hp Hf).
    destruct c. cbn [holds eval_type eval_constr ebind] in *.
    eapply rel_capp; eauto.
  - intros c B A v e Hv IHv He IHe [|n] r f Hr Hp Hf; [exact I|].
    specialize (IHv (S n) r f Hr Hp Hf).
    destruct c. cbn [eval_type eval_constr ebind] in IHv |- *.
    eapply rel_lwith; [exact IHv|].
    intros Hc w Hw. rewrite (closing_subst e f w).
    apply (IHe n r (f ▹ w)); eauto using assumptions_extend, related_extend, related_le, Nat.le_succ_diag_r.
  - intros x A <- n r f Hr Hp Hf. apply Hf.
  - intros v A B Hc Hv IH n r f Hr Hp Hf.
    eapply rel_v_eq; [exact (proves_valid _ _ _ Hc r Hr Hp)|exact (IH n r f Hr Hp Hf)].
  - intros n r f Hr Hp Hf. apply rel_v_all. intros m Hm. cbn [vbind value_clause]. reflexivity.
  - intros A B e He IH n r f Hr Hp Hf.
    apply rel_v_all. intros m Hm. cbn [vbind value_clause].
    exists (eval_type A r), (eval_type B r). split.
    + apply eval_bin; auto.
    + intros w Hw. rewrite (closing_subst e f w). apply IH.
      * exact Hr.
      * exact Hp.
      * eauto using related_extend, related_le, Nat.lt_le_incl.
  - intros A B v w Hv IHv Hw IHw n r f Hr Hp Hf.
    apply rel_v_all. intros m Hm. cbn [vbind value_clause].
    exists (eval_type A r), (eval_type B r). split.
    + apply eval_bin; auto.
    + split; eauto using related_le, Nat.lt_le_incl.
  - intros A B v Hv IH n r f Hr Hp Hf.
    apply rel_v_all. intros m Hm. cbn [vbind value_clause].
    exists (eval_type A r), (eval_type B r). split.
    + apply eval_bin; auto.
    + eauto using related_le, Nat.lt_le_incl.
  - intros A B v Hv IH n r f Hr Hp Hf.
    apply rel_v_all. intros m Hm. cbn [vbind value_clause].
    exists (eval_type A r), (eval_type B r). split.
    + apply eval_bin; auto.
    + eauto using related_le, Nat.lt_le_incl.
  - intros k A e He IH n r f Hr Hp Hf.
    apply rel_v_all. intros m Hm. cbn [vbind value_clause].
    exists k, (eval_type (t_lam A) r). split.
    + apply eval_quant; auto.
    + intros Q HQ. eapply rel_e_eq; [symmetry; apply eval_beta; exact HQ|].
      apply IH; eauto using tenv_ext_valid, assumptions_shift, related_shift,
        related_le, Nat.lt_le_incl.
  - intros k A B v Hv IH n r f Hr Hp Hf.
    apply rel_v_all. intros m Hm. cbn [vbind value_clause].
    exists k, (eval_type (t_lam A) r), (eval_type B r). split.
    + apply eval_quant; auto.
    + split; [now apply eval_valid|].
      eapply rel_v_eq; [symmetry; apply eval_instantiate; exact Hr|].
      eauto using related_le, Nat.lt_le_incl.
  - intros k A s u HF v Hv IH n r f Hr Hp Hf.
    destruct (eval_roll _ _ _ _ _ HF r Hr) as [S [Hs Hu]].
    apply rel_v_all. intros m Hm. cbn [vbind value_clause].
    exists k, (eval_type (t_lam A) r), S. split; [exact Hs|].
    eapply rel_v_eq; eauto using related_le, Nat.lt_le_incl.
  - intros c A e He IH n r f Hr Hp Hf.
    destruct c. apply rel_v_all. intros m Hm. cbn [vbind value_clause].
    exists κ, (eval_type τ₁ r), (eval_type τ₂ r), (eval_type A r).
    split; [reflexivity|].
    intros Hc. apply IH; eauto using assumptions_extend, related_le, Nat.lt_le_incl.
  - intros c A v Hv IH Hc n r f Hr Hp Hf.
    pose proof (proves_valid _ _ _ Hc r Hr Hp) as Hholds.
    destruct c. apply rel_v_all. intros m Hm. cbn [vbind value_clause].
    exists κ, (eval_type τ₁ r), (eval_type τ₂ r), (eval_type A r).
    split; [reflexivity|].
    split; [exact Hholds|]. apply IH; eauto using related_le, Nat.lt_le_incl.
  - intros A B e He IH n r f Hr Hp.
    induction n as [|n IHn]; intro Hf; [exact I|].
    apply rel_v_intro.
    + apply IHn. eauto using related_le, Nat.le_succ_diag_r.
    + cbn [vbind value_clause].
      exists (eval_type A r), (eval_type B r). split.
      * apply eval_bin; auto.
      * intros w Hw. rewrite (closing_subst_rec e f (v_fix (ebind (((sub_val f) ↑) ↑) e)) w).
        apply IH; auto.
        apply related_extend; [|exact Hw].
        apply related_extend; [|apply IHn]; eauto using related_le, Nat.le_succ_diag_r.
Qed.

Lemma head_step_value v e : ~ (e_val v ↦ e).
Proof. intro H. inversion H. Qed.

Lemma head_step_unique e e1 :
  e ↦ e1 -> forall e2, e ↦ e2 -> e1 = e2.
Proof.
  intro H. induction H; intros e2' H'; inversion H'; subst;
    try reflexivity; try solve [match goal with H : e_val _ ↦ _ |- _ => inversion H end].
  f_equal. eauto.
Qed.

Lemma rel_e_preserved n T e e' :
  e ↦ e' -> rel_e (S n) T e -> rel_e n T e'.
Proof.
  intros H [[v [-> _]]|[y [Hy HR]]].
  - exfalso. exact (head_step_value _ _ H).
  - now rewrite (head_step_unique _ _ H _ Hy).
Qed.

Lemma rel_e_safe T e :
  (forall n, rel_e n T e) -> safe e.
Proof.
  intros H y Hy. induction Hy as [e|e e' y He Hsteps IH].
  - destruct (H 1) as [[v [Hv _]]|[e' [He' _]]]; eauto.
  - apply IH. intro n. eapply rel_e_preserved; [exact He|apply H].
Qed.

Theorem soundness e τ (HT : mtC ∣ nil ∣ □ ⊢ₑ e : τ) :
  safe e.
Proof.
  pose (r := (fun _ x => match x with end) : tenv mtC).
  apply (rel_e_safe (eval_type τ r)). intros n.
  pose proof (proj1 (typing_interpreted ∅ mtC nil □) _ _ HT n r (@v_var ∅))
    as H.
  rewrite (proj1 (term_bind_id _) e _ (fun _ => eq_refl)) in H.
  apply H.
  - intros k x. destruct x.
  - intros c [].
  - intros x. destruct x.
Qed.
