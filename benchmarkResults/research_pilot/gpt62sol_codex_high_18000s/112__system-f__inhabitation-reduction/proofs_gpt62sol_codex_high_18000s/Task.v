Require Import H10C SysF Reduction.
From Stdlib Require Import List Lia PeanoNat.
Import ListNotations.
Local Notation "x ⇒ y" := (poly_arr x y) (at level 59, right associativity).

Definition agrees {A} (f g : nat -> A) := forall i, f i = g i.
Definition lift_sub (f : nat -> poly_type) :=
  scons (poly_var 0) (funcomp (ren_poly_type S) f).

Lemma ren_ext f g t : agrees f g -> ren_poly_type f t = ren_poly_type g t.
Proof.
  revert f g. induction t; intros f g H; simpl.
  - now rewrite H.
  - now rewrite (IHt1 f g H), (IHt2 f g H).
  - f_equal. apply IHt. intros [|i]; simpl; unfold funcomp; now try rewrite H.
Qed.

Lemma sub_ext f g t : agrees f g -> subst_poly_type f t = subst_poly_type g t.
Proof.
  revert f g. induction t; intros f g H; simpl.
  - apply H.
  - now rewrite (IHt1 f g H), (IHt2 f g H).
  - f_equal. apply IHt. intros [|i]; simpl; unfold funcomp; now try rewrite H.
Qed.

Lemma ren_ren f g t :
  ren_poly_type f (ren_poly_type g t) = ren_poly_type (funcomp f g) t.
Proof.
  revert f g. induction t; intros f g; simpl.
  - reflexivity.
  - now rewrite IHt1, IHt2.
  - f_equal. rewrite IHt. apply ren_ext. intros [|i]; reflexivity.
Qed.

Lemma sub_ren f g t :
  subst_poly_type f (ren_poly_type g t) = subst_poly_type (funcomp f g) t.
Proof.
  revert f g. induction t; intros f g; simpl.
  - reflexivity.
  - now rewrite IHt1, IHt2.
  - f_equal. rewrite IHt. apply sub_ext. intros [|i]; reflexivity.
Qed.

Lemma ren_sub f g t :
  ren_poly_type f (subst_poly_type g t) =
  subst_poly_type (funcomp (ren_poly_type f) g) t.
Proof.
  revert f g. induction t; intros f g; simpl.
  - reflexivity.
  - now rewrite IHt1, IHt2.
  - f_equal. rewrite IHt. apply sub_ext. intros [|i]; cbv beta delta [scons funcomp] iota.
    + reflexivity.
    + rewrite !ren_ren; apply ren_ext; intros j; reflexivity.
Qed.

Lemma sub_sub f g t :
  subst_poly_type f (subst_poly_type g t) =
  subst_poly_type (funcomp (subst_poly_type f) g) t.
Proof.
  revert f g. induction t; intros f g; simpl.
  - reflexivity.
  - now rewrite IHt1, IHt2.
  - f_equal. rewrite IHt. apply sub_ext. intros [|i]; cbv beta delta [scons funcomp] iota.
    + reflexivity.
    + rewrite sub_ren, ren_sub; apply sub_ext; intros j; reflexivity.
Qed.

Lemma ren_id t : ren_poly_type (fun i => i) t = t.
Proof.
  induction t; simpl; try congruence.
  f_equal. rewrite <- IHt at 2. apply ren_ext. intros [|i]; reflexivity.
Qed.

Lemma sub_id t : subst_poly_type poly_var t = t.
Proof.
  induction t; simpl; try congruence.
  f_equal. rewrite <- IHt at 2. apply sub_ext. intros [|i]; reflexivity.
Qed.

Definition block {A} (n : nat) (xs tail : nat -> A) i :=
  if i <? n then xs i else tail (i - n).
Fixpoint bind (n : nat) (t : poly_type) :=
  match n with 0 => t | S n => poly_abs (bind n t) end.
Fixpoint chain (ts : list poly_type) (t : poly_type) :=
  match ts with [] => t | s :: ss => s ⇒ chain ss t end.
Definition inh G t := exists M, type_assignment G M t.

Lemma hypo G t : In t G -> inh G t.
Proof.
  intros H. apply In_nth_error in H as [i H].
  exists (pure_var i). now constructor.
Qed.
Lemma mp G s t : inh G (s ⇒ t) -> inh G s -> inh G t.
Proof.
  intros [M HM] [N HN]. exists (pure_app M N). eapply type_assignment_app; eassumption.
Qed.
Lemma inst G t u : inh G (poly_abs t) -> inh G (subst_poly_type (scons u poly_var) t).
Proof.
  intros [M HM]. exists M. now apply type_assignment_inst.
Qed.
Lemma use_chain G ts t : inh G (chain ts t) -> Forall (inh G) ts -> inh G t.
Proof.
  intros H Hs. revert H. induction Hs; simpl; intros Hc; [exact Hc|].
  apply IHHs. eapply mp; eassumption.
Qed.

Fixpoint under n f :=
  match n with 0 => f | S n => under n (lift_sub f) end.

Lemma under_index n f i :
  under n f i = block n poly_var (funcomp (ren_poly_type (Nat.add n)) f) i.
Proof.
  revert f i. induction n as [|n IH]; intros f i.
  - simpl. unfold block, funcomp. simpl. now rewrite Nat.sub_0_r, ren_id.
  - simpl. rewrite IH. unfold block, funcomp.
    destruct (i <? n) eqn:Hi.
    + assert (i <? S n = true) as -> by (apply Nat.ltb_lt in Hi; apply Nat.ltb_lt; lia).
      reflexivity.
    + apply Nat.ltb_ge in Hi. destruct (Nat.eq_dec i n) as [->|Hne].
      * replace (n - n) with 0 by lia. assert (n <? S n = true) as -> by (apply Nat.ltb_lt; lia).
        now cbn [lift_sub scons ren_poly_type]; rewrite Nat.add_0_r.
      * assert (i <? S n = false) as -> by (apply Nat.ltb_ge; lia).
        replace (i-n) with (S (i-S n)) by lia.
        simpl. unfold funcomp. rewrite ren_ren. apply ren_ext. intros j.
        unfold funcomp. lia.
Qed.

Lemma sub_bind n f t :
  subst_poly_type f (bind n t) = bind n (subst_poly_type (under n f) t).
Proof.
  revert f. induction n; simpl; intros; [reflexivity|]. now rewrite IHn.
Qed.

Lemma inst_bind n G t xs :
  inh G (bind n t) -> inh G (subst_poly_type (block n xs poly_var) t).
Proof.
  revert t. induction n as [|n IH]; intros t H.
  - replace (subst_poly_type (block 0 xs poly_var) t) with t; [exact H|].
    rewrite <- sub_id at 1. apply sub_ext. intros i. unfold block. simpl. now rewrite Nat.sub_0_r.
  - apply (inst _ _ (xs n)) in H. rewrite sub_bind in H. apply IH in H.
    rewrite sub_sub in H.
    replace (subst_poly_type (block (S n) xs poly_var) t)
      with (subst_poly_type (funcomp (subst_poly_type (block n xs poly_var))
                                 (under n (scons (xs n) poly_var))) t).
    + exact H.
    + apply sub_ext. intros i. unfold funcomp. rewrite under_index. unfold block, funcomp.
      destruct (i <? n) eqn:Hi.
      * assert (i <? S n = true) as -> by (apply Nat.ltb_lt in Hi; apply Nat.ltb_lt; lia).
        simpl. unfold block. now rewrite Hi.
      * apply Nat.ltb_ge in Hi. destruct (Nat.eq_dec i n) as [->|Hne].
        -- replace (n - n) with 0 by lia.
           assert (n <? S n = true) as -> by (apply Nat.ltb_lt; lia).
           simpl. rewrite sub_ren.
           rewrite <- (sub_id (xs n)) at 2. apply sub_ext. intros j.
           unfold funcomp, block. assert (n+j <? n = false) as -> by (apply Nat.ltb_ge; lia).
           f_equal. lia.
        -- assert (i <? S n = false) as -> by (apply Nat.ltb_ge; lia).
           replace (i-n) with (S (i-S n)) by lia. simpl. unfold block.
           assert (n+(i-S n) <? n = false) as -> by (apply Nat.ltb_ge; lia).
           f_equal. lia.
Qed.

Definition shift_rigid n : nat -> poly_type := fun i => poly_var (n+i).
Definition disj s t :=
  poly_abs ((ren_poly_type S s ⇒ poly_var 0) ⇒
            (ren_poly_type S t ⇒ poly_var 0) ⇒ poly_var 0).

Lemma sub_disj f a b :
  subst_poly_type f (disj a b) = disj (subst_poly_type f a) (subst_poly_type f b).
Proof.
  unfold disj. simpl. f_equal.
  now rewrite !sub_ren, !ren_sub.
Qed.

(* A numeral is a pair of types. The successor sends (A, B) to
   (A -> B, A \/ B), using the System F encoding of disjunction. *)
Definition zero (g : nat -> poly_type) := (g 3 ⇒ g 4, g 3).
Definition step (ab : poly_type * poly_type) :=
  (fst ab ⇒ snd ab, disj (fst ab) (snd ab)).
Fixpoint numeral g n := match n with 0 => zero g | S n => step (numeral g n) end.
Definition pair_at (xs : nat -> poly_type) i := (xs (2*i), xs (2*i+1)).
Definition tup (a b c : poly_type * poly_type) i :=
  match i with
  | 0 => fst a | 1 => snd a | 2 => fst b | 3 => snd b | 4 => fst c | _ => snd c
  end.
Definition lift_to m t := (t ⇒ m) ⇒ m.
Definition role i positive := 2*i + if positive : bool then 0 else 1.
Definition observe (g : nat -> poly_type) t (positive : bool) :=
  let see := lift_to (g 2) (g 2 ⇒ t) in
  if positive then see else see ⇒ g 2.
Definition check (g : nat -> poly_type) (xs : nat -> poly_type) i positive :=
  g (9 + role i positive) ⇒ observe g (xs i) positive.
Definition checks g xs :=
  flat_map (fun i => [check g xs i true; check g xs i false]) (seq 0 6).
Definition pred g k xs := lift_to (g 0) (g (5+k) ⇒ chain (checks g xs) (g 1)).
Definition natp g a := pred g 0 (tup a a a).
Definition onep g a := pred g 1 (tup a a a).
Definition addp g a b c := pred g 2 (tup a b c).
Definition mulp g a b c := pred g 3 (tup a b c).

Definition arity r :=
  match r with 0 | 2 => 0 | 1 | 3 | 5 => 2 | 4 => 6 | _ => 8 end.
Definition arithmetic_body r g xs :=
  let a := pair_at xs 0 in let b := pair_at xs 1 in
  let c := pair_at xs 2 in let d := pair_at xs 3 in
  let z := zero g in
  match r with
  | 0 => natp g z
  | 1 => natp g a ⇒ natp g (step a)
  | 2 => onep g (step z)
  | 3 => natp g a ⇒ addp g z a a
  | 4 => addp g a b c ⇒ addp g (step a) b (step c)
  | 5 => natp g a ⇒ mulp g z a z
  | _ => mulp g a b c ⇒ addp g b c d ⇒ mulp g (step a) b d
  end.
Definition rule r := bind (arity r) (arithmetic_body r (shift_rigid (arity r)) poly_var).
Definition rules := map rule (seq 0 7).

Definition bound1 c :=
  match c with
  | h10c_one x => S x
  | h10c_plus x y z | h10c_mult x y z => S (Nat.max x (Nat.max y z))
  end.
Definition bound cs := fold_right (fun c n => Nat.max (bound1 c) n) 0 cs.
Lemma bound_in c cs : In c cs -> bound1 c <= bound cs.
Proof.
  induction cs as [|d cs IH]; simpl; intros H; [contradiction|].
  destruct H as [<-|H]; [apply Nat.le_max_l|].
  etransitivity; [now apply IH|apply Nat.le_max_r].
Qed.
Lemma bound_args c cs : In c cs ->
  match c with
  | h10c_one x => x < bound cs
  | h10c_plus x y z | h10c_mult x y z => x < bound cs /\ y < bound cs /\ z < bound cs
  end.
Proof.
  intros H. pose proof (bound_in c cs H).
  destruct c; cbn [bound1] in *; lia.
Qed.
Definition encode g xs c :=
  match c with
  | h10c_one x => onep g (pair_at xs x)
  | h10c_plus x y z => addp g (pair_at xs x) (pair_at xs y) (pair_at xs z)
  | h10c_mult x y z => mulp g (pair_at xs x) (pair_at xs y) (pair_at xs z)
  end.
Definition premises cs g xs :=
  map (fun i => natp g (pair_at xs i)) (seq 0 (bound cs)) ++ map (encode g xs) cs.
Definition main cs :=
  let n := 2 * bound cs in
  bind n (chain (premises cs (shift_rigid n) poly_var) (shift_rigid n 0)).
Definition context cs := main cs :: rules.

Definition map_pair {A B} (f : A -> B) (a : A * A) := (f (fst a), f (snd a)).
Lemma sub_chain f ts t :
  subst_poly_type f (chain ts t) = chain (map (subst_poly_type f) ts) (subst_poly_type f t).
Proof. induction ts; simpl; now try rewrite IHts. Qed.

Lemma sub_zero f g :
  map_pair (subst_poly_type f) (zero g) = zero (funcomp (subst_poly_type f) g).
Proof. reflexivity. Qed.
Lemma sub_step f a :
  map_pair (subst_poly_type f) (step a) = step (map_pair (subst_poly_type f) a).
Proof. unfold map_pair, step. cbn [fst snd subst_poly_type]. now rewrite sub_disj. Qed.
Lemma sub_pred f g k xs :
  subst_poly_type f (pred g k xs) =
  pred (funcomp (subst_poly_type f) g) k (funcomp (subst_poly_type f) xs).
Proof.
  unfold pred, lift_to. cbn [subst_poly_type].
  rewrite sub_chain. unfold checks. rewrite flat_map_concat_map, concat_map.
  reflexivity.
Qed.

(* Pointwise equality is sufficient for the two families of inputs to a predicate. *)
Lemma pred_ext g g' k xs xs' :
  agrees g g' -> agrees xs xs' -> pred g k xs = pred g' k xs'.
Proof.
  intros Hg Hx. unfold pred, lift_to. rewrite (Hg 0), (Hg (5+k)), (Hg 1).
  f_equal. f_equal. f_equal. f_equal. unfold checks.
  apply flat_map_ext. intros i. unfold check, observe. now rewrite !Hg, !Hx.
Qed.
Lemma sub_tup f a b c :
  agrees (funcomp (subst_poly_type f) (tup a b c))
  (tup (map_pair (subst_poly_type f) a) (map_pair (subst_poly_type f) b)
      (map_pair (subst_poly_type f) c)).
Proof. intros [|[|[|[|[|i]]]]]; reflexivity. Qed.

Lemma sub_natp f g a : subst_poly_type f (natp g a) =
  natp (funcomp (subst_poly_type f) g) (map_pair (subst_poly_type f) a).
Proof. unfold natp. rewrite sub_pred. apply pred_ext; [intros i; reflexivity|apply sub_tup]. Qed.
Lemma sub_onep f g a : subst_poly_type f (onep g a) =
  onep (funcomp (subst_poly_type f) g) (map_pair (subst_poly_type f) a).
Proof. unfold onep. rewrite sub_pred. apply pred_ext; [intros i; reflexivity|apply sub_tup]. Qed.
Lemma sub_addp f g a b c : subst_poly_type f (addp g a b c) =
  addp (funcomp (subst_poly_type f) g) (map_pair (subst_poly_type f) a)
       (map_pair (subst_poly_type f) b) (map_pair (subst_poly_type f) c).
Proof. unfold addp. rewrite sub_pred. apply pred_ext; [intros i; reflexivity|apply sub_tup]. Qed.
Lemma sub_mulp f g a b c : subst_poly_type f (mulp g a b c) =
  mulp (funcomp (subst_poly_type f) g) (map_pair (subst_poly_type f) a)
       (map_pair (subst_poly_type f) b) (map_pair (subst_poly_type f) c).
Proof. unfold mulp. rewrite sub_pred. apply pred_ext; [intros i; reflexivity|apply sub_tup]. Qed.

Lemma block_left {A} n (xs rho : nat -> A) i : i < n -> block n xs rho i = xs i.
Proof. intros H. unfold block. now rewrite (proj2 (Nat.ltb_lt _ _) H). Qed.
Lemma block_right {A} n (xs rho : nat -> A) i : block n xs rho (n+i) = rho i.
Proof.
  unfold block. assert (n+i <? n = false) as -> by (apply Nat.ltb_ge; lia).
  now replace (n+i-n) with i by lia.
Qed.
Lemma rigid_sub n xs g i :
  subst_poly_type (block n xs g) (shift_rigid n i) = g i.
Proof. apply block_right. Qed.

Lemma natp_ext g g' a : agrees g g' -> natp g a = natp g' a.
Proof. intros H; apply pred_ext; [exact H|intros i; reflexivity]. Qed.
Lemma onep_ext g g' a : agrees g g' -> onep g a = onep g' a.
Proof. intros H; apply pred_ext; [exact H|intros i; reflexivity]. Qed.
Lemma addp_ext g g' a b c : agrees g g' -> addp g a b c = addp g' a b c.
Proof. intros H; apply pred_ext; [exact H|intros i; reflexivity]. Qed.
Lemma mulp_ext g g' a b c : agrees g g' -> mulp g a b c = mulp g' a b c.
Proof. intros H; apply pred_ext; [exact H|intros i; reflexivity]. Qed.

Lemma rule_instance G r xs : r < 7 -> In (rule r) G ->
  inh G (arithmetic_body r poly_var xs).
Proof.
  intros Hr Hin. apply hypo in Hin. unfold rule in Hin. apply (inst_bind _ _ _ xs) in Hin.
  assert (Hr' : agrees (funcomp (subst_poly_type (block (arity r) xs poly_var))
                            (shift_rigid (arity r))) poly_var) by (intros i; apply rigid_sub).
  destruct r as [|[|[|[|[|[|[|r]]]]]]]; try lia.
  all: cbn [arithmetic_body] in *.
  all: cbn [subst_poly_type] in Hin.
  all: rewrite ?sub_natp, ?sub_onep, ?sub_addp, ?sub_mulp, ?sub_zero, ?sub_step, ?sub_zero in Hin.
  all: try rewrite ?(natp_ext _ _ _ Hr'), ?(onep_ext _ _ _ Hr'),
        ?(addp_ext _ _ _ _ _ Hr'), ?(mulp_ext _ _ _ _ _ Hr') in Hin.
  all: cbn [map_pair zero pair_at fst snd funcomp arity subst_poly_type] in Hin.
  all: repeat (rewrite block_left in Hin by lia || rewrite block_right in Hin).
  all: exact Hin.
Qed.

Fixpoint slots {A} (f : nat -> A * A) i : A :=
  match i with
  | 0 => fst (f 0)
  | 1 => snd (f 0)
  | S (S j) => slots (fun n => f (S n)) j
  end.
Lemma slots_fst {A} (f : nat -> A * A) i : slots f (2*i) = fst (f i).
Proof.
  revert f. induction i; intros f; [reflexivity|].
  replace (2*S i) with (S (S (2*i))) by lia. apply IHi.
Qed.
Lemma slots_snd {A} (f : nat -> A * A) i : slots f (2*i+1) = snd (f i).
Proof.
  revert f. induction i; intros f; [reflexivity|].
  replace (2*S i+1) with (S (S (2*i+1))) by lia. apply IHi.
Qed.
Lemma pair_slots f i : pair_at (slots f) i = f i.
Proof. unfold pair_at. rewrite slots_fst, slots_snd. now destruct (f i). Qed.

Lemma in_rule cs r : r < 7 -> In (rule r) (context cs).
Proof.
  intros H. right. apply in_map, in_seq. lia.
Qed.
Lemma rule_use cs r xs : r < 7 -> inh (context cs) (arithmetic_body r poly_var xs).
Proof. eauto using rule_instance, in_rule. Qed.

Local Notation "'N' n" := (numeral poly_var n) (at level 4).
Lemma nat_inh cs n : inh (context cs) (natp poly_var (N n)).
Proof.
  induction n as [|n IH].
  - exact (rule_use cs 0 poly_var (Nat.lt_0_succ _)).
  - apply (mp _ (natp poly_var (N n))); [|exact IH].
    exact (rule_use cs 1 (slots (fun _ => N n)) (ltac:(lia))).
Qed.
Lemma add_inh cs x y : inh (context cs) (addp poly_var (N x) (N y) (N (x+y))).
Proof.
  induction x as [|x IH].
  - eapply mp; [|apply nat_inh].
    exact (rule_use cs 3 (slots (fun _ => N y)) (ltac:(lia))).
  - eapply mp; [|exact IH].
    exact (rule_use cs 4 (slots (scons (N x) (scons (N y) (fun _ => N (x+y))))) (ltac:(lia))).
Qed.
Lemma mul_inh cs x y : inh (context cs) (mulp poly_var (N x) (N y) (N (x*y))).
Proof.
  induction x as [|x IH].
  - eapply mp; [|apply nat_inh].
    exact (rule_use cs 5 (slots (fun _ => N y)) (ltac:(lia))).
  - eapply mp; [|apply add_inh].
    eapply mp; [|exact IH].
    exact (rule_use cs 6
      (slots (scons (N x) (scons (N y) (scons (N (x*y)) (fun _ => N (y+x*y))))))
      (ltac:(lia))).
Qed.

Lemma sub_selected n xs i : i < n ->
  map_pair (subst_poly_type (block (2*n) xs poly_var)) (pair_at poly_var i)
  = pair_at xs i.
Proof.
  intros H. unfold map_pair, pair_at. cbn [fst snd subst_poly_type].
  now rewrite !block_left by lia.
Qed.
Lemma sub_premises cs xs :
  let n := 2 * bound cs in
  map (subst_poly_type (block n xs poly_var)) (premises cs (shift_rigid n) poly_var) =
  premises cs poly_var xs.
Proof.
  cbn zeta. unfold premises. rewrite map_app, !map_map. f_equal.
  - apply map_ext_in. intros i Hi. apply in_seq in Hi.
    rewrite sub_natp, sub_selected by lia.
    apply natp_ext. intros j. apply rigid_sub.
  - apply map_ext_in. intros c Hc. apply bound_args in Hc.
    destruct c; cbn [encode] in *.
    + rewrite sub_onep, sub_selected by lia. apply onep_ext. intros j. apply rigid_sub.
    + rewrite sub_addp, !sub_selected by lia. apply addp_ext. intros j. apply rigid_sub.
    + rewrite sub_mulp, !sub_selected by lia. apply mulp_ext. intros j. apply rigid_sub.
Qed.

Lemma forward cs : H10C_SAT cs -> inh (context cs) (poly_var 0).
Proof.
  intros [f Hf]. set (xs := slots (fun i => N (f i))).
  assert (Hmain : inh (context cs) (main cs)) by (apply hypo; now left).
  unfold main in Hmain. apply (inst_bind _ _ _ xs) in Hmain.
  rewrite sub_chain, sub_premises, rigid_sub in Hmain.
  eapply use_chain; [exact Hmain|].
  apply Forall_app; split; apply Forall_map, Forall_forall.
  - intros i _. unfold xs. rewrite pair_slots. apply nat_inh.
  - intros c Hc. specialize (Hf c Hc).
    destruct c; cbn [encode h10c_sem] in *; unfold xs; rewrite !pair_slots.
    + rewrite Hf. exact (rule_use cs 2 poly_var (ltac:(lia))).
    + rewrite <- Hf. apply add_inh.
    + rewrite <- Hf. apply mul_inh.
Qed.

(* Truth at a world contains E and is stable under double negation
   relative to E. Taking E to be solvability lets the converse recover
   a solution constructively, even though the type variables range over
   arbitrary values in the model. *)
Section Model.
Context (E : Prop).
Definition necessary (P : Prop) := (P -> E) -> E.
Lemma necessary_intro P : P -> necessary P.
Proof. firstorder. Qed.
Lemma necessary_map P Q : (P -> Q) -> necessary P -> necessary Q.
Proof. firstorder. Qed.
Lemma necessary_bind P Q : (P -> necessary Q) -> necessary P -> necessary Q.
Proof. firstorder. Qed.
Lemma necessary_stable P : necessary (necessary P) -> necessary P.
Proof. firstorder. Qed.
Lemma necessary_dec P : (P \/ ~P) -> (necessary P <-> E \/ P).
Proof. firstorder. Qed.

Definition pattern := nat -> nat -> Prop.
(* The base worlds form a ladder: n sees itself and every m with
   m + 2 <= n. The remaining worlds test type values on this ladder.
   A worker checks one bit of one argument. A test sees the workers
   selected by its entire pattern. The root sees every test. *)
Inductive world :=
| root
| base (n : nat)
| worker (i : nat) (b : bool) (n : nat)
| test (k : nat) (p : pattern).

Definition down n m := m = n \/ m + 2 <= n.
Lemma down_trans n m l : down n m -> down m l -> down n l.
Proof. unfold down; lia. Qed.

Definition selected (p : pattern) i (b : bool) n :=
  if b then necessary (p i n) else necessary (p i n) -> E.
Definition further w v :=
  match w, v with
  | root, _ => True
  | base n, base m | worker _ _ n, base m => down n m
  | test _ _, base _ => True
  | test _ p, worker i b n => selected p i b n
  | _, _ => False
  end.
Definition reaches w v := w = v \/ further w v.
Lemma reach_self w : reaches w w.
Proof. now left. Qed.
Lemma reach_root w : reaches root w.
Proof. now right. Qed.
Lemma reach_trans w v u : reaches w v -> reaches v u -> reaches w u.
Proof.
  intros [->|H] [->|J]; auto using reach_self; try now right.
  right. destruct w, v, u; simpl in *; try tauto; eauto using down_trans.
Qed.
Lemma reach_base n w : reaches (base n) w <-> exists m, w = base m /\ down n m.
Proof.
  split.
  - intros [<-|H]; [exists n; split; [reflexivity|now left]|].
    destruct w; simpl in H; try contradiction. now exists n0.
  - intros [m [-> H]]. now right.
Qed.

Definition hereditary (p : world -> Prop) := forall w v, reaches w v -> p w -> p v.
Record value := {
  truth :> world -> Prop;
  truth_up : hereditary truth;
  truth_E : forall w, E -> truth w;
  truth_stable : forall w, necessary (truth w) -> truth w
}.

Lemma forall_congr {A : Type} (P Q : A -> Prop) :
  (forall x, P x <-> Q x) -> ((forall x, P x) <-> (forall x, Q x)).
Proof. firstorder. Qed.
Definition implies (p q : world -> Prop) w :=
  forall v, reaches w v -> p v -> q v.
Lemma implies_congr p p' q q' w :
  (forall v, p v <-> p' v) -> (forall v, q v <-> q' v) ->
  implies p q w <-> implies p' q' w.
Proof. unfold implies; firstorder. Qed.

Fixpoint holds (rho : nat -> value) t w : Prop :=
  match t with
  | poly_var i => rho i w
  | s ⇒ t => implies (holds rho s) (holds rho t) w
  | poly_abs s => forall X : value, holds (scons X rho) s w
  end.
Lemma holds_up t rho : hereditary (holds rho t).
Proof.
  revert rho. induction t; intros rho w v H Ht; simpl in *.
  - exact (truth_up _ _ _ H Ht).
  - intros u Hu. apply Ht. eapply reach_trans; eassumption.
  - intros X. eapply IHt; eauto.
Qed.
Lemma holds_E t rho w : E -> holds rho t w.
Proof.
  revert rho w. induction t; simpl; intros rho w H.
  - now apply truth_E.
  - intros v _ _. now apply IHt2.
  - intros X. now apply IHt.
Qed.
Lemma holds_stable t rho w : necessary (holds rho t w) -> holds rho t w.
Proof.
  revert rho w. induction t; simpl; intros rho w H.
  - now apply truth_stable.
  - intros v Hv Hs. apply IHt2. eapply necessary_map; [|exact H].
    intros J. exact (J v Hv Hs).
  - intros X. apply IHt. eapply necessary_map; [|exact H]. intros J. apply J.
Qed.
Definition meaning rho t : value :=
  {| truth := holds rho t; truth_up := holds_up t rho;
     truth_E := holds_E t rho; truth_stable := holds_stable t rho |}.
Definition stable_value p (H : hereditary p) : value.
Proof.
  refine {| truth := fun w => necessary (p w) |}.
  - intros w v Hwv Hw. eapply necessary_map; [|exact Hw]. now apply H.
  - firstorder.
  - intros w. apply necessary_stable.
Defined.
Lemma stable_dec p H w :
  (p w \/ ~p w) -> (stable_value p H w <-> E \/ p w).
Proof. apply necessary_dec. Qed.

Lemma holds_ext (rho rho' : nat -> value) t w :
  (forall i v, rho i v <-> rho' i v) -> (holds rho t w <-> holds rho' t w).
Proof.
  revert rho rho' w. induction t; intros rho rho' w H; simpl.
  - apply H.
  - apply implies_congr; intros v; auto.
  - apply forall_congr. intros X. apply IHt.
    intros [|i] v; simpl; [tauto|apply H].
Qed.
Lemma holds_ren rho xi t w :
  holds rho (ren_poly_type xi t) w <-> holds (funcomp rho xi) t w.
Proof.
  revert rho xi w. induction t; intros rho xi w; simpl.
  - reflexivity.
  - apply implies_congr; [apply IHt1|apply IHt2].
  - apply forall_congr. intros X. etransitivity; [apply IHt|].
    apply holds_ext. intros [|i] v; reflexivity.
Qed.
Lemma holds_sub rho f t w :
  holds rho (subst_poly_type f t) w <-> holds (fun i => meaning rho (f i)) t w.
Proof.
  revert rho f w. induction t; intros rho f w; simpl.
  - reflexivity.
  - apply implies_congr; [apply IHt1|apply IHt2].
  - apply forall_congr. intros X. etransitivity; [apply IHt|].
    apply holds_ext. intros [|i] v; [reflexivity|].
    change (holds (scons X rho) (ren_poly_type S (f i)) v <-> holds rho (f i) v).
    apply holds_ren.
Qed.

Lemma typing_sound G M t :
  type_assignment G M t -> forall rho w,
  (forall a, In a G -> holds rho a w) -> holds rho t w.
Proof.
  induction 1 as [G x t H|G M K s t Hs IHs Ht IHt|G M s t H IH|
                   G M s t H IH|G M s H IH]; intros rho w HG; simpl.
  - apply HG. eapply nth_error_In; eassumption.
  - exact (IHs rho w HG w (reach_self w) (IHt rho w HG)).
  - intros v Hv Hs. apply IH. intros a [<-|Ha]; auto.
    eapply holds_up; [exact Hv|now apply HG].
  - apply holds_sub.
    refine (proj2 (holds_ext _ (scons (meaning rho t) rho) s w _) (IH rho w HG (meaning rho t))).
    intros [|i] v; reflexivity.
  - intros X. apply IH. intros a Ha. apply in_map_iff in Ha as [b [<- Hb]].
    apply holds_ren. now apply HG.
Qed.

Lemma block_tail {A} n (xs rho : nat -> A) i : n <= i ->
  block n xs rho i = rho (i-n).
Proof. intros H. unfold block. now rewrite (proj2 (Nat.ltb_ge _ _) H). Qed.

Lemma holds_bind n rho t w :
  holds rho (bind n t) w <-> forall xs, holds (block n xs rho) t w.
Proof.
  revert rho. induction n as [|n IH]; intros rho.
  - simpl. split.
    + intros H xs. refine (proj1 (holds_ext rho _ t w _) H).
      intros i v. now rewrite block_tail, Nat.sub_0_r by lia.
    + intros H. specialize (H rho). refine (proj1 (holds_ext _ rho t w _) H).
      intros i v. now rewrite block_tail, Nat.sub_0_r by lia.
  - simpl. split.
    + intros H xs. specialize (proj1 (IH (scons (xs n) rho)) (H (xs n)) xs) as Hbody.
      refine (proj1 (holds_ext _ _ t w _) Hbody).
      intros i v. destruct (Nat.lt_ge_cases i n) as [Hi|Hi].
      * rewrite !block_left by lia. reflexivity.
      * rewrite block_tail by lia.
        destruct (Nat.eq_dec i n) as [->|Hne].
        -- rewrite block_left by lia. now replace (n-n) with 0 by lia.
        -- rewrite block_tail by lia. now replace (i-n) with (S (i-S n)) by lia.
    + intros H X. apply IH. intros xs.
      specialize (H (fun i => if i <? n then xs i else X)).
      refine (proj1 (holds_ext _ _ t w _) H).
      intros i v. destruct (Nat.lt_ge_cases i n) as [Hi|Hi].
      * rewrite !block_left by lia. now rewrite (proj2 (Nat.ltb_lt _ _) Hi).
      * rewrite (block_tail n _ _ i) by lia.
        destruct (Nat.eq_dec i n) as [->|Hne].
        -- rewrite block_left by lia. rewrite Nat.ltb_irrefl. now replace (n-n) with 0 by lia.
        -- rewrite block_tail by lia. now replace (i-n) with (S (i-S n)) by lia.
Qed.

Lemma holds_chain rho ts t w :
  holds rho (chain ts t) w <->
  forall v, reaches w v -> Forall (fun a => holds rho a v) ts -> holds rho t v.
Proof.
  revert w. induction ts as [|a ts IH]; intros w; simpl.
  - split; [intros H v Hv _; eapply holds_up; eassumption|].
    intros H. apply H; [apply reach_self|constructor].
  - split.
    + intros H v Hv Hs. inversion Hs as [|? ? Ha Hrest]; subst.
      pose proof (proj1 (IH v) (H v Hv Ha)) as J. exact (J v (reach_self v) Hrest).
    + intros H v Hv Ha. apply IH. intros u Hu Hs. apply H.
      * eapply reach_trans; eassumption.
      * constructor; [eapply holds_up; eassumption|exact Hs].
Qed.


Lemma reach_worker i b n w :
  reaches (worker i b n) w <-> w = worker i b n \/ exists m, w = base m /\ down n m.
Proof.
  split.
  - intros [<-|H]; [now left|right].
    destruct w; simpl in H; try contradiction. now exists n0.
  - intros [->|[m [-> H]]]; [apply reach_self|now right].
Qed.
Lemma reach_test k p w :
  reaches (test k p) w <->
  w = test k p \/ (exists n, w = base n) \/
  (exists i b n, w = worker i b n /\ selected p i b n).
Proof.
  split.
  - intros [<-|H]; [now left|right].
    destruct w; simpl in H; try contradiction.
    + left; now exists n.
    + right; now exists i, b, n.
  - intros [->|[[n ->]|[i [b [n [-> H]]]]]]; [apply reach_self|now right|now right].
Qed.

(* At the base worlds, numeral n has first component true at
   j < n and j = n + 1, and second component true at j < n + 1,
   with both truth values taken relative to E. *)
Definition code_at n (b : bool) j :=
  E \/ if b then j < S n else j < n \/ j = S n.
Definition reads (p : pattern) i n :=
  (forall j, p (2*i) j <-> code_at n false j) /\
  (forall j, p (2*i+1) j <-> code_at n true j).
Definition correct k p :=
  match k with
  | 0 => exists x, reads p 0 x
  | 1 => reads p 0 1
  | 2 => exists x y z, reads p 0 x /\ reads p 1 y /\ reads p 2 z /\ x+y=z
  | _ => exists x y z, reads p 0 x /\ reads p 1 y /\ reads p 2 z /\ x*y=z
  end.
Lemma reads_ext p q i n :
  (forall a j, a < 6 -> (p a j <-> q a j)) -> i < 3 ->
  (reads p i n <-> reads q i n).
Proof.
  intros H Hi. unfold reads. split; intros [H0 H1]; split; intros j.
  all: etransitivity; [first [apply H; lia|symmetry; apply H; lia|apply H0|apply H1]|].
  all: first [apply H0|apply H1|apply H; lia|symmetry; apply H; lia].
Qed.
Lemma correct_ext k p q :
  (forall i n, i < 6 -> (p i n <-> q i n)) -> (correct k p <-> correct k q).
Proof.
  intros H.
  pose proof (reads_ext p q 0) as H0.
  pose proof (reads_ext p q 1) as H1.
  pose proof (reads_ext p q 2) as H2.
  specialize (fun n => H0 n H (ltac:(lia))) as J0.
  specialize (fun n => H1 n H (ltac:(lia))) as J1.
  specialize (fun n => H2 n H (ltac:(lia))) as J2.
  destruct k as [|[|[|k]]]; cbn [correct].
  - split; intros [x Hx]; exists x; now apply J0.
  - apply J0.
  - split; intros [x [y [z [Hx [Hy [Hz He]]]]]]; exists x, y, z.
    all: split; [now apply J0|]; split; [now apply J1|]; split; [now apply J2|exact He].
  - split; intros [x [y [z [Hx [Hy [Hz He]]]]]]; exists x, y, z.
    all: split; [now apply J0|]; split; [now apply J1|]; split; [now apply J2|exact He].
Qed.

Definition off_flag w := match w with root => False | _ => True end.
Definition low_flag w := match w with base _ | worker _ _ _ => True | _ => False end.
Definition base_flag w := match w with base _ => True | _ => False end.
Definition point_flag w := match w with base 0 => True | _ => False end.
Definition role_flag r w :=
  match w with base _ => True | worker i b _ => r = role i b | _ => False end.
Definition tag_flag k w :=
  match w with
  | base _ | worker _ _ _ => True
  | test l p => k = l /\ (correct k (fun i n => necessary (p i n)) -> E)
  | root => False
  end.
Definition marker i :=
  match i with
  | 0 => off_flag | 1 => low_flag | 2 => base_flag | 3 => point_flag
  | 4 => fun _ => False
  | 5 => tag_flag 0 | 6 => tag_flag 1 | 7 => tag_flag 2 | 8 => tag_flag 3
  | S (S (S (S (S (S (S (S (S r)))))))) => role_flag r
  end.
Lemma marker_up i : hereditary (marker i).
Proof.
  intros w v [<-|Hwv] Hw; [exact Hw|].
  destruct i as [|[|[|[|[|[|[|[|[|i]]]]]]]]]; destruct w, v;
    simpl in *; try contradiction; auto.
  destruct n, n0; simpl in *; try contradiction; unfold down in Hwv; lia.
Qed.
Definition rigid i := stable_value (marker i) (marker_up i).
Definition names (rho : nat -> value) (g : nat -> poly_type) :=
  forall i w, holds rho (g i) w <-> rigid i w.
Lemma names_shift n xs : names (block n xs rigid) (shift_rigid n).
Proof. intros i w. change (block n xs rigid (n+i) w <-> rigid i w). now rewrite block_right. Qed.

Lemma plain_marker i w :
  (marker i w \/ ~ marker i w) -> (rigid i w <-> (E \/ marker i w)).
Proof. apply stable_dec. Qed.
Lemma marked i w : marker i w -> rigid i w.
Proof. apply necessary_intro. Qed.
Lemma unmarked i w : ~ marker i w -> (rigid i w <-> E).
Proof. intros H. unfold rigid; change (necessary (marker i w) <-> E). firstorder. Qed.
Lemma marker_tag k w : k < 4 -> (marker (5+k) w <-> tag_flag k w).
Proof. intros H. destruct k as [|[|[|[|k]]]]; try lia; reflexivity. Qed.
Lemma at_tag k l p : k < 4 ->
  (rigid (5+k) (test l p) <-> k = l /\
       (correct k (fun i n => necessary (p i n)) -> E) \/ E).
Proof.
  intros Hk. unfold rigid. cbn [stable_value truth].
  pose proof (marker_tag k (test l p) Hk) as Htag. simpl in Htag.
  destruct (Nat.eq_dec k l) as [Heq|Hne].
  - subst l. split.
    + intros H. left. split; [reflexivity|]. intros J. apply H. intros F.
      exact (proj2 (proj1 Htag F) J).
    + intros [[Heq H]|HE] K; [apply K; apply Htag; now split|exact HE].
  - split.
    + intros H. right. apply H. intros K. apply Htag in K. tauto.
    + intros [[Heq _]|HE] K; [contradiction|exact HE].
Qed.

Lemma role_inj i b i' b' : role i b = role i' b' -> i = i' /\ b = b'.
Proof. destruct b, b'; unfold role; intros H; try (exfalso; lia); (split; [lia|reflexivity]). Qed.

(* At a world where the marker holds above it, (A -> marker) -> marker
   has the same truth as A, unless the marker already holds there. *)
Lemma lift_valid rho m a w : holds rho m w -> holds rho (lift_to m a) w.
Proof. intros H v Hv _. eapply holds_up; eassumption. Qed.
Lemma lift_local rho m a w :
  (holds rho m w -> E) ->
  (forall v, reaches w v -> v = w \/ holds rho m v) ->
  (holds rho (lift_to m a) w <-> holds rho a w).
Proof.
  intros Hm Hstrict. split.
  - intros H. apply holds_stable. intros J. apply Hm.
    apply (H w (reach_self w)). intros v Hv Ha.
    destruct (Hstrict v Hv) as [->|Hv']; [apply holds_E; now apply J|exact Hv'].
  - intros H v Hv Himp. apply (Himp v (reach_self v)).
    eapply holds_up; eassumption.
Qed.


Lemma named_mark rho g i w : names rho g -> marker i w -> holds rho (g i) w.
Proof. intros H J. apply H. now apply marked. Qed.
Lemma named_unmarked rho g i w : names rho g -> ~ marker i w -> holds rho (g i) w -> E.
Proof. intros H J K. exact (proj1 (unmarked i w J) (proj1 (H i w) K)). Qed.

Lemma see_worker rho g t i b n :
  names rho g ->
  (holds rho (observe g t true) (worker i b n) <-> holds rho t (base n)).
Proof.
  intros Hg. unfold observe.
  rewrite lift_local.
  - split.
    + intros H. apply (H (base n)); [right; left; reflexivity|].
      apply (named_mark rho g 2); [exact Hg|exact I].
    + intros H w Hw Hb. apply reach_worker in Hw.
      destruct Hw as [->|[m [-> Hnm]]].
      * apply holds_E. eapply (named_unmarked rho g 2 (worker i b n)); [exact Hg|simpl; tauto|exact Hb].
      * eapply (holds_up t rho (base n) (base m)); [right; exact Hnm|exact H].
  - eapply (named_unmarked rho g 2 (worker i b n)); [exact Hg|simpl; tauto].
  - intros v Hv. apply reach_worker in Hv as [->|[m [-> H]]]; [now left|].
    right. apply named_mark; [exact Hg|exact I].
Qed.

Definition observed (rho : nat -> value) t (b : bool) n :=
  if b then holds rho t (base n) else holds rho t (base n) -> E.
Lemma observe_worker rho g t i b n :
  names rho g ->
  (holds rho (observe g t b) (worker i b n) <-> observed rho t b n).
Proof.
  intros Hg. destruct b; [now apply see_worker|]. cbn [observed].
  change (holds rho (observe g t true ⇒ g 2) (worker i false n) <-> (holds rho t (base n) -> E)).
  split.
  - intros H J. eapply (named_unmarked rho g 2 (worker i false n)); [exact Hg|simpl; tauto|].
    apply (H _ (reach_self _)). now apply see_worker.
  - intros H w Hw J. apply reach_worker in Hw as [->|[m [-> Hm]]].
    + apply holds_E, H. eapply see_worker; eassumption.
    + apply named_mark; [exact Hg|exact I].
Qed.
Lemma observe_base rho g t b n :
  names rho g -> holds rho (observe g t b) (base n).
Proof.
  intros Hg. assert (H : holds rho (g 2) (base n)) by (apply named_mark; [exact Hg|exact I]).
  destruct b; [exact (lift_valid rho (g 2) (g 2 ⇒ t) (base n) H)|].
  intros v Hv _. eapply holds_up; eassumption.
Qed.

Lemma check_test rho g xs k p i b :
  names rho g ->
  (holds rho (check g xs i b) (test k p) <->
   forall n, selected p i b n -> observed rho (xs i) b n).
Proof.
  intros Hg. split.
  - intros H n Hn. apply (observe_worker rho g (xs i) i b n Hg).
    apply (H (worker i b n)); [now right|].
    apply named_mark; [exact Hg|reflexivity].
  - intros H w Hw Hr. apply reach_test in Hw as [->|[[n ->]|[j [c [n [-> Hn]]]]]].
    + apply holds_E. eapply (named_unmarked rho g (9+role i b) (test k p)); [exact Hg|simpl; tauto|exact Hr].
    + now apply observe_base.
    + destruct (Nat.eq_dec (role i b) (role j c)) as [Heq|Hne].
      * apply role_inj in Heq as [<- <-].
        apply (observe_worker rho g (xs i) i b n Hg). now apply H.
      * apply holds_E. eapply (named_unmarked rho g (9+role i b) (worker j c n)); [exact Hg|exact Hne|exact Hr].
Qed.

Definition sampled rho xs : pattern := fun i n => holds rho (xs i) (base n).
Lemma checks_test rho g xs k p :
  names rho g ->
  (Forall (fun a => holds rho a (test k p)) (checks g xs) <->
   forall i n, i < 6 -> (necessary (p i n) <-> sampled rho xs i n)).
Proof.
  intros Hg. unfold checks. rewrite Forall_forall. split.
  - intros H i n Hi.
    assert (J : forall b, holds rho (check g xs i b) (test k p)).
    { intros b. apply H. apply in_flat_map. exists i. split; [apply in_seq; lia|].
      destruct b; simpl; auto. }
    pose proof (proj1 (check_test rho g xs k p i true Hg) (J true) n) as Hpos.
    pose proof (proj1 (check_test rho g xs k p i false Hg) (J false) n) as Hneg.
    cbn [selected observed] in Hpos, Hneg. unfold sampled. split; [exact Hpos|].
    intros Ha Hnp. exact (Hneg (fun J => J Hnp) Ha).
  - intros H a Ha. apply in_flat_map in Ha as [i [Hi Ha]]. apply in_seq in Hi.
    assert (J : forall b, holds rho (check g xs i b) (test k p)).
    { intros b. apply check_test; [exact Hg|]. intros n Hn.
      specialize (H i n (ltac:(lia))). unfold sampled in H.
      destruct b; simpl in *; tauto. }
    simpl in Ha. destruct Ha as [<-|[<-|[]]]; apply J.
Qed.

Lemma test_chain rho g xs k p :
  names rho g ->
  (holds rho (chain (checks g xs) (g 1)) (test k p) <->
   ((forall i n, i < 6 -> (necessary (p i n) <-> sampled rho xs i n)) -> E)).
Proof.
  intros Hg. rewrite holds_chain. split.
  - intros H Hmatch. eapply (named_unmarked rho g 1 (test k p)); [exact Hg|simpl; tauto|].
    apply (H (test k p) (reach_self _)). now apply checks_test.
  - intros H v Hv Hs. apply reach_test in Hv as [->|[[n ->]|[i [b [n [-> _]]]]]].
    + apply holds_E, H. exact (proj1 (checks_test rho g xs k p Hg) Hs).
    + apply named_mark; [exact Hg|exact I].
    + apply named_mark; [exact Hg|exact I].
Qed.

Lemma predicate_off rho g xs k w :
  names rho g -> w <> root -> holds rho (pred g k xs) w.
Proof.
  intros Hg Hw. apply lift_valid. apply named_mark; [exact Hg|].
  now destruct w.
Qed.

(* A predicate holds at the root exactly when the sampled arguments
   satisfy its relation, under relative double negation. For the forward
   implication, test the arguments against their own sampled pattern.
   For the reverse implication, a test that matches these arguments
   can be marked bad only if its relation implies E. *)
Lemma predicate_root rho g xs k :
  names rho g -> k < 4 ->
  (holds rho (pred g k xs) root <-> necessary (correct k (sampled rho xs))).
Proof.
  intros Hg Hk. unfold pred. rewrite lift_local.
  - split.
    + intros H Hbad. set (p := sampled rho xs).
      specialize (H (test k p) (reach_root _)).
      assert (Hm : forall i n, i < 6 -> (necessary (p i n) <-> sampled rho xs i n)).
      { intros i n _. split; [apply holds_stable|apply necessary_intro]. }
      assert (Ht : holds rho (g (5+k)) (test k p)).
      { apply Hg, at_tag; [exact Hk|]. left. split; [reflexivity|].
        intros Hc. apply Hbad. exact (proj1 (correct_ext k _ _ Hm) Hc). }
      exact (proj1 (test_chain rho g xs k p Hg) (H Ht) Hm).
    + intros H. apply holds_stable. eapply necessary_map; [|exact H].
      intros Hgood v _ Htag. destruct v as [|n|i b n|l p].
      * apply holds_E. eapply (named_unmarked rho g (5+k) root); [exact Hg| |exact Htag].
        exact (proj1 (marker_tag k root Hk)).
      * apply holds_chain. intros w Hw _. apply reach_base in Hw as [j [-> _]].
        apply named_mark; [exact Hg|exact I].
      * apply holds_chain. intros w Hw _. apply reach_worker in Hw as [->|[j [-> _]]];
          (apply named_mark; [exact Hg|exact I]).
      * apply (proj2 (test_chain rho g xs l p Hg)). intros Hm. apply Hg in Htag.
        apply at_tag in Htag; [|exact Hk]. destruct Htag as [[<- Hbad]|He]; [|exact He].
        apply Hbad. apply (proj2 (correct_ext k _ _ Hm)); exact Hgood.
  - eapply (named_unmarked rho g 0 root); [exact Hg|simpl; tauto].
  - intros v _. destruct v; [now left|right|right|right];
      (apply named_mark; [exact Hg|exact I]).
Qed.


Lemma holds_disj rho a b w :
  holds rho (disj a b) w <-> necessary (holds rho a w \/ holds rho b w).
Proof.
  change ((forall X : value,
    holds (scons X rho) ((ren_poly_type S a ⇒ poly_var 0) ⇒
      (ren_poly_type S b ⇒ poly_var 0) ⇒ poly_var 0) w) <-> necessary (holds rho a w \/ holds rho b w)).
  assert (Hu : hereditary (fun v => holds rho a v \/ holds rho b v)).
  { intros v u Hvu [H|H]; [left|right]; eapply holds_up; eassumption. }
  split.
  - intros H. specialize (H (stable_value _ Hu)).
    refine (H w (reach_self w) _ w (reach_self w) _); clear H.
    + intros v _ Hv. apply necessary_intro. left. exact (proj1 (holds_ren (scons (stable_value _ Hu) rho) S a v) Hv).
    + intros v _ Hv. apply necessary_intro. right. exact (proj1 (holds_ren (scons (stable_value _ Hu) rho) S b v) Hv).
  - intros H X v Hwv Ha u Hvu Hb. apply truth_stable.
    eapply necessary_map; [|exact H].
    intros [J|J].
    + apply (Ha u Hvu). apply (proj2 (holds_ren (scons X rho) S a u)). eapply holds_up; [|exact J].
      eapply reach_trans; eassumption.
    + apply (Hb u (reach_self u)). apply (proj2 (holds_ren (scons X rho) S b u)). eapply holds_up; [|exact J].
      eapply reach_trans; eassumption.
Qed.
Lemma base_arrow rho a b n :
  holds rho (a ⇒ b) (base n) <->
  forall j, down n j -> holds rho a (base j) -> holds rho b (base j).
Proof.
  split.
  - intros H j Hj. apply H. now right.
  - intros H w Hw. apply reach_base in Hw as [j [-> Hj]]. now apply H.
Qed.

Definition represents rho (ab : poly_type * poly_type) n :=
  (forall j, holds rho (fst ab) (base j) <-> code_at n false j) /\
  (forall j, holds rho (snd ab) (base j) <-> code_at n true j).

Lemma represents_zero rho g : names rho g -> represents rho (zero g) 0.
Proof.
  intros Hg. unfold represents, zero. cbn [fst snd].
  assert (H3 : forall j, holds rho (g 3) (base j) <-> E \/ j = 0).
  { intros j. rewrite (Hg 3), plain_marker; destruct j; cbn [marker point_flag]; intuition discriminate. }
  assert (H4 : forall j, holds rho (g 4) (base j) <-> E).
  { intros j. rewrite (Hg 4), unmarked; simpl; tauto. }
  split; intros j.
  - rewrite base_arrow. cbn [code_at]. split.
    + intros H. destruct (Nat.eq_dec j 1) as [->|Hj]; [right; now right|].
      left. apply (H4 0), H; [unfold down; lia|].
      apply H3. now right.
    + intros [HE|Hj] l Hl H; [now apply H4|]. apply H4. destruct (proj1 (H3 l) H) as [J | ->]; auto.
      unfold down in Hl. lia.
  - rewrite H3. unfold code_at; cbn. intuition lia.
Qed.

Lemma represents_step rho ab x :
  represents rho ab x -> represents rho (step ab) (S x).
Proof.
  intros [Ha Hb]. unfold represents, step. cbn [fst snd].
  split; intros j.
  - rewrite base_arrow. cbn [code_at]. split.
    + intros H. destruct (Nat.eq_dec j (S (S x))) as [->|Hj]; [right; now right|].
      destruct (Nat.lt_ge_cases j (S x)) as [Hlt|Hge]; [right; now left|].
      assert (down j (S x)) as Hd by (unfold down; lia).
      pose proof (H (S x) Hd (proj2 (Ha _) (or_intror (or_intror eq_refl)))) as J.
      apply Hb in J. unfold code_at in J; cbn in J. left. intuition lia.
    + intros [HE|Hj] l Hl H; [apply Hb; now left|]. apply Hb. apply Ha in H.
      unfold code_at in *; cbn in *. unfold down in Hl. intuition lia.
  - rewrite holds_disj.
    assert (D : holds rho (fst ab) (base j) \/ holds rho (snd ab) (base j)
                  <-> code_at (S x) true j).
    { rewrite Ha, Hb. unfold code_at. cbn. intuition lia. }
    split.
    + intros H. unfold code_at; cbn.
      destruct (Nat.lt_ge_cases j (S (S x))) as [Hj|Hj]; [now right|].
      left. apply H. intros J. apply D in J. unfold code_at in J; cbn in J. intuition lia.
    + intros H. apply necessary_intro. now apply D.
Qed.

Lemma represents_unique rho a x y :
  represents rho a x -> represents rho a y -> E \/ x = y.
Proof.
  intros [_ Hx] [_ Hy].
  destruct (Nat.lt_trichotomy x y) as [Hlt|[->|Hlt]]; [left|now right|left].
  - assert (J : code_at y true (S x)) by (unfold code_at; right; lia).
    pose proof (proj1 (Hx (S x)) (proj2 (Hy (S x)) J)) as K.
    unfold code_at in K; cbn in K. intuition lia.
  - assert (J : code_at x true (S y)) by (unfold code_at; right; lia).
    pose proof (proj1 (Hy (S y)) (proj2 (Hx (S y)) J)) as K.
    unfold code_at in K; cbn in K. intuition lia.
Qed.

Lemma at_natp rho g a :
  names rho g -> (holds rho (natp g a) root <-> necessary (exists x, represents rho a x)).
Proof.
  intros H. unfold natp. rewrite predicate_root by (assumption || lia).
  reflexivity.
Qed.
Lemma at_onep rho g a :
  names rho g -> (holds rho (onep g a) root <-> necessary (represents rho a 1)).
Proof.
  intros H. unfold onep. rewrite predicate_root by (assumption || lia).
  reflexivity.
Qed.
Lemma at_addp rho g a b c :
  names rho g ->
  (holds rho (addp g a b c) root <->
   necessary (exists x y z, represents rho a x /\ represents rho b y /\ represents rho c z /\ x+y=z)).
Proof.
  intros H. unfold addp. rewrite predicate_root by (assumption || lia).
  reflexivity.
Qed.
Lemma at_mulp rho g a b c :
  names rho g ->
  (holds rho (mulp g a b c) root <->
   necessary (exists x y z, represents rho a x /\ represents rho b y /\ represents rho c z /\ x*y=z)).
Proof.
  intros H. unfold mulp. rewrite predicate_root by (assumption || lia).
  reflexivity.
Qed.


Lemma predicate_clause rho g ps k xs :
  names rho g ->
  (Forall (fun a => holds rho a root) ps -> holds rho (pred g k xs) root) ->
  holds rho (chain ps (pred g k xs)) root.
Proof.
  intros Hg H. apply holds_chain. intros w _ Hs.
  destruct w; [now apply H| | |]; (apply predicate_off; [exact Hg|discriminate]).
Qed.

Lemma arithmetic_sound r rho g xs :
  r < 7 -> names rho g -> holds rho (arithmetic_body r g xs) root.
Proof.
  intros Hr Hg.
  set (a := pair_at xs 0). set (b := pair_at xs 1).
  set (c := pair_at xs 2). set (d := pair_at xs 3).
  destruct r as [|[|[|[|[|[|[|r]]]]]]]; try lia.
  - apply at_natp; [exact Hg|]. apply necessary_intro. exists 0. now apply represents_zero.
  - change (holds rho (chain [natp g a] (natp g (step a))) root).
    apply predicate_clause; [exact Hg|]. intros H. inversion H as [|? ? Ha _]; subst.
    apply at_natp in Ha; [|exact Hg]. apply at_natp; [exact Hg|].
    eapply necessary_map; [|exact Ha]. intros [x Hx]. exists (S x). now apply represents_step.
  - apply at_onep; [exact Hg|]. apply necessary_intro, represents_step. now apply represents_zero.
  - change (holds rho (chain [natp g a] (addp g (zero g) a a)) root).
    apply predicate_clause; [exact Hg|]. intros H. inversion H as [|? ? Ha _]; subst.
    apply at_natp in Ha; [|exact Hg]. apply at_addp; [exact Hg|].
    eapply necessary_map; [|exact Ha]. intros [x Hx]. exists 0, x, x.
    split; [now apply represents_zero|]. auto.
  - change (holds rho (chain [addp g a b c] (addp g (step a) b (step c))) root).
    apply predicate_clause; [exact Hg|]. intros H. inversion H as [|? ? Ha _]; subst.
    apply at_addp in Ha; [|exact Hg]. apply at_addp; [exact Hg|].
    eapply necessary_map; [|exact Ha]. intros [x [y [z [Hx [Hy [Hz He]]]]]].
    exists (S x), y, (S z). split; [now apply represents_step|].
    split; [exact Hy|]. split; [now apply represents_step|lia].
  - change (holds rho (chain [natp g a] (mulp g (zero g) a (zero g))) root).
    apply predicate_clause; [exact Hg|]. intros H. inversion H as [|? ? Ha _]; subst.
    apply at_natp in Ha; [|exact Hg]. apply at_mulp; [exact Hg|].
    eapply necessary_map; [|exact Ha]. intros [x Hx]. exists 0, x, 0.
    pose proof (represents_zero rho g Hg). auto.
  - change (holds rho (chain [mulp g a b c; addp g b c d] (mulp g (step a) b d)) root).
    apply predicate_clause; [exact Hg|]. intros H.
    inversion H as [|? ? Hm Hrest]; subst. inversion Hrest as [|? ? Ha _]; subst.
    apply at_mulp in Hm; [|exact Hg]. apply at_addp in Ha; [|exact Hg].
    apply at_mulp; [exact Hg|].
    eapply necessary_bind; [|exact Hm]. intros [x [y [z [Hx [Hy [Hz Hmul]]]]]].
    eapply necessary_bind; [|exact Ha]. intros [y' [z' [u [Hy' [Hz' [Hu Hadd]]]]]].
    destruct (represents_unique rho b y y' Hy Hy') as [HE|<-]; [now intros _|].
    destruct (represents_unique rho c z z' Hz Hz') as [HE|<-]; [now intros _|].
    apply necessary_intro. exists (S x), y, u. split; [now apply represents_step|].
    split; [exact Hy|]. split; [exact Hu|]. simpl. lia.
Qed.

Lemma rule_sound r : r < 7 -> holds rigid (rule r) root.
Proof.
  intros Hr. unfold rule. apply holds_bind. intros xs.
  apply arithmetic_sound; [exact Hr|apply names_shift].
Qed.

Lemma choose_codes rho xs n :
  (forall i, i < n -> necessary (exists x, represents rho (pair_at xs i) x)) ->
  necessary (exists f : nat -> nat, forall i, i < n -> represents rho (pair_at xs i) (f i)).
Proof.
  induction n as [|n IH]; intros H.
  - apply necessary_intro. exists (fun _ => 0). intros i Hi. lia.
  - assert (Hn : necessary (exists x, represents rho (pair_at xs n) x)) by (apply H; lia).
    eapply necessary_bind; [|exact Hn]. intros [x Hx].
    assert (Hrest : necessary (exists f : nat -> nat,
                forall i, i < n -> represents rho (pair_at xs i) (f i))).
    { apply IH. intros i Hi. apply H. lia. }
    eapply necessary_map; [|exact Hrest]. intros [f Hf].
    exists (fun i => if Nat.eq_dec i n then x else f i).
    intros i Hi. destruct (Nat.eq_dec i n) as [->|Hne]; [exact Hx|].
    apply Hf. lia.
Qed.

Lemma necessary_list {A} (p : A -> Prop) l :
  (forall x, In x l -> necessary (p x)) ->
  necessary (forall x, In x l -> p x).
Proof.
  induction l as [|a l IH]; intros H.
  - apply necessary_intro. simpl. contradiction.
  - assert (Ha : necessary (p a)) by (apply H; now left).
    eapply necessary_bind; [|exact Ha]. intros Hpa.
    assert (Hl : necessary (forall x, In x l -> p x)) by (apply IH; eauto using in_cons).
    eapply necessary_map; [|exact Hl].
    intros J x [<-|Hx]; auto.
Qed.

Lemma constraint_sound rho g xs cs f c :
  names rho g ->
  (forall i, i < bound cs -> represents rho (pair_at xs i) (f i)) ->
  In c cs -> holds rho (encode g xs c) root -> necessary (h10c_sem c f).
Proof.
  intros Hg Hf Hc Henc. apply bound_args in Hc.
  destruct c as [x|x y z|x y z]; cbn [encode h10c_sem] in *.
  - apply at_onep in Henc; [|exact Hg].
    eapply necessary_bind; [|exact Henc]. intros Hx.
    destruct (represents_unique _ _ _ _ (Hf x Hc) Hx) as [HE|He].
    + now intros _.
    + now apply necessary_intro.
  - apply at_addp in Henc; [|exact Hg].
    eapply necessary_bind; [|exact Henc]. intros [u [v [w [Hu [Hv [Hw He]]]]]].
    destruct Hc as [Hcx [Hcy Hcz]].
    destruct (represents_unique _ _ _ _ (Hf x Hcx) Hu) as [HE|<-]; [now intros _|].
    destruct (represents_unique _ _ _ _ (Hf y Hcy) Hv) as [HE|<-]; [now intros _|].
    destruct (represents_unique _ _ _ _ (Hf z Hcz) Hw) as [HE|<-]; [now intros _|].
    now apply necessary_intro.
  - apply at_mulp in Henc; [|exact Hg].
    eapply necessary_bind; [|exact Henc]. intros [u [v [w [Hu [Hv [Hw He]]]]]].
    destruct Hc as [Hcx [Hcy Hcz]].
    destruct (represents_unique _ _ _ _ (Hf x Hcx) Hu) as [HE|<-]; [now intros _|].
    destruct (represents_unique _ _ _ _ (Hf y Hcy) Hv) as [HE|<-]; [now intros _|].
    destruct (represents_unique _ _ _ _ (Hf z Hcz) Hw) as [HE|<-]; [now intros _|].
    now apply necessary_intro.
Qed.

Lemma premises_solution rho g xs cs :
  names rho g ->
  Forall (fun a => holds rho a root) (premises cs g xs) ->
  necessary (H10C_SAT cs).
Proof.
  intros Hg H. apply Forall_app in H as [Hnat Hcs].
  rewrite Forall_map, Forall_forall in Hnat.
  rewrite Forall_map, Forall_forall in Hcs.
  assert (Hchoose : necessary (exists f : nat -> nat,
    forall i, i < bound cs -> represents rho (pair_at xs i) (f i))).
  { apply choose_codes. intros i Hi. apply (proj1 (at_natp rho g (pair_at xs i) Hg)).
    apply Hnat, in_seq. lia. }
  eapply necessary_bind; [|exact Hchoose]. intros [f Hf].
  eapply necessary_map.
  - intros Hsem. exists f. exact Hsem.
  - apply necessary_list. intros c Hc. eapply constraint_sound; eauto.
Qed.

Lemma main_sound cs : (H10C_SAT cs -> E) -> holds rigid (main cs) root.
Proof.
  intros Hsol. unfold main. apply holds_bind. intros xs. apply holds_chain.
  intros v _ Hs.
  pose proof (names_shift (2*bound cs) xs) as Hg.
  destruct v.
  - apply holds_E. exact (premises_solution _ _ _ cs Hg Hs Hsol).
  - apply named_mark; [exact Hg|exact I].
  - apply named_mark; [exact Hg|exact I].
  - apply named_mark; [exact Hg|exact I].
Qed.
End Model.

Lemma backward cs : inh (context cs) (poly_var 0) -> H10C_SAT cs.
Proof.
  intros [M HM]. set (E := H10C_SAT cs).
  assert (H : holds E (rigid E) (poly_var 0) root).
  { eapply typing_sound; [exact HM|].
    intros a [<-|Ha].
    - apply main_sound. exact (fun h => h).
    - apply in_map_iff in Ha as [r [<- Hr]]. apply in_seq in Hr.
      apply rule_sound. lia. }
  exact (proj1 (unmarked E 0 root (fun h => h)) H).
Qed.

Theorem reduction : H10C_SAT ⪯ SysF_INH.
Proof.
  exists (fun cs => (context cs, poly_var 0)).
  intros cs. split; [apply forward|apply backward].
Qed.
