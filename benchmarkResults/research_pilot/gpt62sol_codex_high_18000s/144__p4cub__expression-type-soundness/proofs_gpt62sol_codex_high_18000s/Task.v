From Stdlib Require Import micromega.Lia ZArith NArith.

From Poulet4.P4cub.Semantics.Dynamic Require Import BigStep.Value.Typing BigStep.Semantics.

Require Import Poulet4.P4cub.Semantics.Static.Typing Poulet4.Utils.ForallMap.

Require Import VST.zlist.Zlist.
From Poulet4.P4cub.Semantics.Dynamic.BigStep Require Import Value.Syntax ExprUtil.
From Poulet4.P4cub.Semantics.Static Require Import Util.
From Poulet4.P4light.Syntax Require SyntaxUtil.
From Poulet4.P4light.Semantics Require Ops.

Section BigStepTheorems.

Local Open Scope nat_scope.

Local Lemma bit_mod_bound w z : BitArith.bound w (BitArith.mod_bound w z).
Proof.
  unfold BitArith.bound, BitArith.mod_bound.
  pose proof (Z.mod_pos_bound z (BitArith.upper_bound w)) as Hmod.
  assert (0 < BitArith.upper_bound w)%Z.
  { unfold BitArith.upper_bound. apply Z.pow_pos_nonneg; lia. }
  lia.
Qed.

Local Lemma bit_sat_bound w z : BitArith.bound w (BitArith.sat_bound w z).
Proof.
  assert (0 < BitArith.upper_bound w)%Z.
  { unfold BitArith.upper_bound. apply Z.pow_pos_nonneg; lia. }
  unfold BitArith.sat_bound, BitArith.bound, BitArith.maxZ.
  destruct (Z.gtb_spec z (BitArith.upper_bound w - 1)); [lia |].
  destruct (Z.ltb_spec z 0); lia.
Qed.

Local Lemma int_mod_bound w z : IntArith.bound w (IntArith.mod_bound w z).
Proof.
  assert (0 < IntArith.upper_bound w)%Z.
  { unfold IntArith.upper_bound. apply Z.pow_pos_nonneg; lia. }
  assert (IntArith.mod_amt w = 2 * IntArith.upper_bound w)%Z as Hwidth.
  { unfold IntArith.mod_amt, IntArith.upper_bound.
    replace (Z.pos w) with (Z.succ (Z.pos w - 1)) at 1 by lia.
    apply Z.pow_succ_r. lia. }
  unfold IntArith.mod_bound, IntArith.bound, IntArith.minZ, IntArith.maxZ.
  pose proof (Z.mod_pos_bound z (IntArith.mod_amt w)) as Hmod.
  destruct (Z.ltb_spec (z mod IntArith.mod_amt w) (IntArith.upper_bound w)); lia.
Qed.

Local Lemma int_sat_bound w z : IntArith.bound w (IntArith.sat_bound w z).
Proof.
  assert (0 < IntArith.upper_bound w)%Z.
  { unfold IntArith.upper_bound. apply Z.pow_pos_nonneg; lia. }
  unfold IntArith.sat_bound, IntArith.bound, IntArith.minZ, IntArith.maxZ.
  destruct (Z.gtb_spec z (IntArith.upper_bound w - 1)); [lia |].
  destruct (Z.ltb_spec z (- IntArith.upper_bound w)); lia.
Qed.

Local Lemma int_concat_bound w1 w2 z1 z2 :
  IntArith.bound (w1 + w2)%positive
    (IntArith.concat (N.pos w1) (N.pos w2) z1 z2).
Proof.
  unfold IntArith.concat.
  change (SyntaxUtil.pos_of_N (N.pos w1 + N.pos w2)%N)
    with (w1 + w2)%positive.
  apply int_mod_bound.
Qed.

Local Ltac invert_list_type :=
  match goal with
  | H : type_lst_ok _ _ _ |- _ => inversion H; subst; clear H
  end.

Local Ltac invert_value_types :=
  repeat match goal with
  | H : numeric _ |- _ => destruct H
  | H : numeric_width _ _ |- _ => inversion H; subst; clear H
  | H : type_val _ _ |- _ => inversion H; subst; clear H
  | H : type_lst_ok _ _ _ |- _ => invert_list_type
  end.

Local Ltac operator_bound :=
  cbn [BitArith.neg BitArith.bit_not BitArith.plus_mod BitArith.plus_sat
       BitArith.minus_mod BitArith.minus_sat BitArith.mult_mod
       BitArith.shift_left BitArith.shift_right BitArith.bit_and
       BitArith.bit_or BitArith.bit_xor BitArith.concat
       IntArith.neg IntArith.bit_not IntArith.plus_mod IntArith.plus_sat
       IntArith.minus_mod IntArith.minus_sat IntArith.mult_mod
       IntArith.shift_left IntArith.shift_right IntArith.bit_and
       IntArith.bit_or IntArith.bit_xor];
  first [assumption | apply bit_mod_bound | apply bit_sat_bound |
         apply int_mod_bound | apply int_sat_bound | apply int_concat_bound].

Local Lemma cast_typed target source v :
  proper_cast source target ->
  type_val v source ->
  exists result, eval_cast target v = Some result /\ type_val result target.
Proof.
  intros Hcast Hv. destruct Hcast; invert_value_types.
  all: try match goal with
           | |- context [eval_cast (Typ.Bit (N.pos ?w)) _] =>
               is_var w; destruct w
           | |- context [eval_cast (Typ.Bit ?w) _] =>
               is_var w; destruct w as [|p]; [|destruct p]
           end.
  all: eexists; split; [reflexivity |].
  all: first [apply typ_bit | apply typ_int | apply typ_bool | eapply typ_lists];
    try solve [operator_bound | constructor | assumption].
  destruct b; unfold BitArith.bound, BitArith.upper_bound; cbn; lia.
Qed.

Local Lemma unary_typed op source target v :
  una_type op source target ->
  type_val v source ->
  exists result, eval_una op v = Some result /\ type_val result target.
Proof.
  intros Hop Hv. destruct Hop; invert_value_types.
  all: eexists; split; [reflexivity |].
  all: first [apply typ_bit | apply typ_int | apply typ_bool | eapply typ_lists];
    try solve [operator_bound | constructor | assumption].
Qed.

Local Lemma binary_typed op left right target v1 v2 :
  bin_type op left right target ->
  type_val v1 left ->
  type_val v2 right ->
  exists result, eval_bin op v1 v2 = Some result /\ type_val result target.
Proof.
  intros Hop Hv1 Hv2. destruct Hop;
    try solve [eexists; split; [reflexivity | apply typ_bool]];
    invert_value_types.
  all: eexists; split; [reflexivity |].
  all: first [apply typ_bit | apply typ_int | apply typ_bool]; operator_bound.
Qed.

Local Lemma to_lbool_length w z : length (to_lbool w z) = N.to_nat w.
Proof.
  assert (forall n x acc, length (le_to_lbool' n x acc) = n + length acc) as H.
  { induction n as [|n IH]; intros x acc; [reflexivity |].
    cbn [le_to_lbool']. rewrite IH. cbn. lia. }
  unfold to_lbool. rewrite H. cbn. lia.
Qed.

Local Lemma bitstring_slice_length (A : Type) (bits : list A) lo hi :
  lo <= hi -> hi < length bits ->
  length (Ops.bitstring_slice bits lo hi) = hi - lo + 1.
Proof.
  assert (forall (xs : list A) start stop acc,
    start <= stop -> stop < length xs ->
    length (Ops.bitstring_slice' xs start stop acc) =
      stop - start + 1 + length acc) as H.
  { induction xs as [|x xs IH]; intros [|start] [|stop] acc Hlo Hhi;
      cbn in Hhi; try lia.
    - cbn. lia.
    - cbn [Ops.bitstring_slice']. rewrite IH by lia. cbn. lia.
    - cbn [Ops.bitstring_slice']. rewrite IH by lia. lia. }
  intros Hlo Hhi. unfold Ops.bitstring_slice.
  rewrite H by (try rewrite length_rev; lia). cbn. lia.
Qed.

Local Lemma le_lbool_to_val_bound bits order acc :
  (0 < order)%Z ->
  (acc <= BitArith.le_lbool_to_val bits order acc <=
    acc + order * (Z.pow 2 (Z.of_nat (length bits)) - 1))%Z.
Proof.
  revert order acc. induction bits as [|bit bits IH]; intros order acc Horder.
  - cbn. lia.
  - cbn [length BitArith.le_lbool_to_val].
    rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia.
    rewrite Z.shiftl_mul_pow2 by lia.
    change (Z.pow 2 1) with 2%Z.
    destruct bit.
    + specialize (IH (order * 2)%Z (acc + order)%Z ltac:(lia)).
      nia.
    + specialize (IH (order * 2)%Z acc ltac:(lia)).
      nia.
Qed.

Local Lemma slice_bits_typed bits hi lo w :
  length bits = N.to_nat w ->
  (N.pos lo <= N.pos hi < w)%N ->
  exists result,
    (let '(w', z) := BitArith.from_lbool
                     (Ops.bitstring_slice bits (Pos.to_nat lo) (Pos.to_nat hi)) in
     Some (Val.Bit w' z)) = Some result /\
    type_val result (Typ.Bit (N.pos hi - N.pos lo + 1)%N).
Proof.
  intros Hlength Hbounds.
  set (sliced := Ops.bitstring_slice bits (Pos.to_nat lo) (Pos.to_nat hi)).
  assert (Hwidth : Z.to_N (Zlength sliced) = (N.pos hi - N.pos lo + 1)%N).
  { apply N2Nat.inj. rewrite Z_N_nat, Zlength_correct, Nat2Z.id.
    rewrite N2Nat.inj_add, N2Nat.inj_sub.
    unfold sliced. rewrite bitstring_slice_length; lia. }
  unfold BitArith.from_lbool.
  eexists. split; [reflexivity |].
  rewrite <- Hwidth. constructor.
  unfold BitArith.bound, BitArith.upper_bound, BitArith.lbool_to_val.
  rewrite Z2N.id by (rewrite Zlength_correct; lia).
  rewrite Zlength_correct.
  pose proof (le_lbool_to_val_bound (rev sliced) 1 0 ltac:(lia)) as Hvalue.
  rewrite length_rev in Hvalue. lia.
Qed.

Local Lemma slice_typed hi lo w t v :
  (N.pos lo <= N.pos hi < w)%N ->
  numeric_width w t ->
  type_val v t ->
  exists result, slice_val hi lo v = Some result /\
    type_val result (Typ.Bit (N.pos hi - N.pos lo + 1)%N).
Proof.
  intros Hbounds Hwidth Hv. invert_value_types.
  all: cbn [slice_val]; eapply slice_bits_typed;
    [apply to_lbool_length | exact Hbounds].
Qed.

Local Lemma forall2_lookup_right {A B} (R : A -> B -> Prop) xs ys :
  Forall2 R xs ys ->
  forall i y, nth_error ys i = Some y ->
  exists x, nth_error xs i = Some x /\ R x y.
Proof.
  intros H. induction H as [|x y xs ys Hxy Hrest IH];
    intros [|i] found Hfind; cbn in Hfind; try discriminate.
  - injection Hfind as <-. exists x. split; [reflexivity | exact Hxy].
  - apply IH. exact Hfind.
Qed.

Local Lemma bound_array_index w n (τ : Typ.t) :
  BitArith.bound w n ->
  nth_error (repeat τ (N.to_nat (Z.to_N (BitArith.upper_bound w))))
            (Z.to_nat n) = Some τ.
Proof.
  intros Hbound. apply nth_error_repeat.
  rewrite Z_N_nat. unfold BitArith.bound in Hbound. lia.
Qed.

(* Recurse on typing, including the derivations stored in a list literal. *)
Local Lemma typed_evaluation : forall Δ Γ ϵ,
  Forall2 type_val ϵ Γ ->
  forall e τ, type_exp Δ Γ e τ ->
  exists v, exp_big_step ϵ e v /\ type_val v τ.
Proof.
  intros Δ Γ ϵ Henv.
  fix IH 3.
  intros e τ Htyped.
  destruct Htyped as
    [b | w n Hbound | w z Hbound | m w n Hwidth Hbound
    | τ og x Hlookup Hok
    | hi lo e w τ Hbounds Hwidth He
    | τ τ' e Hcast Hok He
    | op τ τ' e Hop Hok He
    | op τ1 τ2 τ e1 e2 Hop Hok He1 He2
    | e1 e2 w τ Hok He1 He2
    | τ x e τs b Hlookup Hok He
    | ls es τ τs Hls Hlst Hfields
    | err].
  - exists (Val.Bool b). split; constructor.
  - exists (Val.Bit w n). split; constructor; assumption.
  - exists (Val.Int w z). split; constructor; assumption.
  - exists (Val.VarBit m w n). split; constructor; assumption.
  - destruct (forall2_lookup_right _ _ _ Henv _ _ Hlookup)
      as [v [Hv Htype]].
    exists v. split; [apply ebs_var |]; assumption.
  - destruct (IH _ _ He) as [v [Hv Htype]].
    destruct (slice_typed _ _ _ _ _ Hbounds Hwidth Htype)
      as [result [Hresult Hresult_type]].
    exists result. split; [eapply ebs_slice |]; eassumption.
  - destruct (IH _ _ He) as [v [Hv Htype]].
    destruct (cast_typed _ _ _ Hcast Htype)
      as [result [Hresult Hresult_type]].
    exists result. split; [eapply ebs_cast |]; eassumption.
  - destruct (IH _ _ He) as [v [Hv Htype]].
    destruct (unary_typed _ _ _ _ Hop Htype)
      as [result [Hresult Hresult_type]].
    exists result. split; [eapply ebs_uop |]; eassumption.
  - destruct (IH _ _ He1) as [v1 [Hv1 Htype1]].
    destruct (IH _ _ He2) as [v2 [Hv2 Htype2]].
    destruct (binary_typed _ _ _ _ _ _ Hop Htype1 Htype2)
      as [result [Hresult Hresult_type]].
    exists result. split; [eapply ebs_bop |]; eassumption.
  - destruct (IH _ _ He1) as [v1 [Hv1 Htype1]].
    destruct (IH _ _ He2) as [v2 [Hv2 Htype2]].
    invert_value_types.
    match goal with
    | Hbound : BitArith.bound w ?n |- _ =>
        pose proof (bound_array_index w n τ Hbound) as Hindex
    end.
    match goal with
    | Hvalues : Forall2 type_val _ _ |- _ =>
        destruct (forall2_lookup_right _ _ _ Hvalues _ _ Hindex)
          as [result [Hresult Hresult_type]]
    end.
    exists result. split; [eapply ebs_index |]; eassumption.
  - destruct (IH _ _ He) as [v [Hv Htype]].
    inversion Htype; subst; invert_list_type.
    all: match goal with
         | Hvalues : Forall2 type_val _ _ |- _ =>
             destruct (forall2_lookup_right _ _ _ Hvalues _ _ Hlookup)
               as [result [Hresult Hresult_type]]
         end.
    all: exists result; split; [eapply ebs_member |]; eassumption.
  - assert (exists vs, Forall2 (exp_big_step ϵ) es vs /\
                       Forall2 type_val vs τs) as [vs [Heval Htypes]].
    { clear Hls Hlst. revert es τs Hfields.
      fix IHfields 3.
      intros es τs Hfields.
      destruct Hfields as [|e τ' es τs He Hrest].
      - exists []. split; constructor.
      - destruct (IH _ _ He) as [v [Hv Htype]].
        destruct (IHfields _ _ Hrest) as [vs [Hvs Htypes]].
        exists (v :: vs). split; constructor; assumption. }
    exists (Val.Lists ls vs). split.
    + apply ebs_lists. exact Heval.
    + eapply typ_lists; eassumption.
  - exists (Val.Error err). split; constructor.
Qed.

Local Ltac compare_evaluation IH Heval :=
  lazymatch type of Heval with
  | exp_big_step ?env ?e _ =>
      multimatch goal with
      | H : exp_big_step env e _ |- _ =>
          tryif constr_eq Heval H then fail
          else pose proof (IH _ _ Heval _ H)
      end
  end.

Local Lemma evaluation_deterministic : forall ϵ e v,
  exp_big_step ϵ e v -> forall v', exp_big_step ϵ e v' -> v = v'.
Proof.
  intros ϵ.
  fix IH 3.
  intros e v Heval.
  destruct Heval as
    [b | w n | w z | m w n | τ og x v Hlookup
    | e hi lo v result Hslice He
    | τ e v result Hcast He
    | err
    | τ op e v result Hunary He
    | τ op e1 e2 result v1 v2 Hbinary He1 He2
    | τ x e ls vs v Hlookup He
    | τ e1 e2 ls vs w n v Hlookup He1 He2
    | ls es vs Hfields].
  all: intros v' Hother; inversion Hother; subst; clear Hother;
    try reflexivity.
  - congruence.
  - compare_evaluation IH He. congruence.
  - compare_evaluation IH He. congruence.
  - compare_evaluation IH He. congruence.
  - compare_evaluation IH He1. compare_evaluation IH He2. congruence.
  - compare_evaluation IH He. congruence.
  - compare_evaluation IH He1. compare_evaluation IH He2. congruence.
  - f_equal.
    match goal with
    | H : Forall2 (exp_big_step ϵ) es ?vs' |- _ => revert vs' H
    end.
    revert es vs Hfields.
    fix IHfields 3.
    intros es vs Hfields.
    destruct Hfields as [|e v es vs He Htail];
      intros vs' Hother; inversion Hother; subst; clear Hother.
    + reflexivity.
    + f_equal.
      * compare_evaluation IH He. assumption.
      * eapply (IHfields _ _ Htail). eassumption.
Qed.

Section ExpPreservation.

Theorem exp_big_step_preservation : forall ϵ e v Δ Γ τ,
        ⟨ ϵ, e ⟩ ⇓ v ->
        Forall2 type_val ϵ Γ ->
        `⟨ Δ, Γ ⟩ ⊢ e ∈ τ ->
        ⊢ᵥ v ∈ τ.
Proof.
  intros ϵ e v Δ Γ τ Heval Henv Htype.
  destruct (typed_evaluation Δ Γ ϵ Henv e τ Htype)
    as [result [Hresult Hresult_type]].
  rewrite (evaluation_deterministic ϵ e v Heval result Hresult).
  exact Hresult_type.
Qed.

End ExpPreservation.

Section ExpProgress.

Theorem exp_big_step_progress : forall Δ Γ e τ ϵ,
        Forall2 type_val ϵ Γ ->
        `⟨ Δ, Γ ⟩ ⊢ e ∈ τ ->
        exists v, ⟨ ϵ, e ⟩ ⇓ v.
Proof.
  intros Δ Γ e τ ϵ Henv Htype.
  destruct (typed_evaluation Δ Γ ϵ Henv e τ Htype) as [v [Heval _]].
  exists v. exact Heval.
Qed.

End ExpProgress.

End BigStepTheorems.
