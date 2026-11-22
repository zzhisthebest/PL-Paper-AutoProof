Require Import Coq.micromega.Lia.
From Coq Require Import Lists.List Strings.String ZArith.BinInt NArith.BinNat NArith.Nnat ZArith.Znat ZArith.ZArith.
Require Import VST.zlist.Zlist.

From Poulet4.P4cub.Semantics.Dynamic Require Import BigStep.Value.Typing BigStep.Semantics.

Require Import Poulet4.P4cub.Semantics.Static.Typing Poulet4.Utils.ForallMap.

From Poulet4.P4cub.Semantics.Dynamic.BigStep.Value Require Import Syntax.
From Poulet4.P4cub.Semantics.Dynamic.BigStep Require Import ExprUtil.
Require Import Poulet4.P4cub.Semantics.Static.Util.
Require Import Poulet4.Utils.P4Arith.
Require Poulet4.P4light.Semantics.Ops.

Import ListNotations.
Close Scope Z_scope.

(* ===================================================================== *)
(* Arithmetic helper lemmas                                              *)
(* ===================================================================== *)

Section ZLemmas.
Local Open Scope Z_scope.

Lemma bit_upper_bound_pos (w : N) : 0 < BitArith.upper_bound w.
Proof. unfold BitArith.upper_bound. apply Z.pow_pos_nonneg; lia. Qed.

Lemma bit_mod_bound (w : N) (n : Z) : BitArith.bound w (BitArith.mod_bound w n).
Proof.
  unfold BitArith.bound, BitArith.mod_bound.
  pose proof bit_upper_bound_pos w.
  pose proof Z.mod_pos_bound n (BitArith.upper_bound w) H.
  lia.
Qed.

Lemma bit_sat_bound (w : N) (n : Z) : BitArith.bound w (BitArith.sat_bound w n).
Proof.
  unfold BitArith.bound, BitArith.sat_bound, BitArith.maxZ.
  pose proof bit_upper_bound_pos w as Hpos.
  destruct (n >? BitArith.upper_bound w - 1) eqn:E.
  - apply Z.gtb_lt in E. lia.
  - assert (Hge : ~ (BitArith.upper_bound w - 1 < n)).
    { intro Hc. apply Z.gtb_lt in Hc. rewrite Hc in E. discriminate. }
    destruct (n <? 0) eqn:E2.
    + apply Z.ltb_lt in E2. lia.
    + apply Z.ltb_ge in E2. lia.
Qed.

Lemma int_upper_bound_pos (w : positive) : 0 < IntArith.upper_bound w.
Proof. unfold IntArith.upper_bound. apply Z.pow_pos_nonneg; lia. Qed.

Lemma int_mod_amt_pos (w : positive) : 0 < IntArith.mod_amt w.
Proof. unfold IntArith.mod_amt. apply Z.pow_pos_nonneg; lia. Qed.

Lemma int_mod_bound (w : positive) (n : Z) : IntArith.bound w (IntArith.mod_bound w n).
Proof.
  unfold IntArith.bound, IntArith.mod_bound, IntArith.maxZ, IntArith.minZ,
         IntArith.mod_amt, IntArith.upper_bound.
  set (P := Z.pow 2 (Zpos w - 1)).
  assert (Hup : 0 < P) by (subst P; apply Z.pow_pos_nonneg; lia).
  assert (Hpow2 : Z.pow 2 (Zpos w) = P * 2).
  { subst P. change (Z.pow 2 (Zpos w) = Z.pow 2 (Zpos w - 1) * Z.pow 2 1).
    rewrite <- Z.pow_add_r by lia. f_equal. lia. }
  pose proof Z.mod_pos_bound n (Z.pow 2 (Zpos w)) ltac:(apply Z.pow_pos_nonneg; lia) as Hb.
  rewrite Hpow2 in Hb.
  rewrite Hpow2.
  set (m := n mod (P * 2)) in *.
  destruct (m <? P) eqn:E.
  - apply Z.ltb_lt in E. lia.
  - apply Z.ltb_ge in E. lia.
Qed.

Lemma int_sat_bound (w : positive) (n : Z) : IntArith.bound w (IntArith.sat_bound w n).
Proof.
  unfold IntArith.bound, IntArith.sat_bound, IntArith.maxZ, IntArith.minZ.
  pose proof int_upper_bound_pos w as Hpos.
  destruct (n >? IntArith.upper_bound w - 1) eqn:E.
  - apply Z.gtb_lt in E. lia.
  - assert (Hge : ~ (IntArith.upper_bound w - 1 < n)).
    { intro Hc. apply Z.gtb_lt in Hc. rewrite Hc in E. discriminate. }
    destruct (n <? - IntArith.upper_bound w) eqn:E2.
    + apply Z.ltb_lt in E2. lia.
    + apply Z.ltb_ge in E2. lia.
Qed.

Lemma le_lbool_to_val_cons_true (tl : list bool) (order res : Z) :
  BitArith.le_lbool_to_val (true :: tl) order res =
  BitArith.le_lbool_to_val tl (Z.shiftl order 1) (res + order).
Proof. reflexivity. Qed.

Lemma le_lbool_to_val_cons_false (tl : list bool) (order res : Z) :
  BitArith.le_lbool_to_val (false :: tl) order res =
  BitArith.le_lbool_to_val tl (Z.shiftl order 1) res.
Proof. reflexivity. Qed.

Lemma le_lbool_to_val_bound :
  forall (bits : list bool) (order res : Z),
    0 < order ->
    0 <= res ->
    res <= BitArith.le_lbool_to_val bits order res <=
           res + order * (Z.pow 2 (Zlength bits) - 1).
Proof.
  induction bits as [| hd tl IH]; intros order res Ho Hr.
  - simpl. lia.
  - rewrite Zlength_cons.
    rewrite Z.pow_succ_r by (apply Zlength_nonneg).
    set (P := Z.pow 2 (Zlength tl)) in *.
    clearbody P.
    assert (Hsh : Z.shiftl order 1 = order * 2).
    { rewrite Z.shiftl_mul_pow2 by lia. rewrite Z.pow_1_r. lia. }
    assert (Ho' : 0 < Z.shiftl order 1) by (rewrite Hsh; lia).
    destruct hd.
    + rewrite le_lbool_to_val_cons_true.
      specialize (IH (Z.shiftl order 1) (res + order) Ho' ltac:(lia)) as [IH1 IH2].
      split.
      * lia.
      * eapply Z.le_trans; [exact IH2 |]. rewrite Hsh. nia.
    + rewrite le_lbool_to_val_cons_false.
      specialize (IH (Z.shiftl order 1) res Ho' Hr) as [IH1 IH2].
      split.
      * exact IH1.
      * eapply Z.le_trans; [exact IH2 |]. rewrite Hsh. nia.
Qed.

Lemma lbool_to_val_bound (bits : list bool) :
  0 <= BitArith.lbool_to_val bits 1 0 <= Z.pow 2 (Zlength bits) - 1.
Proof.
  unfold BitArith.lbool_to_val.
  pose proof le_lbool_to_val_bound (rev bits) 1 0 ltac:(lia) ltac:(lia) as H.
  rewrite Zlength_rev in H.
  rewrite Z.add_0_l, Z.mul_1_l in H.
  exact H.
Qed.

Lemma from_lbool_bound (bits : list bool) :
  BitArith.bound (Z.to_N (Zlength bits)) (BitArith.lbool_to_val bits 1 0).
Proof.
  unfold BitArith.bound, BitArith.upper_bound.
  rewrite Z2N.id by apply Zlength_nonneg.
  pose proof lbool_to_val_bound bits as H.
  set (P := Z.pow 2 (Zlength bits)) in *.
  assert (HP : 0 < P) by (subst P; apply Z.pow_pos_nonneg; [lia | apply Zlength_nonneg]).
  lia.
Qed.

End ZLemmas.

Lemma le_to_lbool'_length :
  forall (k : nat) (v : Z) (res : list bool),
    length (le_to_lbool' k v res) = (k + length res)%nat.
Proof.
  induction k; intros; simpl; [lia|].
  rewrite IHk. simpl. lia.
Qed.

Lemma to_lbool_length (w : N) (n : Z) : length (to_lbool w n) = N.to_nat w.
Proof. unfold to_lbool. rewrite le_to_lbool'_length. simpl. lia. Qed.

Lemma Z_to_N_Zlength (l : list bool) : Z.to_N (Zlength l) = N.of_nat (length l).
Proof.
  apply N2Z.inj.
  rewrite Z2N.id by apply Zlength_nonneg.
  rewrite Zlength_correct.
  rewrite Znat.nat_N_Z.
  reflexivity.
Qed.

Lemma bitstring_slice'_length :
  forall {A : Type} (bits : list A) lo hi (slice : list A),
    (lo <= hi)%nat -> (hi < length bits)%nat ->
    length (Ops.bitstring_slice' bits lo hi slice) = (length slice + (hi - lo + 1))%nat.
Proof.
  intros A bits. induction bits as [| hd tl IH]; intros lo hi slice Hle Hlt.
  - simpl in Hlt. lia.
  - destruct lo as [| lo'], hi as [| hi'].
    + simpl. lia.
    + simpl. rewrite IH.
      * simpl. lia.
      * lia.
      * simpl in Hlt. lia.
    + lia.
    + simpl. rewrite IH.
      * lia.
      * lia.
      * simpl in Hlt. lia.
Qed.

Lemma bitstring_slice_length :
  forall {A : Type} (bits : list A) lo hi,
    (lo <= hi)%nat -> (hi < length bits)%nat ->
    length (Ops.bitstring_slice bits lo hi) = (hi - lo + 1)%nat.
Proof.
  intros. unfold Ops.bitstring_slice.
  rewrite bitstring_slice'_length; auto. rewrite length_rev. lia.
Qed.

Lemma Npos_to_nat_le (a b : positive) :
  (Npos a <= Npos b)%N -> (Pos.to_nat a <= Pos.to_nat b)%nat.
Proof.
  intro H. apply N2Z.inj_le in H.
  exact (proj1 (Z2Nat.inj_le (Z.pos a) (Z.pos b) ltac:(lia) ltac:(lia)) H).
Qed.

Lemma Npos_to_nat_lt_l (a : positive) (w : N) :
  (Npos a < w)%N -> (Pos.to_nat a < N.to_nat w)%nat.
Proof.
  intro H. apply N2Z.inj_lt in H.
  destruct w as [| p].
  - simpl in H. lia.
  - simpl. simpl in H.
    exact (proj1 (Z2Nat.inj_lt (Z.pos a) (Z.pos p) ltac:(lia) ltac:(lia)) H).
Qed.

Lemma slice_from_lbool_spec (w : N) (n : Z) (lo hi : positive) :
  (Npos lo <= Npos hi)%N ->
  (Npos hi < w)%N ->
  let bits' := Ops.bitstring_slice (to_lbool w n) (Pos.to_nat lo) (Pos.to_nat hi) in
  let '(w', n') := BitArith.from_lbool bits' in
  BitArith.bound w' n' /\ w' = (Npos hi - Npos lo + 1)%N.
Proof.
  intros Hle Hlt.
  set (bits0 := to_lbool w n).
  set (bits' := Ops.bitstring_slice bits0 (Pos.to_nat lo) (Pos.to_nat hi)).
  assert (Hle' : (Pos.to_nat lo <= Pos.to_nat hi)%nat).
  { apply Npos_to_nat_le. exact Hle. }
  assert (Hhi' : (Pos.to_nat hi < N.to_nat w)%nat).
  { apply Npos_to_nat_lt_l. exact Hlt. }
  assert (Hlen0 : length bits0 = N.to_nat w).
  { subst bits0. apply to_lbool_length. }
  assert (Hlen : length bits' = (Pos.to_nat hi - Pos.to_nat lo + 1)%nat).
  { subst bits'. apply bitstring_slice_length; [exact Hle'|]. rewrite Hlen0. exact Hhi'. }
  destruct (BitArith.from_lbool bits') as [w' n'] eqn:E.
  unfold BitArith.from_lbool in E. injection E as Hw Hn. subst w'. subst n'.
  simpl. split.
  - apply from_lbool_bound.
  - rewrite Z_to_N_Zlength, Hlen.
    rewrite Nat2N.inj_add, Nat2N.inj_sub.
    rewrite Znat.positive_nat_N, Znat.positive_nat_N.
    reflexivity.
Qed.

Lemma index_in_bounds (w : N) (n : Z) :
  BitArith.bound w n ->
  (Z.to_nat n < N.to_nat (Z.to_N (BitArith.upper_bound w)))%nat.
Proof.
  intros H. unfold BitArith.bound, BitArith.upper_bound in H.
  rewrite Znat.Z_N_nat.
  apply Z2Nat.inj_lt.
  - lia.
  - apply Z.pow_nonneg; lia.
  - exact (proj2 H).
Qed.

Lemma slice_from_lbool_spec' (w : N) (n : Z) (lo hi : positive) (w' : N) (n' : Z) :
  (Npos lo <= Npos hi)%N -> (Npos hi < w)%N ->
  BitArith.from_lbool (Ops.bitstring_slice (to_lbool w n) (Pos.to_nat lo) (Pos.to_nat hi)) = (w', n') ->
  BitArith.bound w' n' /\ w' = (Npos hi - Npos lo + 1)%N.
Proof.
  intros Hle Hlt E.
  pose proof (slice_from_lbool_spec w n lo hi Hle Hlt) as Hspec.
  cbv zeta in Hspec.
  rewrite E in Hspec. exact Hspec.
Qed.

(* ===================================================================== *)
(* Value shape lemmas                                                    *)
(* ===================================================================== *)

Lemma type_lst_ok_array_inv : forall ls (w : N) (τ : Typ.t) τs,
  type_lst_ok ls (Typ.Array w τ) τs ->
  ls = Lst.Array τ /\ τs = repeat τ (N.to_nat w).
Proof. intros. inversion H. subst. auto. Qed.

Lemma type_lst_ok_struct_inv : forall ls (b : bool) τs τs',
  type_lst_ok ls (Typ.Struct b τs) τs' ->
  (b = false /\ ls = Lst.Struct /\ τs' = τs) \/
  (b = true /\ exists b0, ls = Lst.Header b0 /\ τs' = τs).
Proof.
  intros ls b τs τs' H. destruct b.
  - inversion H; subst. right. eauto.
  - inversion H; subst. left. eauto.
Qed.

Lemma type_val_bool_inv (v : Val.t) :
  type_val v Typ.Bool -> exists b, v = Val.Bool b.
Proof.
  intros H. inversion H; subst; eauto.
  match goal with H2 : type_lst_ok _ _ _ |- _ => inversion H2 end.
Qed.

Lemma type_val_bit_inv (w : N) (v : Val.t) :
  type_val v (Typ.Bit w) -> exists n, v = Val.Bit w n /\ BitArith.bound w n.
Proof.
  intros H. inversion H; subst; eauto.
  match goal with H2 : type_lst_ok _ _ _ |- _ => inversion H2 end.
Qed.

Lemma type_val_int_inv (w : positive) (v : Val.t) :
  type_val v (Typ.Int w) -> exists n, v = Val.Int w n /\ IntArith.bound w n.
Proof.
  intros H. inversion H; subst; eauto.
  match goal with H2 : type_lst_ok _ _ _ |- _ => inversion H2 end.
Qed.

Lemma type_val_varbit_inv (m : N) (v : Val.t) :
  type_val v (Typ.VarBit m) ->
  exists w n, v = Val.VarBit m w n /\ (w <= m)%N /\ BitArith.bound w n.
Proof.
  intros H. inversion H; subst; eauto.
  match goal with H2 : type_lst_ok _ _ _ |- _ => inversion H2 end.
Qed.

Lemma type_val_error_inv (v : Val.t) :
  type_val v Typ.Error -> exists e, v = Val.Error e.
Proof.
  intros H. inversion H; subst; eauto.
  match goal with H2 : type_lst_ok _ _ _ |- _ => inversion H2 end.
Qed.

Lemma type_val_struct_true_inv (ts : list Typ.t) (v : Val.t) :
  type_val v (Typ.Struct true ts) ->
  exists b vs, v = Val.Lists (Lst.Header b) vs /\ Forall2 type_val vs ts.
Proof.
  intros H. inversion H; subst; try (match goal with H2 : type_lst_ok _ _ _ |- _ => inversion H2 end).
  match goal with H2 : type_lst_ok _ _ _ |- _ =>
    destruct (type_lst_ok_struct_inv _ _ _ _ H2) as [[Hb [_ _]] | [Hb [b0 [Hls Hts]]]] end.
  - discriminate.
  - subst. eauto.
Qed.

Lemma type_val_struct_false_inv (ts : list Typ.t) (v : Val.t) :
  type_val v (Typ.Struct false ts) ->
  exists vs, v = Val.Lists Lst.Struct vs /\ Forall2 type_val vs ts.
Proof.
  intros H. inversion H; subst; try (match goal with H2 : type_lst_ok _ _ _ |- _ => inversion H2 end).
  match goal with H2 : type_lst_ok _ _ _ |- _ =>
    destruct (type_lst_ok_struct_inv _ _ _ _ H2) as [[Hb [Hls Hts]] | [Hb [_ _]]] end.
  - subst. eauto.
  - discriminate.
Qed.

Lemma type_val_array_inv (w : N) (τ : Typ.t) (v : Val.t) :
  type_val v (Typ.Array w τ) ->
  exists vs, v = Val.Lists (Lst.Array τ) vs /\ Forall2 type_val vs (repeat τ (N.to_nat w)).
Proof.
  intros H. inversion H; subst; try (match goal with H2 : type_lst_ok _ _ _ |- _ => inversion H2 end).
  match goal with H2 : type_lst_ok _ _ _ |- _ =>
    destruct (type_lst_ok_array_inv _ _ _ _ H2) as [Hls Hts] end. subst. eauto.
Qed.

Lemma type_val_numeric_inv (τ : Typ.t) (v : Val.t) :
  numeric τ -> type_val v τ ->
  (exists w n, τ = Typ.Bit w /\ v = Val.Bit w n /\ BitArith.bound w n) \/
  (exists w n, τ = Typ.Int w /\ v = Val.Int w n /\ IntArith.bound w n).
Proof.
  intros [w Hnw] Htv. inversion Hnw; subst.
  - left. apply type_val_bit_inv in Htv. destruct Htv as [n [-> Hb]]. eauto.
  - right. apply type_val_int_inv in Htv. destruct Htv as [n [-> Hb]]. eauto.
Qed.

Lemma numeric_width_inv (w : N) (τ : Typ.t) :
  numeric_width w τ -> τ = Typ.Bit w \/ (exists w', w = Npos w' /\ τ = Typ.Int w').
Proof. intros H. inversion H; subst; [left; reflexivity | right; eauto]. Qed.

(* ===================================================================== *)
(* Evaluation lemmas                                                     *)
(* ===================================================================== *)

Lemma slice_val_bit_spec (w : N) (n : Z) (lo hi : positive) :
  (Npos lo <= Npos hi)%N -> (Npos hi < w)%N ->
  exists v', slice_val hi lo (Val.Bit w n) = Some v' /\
             type_val v' (Typ.Bit (Npos hi - Npos lo + 1)%N).
Proof.
  intros Hle Hlt.
  unfold slice_val.
  set (bits' := Ops.bitstring_slice (to_lbool w n) (Pos.to_nat lo) (Pos.to_nat hi)).
  destruct (BitArith.from_lbool bits') as [w1 n1] eqn:E.
  destruct (slice_from_lbool_spec' w n lo hi w1 n1 Hle Hlt E) as [Hb Hw].
  exists (Val.Bit w1 n1). split.
  - reflexivity.
  - rewrite Hw. rewrite Hw in Hb. apply typ_bit. exact Hb.
Qed.

Lemma slice_val_int_spec (w : positive) (n : Z) (lo hi : positive) :
  (Npos lo <= Npos hi)%N -> (Npos hi < Npos w)%N ->
  exists v', slice_val hi lo (Val.Int w n) = Some v' /\
             type_val v' (Typ.Bit (Npos hi - Npos lo + 1)%N).
Proof.
  intros Hle Hlt.
  unfold slice_val.
  set (bits' := Ops.bitstring_slice (to_lbool (Npos w) n) (Pos.to_nat lo) (Pos.to_nat hi)).
  destruct (BitArith.from_lbool bits') as [w1 n1] eqn:E.
  destruct (slice_from_lbool_spec' (Npos w) n lo hi w1 n1 Hle Hlt E) as [Hb Hw].
  exists (Val.Bit w1 n1). split.
  - reflexivity.
  - rewrite Hw. rewrite Hw in Hb. apply typ_bit. exact Hb.
Qed.

Lemma slice_val_spec (v : Val.t) (τ : Typ.t) (w : N) (lo hi : positive) :
  numeric_width w τ -> type_val v τ ->
  (Npos lo <= Npos hi)%N -> (Npos hi < w)%N ->
  exists v', slice_val hi lo v = Some v' /\
             type_val v' (Typ.Bit (Npos hi - Npos lo + 1)%N).
Proof.
  intros Hnw Htv Hle Hlt.
  destruct (numeric_width_inv w τ Hnw) as [Heq | [w' [Heqw Heqτ]]]; subst.
  - apply type_val_bit_inv in Htv. destruct Htv as [n [-> Hb]].
    apply slice_val_bit_spec; auto.
  - apply type_val_int_inv in Htv. destruct Htv as [n [-> Hb]].
    apply slice_val_int_spec; auto.
Qed.

(* ---------------- cast ---------------- *)

Lemma eval_cast_spec : forall (τ' τ : Typ.t) (v : Val.t),
  proper_cast τ' τ -> type_val v τ' ->
  exists v', eval_cast τ v = Some v' /\ type_val v' τ.
Proof.
  intros τ' τ v Hpc Htv. destruct Hpc.
  - (* pc_bool_bit *)
    apply type_val_bool_inv in Htv. destruct Htv as [b ->].
    eexists. split; [reflexivity|]. apply typ_bit.
    destruct b; unfold BitArith.bound, BitArith.upper_bound; simpl; lia.
  - (* pc_bit_bool *)
    apply type_val_bit_inv in Htv. destruct Htv as [n [-> Hb]].
    eexists. split; [reflexivity|]. apply typ_bool.
  - (* pc_bit_int w *)
    apply type_val_bit_inv in Htv. destruct Htv as [n [-> Hb]].
    eexists. split; [reflexivity|]. apply typ_int. apply int_mod_bound.
  - (* pc_int_bit w *)
    apply type_val_int_inv in Htv. destruct Htv as [n [-> Hb]].
    destruct w.
    all: eexists; split; [reflexivity|]; apply typ_bit; apply bit_mod_bound.
  - (* pc_bit_bit *)
    apply type_val_bit_inv in Htv. destruct Htv as [n [-> Hb]].
    destruct w2 as [|p]; [| destruct p].
    all: eexists; split; [reflexivity|]; apply typ_bit; apply bit_mod_bound.
  - (* pc_int_int *)
    apply type_val_int_inv in Htv. destruct Htv as [n [-> Hb]].
    eexists. split; [reflexivity|]. apply typ_int. apply int_mod_bound.
  - (* pc_struct_hdr *)
    apply type_val_struct_true_inv in Htv.
    destruct Htv as [b [vs [-> HF]]].
    eexists. split; [reflexivity|].
    eapply typ_lists. apply type_struct_ok. exact HF.
Qed.

(* ---------------- unary ---------------- *)

Lemma eval_una_spec : forall (op : Una.t) (τ τ' : Typ.t) (v : Val.t),
  una_type op τ τ' -> type_val v τ ->
  exists v', eval_una op v = Some v' /\ type_val v' τ'.
Proof.
  intros op τ τ' v Hut Htv. destruct Hut as [| τa Hnum | τa Hnum | ts | b ts].
  - (* una_Bool *)
    apply type_val_bool_inv in Htv. destruct Htv as [b ->].
    eexists. split; [reflexivity|]. apply typ_bool.
  - (* una_BitNot, numeric τ *)
    destruct Hnum as [w Hnw].
    destruct Hnw.
    + apply type_val_bit_inv in Htv. destruct Htv as [n [-> Hb]].
      eexists. split; [reflexivity|]. apply typ_bit. apply bit_mod_bound.
    + apply type_val_int_inv in Htv. destruct Htv as [n [-> Hb]].
      eexists. split; [reflexivity|]. apply typ_int. apply int_mod_bound.
  - (* una_UMinus, numeric τ *)
    destruct Hnum as [w Hnw].
    destruct Hnw.
    + apply type_val_bit_inv in Htv. destruct Htv as [n [-> Hb]].
      eexists. split; [reflexivity|]. apply typ_bit. apply bit_mod_bound.
    + apply type_val_int_inv in Htv. destruct Htv as [n [-> Hb]].
      eexists. split; [reflexivity|]. apply typ_int. apply int_mod_bound.
  - (* una_IsValid *)
    apply type_val_struct_true_inv in Htv.
    destruct Htv as [b [vs [-> HF]]].
    eexists. split; [reflexivity|]. apply typ_bool.
  - (* una_SetValidity *)
    apply type_val_struct_true_inv in Htv.
    destruct Htv as [b0 [vs [-> HF]]].
    eexists. split; [reflexivity|].
    eapply typ_lists. apply type_header_ok. exact HF.
Qed.

(* ---------------- binary ---------------- *)

Lemma eval_bin_spec : forall (op : Bin.t) (τ1 τ2 τ : Typ.t) (v1 v2 : Val.t),
  bin_type op τ1 τ2 τ -> type_val v1 τ1 -> type_val v2 τ2 ->
  exists v, eval_bin op v1 v2 = Some v /\ type_val v τ.
Proof.
  intros op τ1 τ2 τ v1 v2 Hbt Htv1 Htv2.
  destruct Hbt as
    [ τa Hnum | τa Hnum | τa Hnum | τa Hnum | τa Hnum
    | τa w2 Hnum | τa w2 Hnum
    | τa Hnum | τa Hnum | τa Hnum
    | τa Hnum | τa Hnum | τa Hnum | τa Hnum
    | | | τa | τa
    | w1 w2 τ2b Hnw2 | w1 w2 τ2b Hnw2 | w1 τ2b Hnw2 ].
  - (* Plus *)
    destruct Hnum as [w Hnw].
    destruct Hnw.
    + apply type_val_bit_inv in Htv1. destruct Htv1 as [n1 [-> Hb1]].
      apply type_val_bit_inv in Htv2. destruct Htv2 as [n2 [-> Hb2]].
      eexists. split; [reflexivity|]. apply typ_bit. apply bit_mod_bound.
    + apply type_val_int_inv in Htv1. destruct Htv1 as [n1 [-> Hb1]].
      apply type_val_int_inv in Htv2. destruct Htv2 as [n2 [-> Hb2]].
      eexists. split; [reflexivity|]. apply typ_int. apply int_mod_bound.
  - (* PlusSat *)
    destruct Hnum as [w Hnw].
    destruct Hnw.
    + apply type_val_bit_inv in Htv1. destruct Htv1 as [n1 [-> Hb1]].
      apply type_val_bit_inv in Htv2. destruct Htv2 as [n2 [-> Hb2]].
      eexists. split; [reflexivity|]. apply typ_bit. apply bit_sat_bound.
    + apply type_val_int_inv in Htv1. destruct Htv1 as [n1 [-> Hb1]].
      apply type_val_int_inv in Htv2. destruct Htv2 as [n2 [-> Hb2]].
      eexists. split; [reflexivity|]. apply typ_int. apply int_sat_bound.
  - (* Minus *)
    destruct Hnum as [w Hnw].
    destruct Hnw.
    + apply type_val_bit_inv in Htv1. destruct Htv1 as [n1 [-> Hb1]].
      apply type_val_bit_inv in Htv2. destruct Htv2 as [n2 [-> Hb2]].
      eexists. split; [reflexivity|]. apply typ_bit. apply bit_mod_bound.
    + apply type_val_int_inv in Htv1. destruct Htv1 as [n1 [-> Hb1]].
      apply type_val_int_inv in Htv2. destruct Htv2 as [n2 [-> Hb2]].
      eexists. split; [reflexivity|]. apply typ_int. apply int_mod_bound.
  - (* MinusSat *)
    destruct Hnum as [w Hnw].
    destruct Hnw.
    + apply type_val_bit_inv in Htv1. destruct Htv1 as [n1 [-> Hb1]].
      apply type_val_bit_inv in Htv2. destruct Htv2 as [n2 [-> Hb2]].
      eexists. split; [reflexivity|]. apply typ_bit. apply bit_sat_bound.
    + apply type_val_int_inv in Htv1. destruct Htv1 as [n1 [-> Hb1]].
      apply type_val_int_inv in Htv2. destruct Htv2 as [n2 [-> Hb2]].
      eexists. split; [reflexivity|]. apply typ_int. apply int_sat_bound.
  - (* Times *)
    destruct Hnum as [w Hnw].
    destruct Hnw.
    + apply type_val_bit_inv in Htv1. destruct Htv1 as [n1 [-> Hb1]].
      apply type_val_bit_inv in Htv2. destruct Htv2 as [n2 [-> Hb2]].
      eexists. split; [reflexivity|]. apply typ_bit. apply bit_mod_bound.
    + apply type_val_int_inv in Htv1. destruct Htv1 as [n1 [-> Hb1]].
      apply type_val_int_inv in Htv2. destruct Htv2 as [n2 [-> Hb2]].
      eexists. split; [reflexivity|]. apply typ_int. apply int_mod_bound.
  - (* Shl *)
    destruct Hnum as [w Hnw].
    apply type_val_bit_inv in Htv2. destruct Htv2 as [n2 [-> Hb2]].
    destruct Hnw.
    + apply type_val_bit_inv in Htv1. destruct Htv1 as [n1 [-> Hb1]].
      eexists. split; [reflexivity|]. apply typ_bit. apply bit_mod_bound.
    + apply type_val_int_inv in Htv1. destruct Htv1 as [n1 [-> Hb1]].
      eexists. split; [reflexivity|]. apply typ_int. apply int_mod_bound.
  - (* Shr *)
    destruct Hnum as [w Hnw].
    apply type_val_bit_inv in Htv2. destruct Htv2 as [n2 [-> Hb2]].
    destruct Hnw.
    + apply type_val_bit_inv in Htv1. destruct Htv1 as [n1 [-> Hb1]].
      eexists. split; [reflexivity|]. apply typ_bit. apply bit_mod_bound.
    + apply type_val_int_inv in Htv1. destruct Htv1 as [n1 [-> Hb1]].
      eexists. split; [reflexivity|]. apply typ_int. apply int_mod_bound.
  - (* BitAnd *)
    destruct Hnum as [w Hnw].
    destruct Hnw.
    + apply type_val_bit_inv in Htv1. destruct Htv1 as [n1 [-> Hb1]].
      apply type_val_bit_inv in Htv2. destruct Htv2 as [n2 [-> Hb2]].
      eexists. split; [reflexivity|]. apply typ_bit. apply bit_mod_bound.
    + apply type_val_int_inv in Htv1. destruct Htv1 as [n1 [-> Hb1]].
      apply type_val_int_inv in Htv2. destruct Htv2 as [n2 [-> Hb2]].
      eexists. split; [reflexivity|]. apply typ_int. apply int_mod_bound.
  - (* BitXor *)
    destruct Hnum as [w Hnw].
    destruct Hnw.
    + apply type_val_bit_inv in Htv1. destruct Htv1 as [n1 [-> Hb1]].
      apply type_val_bit_inv in Htv2. destruct Htv2 as [n2 [-> Hb2]].
      eexists. split; [reflexivity|]. apply typ_bit. apply bit_mod_bound.
    + apply type_val_int_inv in Htv1. destruct Htv1 as [n1 [-> Hb1]].
      apply type_val_int_inv in Htv2. destruct Htv2 as [n2 [-> Hb2]].
      eexists. split; [reflexivity|]. apply typ_int. apply int_mod_bound.
  - (* BitOr *)
    destruct Hnum as [w Hnw].
    destruct Hnw.
    + apply type_val_bit_inv in Htv1. destruct Htv1 as [n1 [-> Hb1]].
      apply type_val_bit_inv in Htv2. destruct Htv2 as [n2 [-> Hb2]].
      eexists. split; [reflexivity|]. apply typ_bit. apply bit_mod_bound.
    + apply type_val_int_inv in Htv1. destruct Htv1 as [n1 [-> Hb1]].
      apply type_val_int_inv in Htv2. destruct Htv2 as [n2 [-> Hb2]].
      eexists. split; [reflexivity|]. apply typ_int. apply int_mod_bound.
  - (* Le *)
    destruct Hnum as [w Hnw].
    destruct Hnw.
    + apply type_val_bit_inv in Htv1. destruct Htv1 as [n1 [-> Hb1]].
      apply type_val_bit_inv in Htv2. destruct Htv2 as [n2 [-> Hb2]].
      eexists. split; [reflexivity|]. apply typ_bool.
    + apply type_val_int_inv in Htv1. destruct Htv1 as [n1 [-> Hb1]].
      apply type_val_int_inv in Htv2. destruct Htv2 as [n2 [-> Hb2]].
      eexists. split; [reflexivity|]. apply typ_bool.
  - (* Lt *)
    destruct Hnum as [w Hnw].
    destruct Hnw.
    + apply type_val_bit_inv in Htv1. destruct Htv1 as [n1 [-> Hb1]].
      apply type_val_bit_inv in Htv2. destruct Htv2 as [n2 [-> Hb2]].
      eexists. split; [reflexivity|]. apply typ_bool.
    + apply type_val_int_inv in Htv1. destruct Htv1 as [n1 [-> Hb1]].
      apply type_val_int_inv in Htv2. destruct Htv2 as [n2 [-> Hb2]].
      eexists. split; [reflexivity|]. apply typ_bool.
  - (* Ge *)
    destruct Hnum as [w Hnw].
    destruct Hnw.
    + apply type_val_bit_inv in Htv1. destruct Htv1 as [n1 [-> Hb1]].
      apply type_val_bit_inv in Htv2. destruct Htv2 as [n2 [-> Hb2]].
      eexists. split; [reflexivity|]. apply typ_bool.
    + apply type_val_int_inv in Htv1. destruct Htv1 as [n1 [-> Hb1]].
      apply type_val_int_inv in Htv2. destruct Htv2 as [n2 [-> Hb2]].
      eexists. split; [reflexivity|]. apply typ_bool.
  - (* Gt *)
    destruct Hnum as [w Hnw].
    destruct Hnw.
    + apply type_val_bit_inv in Htv1. destruct Htv1 as [n1 [-> Hb1]].
      apply type_val_bit_inv in Htv2. destruct Htv2 as [n2 [-> Hb2]].
      eexists. split; [reflexivity|]. apply typ_bool.
    + apply type_val_int_inv in Htv1. destruct Htv1 as [n1 [-> Hb1]].
      apply type_val_int_inv in Htv2. destruct Htv2 as [n2 [-> Hb2]].
      eexists. split; [reflexivity|]. apply typ_bool.
  - (* And *)
    apply type_val_bool_inv in Htv1. destruct Htv1 as [b1 ->].
    apply type_val_bool_inv in Htv2. destruct Htv2 as [b2 ->].
    eexists. split; [reflexivity|]. apply typ_bool.
  - (* Or *)
    apply type_val_bool_inv in Htv1. destruct Htv1 as [b1 ->].
    apply type_val_bool_inv in Htv2. destruct Htv2 as [b2 ->].
    eexists. split; [reflexivity|]. apply typ_bool.
  - (* Eq *)
    eexists. split; [reflexivity|]. apply typ_bool.
  - (* NotEq *)
    eexists. split; [reflexivity|]. apply typ_bool.
  - (* PlusPlusBit *)
    apply type_val_bit_inv in Htv1. destruct Htv1 as [n1 [-> Hb1]].
    destruct Hnw2.
    + apply type_val_bit_inv in Htv2. destruct Htv2 as [n2 [-> Hb2]].
      eexists. split; [reflexivity|]. apply typ_bit. apply bit_mod_bound.
    + apply type_val_int_inv in Htv2. destruct Htv2 as [n2 [-> Hb2]].
      eexists. split; [reflexivity|]. apply typ_bit. apply bit_mod_bound.
  - (* PlusPlusInt *)
    apply type_val_int_inv in Htv1. destruct Htv1 as [n1 [-> Hb1]].
    inversion Hnw2; subst.
    + apply type_val_bit_inv in Htv2. destruct Htv2 as [n2 [-> Hb2]].
      eexists. split; [reflexivity|]. apply typ_int. apply int_mod_bound.
    + apply type_val_int_inv in Htv2. destruct Htv2 as [n2 [-> Hb2]].
      eexists. split; [reflexivity|]. apply typ_int. apply int_mod_bound.
  - (* PlusPlusIntZero *)
    apply type_val_int_inv in Htv1. destruct Htv1 as [n1 [-> Hb1]].
    inversion Hnw2; subst.
    apply type_val_bit_inv in Htv2. destruct Htv2 as [n2 [-> Hb2]].
    eexists. split; [reflexivity|]. apply typ_int. exact Hb1.
Qed.

(* ===================================================================== *)
(* List helpers, expression size, strong induction                       *)
(* ===================================================================== *)

(* ------------- Forall2 nth ------------- *)

Lemma Forall2_nth_error_r :
  forall (A B : Type) (R : A -> B -> Prop) (l1 : list A) (l2 : list B) (n : nat) (b : B),
    Forall2 R l1 l2 -> nth_error l2 n = Some b ->
    exists a, nth_error l1 n = Some a /\ R a b.
Proof.
  intros A B R l1 l2. revert l2.
  induction l1 as [| a l1 IH]; intros l2 n b HF Hn.
  - destruct l2 as [| b0 l2].
    + destruct n; simpl in Hn; discriminate.
    + inversion HF.
  - destruct l2 as [| b0 l2].
    + inversion HF.
    + inversion HF as [| a0 b0' l1' l2' HR HF']; subst.
      destruct n as [| n]; simpl in Hn.
      * injection Hn as ->. exists a. split; [reflexivity| exact HR].
      * apply (IH l2 n b HF') in Hn. destruct Hn as [x [Hx HRx]].
        exists x. split; assumption.
Qed.

(* ------------- inversion lemmas: big step ------------- *)

Lemma ebs_bool_inv (ϵ : list Val.t) (b : bool) (v : Val.t) :
  exp_big_step ϵ (Exp.Bool b) v -> v = Val.Bool b.
Proof. intros H; inversion H; reflexivity. Qed.

Lemma ebs_varbit_inv (ϵ : list Val.t) (m w : N) (n : Z) (v : Val.t) :
  exp_big_step ϵ (Exp.VarBit m w n) v -> v = Val.VarBit m w n.
Proof. intros H; inversion H; reflexivity. Qed.

Lemma ebs_bit_inv (ϵ : list Val.t) (w : N) (n : Z) (v : Val.t) :
  exp_big_step ϵ (Exp.Bit w n) v -> v = Val.Bit w n.
Proof. intros H; inversion H; reflexivity. Qed.

Lemma ebs_int_inv (ϵ : list Val.t) (p : positive) (n : Z) (v : Val.t) :
  exp_big_step ϵ (Exp.Int p n) v -> v = Val.Int p n.
Proof. intros H; inversion H; reflexivity. Qed.

Lemma ebs_var_inv (ϵ : list Val.t) (ty : Typ.t) (og : String.string) (x : nat) (v : Val.t) :
  exp_big_step ϵ (Exp.Var ty og x) v -> nth_error ϵ x = Some v.
Proof. intros H; inversion H; assumption. Qed.

Lemma ebs_slice_inv (ϵ : list Val.t) (hi lo : positive) (e : Exp.t) (v : Val.t) :
  exp_big_step ϵ (Exp.Slice hi lo e) v ->
  exists v0, slice_val hi lo v0 = Some v /\ exp_big_step ϵ e v0.
Proof. intros H; inversion H; subst; eauto. Qed.

Lemma ebs_cast_inv (ϵ : list Val.t) (ty : Typ.t) (e : Exp.t) (v : Val.t) :
  exp_big_step ϵ (Exp.Cast ty e) v ->
  exists v0, eval_cast ty v0 = Some v /\ exp_big_step ϵ e v0.
Proof. intros H; inversion H; subst; eauto. Qed.

Lemma ebs_error_inv (ϵ : list Val.t) (err : String.string) (v : Val.t) :
  exp_big_step ϵ (Exp.Error err) v -> v = Val.Error err.
Proof. intros H; inversion H; reflexivity. Qed.

Lemma ebs_uop_inv (ϵ : list Val.t) (r : Typ.t) (op : Una.t) (e : Exp.t) (v : Val.t) :
  exp_big_step ϵ (Exp.Uop r op e) v ->
  exists v0, eval_una op v0 = Some v /\ exp_big_step ϵ e v0.
Proof. intros H; inversion H; subst; eauto. Qed.

Lemma ebs_bop_inv (ϵ : list Val.t) (r : Typ.t) (op : Bin.t) (e1 e2 : Exp.t) (v : Val.t) :
  exp_big_step ϵ (Exp.Bop r op e1 e2) v ->
  exists v1 v2, eval_bin op v1 v2 = Some v /\
               exp_big_step ϵ e1 v1 /\ exp_big_step ϵ e2 v2.
Proof. intros H; inversion H; subst; eauto. Qed.

Lemma ebs_member_inv (ϵ : list Val.t) (r : Typ.t) (x : nat) (e : Exp.t) (v : Val.t) :
  exp_big_step ϵ (Exp.Member r x e) v ->
  exists ls vs, nth_error vs x = Some v /\ exp_big_step ϵ e (Val.Lists ls vs).
Proof. intros H; inversion H; subst; eauto. Qed.

Lemma ebs_index_inv (ϵ : list Val.t) (r : Typ.t) (e1 e2 : Exp.t) (v : Val.t) :
  exp_big_step ϵ (Exp.Index r e1 e2) v ->
  exists ls vs w n, nth_error vs (Z.to_nat n) = Some v /\
                    exp_big_step ϵ e1 (Val.Lists ls vs) /\
                    exp_big_step ϵ e2 (Val.Bit w n).
Proof.
  intros H. inversion H; subst.
  exists ls, vs, w, n.
  split; [assumption | split; assumption].
Qed.

Lemma ebs_lists_inv (ϵ : list Val.t) (ls : Lst.t) (es : list Exp.t) (vs : Val.t) :
  exp_big_step ϵ (Exp.Lists ls es) vs ->
  exists vs', vs = Val.Lists ls vs' /\ Forall2 (exp_big_step ϵ) es vs'.
Proof. intros H; inversion H; subst; eauto. Qed.

(* ------------- inversion lemmas: typing ------------- *)

Lemma type_bool_inv (Δ : nat) (Γ : list Typ.t) (b : bool) (τ : Typ.t) :
  type_exp Δ Γ (Exp.Bool b) τ -> τ = Typ.Bool.
Proof. intros H; inversion H; reflexivity. Qed.

Lemma type_bit_inv (Δ : nat) (Γ : list Typ.t) (w : N) (n : Z) (τ : Typ.t) :
  type_exp Δ Γ (Exp.Bit w n) τ -> τ = Typ.Bit w /\ BitArith.bound w n.
Proof. intros H; inversion H; subst; auto. Qed.

Lemma type_int_inv (Δ : nat) (Γ : list Typ.t) (p : positive) (n : Z) (τ : Typ.t) :
  type_exp Δ Γ (Exp.Int p n) τ -> τ = Typ.Int p /\ IntArith.bound p n.
Proof. intros H; inversion H; subst; auto. Qed.

Lemma type_varbit_inv (Δ : nat) (Γ : list Typ.t) (m w : N) (n : Z) (τ : Typ.t) :
  type_exp Δ Γ (Exp.VarBit m w n) τ ->
  τ = Typ.VarBit m /\ (w <= m)%N /\ BitArith.bound w n.
Proof. intros H; inversion H; subst; auto. Qed.

Lemma type_var_inv (Δ : nat) (Γ : list Typ.t) (ty : Typ.t) (og : String.string) (x : nat) (τ : Typ.t) :
  type_exp Δ Γ (Exp.Var ty og x) τ ->
  τ = ty /\ nth_error Γ x = Some ty /\ typ_ok Δ ty.
Proof. intros H; inversion H; subst; auto. Qed.

Lemma type_slice_inv (Δ : nat) (Γ : list Typ.t) (hi lo : positive) (e : Exp.t) (τ : Typ.t) :
  type_exp Δ Γ (Exp.Slice hi lo e) τ ->
  exists w τ0, (Npos lo <= Npos hi)%N /\ (Npos hi < w)%N /\ numeric_width w τ0 /\
              type_exp Δ Γ e τ0 /\ τ = Typ.Bit (Npos hi - Npos lo + 1)%N.
Proof. intros H; inversion H; subst;
  repeat match goal with Hc : _ /\ _ |- _ => destruct Hc end;
  repeat eexists; repeat split; eauto. Qed.

Lemma type_cast_inv (Δ : nat) (Γ : list Typ.t) (ty : Typ.t) (e : Exp.t) (τ : Typ.t) :
  type_exp Δ Γ (Exp.Cast ty e) τ ->
  exists τ0, τ = ty /\ proper_cast τ0 ty /\ typ_ok Δ ty /\ type_exp Δ Γ e τ0.
Proof. intros H; inversion H; subst;
  repeat match goal with Hc : _ /\ _ |- _ => destruct Hc end;
  repeat eexists; repeat split; eauto. Qed.

Lemma type_error_inv (Δ : nat) (Γ : list Typ.t) (err : String.string) (τ : Typ.t) :
  type_exp Δ Γ (Exp.Error err) τ -> τ = Typ.Error.
Proof. intros H; inversion H; reflexivity. Qed.

Lemma type_uop_inv (Δ : nat) (Γ : list Typ.t) (r : Typ.t) (op : Una.t) (e : Exp.t) (τ : Typ.t) :
  type_exp Δ Γ (Exp.Uop r op e) τ ->
  exists τ0, τ = r /\ una_type op τ0 r /\ typ_ok Δ r /\ type_exp Δ Γ e τ0.
Proof. intros H; inversion H; subst;
  repeat match goal with Hc : _ /\ _ |- _ => destruct Hc end;
  repeat eexists; repeat split; eauto. Qed.

Lemma type_bop_inv (Δ : nat) (Γ : list Typ.t) (r : Typ.t) (op : Bin.t) (e1 e2 : Exp.t) (τ : Typ.t) :
  type_exp Δ Γ (Exp.Bop r op e1 e2) τ ->
  exists τ1 τ2, τ = r /\ bin_type op τ1 τ2 r /\ typ_ok Δ r /\
               type_exp Δ Γ e1 τ1 /\ type_exp Δ Γ e2 τ2.
Proof. intros H; inversion H; subst;
  repeat match goal with Hc : _ /\ _ |- _ => destruct Hc end;
  repeat eexists; repeat split; eauto. Qed.

Lemma type_member_inv (Δ : nat) (Γ : list Typ.t) (r : Typ.t) (x : nat) (e : Exp.t) (τ : Typ.t) :
  type_exp Δ Γ (Exp.Member r x e) τ ->
  exists τs b, τ = r /\ nth_error τs x = Some r /\ typ_ok Δ r /\
              type_exp Δ Γ e (Typ.Struct b τs).
Proof. intros H; inversion H; subst;
  repeat match goal with Hc : _ /\ _ |- _ => destruct Hc end;
  repeat eexists; repeat split; eauto. Qed.

Lemma type_index_inv (Δ : nat) (Γ : list Typ.t) (r : Typ.t) (e1 e2 : Exp.t) (τ : Typ.t) :
  type_exp Δ Γ (Exp.Index r e1 e2) τ ->
  exists w, τ = r /\ typ_ok Δ r /\
            type_exp Δ Γ e1 (Typ.Array (Z.to_N (BitArith.upper_bound w)) r) /\
            type_exp Δ Γ e2 (Typ.Bit w).
Proof. intros H; inversion H; subst;
  repeat match goal with Hc : _ /\ _ |- _ => destruct Hc end;
  repeat eexists; repeat split; eauto. Qed.

Lemma type_lists_inv (Δ : nat) (Γ : list Typ.t) (ls : Lst.t) (es : list Exp.t) (τ : Typ.t) :
  type_exp Δ Γ (Exp.Lists ls es) τ ->
  exists τs, typ_ok_lists Δ ls /\ type_lst_ok ls τ τs /\ Forall2 (type_exp Δ Γ) es τs.
Proof. intros H; inversion H; subst;
  repeat match goal with Hc : _ /\ _ |- _ => destruct Hc end;
  repeat eexists; repeat split; eauto. Qed.

(* ------------- expression size and induction ------------- *)

Fixpoint exp_size (e : Exp.t) : nat :=
  match e with
  | Exp.Bool _ => 1
  | Exp.VarBit _ _ _ => 1
  | Exp.Bit _ _ => 1
  | Exp.Int _ _ => 1
  | Exp.Var _ _ _ => 1
  | Exp.Slice _ _ a => S (exp_size a)
  | Exp.Cast _ a => S (exp_size a)
  | Exp.Uop _ _ a => S (exp_size a)
  | Exp.Bop _ _ a b => S (exp_size a + exp_size b)
  | Exp.Lists _ es => S (fold_right (fun e acc => exp_size e + acc) 0 es)
  | Exp.Index _ a b => S (exp_size a + exp_size b)
  | Exp.Member _ _ a => S (exp_size a)
  | Exp.Error _ => 1
  end.

Definition exp_sizes (es : list Exp.t) : nat :=
  fold_right (fun e acc => exp_size e + acc) 0 es.

Lemma exp_sizes_cons (e : Exp.t) (es : list Exp.t) :
  exp_sizes (e :: es) = exp_size e + exp_sizes es.
Proof. reflexivity. Qed.

Lemma exp_sizes_nil : exp_sizes [] = 0.
Proof. reflexivity. Qed.

Lemma In_exp_sizes (e : Exp.t) (es : list Exp.t) :
  In e es -> exp_size e <= exp_sizes es.
Proof.
  induction es as [| a l IH]; intros H.
  - contradiction.
  - destruct H as [-> | H].
    + rewrite exp_sizes_cons. lia.
    + rewrite exp_sizes_cons. pose proof IH H. lia.
Qed.

Lemma exp_size_pos (e : Exp.t) : 1 <= exp_size e.
Proof. destruct e; simpl; auto with arith. Qed.

Lemma exp_ind_size (P : Exp.t -> Prop) :
  (forall b, P (Exp.Bool b)) ->
  (forall m w n, P (Exp.VarBit m w n)) ->
  (forall w n, P (Exp.Bit w n)) ->
  (forall w n, P (Exp.Int w n)) ->
  (forall ty s x, P (Exp.Var ty s x)) ->
  (forall hi lo a, P a -> P (Exp.Slice hi lo a)) ->
  (forall ty a, P a -> P (Exp.Cast ty a)) ->
  (forall r op a, P a -> P (Exp.Uop r op a)) ->
  (forall r op a b, P a -> P b -> P (Exp.Bop r op a b)) ->
  (forall flag es, Forall P es -> P (Exp.Lists flag es)) ->
  (forall ty a b, P a -> P b -> P (Exp.Index ty a b)) ->
  (forall r x a, P a -> P (Exp.Member r x a)) ->
  (forall err, P (Exp.Error err)) ->
  forall e, P e.
Proof.
  intros H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 e.
  assert (Hsz : forall n e0, exp_size e0 <= n -> P e0).
  { intros n. induction n as [| n IH]; intros e0 He.
    - exfalso.
      exact (Nat.nle_succ_0 0 (Nat.le_trans 1 (exp_size e0) 0 (exp_size_pos e0) He)).
    - destruct e0; simpl in He.
      + apply H1.
      + apply H2.
      + apply H3.
      + apply H4.
      + apply H5.
      + apply H6. apply IH. apply le_S_n in He. exact He.
      + apply H7. apply IH. apply le_S_n in He. exact He.
      + apply H8. apply IH. apply le_S_n in He. exact He.
      + apply H9.
        * apply IH. apply le_S_n in He.
          apply Nat.le_trans with (exp_size e0_1 + exp_size e0_2); [apply Nat.le_add_r | exact He].
        * apply IH. apply le_S_n in He.
          apply Nat.le_trans with (exp_size e0_1 + exp_size e0_2); [apply Nat.le_add_l | exact He].
      + apply H10. apply Forall_forall. intros x Hx.
        apply In_exp_sizes in Hx.
        fold exp_sizes in He.
        apply IH. apply le_S_n in He.
        exact (Nat.le_trans (exp_size x) (exp_sizes es) n Hx He).
      + apply H11.
        * apply IH. apply le_S_n in He.
          apply Nat.le_trans with (exp_size e0_1 + exp_size e0_2); [apply Nat.le_add_r | exact He].
        * apply IH. apply le_S_n in He.
          apply Nat.le_trans with (exp_size e0_1 + exp_size e0_2); [apply Nat.le_add_l | exact He].
      + apply H12. apply IH. apply le_S_n in He. exact He.
      + apply H13.
  }
  apply (Hsz (exp_size e) e). apply Nat.le_refl.
Qed.

(* ------------- Forall2 helpers for Lists ------------- *)

Lemma Forall2_pres :
  forall (ϵ : list Val.t) (es : list Exp.t) (vs : list Val.t) (τs : list Typ.t)
         (Δ : nat) (Γ : list Typ.t),
    Forall2 type_val ϵ Γ ->
    Forall (fun e => forall v Δ Γ τ,
        ⟨ϵ, e⟩ ⇓ v -> Forall2 type_val ϵ Γ -> `⟨Δ, Γ⟩ ⊢ e ∈ τ -> ⊢ᵥ v ∈ τ) es ->
    Forall2 (exp_big_step ϵ) es vs ->
    Forall2 (type_exp Δ Γ) es τs ->
    Forall2 type_val vs τs.
Proof.
  intros ϵ es. induction es as [| e es IH]; intros vs τs Δ Γ Henv Hfa HFbs HFty.
  - inversion HFbs; subst. inversion HFty; subst. constructor.
  - destruct vs as [| v vs].
    + inversion HFbs.
    + destruct τs as [| τ τs].
      * inversion HFty.
      * inversion HFbs as [| ? ? ? ? Hbs Hbs']; subst.
        inversion HFty as [| ? ? ? ? Hty Hty']; subst.
        constructor.
        -- exact ((Forall_inv Hfa) v Δ Γ τ Hbs Henv Hty).
        -- apply IH with (Δ := Δ) (Γ := Γ).
           ++ exact Henv.
           ++ apply Forall_inv_tail in Hfa. exact Hfa.
           ++ exact Hbs'.
           ++ exact Hty'.
Qed.

Lemma Forall2_prog :
  forall (ϵ : list Val.t) (es : list Exp.t) (τs : list Typ.t)
         (Δ : nat) (Γ : list Typ.t),
    Forall2 type_val ϵ Γ ->
    Forall (fun e => forall τ ϵ,
        Forall2 type_val ϵ Γ -> `⟨Δ, Γ⟩ ⊢ e ∈ τ -> exists v, ⟨ϵ, e⟩ ⇓ v) es ->
    Forall2 (type_exp Δ Γ) es τs ->
    exists vs, Forall2 (exp_big_step ϵ) es vs.
Proof.
  intros ϵ es. induction es as [| e es IH]; intros τs Δ Γ Henv Hfa HFty.
  - exists []. constructor.
  - destruct τs as [| τ τs].
    + inversion HFty.
    + inversion HFty as [| ? ? ? ? Hty Hty']; subst.
      assert (Hex : exists v, exp_big_step ϵ e v).
      { exact ((Forall_inv Hfa) τ ϵ Henv Hty). }
      destruct Hex as [v Hv].
      destruct (IH τs Δ Γ Henv (Forall_inv_tail Hfa) Hty') as [vs Hvs].
      exists (v :: vs). constructor; assumption.
Qed.


(* ===================================================================== *)
(* Main theorems                                                         *)
(* ===================================================================== *)

Section BigStepTheorems.

Section ExpPreservation.

(* ------------- preservation ------------- *)

Theorem exp_big_step_preservation : forall ϵ e v Δ Γ τ,
    ⟨ ϵ, e ⟩ ⇓ v ->
    Forall2 type_val ϵ Γ ->
    `⟨ Δ, Γ ⟩ ⊢ e ∈ τ ->
    ⊢ᵥ v ∈ τ.
Proof.
  intros ϵ.
  apply (exp_ind_size (fun e => forall v Δ Γ τ,
    ⟨ ϵ, e ⟩ ⇓ v -> Forall2 type_val ϵ Γ -> `⟨ Δ, Γ ⟩ ⊢ e ∈ τ -> ⊢ᵥ v ∈ τ)).
  - (* Bool *)
    intros b v Δ Γ τ Hbs Henv Hty.
    apply ebs_bool_inv in Hbs. subst v.
    apply type_bool_inv in Hty. subst τ. apply typ_bool.
  - (* VarBit *)
    intros m w n v Δ Γ τ Hbs Henv Hty.
    apply ebs_varbit_inv in Hbs. subst v.
    apply type_varbit_inv in Hty. destruct Hty as [Heq [Hle Hb]]. subst τ.
    apply typ_varbit; assumption.
  - (* Bit *)
    intros w n v Δ Γ τ Hbs Henv Hty.
    apply ebs_bit_inv in Hbs. subst v.
    apply type_bit_inv in Hty. destruct Hty as [Heq Hb]. subst τ.
    apply typ_bit. exact Hb.
  - (* Int *)
    intros p n v Δ Γ τ Hbs Henv Hty.
    apply ebs_int_inv in Hbs. subst v.
    apply type_int_inv in Hty. destruct Hty as [Heq Hb]. subst τ.
    apply typ_int. exact Hb.
  - (* Var *)
    intros ty og x v Δ Γ τ Hbs Henv Hty.
    apply ebs_var_inv in Hbs.
    apply type_var_inv in Hty. destruct Hty as [Heq [Hnth Hok]]. subst τ.
    destruct (Forall2_nth_error_r _ _ _ _ _ x ty Henv Hnth) as [a [Ha HR]].
    rewrite Hbs in Ha. injection Ha as ->. exact HR.
  - (* Slice *)
    intros hi lo a IHa v Δ Γ τ Hbs Henv Hty.
    apply ebs_slice_inv in Hbs. destruct Hbs as [v0 [Hsv Hbs0]].
    apply type_slice_inv in Hty.
    destruct Hty as [w [τ0 [Hle [Hlt [Hnw [Hty0 Heq]]]]]]. subst τ.
    pose proof (IHa v0 Δ Γ τ0 Hbs0 Henv Hty0) as Htv0.
    destruct (slice_val_spec v0 τ0 w lo hi Hnw Htv0 Hle Hlt) as [v' [Hsv' Htv']].
    rewrite Hsv in Hsv'. injection Hsv' as ->. exact Htv'.
  - (* Cast *)
    intros ty a IHa v Δ Γ τ Hbs Henv Hty.
    apply ebs_cast_inv in Hbs. destruct Hbs as [v0 [Hcv Hbs0]].
    apply type_cast_inv in Hty. destruct Hty as [τ0 [Heq [Hpc [Hok Hty0]]]]. subst τ.
    pose proof (IHa v0 Δ Γ τ0 Hbs0 Henv Hty0) as Htv0.
    destruct (eval_cast_spec τ0 ty v0 Hpc Htv0) as [v' [Hcv' Htv']].
    rewrite Hcv in Hcv'. injection Hcv' as ->. exact Htv'.
  - (* Uop *)
    intros r op a IHa v Δ Γ τ Hbs Henv Hty.
    apply ebs_uop_inv in Hbs. destruct Hbs as [v0 [Huv Hbs0]].
    apply type_uop_inv in Hty. destruct Hty as [τ0 [Heq [Hut [Hok Hty0]]]]. subst τ.
    pose proof (IHa v0 Δ Γ τ0 Hbs0 Henv Hty0) as Htv0.
    destruct (eval_una_spec op τ0 r v0 Hut Htv0) as [v' [Huv' Htv']].
    rewrite Huv in Huv'. injection Huv' as ->. exact Htv'.
  - (* Bop *)
    intros r op a b IHa IHb v Δ Γ τ Hbs Henv Hty.
    apply ebs_bop_inv in Hbs. destruct Hbs as [v1 [v2 [Hbv [Hbs1 Hbs2]]]].
    apply type_bop_inv in Hty.
    destruct Hty as [τ1 [τ2 [Heq [Hbin [Hok [Hty1 Hty2]]]]]]. subst τ.
    pose proof (IHa v1 Δ Γ τ1 Hbs1 Henv Hty1) as Htv1.
    pose proof (IHb v2 Δ Γ τ2 Hbs2 Henv Hty2) as Htv2.
    destruct (eval_bin_spec op τ1 τ2 r v1 v2 Hbin Htv1 Htv2) as [v' [Hbv' Htv']].
    rewrite Hbv in Hbv'. injection Hbv' as ->. exact Htv'.
  - (* Lists *)
    intros flag es Hfa v Δ Γ τ Hbs Henv Hty.
    apply ebs_lists_inv in Hbs. destruct Hbs as [vs [Heq HFbs]]. subst v.
    apply type_lists_inv in Hty. destruct Hty as [τs [Hok [Hlok HFty]]].
    apply typ_lists with τs; [exact Hlok|].
    eapply Forall2_pres; [exact Henv | exact Hfa | exact HFbs | exact HFty].
  - (* Index *)
    intros r a b IHa IHb v Δ Γ τ Hbs Henv Hty.
    apply ebs_index_inv in Hbs.
    destruct Hbs as [ls [vs [w [n [Hnthv [Hbs1 Hbs2]]]]]].
    apply type_index_inv in Hty. destruct Hty as [w0 [Heq [Hok [Hty1 Hty2]]]]. subst τ.
    pose proof (IHa (Val.Lists ls vs) Δ Γ
                  (Typ.Array (Z.to_N (BitArith.upper_bound w0)) r) Hbs1 Henv Hty1) as Htv1.
    pose proof (IHb (Val.Bit w n) Δ Γ (Typ.Bit w0) Hbs2 Henv Hty2) as Htv2.
    apply type_val_array_inv in Htv1. destruct Htv1 as [vs0 [Heq2 HF2]].
    injection Heq2 as Hls Hvv. subst vs0.
    apply type_val_bit_inv in Htv2. destruct Htv2 as [n0 [Heq3 Hb]].
    injection Heq3 as Hw Hn. subst w. subst n.
    pose proof (nth_error_repeat r
                  (m := N.to_nat (Z.to_N (BitArith.upper_bound w0)))
                  (n := Z.to_nat n0) (index_in_bounds w0 n0 Hb)) as Hrep.
    destruct (Forall2_nth_error_r _ _ _ _ _ (Z.to_nat n0) r HF2 Hrep) as [v' [Hv' HR]].
    rewrite Hnthv in Hv'. injection Hv' as ->. exact HR.
  - (* Member *)
    intros r x a IHa v Δ Γ τ Hbs Henv Hty.
    apply ebs_member_inv in Hbs. destruct Hbs as [ls [vs [Hnthv Hbs0]]].
    apply type_member_inv in Hty. destruct Hty as [τs [b [Heq [Hnth [Hok Hty0]]]]]. subst τ.
    pose proof (IHa (Val.Lists ls vs) Δ Γ (Typ.Struct b τs) Hbs0 Henv Hty0) as Htv0.
    destruct b.
    + apply type_val_struct_true_inv in Htv0.
      destruct Htv0 as [b0 [vs0 [Heq2 HF2]]].
      injection Heq2 as Hls Hvv. subst vs0.
      destruct (Forall2_nth_error_r _ _ _ _ _ x r HF2 Hnth) as [v' [Hv' HR]].
      rewrite Hnthv in Hv'. injection Hv' as ->. exact HR.
    + apply type_val_struct_false_inv in Htv0.
      destruct Htv0 as [vs0 [Heq2 HF2]].
      injection Heq2 as Hls Hvv. subst vs0.
      destruct (Forall2_nth_error_r _ _ _ _ _ x r HF2 Hnth) as [v' [Hv' HR]].
      rewrite Hnthv in Hv'. injection Hv' as ->. exact HR.
  - (* Error *)
    intros err v Δ Γ τ Hbs Henv Hty.
    apply ebs_error_inv in Hbs. subst v.
    apply type_error_inv in Hty. subst τ. apply typ_error.
Qed.


End ExpPreservation.

Section ExpProgress.

(* ------------- progress ------------- *)

Theorem exp_big_step_progress : forall Δ Γ e τ ϵ,
    Forall2 type_val ϵ Γ ->
    `⟨ Δ, Γ ⟩ ⊢ e ∈ τ ->
    exists v, ⟨ ϵ, e ⟩ ⇓ v.
Proof.
  intros Δ Γ.
  apply (exp_ind_size (fun e => forall τ ϵ,
    Forall2 type_val ϵ Γ -> `⟨ Δ, Γ ⟩ ⊢ e ∈ τ -> exists v, ⟨ ϵ, e ⟩ ⇓ v)).
  - (* Bool *)
    intros b τ ϵ Henv Hty.
    apply type_bool_inv in Hty. subst τ.
    eexists. apply ebs_bool.
  - (* VarBit *)
    intros m w n τ ϵ Henv Hty.
    apply type_varbit_inv in Hty. destruct Hty as [Heq [Hle Hb]]. subst τ.
    eexists. apply ebs_varbit.
  - (* Bit *)
    intros w n τ ϵ Henv Hty.
    apply type_bit_inv in Hty. destruct Hty as [Heq Hb]. subst τ.
    eexists. apply ebs_bit.
  - (* Int *)
    intros p n τ ϵ Henv Hty.
    apply type_int_inv in Hty. destruct Hty as [Heq Hb]. subst τ.
    eexists. apply ebs_int.
  - (* Var *)
    intros ty og x τ ϵ Henv Hty.
    apply type_var_inv in Hty. destruct Hty as [Heq [Hnth Hok]]. subst τ.
    destruct (Forall2_nth_error_r _ _ _ _ _ x ty Henv Hnth) as [v [Hv HR]].
    exists v. apply ebs_var. exact Hv.
  - (* Slice *)
    intros hi lo a IHa τ ϵ Henv Hty.
    apply type_slice_inv in Hty.
    destruct Hty as [w [τ0 [Hle [Hlt [Hnw [Hty0 Heq]]]]]]. subst τ.
    destruct (IHa τ0 ϵ Henv Hty0) as [v0 Hbs0].
    pose proof (exp_big_step_preservation ϵ a v0 Δ Γ τ0 Hbs0 Henv Hty0) as Htv0.
    destruct (slice_val_spec v0 τ0 w lo hi Hnw Htv0 Hle Hlt) as [v' [Hsv' Htv']].
    exists v'. eapply ebs_slice; eassumption.
  - (* Cast *)
    intros ty a IHa τ ϵ Henv Hty.
    apply type_cast_inv in Hty. destruct Hty as [τ0 [Heq [Hpc [Hok Hty0]]]]. subst τ.
    destruct (IHa τ0 ϵ Henv Hty0) as [v0 Hbs0].
    pose proof (exp_big_step_preservation ϵ a v0 Δ Γ τ0 Hbs0 Henv Hty0) as Htv0.
    destruct (eval_cast_spec τ0 ty v0 Hpc Htv0) as [v' [Hcv' Htv']].
    exists v'. eapply ebs_cast; eassumption.
  - (* Uop *)
    intros r op a IHa τ ϵ Henv Hty.
    apply type_uop_inv in Hty. destruct Hty as [τ0 [Heq [Hut [Hok Hty0]]]]. subst τ.
    destruct (IHa τ0 ϵ Henv Hty0) as [v0 Hbs0].
    pose proof (exp_big_step_preservation ϵ a v0 Δ Γ τ0 Hbs0 Henv Hty0) as Htv0.
    destruct (eval_una_spec op τ0 r v0 Hut Htv0) as [v' [Huv' Htv']].
    exists v'. eapply ebs_uop; eassumption.
  - (* Bop *)
    intros r op a b IHa IHb τ ϵ Henv Hty.
    apply type_bop_inv in Hty.
    destruct Hty as [τ1 [τ2 [Heq [Hbin [Hok [Hty1 Hty2]]]]]]. subst τ.
    destruct (IHa τ1 ϵ Henv Hty1) as [v1 Hbs1].
    destruct (IHb τ2 ϵ Henv Hty2) as [v2 Hbs2].
    pose proof (exp_big_step_preservation ϵ a v1 Δ Γ τ1 Hbs1 Henv Hty1) as Htv1.
    pose proof (exp_big_step_preservation ϵ b v2 Δ Γ τ2 Hbs2 Henv Hty2) as Htv2.
    destruct (eval_bin_spec op τ1 τ2 r v1 v2 Hbin Htv1 Htv2) as [v [Hbv Htv]].
    exists v. eapply ebs_bop; eassumption.
  - (* Lists *)
    intros flag es Hfa τ ϵ Henv Hty.
    apply type_lists_inv in Hty. destruct Hty as [τs [Hok [Hlok HFty]]].
    destruct (Forall2_prog ϵ es τs Δ Γ Henv Hfa HFty) as [vs HFbs].
    exists (Val.Lists flag vs). apply ebs_lists. exact HFbs.
  - (* Index *)
    intros r a b IHa IHb τ ϵ Henv Hty.
    apply type_index_inv in Hty. destruct Hty as [w [Heq [Hok [Hty1 Hty2]]]]. subst τ.
    destruct (IHa (Typ.Array (Z.to_N (BitArith.upper_bound w)) r) ϵ Henv Hty1) as [v1 Hbs1].
    destruct (IHb (Typ.Bit w) ϵ Henv Hty2) as [v2 Hbs2].
    pose proof (exp_big_step_preservation ϵ a v1 Δ Γ
                  (Typ.Array (Z.to_N (BitArith.upper_bound w)) r) Hbs1 Henv Hty1) as Htv1.
    pose proof (exp_big_step_preservation ϵ b v2 Δ Γ (Typ.Bit w) Hbs2 Henv Hty2) as Htv2.
    apply type_val_array_inv in Htv1. destruct Htv1 as [vs0 [Heq2 HF2]]. subst v1.
    apply type_val_bit_inv in Htv2. destruct Htv2 as [n0 [Heq3 Hb]]. subst v2.
    pose proof (nth_error_repeat r
                  (m := N.to_nat (Z.to_N (BitArith.upper_bound w)))
                  (n := Z.to_nat n0) (index_in_bounds w n0 Hb)) as Hrep.
    destruct (Forall2_nth_error_r _ _ _ _ _ (Z.to_nat n0) r HF2 Hrep) as [v [Hv' HR]].
    exists v. eapply ebs_index; eassumption.
  - (* Member *)
    intros r x a IHa τ ϵ Henv Hty.
    apply type_member_inv in Hty. destruct Hty as [τs [b [Heq [Hnth [Hok Hty0]]]]]. subst τ.
    destruct (IHa (Typ.Struct b τs) ϵ Henv Hty0) as [v0 Hbs0].
    pose proof (exp_big_step_preservation ϵ a v0 Δ Γ (Typ.Struct b τs) Hbs0 Henv Hty0) as Htv0.
    destruct b.
    + apply type_val_struct_true_inv in Htv0.
      destruct Htv0 as [b0 [vs0 [Heq2 HF2]]]. subst v0.
      destruct (Forall2_nth_error_r _ _ _ _ _ x r HF2 Hnth) as [v [Hv' HR]].
      exists v. eapply ebs_member; eassumption.
    + apply type_val_struct_false_inv in Htv0.
      destruct Htv0 as [vs0 [Heq2 HF2]]. subst v0.
      destruct (Forall2_nth_error_r _ _ _ _ _ x r HF2 Hnth) as [v [Hv' HR]].
      exists v. eapply ebs_member; eassumption.
  - (* Error *)
    intros err τ ϵ Henv Hty.
    apply type_error_inv in Hty. subst τ.
    eexists. apply ebs_error.
Qed.

End ExpProgress.

End BigStepTheorems.
