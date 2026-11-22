Require Export Arith.EqNat.

From Stdlib Require Export PeanoNat.

Require Export stlc1.

Require Export stlc2.

Inductive equiv_val : stack vl_stack -> vl -> vl_stack -> Prop :=
  | equiv_const : forall b st, equiv_val st (vbool b) (vbool_stack b)
  | equiv_abs : forall H1 H2 idx lS i t c1 c2 H fr,
                      get_stack_frame lS i = Some (fr, idx) ->
                      equiv_env lS (Def H1 H2 idx) (H, (fr, idx)) ->
                      equiv_val lS (vabs (Def H1 H2 idx) c1 t c2) (vabs_stack H i c1 t c2)
with equiv_env : stack vl_stack -> venv -> venv_stack -> Prop :=
  | eqv_forall : forall lS H1 H1s H2 H2s H20,
                      Forall2(fun v vs => equiv_val lS v vs) H1 H1s ->
                      Forall2(fun v vs => equiv_val lS v vs) H2 H2s ->
                      equiv_env lS (Def H1 (H2++H20) (length H20)) (H1s, (H2s, length H20))
.

Definition eqv_nested_ind := fun
  (Pv : stack vl_stack -> vl -> vl_stack -> Prop)
  (Pe : stack vl_stack -> venv -> venv_stack -> Prop)
  (fconst : forall (b : bool) (st : stack vl_stack),
       Pv st (vbool b) (vbool_stack b))
  (fabs : forall (H1 H2 : list vl) (idx : nat) (lS : stack vl_stack)
          (i : st_ptr) (t : tm) (c1 c2 : class) (H : heap vl_stack)
          (fr : list vl_stack),
        get_stack_frame lS i = Some (fr, idx) ->
        Pe lS (Def H1 H2 idx) (H, (fr, idx)) ->
        Pv lS (vabs (Def H1 H2 idx) c1 t c2) (vabs_stack H i c1 t c2))
  (fenv : forall (lS : stack vl_stack) (H1 : list vl)
         (H1s : list vl_stack) (H2 : list vl) (H2s : list vl_stack)
         (H20 : list vl),
       Forall2 (fun (v : vl) (vs : vl_stack) => Pv lS v vs) H1 H1s ->
       Forall2 (fun (v : vl) (vs : vl_stack) => Pv lS v vs) H2 H2s ->
       Pe lS (Def H1 (H2 ++ H20) (length H20)) (H1s, (H2s, length H20)))
=>
  fix F (s : stack vl_stack) (v : vl) (v0 : vl_stack) (e : equiv_val s v v0): Pv s v v0 :=
match e in (equiv_val s0 v1 v2) return (Pv s0 v1 v2) with
| equiv_const x x0 => fconst x x0
| equiv_abs x x0 x1 x2 x3 x4 c1 c2 x6 x7 x8 x9 =>
  fabs x x0 x1 x2 x3 x4 c1 c2 x6 x7 x8 (
         match x9 in (equiv_env s0 v1 v2) return (Pe s0 v1 v2) with
           | eqv_forall x x0 x1 x2 x3 x4 x5 x6 =>
             fenv x x0 x1 x2 x3 x4
                  ((fix G l l' (fa: Forall2 (fun v v' => equiv_val x v v') l l') := match fa in (Forall2 _ l1 l2) return Forall2 _ l1 l2 with
                                | Forall2_nil _ => Forall2_nil _
                                | @Forall2_cons _ _ _ a b x1 x2 r x4 =>
                                  Forall2_cons a b (F x a b r) (G x1 x2 x4)
                              end) x0 x1 x5)
                  ((fix G l l' (fa: Forall2 (fun v v' => equiv_val x v v') l l') := match fa in (Forall2 _ l1 l2) return Forall2 _ l1 l2 with
                                | Forall2_nil _ => Forall2_nil _
                                | @Forall2_cons _ _ _ a b x1 x2 r x4 =>
                                  Forall2_cons a b (F x a b r) (G x1 x2 x4)
                              end) x2 x3 x6)
         end)
end.

Inductive equiv_opt: stack vl_stack -> option (vl) -> option (vl_stack) -> Prop :=
| e_stuck : forall lS, equiv_opt lS None None
| e_val : forall lS v v_stack, equiv_val lS v v_stack -> equiv_opt lS (Some v) ((Some v_stack)).

Inductive equiv_res: stack vl_stack -> option (option vl) -> option (option vl_stack) -> Prop :=
| e_time : forall lS, equiv_res lS None None
| e_res : forall lS v v_stack, equiv_opt lS v v_stack -> equiv_res lS ((Some v)) ((Some v_stack)).

Definition get_fenv (vs : option (option vl_stack)) :=
  match vs with
  | Some (Some (vabs_stack h _ _ _ _)) => h
  | _ => []
  end.

(* ---------- index lemmas ---------- *)
Lemma index_ge_None : forall {X : Type} (l : list X) i, i >= length l -> index i l = None.
Proof.
  intros X l. induction l as [|a l' IH]; intros i Hge.
  - reflexivity.
  - simpl. destruct (Nat.eqb i (length l')) eqn:E.
    + apply Nat.eqb_eq in E. simpl in Hge. lia.
    + apply IH. simpl in Hge. lia.
Qed.

Lemma index_lt_Some : forall {X : Type} (l : list X) i (a : X), index i l = Some a -> i < length l.
Proof.
  intros X l i a H.
  destruct (Nat.lt_ge_cases i (length l)) as [Hlt|Hge]; auto.
  apply index_ge_None in Hge. rewrite Hge in H. discriminate.
Qed.

Lemma index_app_in : forall {X : Type} (d l : list X) i, i < length l -> index i (d ++ l) = index i l.
Proof.
  intros X d. induction d as [|a d' IH]; intros l i Hlt.
  - reflexivity.
  - simpl. rewrite length_app.
    destruct (Nat.eqb i (length d' + length l)) eqn:E.
    + apply Nat.eqb_eq in E. lia.
    + apply IH. auto.
Qed.

Lemma index_app_tail : forall {X : Type} (l1 l2 : list X) i,
    length l2 <= i -> index i (l1 ++ l2) = index (i - length l2) l1.
Proof.
  intros X l1. induction l1 as [|a l1' IH]; intros l2 i Hle.
  - simpl. rewrite (index_ge_None l2 i) by lia. reflexivity.
  - simpl. rewrite length_app.
    destruct (Nat.eqb i (length l1' + length l2)) eqn:E.
    + apply Nat.eqb_eq in E.
      destruct (Nat.eqb (i - length l2) (length l1')) eqn:E2.
      * reflexivity.
      * apply Nat.eqb_neq in E2. exfalso. apply E2. lia.
    + destruct (Nat.eqb (i - length l2) (length l1')) eqn:E2.
      * apply Nat.eqb_eq in E2. apply Nat.eqb_neq in E. exfalso. apply E. lia.
      * apply IH. lia.
Qed.

Lemma index_In : forall {X : Type} (l : list X) i (v : X), index i l = Some v -> In v l.
Proof.
  intros X l. induction l as [|a l' IH]; intros i v H.
  - simpl in H. discriminate.
  - simpl in H. destruct (Nat.eqb i (length l')) eqn:E.
    + inversion H; subst. left. auto.
    + right. exact (IH i v H).
Qed.

Lemma Forall_index : forall {X : Type} (P : X -> Prop) (l : list X),
    Forall P l -> forall i v, index i l = Some v -> P v.
Proof.
  intros X P l H. induction H as [|a l' Ha Hl IH]; intros i v Hi.
  - simpl in Hi. discriminate.
  - simpl in Hi. destruct (Nat.eqb i (length l')) eqn:E.
    + apply Nat.eqb_eq in E. inversion Hi; subst; auto.
    + exact (IH i v Hi).
Qed.

Lemma forall2_index_Some : forall {X Y : Type} (R : X -> Y -> Prop) (l : list X) (l' : list Y),
    Forall2 R l l' -> forall i v, index i l = Some v -> exists v', index i l' = Some v' /\ R v v'.
Proof.
  intros X Y R l l' HF. induction HF as [|a b l l' HR Htail IH]; intros i v Hi.
  - simpl in Hi. discriminate.
  - pose proof (Forall2_length Htail) as Hlen.
    simpl in Hi |- *.
    destruct (Nat.eqb i (length l)) eqn:E.
    + apply Nat.eqb_eq in E. simpl in Hi. injection Hi as Hv. subst v.
      exists b. split.
      * replace i with (length l') by lia. simpl. rewrite Nat.eqb_refl. reflexivity.
      * auto.
    + apply Nat.eqb_neq in E.
      destruct (IH i v Hi) as [v' [Hv' HR']]. exists v'. split; auto.
      assert (E2 : (i =? length l') = false) by (apply Nat.eqb_neq; lia).
      rewrite E2. auto.
Qed.

Lemma forall2_index_None : forall {X Y : Type} (R : X -> Y -> Prop) (l : list X) (l' : list Y),
    Forall2 R l l' -> forall i, index i l = None -> index i l' = None.
Proof.
  intros X Y R l l' HF. induction HF as [|a b l l' HR Htail IH]; intros i Hi.
  - simpl. reflexivity.
  - pose proof (Forall2_length Htail) as Hlen.
    simpl in Hi |- *.
    destruct (Nat.eqb i (length l)) eqn:E.
    + discriminate.
    + apply Nat.eqb_neq in E.
      assert (E2 : (i =? length l') = false) by (apply Nat.eqb_neq; lia).
      rewrite E2. apply IH; auto.
Qed.

(* ---------- stack_split ---------- *)
Lemma stack_split_app : forall (d s : stack vl_stack), s <> [] -> stack_split (d ++ s) (length s) = Some (d, s).
Proof.
  intros d. induction d as [|a d' IH]; intros s Hs.
  - destruct s as [|b s']; [contradiction|]. simpl. rewrite Nat.eqb_refl. reflexivity.
  - destruct s as [|b s']; [contradiction|].
    simpl.
    assert (Hneq : (length (d' ++ b :: s') =? length s') = false).
    { apply Nat.eqb_neq. rewrite length_app. simpl. lia. }
    rewrite Hneq.
    rewrite IH by discriminate.
    reflexivity.
Qed.

(* ---------- sc_env lemmas ---------- *)
Lemma sc_env_tail : forall (a : stack_frame vl_stack) (S : stack vl_stack), sc_env (a :: S) -> sc_env S.
Proof. intros. inversion H. auto. Qed.

Lemma sc_env_skip : forall (d S : stack vl_stack), sc_env (d ++ S) -> sc_env S.
Proof.
  intros d. induction d as [|a d' IH]; intros S H.
  - exact H.
  - simpl in H. apply IH. apply sc_env_tail in H. exact H.
Qed.

Lemma sc_env_frame_In : forall (S : stack vl_stack), sc_env S ->
    forall (f : stack_frame vl_stack), In f S -> Forall (wf_val Second) (fst f).
Proof.
  intros S H. induction H as [|vstack fr idx Hsc IH Hfa]; intros f Hin.
  - simpl in Hin. destruct Hin.
  - simpl in Hin. destruct Hin as [Heq | Hin].
    + subst. simpl. auto.
    + exact (IH f Hin).
Qed.

Lemma sc_env_get : forall (S : stack vl_stack), sc_env S ->
    forall (i : st_ptr) (f : stack_frame vl_stack), get_stack_frame S i = Some f ->
    Forall (wf_val Second) (fst f).
Proof.
  intros S Hsc i f Hgf.
  destruct i as [idx|idx].
  - simpl in Hgf. inversion Hgf; subst. simpl. constructor.
  - simpl in Hgf. apply sc_env_frame_In with (S:=S); auto.
    exact (index_In S idx f Hgf).
Qed.

(* ---------- fc_env lemmas ---------- *)
Lemma fc_env_Forall : forall (h : heap vl_stack), fc_env h -> Forall (wf_val First) h.
Proof.
  intros h H. induction H as [|v vheap Hv Hh IH].
  - constructor.
  - constructor; auto.
Qed.

Lemma fc_env_index : forall (h : heap vl_stack), fc_env h ->
    forall i v, index i h = Some v -> wf_val First v.
Proof.
  intros h H. intros i v Hi. exact (Forall_index (wf_val First) h (fc_env_Forall h H) i v Hi).
Qed.

(* ---------- wf_val monotonicity ---------- *)
Lemma wf_val_first_second : forall v, wf_val First v -> wf_val Second v.
Proof.
  intros v H. inversion H; subst.
  - apply wf_val_const.
  - eapply wf_val_closureS; eauto.
Qed.


Lemma equiv_val_ext : forall (lS : stack vl_stack) (v : vl) (vs : vl_stack),
    equiv_val lS v vs -> forall d : stack vl_stack, equiv_val (d ++ lS) v vs.
Proof.
  intros lS v vs H.
  apply (eqv_nested_ind
    (fun s v vs => forall d, equiv_val (d ++ s) v vs)
    (fun s e es => forall d, equiv_env (d ++ s) e es)).
  - (* fconst *) intros b st d. apply equiv_const.
  - (* fabs *) intros H1 H2 idx0 lS0 i t c1 c2 Hheap fr Hgf HPe d.
    eapply equiv_abs.
    + destruct i as [k|k].
      * simpl. exact Hgf.
      * simpl in Hgf |- *.
        assert (Hlt : k < length lS0) by (apply index_lt_Some in Hgf; auto).
        rewrite (index_app_in d lS0 k Hlt). exact Hgf.
    + apply HPe.
  - (* fenv *) intros lS0 H1 H1s H2 H2s H20 Hf1 Hf2 d.
    eapply eqv_forall.
    + apply Forall2_impl with (R1 := fun v vs => forall d0, equiv_val (d0 ++ lS0) v vs)
                               (R2 := fun v vs => equiv_val (d ++ lS0) v vs).
      * intros a b Hb. exact (Hb d).
      * exact Hf1.
    + apply Forall2_impl with (R1 := fun v vs => forall d0, equiv_val (d0 ++ lS0) v vs)
                               (R2 := fun v vs => equiv_val (d ++ lS0) v vs).
      * intros a b Hb. exact (Hb d).
      * exact Hf2.
  - exact H.
Qed.

Lemma equiv_env_ext : forall (lS : stack vl_stack) (e : venv) (es : venv_stack),
    equiv_env lS e es -> forall d : stack vl_stack, equiv_env (d ++ lS) e es.
Proof.
  intros lS e es H. destruct H as [lS0 H1 H1s H2 H2s H20 Hf1 Hf2]. intros d.
  eapply eqv_forall.
  - apply Forall2_impl with (R1 := fun v vs => equiv_val lS0 v vs)
                             (R2 := fun v vs => equiv_val (d ++ lS0) v vs).
    + intros a b Hb. exact (equiv_val_ext lS0 a b Hb d).
    + exact Hf1.
  - apply Forall2_impl with (R1 := fun v vs => equiv_val lS0 v vs)
                             (R2 := fun v vs => equiv_val (d ++ lS0) v vs).
    + intros a b Hb. exact (equiv_val_ext lS0 a b Hb d).
    + exact Hf2.
Qed.


(* First-class values are stack independent *)
Definition PvF := fun (s : stack vl_stack) (v : vl) (vs : vl_stack) =>
  wf_val First vs -> forall lS2, equiv_val lS2 v vs.
Definition PeF := fun (s : stack vl_stack) (e : venv) (es : venv_stack) =>
  (fc_env (fst es) /\ Forall (wf_val First) (fst (snd es))) -> forall lS2, equiv_env lS2 e es.

Lemma fir_fconst : forall (b : bool) (st : stack vl_stack), PvF st (vbool b) (vbool_stack b).
Proof. intros b st Hw lS2. apply equiv_const. Qed.

Lemma fir_fabs : forall (H1 H2 : list vl) (idx : nat) (lS : stack vl_stack)
    (i : st_ptr) (t : tm) (c1 c2 : class) (H : heap vl_stack) (fr : list vl_stack),
    get_stack_frame lS i = Some (fr, idx) ->
    PeF lS (Def H1 H2 idx) (H, (fr, idx)) ->
    PvF lS (vabs (Def H1 H2 idx) c1 t c2) (vabs_stack H i c1 t c2).
Proof.
  intros H1 H2 idx0 lS0 i t c1 c2 Hheap fr Hgf HPe Hw lS2.
  destruct i as [k|k].
  - inversion Hw; subst. simpl in Hgf. injection Hgf as Hfr Hidx. subst fr. subst idx0.
    eapply equiv_abs.
    + simpl. reflexivity.
    + apply HPe. simpl. split; [assumption|constructor].
  - inversion Hw.
Qed.

Lemma Forall2_PvF_fc : forall (lS lS2 : stack vl_stack) (H1 : list vl) (H1s : list vl_stack),
    fc_env H1s ->
    Forall2 (fun (v : vl) (vs : vl_stack) => PvF lS v vs) H1 H1s ->
    Forall2 (fun (v : vl) (vs : vl_stack) => equiv_val lS2 v vs) H1 H1s.
Proof.
  intros lS lS2 H1 H1s Hfc HF.
  induction HF as [|a b l1 l1' HPv Htl IH].
  - constructor.
  - inversion Hfc as [|v0 vheap Hwv Hfch]; subst.
    constructor.
    + apply HPv. exact Hwv.
    + apply IH. exact Hfch.
Qed.

Lemma Forall2_PvF_forall : forall (lS lS2 : stack vl_stack) (H2 : list vl) (H2s : list vl_stack),
    Forall (wf_val First) H2s ->
    Forall2 (fun (v : vl) (vs : vl_stack) => PvF lS v vs) H2 H2s ->
    Forall2 (fun (v : vl) (vs : vl_stack) => equiv_val lS2 v vs) H2 H2s.
Proof.
  intros lS lS2 H2 H2s Hfor HF.
  induction HF as [|a b l1 l1' HPv Htl IH].
  - constructor.
  - inversion Hfor as [|v0 vheap Hwv Hfh]; subst.
    constructor.
    + apply HPv. exact Hwv.
    + apply IH. exact Hfh.
Qed.

Lemma fir_fenv : forall (lS : stack vl_stack) (H1 : list vl) (H1s : list vl_stack)
    (H2 : list vl) (H2s : list vl_stack) (H20 : list vl),
    Forall2 (fun (v : vl) (vs : vl_stack) => PvF lS v vs) H1 H1s ->
    Forall2 (fun (v : vl) (vs : vl_stack) => PvF lS v vs) H2 H2s ->
    PeF lS (Def H1 (H2 ++ H20) (length H20)) (H1s, (H2s, length H20)).
Proof.
  intros lS0 H1 H1s H2 H2s H20 Hf1 Hf2 [Hfc Hfor] lS2.
  eapply eqv_forall.
  - apply (Forall2_PvF_fc lS0 lS2 H1 H1s Hfc Hf1).
  - apply (Forall2_PvF_forall lS0 lS2 H2 H2s Hfor Hf2).
Qed.

Lemma equiv_val_first_irrel : forall (lS : stack vl_stack) (v : vl) (vs : vl_stack),
    wf_val First vs -> equiv_val lS v vs -> forall lS2, equiv_val lS2 v vs.
Proof.
  intros lS v vs Hwf H.
  exact ((eqv_nested_ind PvF PeF fir_fconst fir_fabs fir_fenv lS v vs H) Hwf).
Qed.


Lemma lookup_stack_head : forall (x : var) (h : heap vl_stack) (f : stack_frame vl_stack) (rest : stack vl_stack),
    lookup_stack x h (f :: rest) = lookup_stack x h (f :: nil).
Proof.
  intros x h f rest. destruct x as [c i]. destruct c; simpl.
  - reflexivity.
  - destruct f as [l off]. reflexivity.
Qed.

(* V First i, any context class *)
Lemma lookup_equiv_first : forall (lS : stack vl_stack) (H1 : list vl) (H1s : heap vl_stack)
    (H2 H20 : list vl) (i : nat) (c : class),
    Forall2 (fun v vs => equiv_val lS v vs) H1 H1s ->
    (forall v, lookup (V First i) (sanitize_env c (Def H1 (H2 ++ H20) (length H20))) = Some v ->
       exists vs, lookup_stack (V First i) H1s nil = Some vs /\ equiv_val lS v vs) /\
    (lookup (V First i) (sanitize_env c (Def H1 (H2 ++ H20) (length H20))) = None ->
       lookup_stack (V First i) H1s nil = None).
Proof.
  intros lS H1 H1s H2 H20 i c Hf. destruct c; simpl; split.
  - intros v Hv. destruct (forall2_index_Some (fun v vs => equiv_val lS v vs) H1 H1s Hf i v Hv)
      as [vs [Hs HR]]. exists vs. split; auto.
  - intros Hv. exact (forall2_index_None (fun v vs => equiv_val lS v vs) H1 H1s Hf i Hv).
  - intros v Hv. destruct (forall2_index_Some (fun v vs => equiv_val lS v vs) H1 H1s Hf i v Hv)
      as [vs [Hs HR]]. exists vs. split; auto.
  - intros Hv. exact (forall2_index_None (fun v vs => equiv_val lS v vs) H1 H1s Hf i Hv).
Qed.

Lemma lookup_second_first_none : forall (H1 : list vl) (H2 H20 : list vl) (i : nat),
    lookup (V Second i) (sanitize_env First (Def H1 (H2 ++ H20) (length H20))) = None.
Proof.
  intros. simpl. destruct (length (H2 ++ H20) <=? i) eqn:E.
  - apply Nat.leb_le in E. rewrite (index_ge_None (H2 ++ H20) i E). reflexivity.
  - reflexivity.
Qed.

Lemma lookup_equiv_second : forall (lS : stack vl_stack) (H1 : list vl) (H1s : heap vl_stack)
    (H2 : list vl) (H2s : list vl_stack) (H20 : list vl) (i : nat),
    Forall2 (fun v vs => equiv_val lS v vs) H2 H2s ->
    (forall v, lookup (V Second i) (sanitize_env Second (Def H1 (H2 ++ H20) (length H20))) = Some v ->
       exists vs, lookup_stack (V Second i) H1s ((H2s, length H20) :: nil) = Some vs /\ equiv_val lS v vs) /\
    (lookup (V Second i) (sanitize_env Second (Def H1 (H2 ++ H20) (length H20))) = None ->
       lookup_stack (V Second i) H1s ((H2s, length H20) :: nil) = None).
Proof.
  intros lS H1 H1s H2 H2s H20 i Hf. simpl. split.
  - intros v Hv.
    destruct (length H20 <=? i) eqn:E.
    + apply Nat.leb_le in E.
      assert (Hidx : index i (H2 ++ H20) = index (i - length H20) H2)
        by (apply index_app_tail; auto).
      rewrite Hidx in Hv.
      destruct (forall2_index_Some (fun v vs => equiv_val lS v vs) H2 H2s Hf (i - length H20) v Hv)
        as [vs [Hs HR]].
      exists vs. split; auto.
    + discriminate.
  - intros Hv.
    destruct (length H20 <=? i) eqn:E.
    + apply Nat.leb_le in E.
      assert (Hidx : index i (H2 ++ H20) = index (i - length H20) H2)
        by (apply index_app_tail; auto).
      rewrite Hidx in Hv.
      apply (forall2_index_None (fun v vs => equiv_val lS v vs) H2 H2s Hf (i - length H20) Hv).
    + reflexivity.
Qed.


Lemma equiv_res_val_inv : forall (st : stack vl_stack) (a : option (option vl)) (vs : vl_stack),
  equiv_res st a (Some (Some vs)) -> exists v, a = Some (Some v) /\ equiv_val st v vs.
Proof.
  intros st a vs H. inversion H as [st0 | st0 v vst Ho]; subst.
  - inversion Ho as [| st1 v0 vs0 Hval]; subst. exists v0. split; [reflexivity | exact Hval].
Qed.
Lemma equiv_res_somenone_inv : forall (st : stack vl_stack) (a : option (option vl)),
  equiv_res st a (Some None) -> a = Some None.
Proof.
  intros st a H. inversion H as [st0 | st0 v vst Ho]; subst.
  inversion Ho as [st1 | st1 v0 vs0 Hval]; subst. reflexivity.
Qed.
Lemma equiv_res_none_inv : forall (st : stack vl_stack) (a : option (option vl)),
  equiv_res st a None -> a = None.
Proof. intros st a H. inversion H as [st0 | st0 v vst Ho]; subst. reflexivity. Qed.

Lemma equiv_res_somenone_right : forall (st : stack vl_stack) (b : option (option vl_stack)),
  equiv_res st (Some None) b -> b = Some None.
Proof.
  intros st b H. inversion H as [st0 | st0 v vst Ho]; subst.
  inversion Ho as [st1 | st1 v0 vs0 Hval]; subst. reflexivity.
Qed.
Lemma equiv_res_none_right : forall (st : stack vl_stack) (b : option (option vl_stack)),
  equiv_res st None b -> b = None.
Proof.
  intros st b H. inversion H as [st0 | st0 v vst Ho]; subst. reflexivity.
Qed.

Definition wf_res (n : class) (r : option (option vl_stack)) : Prop :=
  match r with Some (Some vs) => wf_val n vs | _ => True end.

Lemma equiv_env_inv : forall (lS : stack vl_stack) (env : venv) (h : heap vl_stack) (fr : stack_frame vl_stack),
  equiv_env lS env (h, fr) ->
  exists H1 H2 H20 H2s,
    env = Def H1 (H2++H20) (length H20) /\
    fr = (H2s, length H20) /\
    Forall2 (fun v vs => equiv_val lS v vs) H1 h /\
    Forall2 (fun v vs => equiv_val lS v vs) H2 H2s.
Proof.
  intros lS env h fr H. inversion H as [lS0 H1 H1s H2 H2s H20 Hf1 Hf2]; subst.
  exists H1, H2, H20, H2s. split; [reflexivity|]. split; [reflexivity|]. split; assumption.
Qed.

Lemma sc_env_head : forall (f : stack_frame vl_stack) (lS : stack vl_stack),
  sc_env (f :: lS) -> Forall (wf_val Second) (fst f).
Proof. intros f lS H. inversion H as [|vstack fr idx Hsc Hfa]; subst. simpl. exact Hfa. Qed.

Lemma sc_env_head_app : forall (d : stack vl_stack) (f : stack_frame vl_stack) (lS : stack vl_stack),
  sc_env (d ++ f :: lS) -> Forall (wf_val Second) (fst f).
Proof. intros d f lS H. apply (sc_env_head f lS). apply (sc_env_skip d (f :: lS) H). Qed.

Lemma lookup_stack_second_conv : forall (i : nat) (h : heap vl_stack) (frl : list vl_stack) (off : nat)
    (rest : stack vl_stack) (r : option vl_stack),
  lookup_stack (V Second i) h ((frl, off) :: nil) = r ->
  lookup_stack (V Second i) h ((frl, off) :: rest) = r.
Proof. intros. simpl in *. destruct (off <=? i); auto. Qed.

Lemma equiv_res_Some : forall (st : stack vl_stack) (a : option vl) (b : option vl_stack),
  equiv_res st (Some a) (Some b) <-> equiv_opt st a b.
Proof.
  intros st a b. split.
  - intros H. inversion H. assumption.
  - intros H. apply e_res. exact H.
Qed.

Lemma equiv_opt_Some : forall (st : stack vl_stack) (v : vl) (vs : vl_stack),
  equiv_opt st (Some v) (Some vs) <-> equiv_val st v vs.
Proof.
  intros st v vs. split.
  - intros H. inversion H. assumption.
  - intros H. apply e_val. exact H.
Qed.

Lemma get_stack_frame_app : forall (d st : stack vl_stack) (i : st_ptr) (f : stack_frame vl_stack),
  get_stack_frame st i = Some f -> get_stack_frame (d ++ st) i = get_stack_frame st i.
Proof.
  intros d st i f H. destruct i as [k|k].
  - reflexivity.
  - simpl in *. apply index_app_in. apply index_lt_Some in H. auto.
Qed.

Lemma index_head : forall (d : stack vl_stack) (a : stack_frame vl_stack) (lS : stack vl_stack),
  index (length lS) (d ++ a :: lS) = Some a.
Proof.
  intros d a lS. rewrite index_app_in by (simpl; lia). simpl. rewrite Nat.eqb_refl. reflexivity.
Qed.

Lemma expand_equiv :
  forall (lS : stack vl_stack) (H1 : list vl) (H1s : heap vl_stack) (H2 : list vl) (H2s : list vl_stack) (H20 : list vl)
         (i : st_ptr) (m retcl : class) (ey : tm) (vx : vl) (vx_s : vl_stack),
    Forall2 (fun v vs => equiv_val lS v vs) H1 H1s ->
    Forall2 (fun v vs => equiv_val lS v vs) H2 H2s ->
    equiv_val lS vx vx_s ->
    equiv_val lS (vabs (Def H1 (H2++H20) (length H20)) m ey retcl) (vabs_stack H1s i m ey retcl) ->
    equiv_env lS (expand_env (expand_env (Def H1 (H2++H20) (length H20))
                        (vabs (Def H1 (H2++H20) (length H20)) m ey retcl) Second) vx m)
                 (expand_env_stack (expand_env_stack (H1s, (H2s, length H20))
                        (vabs_stack H1s i m ey retcl) Second) vx_s m).
Proof.
  intros lS H1 H1s H2 H2s H20 i m retcl ey vx vx_s Hf1 Hf2 Hvx Hclo.
  destruct m; simpl.
  - eapply eqv_forall with (H1 := vx :: H1) (H1s := vx_s :: H1s)
       (H2 := vabs (Def H1 (H2 ++ H20) (length H20)) First ey retcl :: H2)
       (H2s := vabs_stack H1s i First ey retcl :: H2s) (H20 := H20).
    + constructor; assumption.
    + constructor; assumption.
  - eapply eqv_forall with (H1 := H1) (H1s := H1s)
       (H2 := vx :: vabs (Def H1 (H2 ++ H20) (length H20)) Second ey retcl :: H2)
       (H2s := vx_s :: vabs_stack H1s i Second ey retcl :: H2s) (H20 := H20).
    + assumption.
    + constructor; [assumption|constructor; assumption].
Qed.

Lemma expand_fc : forall (H1s : heap vl_stack) (H2s : list vl_stack) (off : nat)
    (i : st_ptr) (m retcl : class) (ey : tm) (vx_s : vl_stack),
  fc_env H1s -> wf_val m vx_s ->
  fc_env (fst (expand_env_stack (expand_env_stack (H1s, (H2s, off))
             (vabs_stack H1s i m ey retcl) Second) vx_s m)).
Proof.
  intros. destruct m; simpl.
  - constructor; assumption.
  - assumption.
Qed.

Lemma expand_sc : forall (H1s : heap vl_stack) (H2s : list vl_stack) (off : nat)
    (i : st_ptr) (m retcl : class) (ey : tm) (vx_s : vl_stack),
  Forall (wf_val Second) H2s -> wf_val Second (vabs_stack H1s i m ey retcl) -> wf_val m vx_s ->
  Forall (wf_val Second) (fst (snd (expand_env_stack (expand_env_stack (H1s, (H2s, off))
             (vabs_stack H1s i m ey retcl) Second) vx_s m))).
Proof.
  intros. destruct m; simpl.
  - constructor; assumption.
  - constructor; [assumption|constructor; assumption].
Qed.

Lemma teval_equiv_aux : forall (k : nat),
  forall (n : class) (t : tm) (env : venv) (v : option (option vl))
         (fr : stack_frame vl_stack) (lS : stack vl_stack)
         (env_heap : heap vl_stack) (v_stack : option (option vl_stack))
         (st_over : stack vl_stack) (delay : stack vl_stack) (st_out : stack vl_stack),
    st_over = delay ++ fr :: lS ->
    teval k env t n = v ->
    teval_stack k (length (fr :: lS)) st_over env_heap t n = (v_stack, st_out) ->
    equiv_env (fr :: lS) env (env_heap, fr) ->
    fc_env env_heap ->
    sc_env st_over ->
    equiv_res st_out v v_stack /\
    sc_env st_out /\
    wf_res n v_stack /\
    (exists d, st_out = d ++ st_over).
Proof.
  intros k. induction k as [|k' IH].
  - intros n t env v fr lS env_heap v_stack st_over delay st_out Hst Hev Hstk Henv Hfc Hsc.
    cbn [teval] in Hev. cbn [teval_stack] in Hstk.
    injection Hstk as Hvs Hso. subst v_stack. subst st_out. subst v.
    repeat split; auto.
    + apply e_time.
    + exists (@nil (stack_frame vl_stack)). reflexivity.
  - intros n t env v fr lS env_heap v_stack st_over delay st_out Hst Hev Hstk Henv Hfc Hsc.
    subst st_over.
    assert (Hne : fr :: lS <> []) by discriminate.
    cbn [teval] in Hev.
    cbn [teval_stack] in Hstk.
    rewrite (stack_split_app delay (fr::lS) Hne) in Hstk.
    cbn in Hstk.
    destruct t as [| | x | ef ex | m ey retcl].
    + (* ttrue *)
      injection Hstk as Hvs Hso. subst v_stack. subst st_out. subst v.
      repeat split; auto.
      * apply e_res, e_val, equiv_const.
      * apply wf_val_const.
      * exists (@nil (stack_frame vl_stack)). reflexivity.
    + (* tfalse *)
      injection Hstk as Hvs Hso. subst v_stack. subst st_out. subst v.
      repeat split; auto.
      * apply e_res, e_val, equiv_const.
      * apply wf_val_const.
      * exists (@nil (stack_frame vl_stack)). reflexivity.
    + (* tvar *)
      destruct (equiv_env_inv (fr::lS) env env_heap fr Henv) as [H1 [H2 [H20 [H2s [Heqenv [Heqfr [Hf1 Hf2]]]]]]].
      subst env. subst fr.
      destruct x as [c i]. destruct c; destruct n; simpl in Hstk.
      * (* V First, First *)
        injection Hstk as Hvs Hso. subst v_stack. subst st_out.
        destruct v as [[vv|]|].
        -- (* Some (Some vv) *)
           injection Hev as Hidx. simpl in Hidx.
           destruct (forall2_index_Some (fun v vs => equiv_val ((H2s,length H20)::lS) v vs) H1 env_heap Hf1 i vv Hidx)
             as [vs [Hs HR]].
           rewrite Hs. split.
           ++ apply e_res, e_val. apply (equiv_val_ext ((H2s,length H20)::lS) vv vs HR delay).
           ++ split. { exact Hsc. }
              split. { cbn [wf_res]. apply (Forall_index (wf_val First) env_heap (fc_env_Forall env_heap Hfc) i vs Hs). }
              exists (@nil (stack_frame vl_stack)). reflexivity.
        -- (* Some None *)
           injection Hev as Hidx. simpl in Hidx.
           assert (Hn : index i env_heap = None) by
             exact (forall2_index_None (fun v vs => equiv_val ((H2s,length H20)::lS) v vs) H1 env_heap Hf1 i Hidx).
           rewrite Hn. split.
           ++ apply e_res, e_stuck.
           ++ split. { exact Hsc. }
              split. { cbn [wf_res]. exact I. }
              exists (@nil (stack_frame vl_stack)). reflexivity.
        -- (* None *) discriminate.
      * (* V First, Second *)
        injection Hstk as Hvs Hso. subst v_stack. subst st_out.
        destruct v as [[vv|]|].
        -- (* Some (Some vv) *)
           injection Hev as Hidx. simpl in Hidx.
           destruct (forall2_index_Some (fun v vs => equiv_val ((H2s,length H20)::lS) v vs) H1 env_heap Hf1 i vv Hidx)
             as [vs [Hs HR]].
           rewrite Hs. split.
           ++ apply e_res, e_val. apply (equiv_val_ext ((H2s,length H20)::lS) vv vs HR delay).
           ++ split. { exact Hsc. }
              split. { cbn [wf_res]. apply wf_val_first_second, (Forall_index (wf_val First) env_heap (fc_env_Forall env_heap Hfc) i vs Hs). }
              exists (@nil (stack_frame vl_stack)). reflexivity.
        -- (* Some None *)
           injection Hev as Hidx. simpl in Hidx.
           assert (Hn : index i env_heap = None) by
             exact (forall2_index_None (fun v vs => equiv_val ((H2s,length H20)::lS) v vs) H1 env_heap Hf1 i Hidx).
           rewrite Hn. split.
           ++ apply e_res, e_stuck.
           ++ split. { exact Hsc. }
              split. { cbn [wf_res]. exact I. }
              exists (@nil (stack_frame vl_stack)). reflexivity.
        -- (* None *) discriminate.
      * (* V Second, First *)
        injection Hstk as Hvs Hso. subst v_stack. subst st_out.
        destruct v as [[vv|]|].
        -- (* Some (Some vv) *) rewrite lookup_second_first_none in Hev. discriminate.
        -- (* Some None *)
           split.
           ++ apply e_res, e_stuck.
           ++ split. { exact Hsc. }
              split. { cbn [wf_res]. exact I. }
              exists (@nil (stack_frame vl_stack)). reflexivity.
        -- (* None *) discriminate.
      * (* V Second, Second *)
        injection Hstk as Hvs Hso. subst v_stack. subst st_out.
        destruct v as [[vv|]|].
        -- (* Some (Some vv) *)
           injection Hev as Hidx.
           destruct (proj1 (lookup_equiv_second ((H2s,length H20)::lS) H1 env_heap H2 H2s H20 i Hf2) vv Hidx)
             as [vs [Hs HR]].
           apply (lookup_stack_second_conv i env_heap H2s (length H20) lS (Some vs)) in Hs.
           simpl in Hs. rewrite Hs. split.
           ++ apply e_res, e_val. apply (equiv_val_ext ((H2s,length H20)::lS) vv vs HR delay).
           ++ split. { exact Hsc. }
              split. { cbn [wf_res].
                       destruct (length H20 <=? i) eqn:E.
                       ** apply Nat.leb_le in E.
                          apply (Forall_index (wf_val Second) H2s (sc_env_head_app delay (H2s,length H20) lS Hsc) (i - length H20) vs). exact Hs.
                       ** discriminate. }
              exists (@nil (stack_frame vl_stack)). reflexivity.
        -- (* Some None *)
           injection Hev as Hidx.
           pose proof (proj2 (lookup_equiv_second ((H2s,length H20)::lS) H1 env_heap H2 H2s H20 i Hf2) Hidx) as Hn.
           apply (lookup_stack_second_conv i env_heap H2s (length H20) lS None) in Hn.
           simpl in Hn. rewrite Hn. split.
           ++ apply e_res, e_stuck.
           ++ split. { exact Hsc. }
              split. { cbn [wf_res]. exact I. }
              exists (@nil (stack_frame vl_stack)). reflexivity.
        -- (* None *) discriminate.
    + (* tapp *)
      destruct (teval_stack k' (S (length lS)) (delay ++ fr :: lS) env_heap ef Second) as [vfs1 st1] eqn:E2.
      pose proof (IH Second ef env (teval k' env ef Second) fr lS env_heap vfs1 (delay ++ fr :: lS) delay st1 eq_refl eq_refl E2 Henv Hfc Hsc) as Hef.
      destruct Hef as [Hef_res [Hef_sc [Hef_wf Hef_ext]]].
      destruct Hef_ext as [d1 Hef_ext].
      destruct (teval k' env ef Second) as [[vf|]|] eqn:E1.
      * (* E1 = Some (Some vf) *)
        destruct vfs1 as [[vs|]|] eqn:E2b.
        -- (* E2b = Some (Some vs) *)
           apply equiv_res_Some in Hef_res. apply equiv_opt_Some in Hef_res.
           destruct vf as [b|env2 m ey retcl].
           ++ destruct vs as [b'|env2s ip m' ey' retcl'].
              ** (* both vbool : stuck *)
                 cbn in Hev, Hstk.
                 subst v. injection Hstk as Hvs Hso. subst v_stack. subst st_out.
                 split. { apply e_res, e_stuck. }
                 split. { exact Hsc. }
                 split. { cbn [wf_res]. exact I. }
                 exists (@nil (stack_frame vl_stack)). reflexivity.
              ** inversion Hef_res.
           ++ destruct vs as [b'|env2s ip m' ey' retcl'].
              ** inversion Hef_res.
              ** (* both closures *)
                 cbn in Hev, Hstk.
                 subst v.
                 destruct env2 as [H1 H2 idx0].
                 inversion Hef_res as [b0 st0 | Ha Hb ida lSa ipa ta c1a c2a Hha fra Hgfa HRenva]; subst; clear Hef_res.
                 destruct (equiv_env_inv (d1 ++ delay ++ fr :: lS) (Def H1 H2 idx0) env2s (fra, idx0) HRenva)
                   as [K1 [K2 [K20 [K2s [E1a [E2a [Kf1 Kf2]]]]]]].
                 injection E1a as EK1 EK2 EKidx. subst K1. subst H2. subst idx0.
                 injection E2a as Efr0. subst fra.
                 destruct (teval_stack k' (S (length lS)) (d1 ++ delay ++ fr :: lS) env_heap ex m') as [vxs1 st2] eqn:E3.
                 pose proof (IH m' ex env (teval k' env ex m') fr lS env_heap vxs1 (d1 ++ delay ++ fr :: lS) (d1 ++ delay) st2
                    (ltac:(rewrite app_assoc; reflexivity)) eq_refl E3 Henv Hfc Hef_sc) as Hex.
                 destruct Hex as [Hex_res [Hex_sc [Hex_wf Hex_ext]]].
                 destruct Hex_ext as [d2 Hex_ext].
                 destruct (teval k' env ex m') as [[vx|]|] eqn:E4.
                 { destruct vxs1 as [[vxs|]|] eqn:E5.
                   - (* ex = Some (Some vx), stack = Some (Some vxs) *)
                     apply equiv_res_Some in Hex_res. apply equiv_opt_Some in Hex_res.
                     destruct (expand_env_stack (expand_env_stack (env2s, (K2s, length K20))
                                 (vabs_stack env2s ip m' ey' retcl') Second) vxs m') as [env'_heap fr'] eqn:Eexp.
                     destruct fr' as [frlist' off'].
                     assert (Hfe : ((frlist',off')::st2) = ((frlist',off')::d2) ++ (d1 ++ delay ++ fr :: lS)).
                     { rewrite Hex_ext. reflexivity. }
                     assert (Hf1e : Forall2 (fun v vs => equiv_val ((frlist',off')::st2) v vs) H1 env2s).
                     { apply Forall2_impl with (R1 := fun v vs => equiv_val (d1++delay++fr::lS) v vs).
                       - intros a b Hb. rewrite Hfe. apply (equiv_val_ext (d1++delay++fr::lS) a b Hb ((frlist',off')::d2)).
                       - exact Kf1. }
                     assert (Hf2e : Forall2 (fun v vs => equiv_val ((frlist',off')::st2) v vs) K2 K2s).
                     { apply Forall2_impl with (R1 := fun v vs => equiv_val (d1++delay++fr::lS) v vs).
                       - intros a b Hb. rewrite Hfe. apply (equiv_val_ext (d1++delay++fr::lS) a b Hb ((frlist',off')::d2)).
                       - exact Kf2. }
                     assert (Hvxe : equiv_val ((frlist',off')::st2) vx vxs).
                     { apply (equiv_val_ext st2 vx vxs Hex_res ((frlist',off')::nil)). }
                     assert (Hcloe : equiv_val ((frlist',off')::st2)
                               (vabs (Def H1 (K2++K20) (length K20)) m' ey' retcl')
                               (vabs_stack env2s ip m' ey' retcl')).
                     { eapply equiv_abs.
                       - rewrite Hfe. erewrite get_stack_frame_app. 2: exact Hgfa. exact Hgfa.
                       - rewrite Hfe. apply (equiv_env_ext (d1++delay++fr::lS) (Def H1 (K2++K20) (length K20)) (env2s,(K2s,length K20)) HRenva ((frlist',off')::d2)). }
                     assert (Hbodyenv : equiv_env ((frlist',off')::st2)
                        (expand_env (expand_env (Def H1 (K2++K20) (length K20)) (vabs (Def H1 (K2++K20) (length K20)) m' ey' retcl') Second) vx m')
                        (env'_heap, (frlist',off'))).
                     { rewrite <- Eexp. apply (expand_equiv ((frlist',off')::st2) H1 env2s K2 K2s K20 ip m' retcl' ey' vx vxs Hf1e Hf2e Hvxe Hcloe). }
                     assert (Hfc_body0 : fc_env (fst (expand_env_stack (expand_env_stack (env2s, (K2s, length K20))
                                          (vabs_stack env2s ip m' ey' retcl') Second) vxs m'))).
                     { apply (expand_fc env2s K2s (length K20) ip m' retcl' ey' vxs).
                       - cbn [wf_res] in Hef_wf. inversion Hef_wf; assumption.
                       - cbn [wf_res] in Hex_wf. exact Hex_wf. }
                     rewrite Eexp in Hfc_body0. simpl in Hfc_body0.
                     assert (Hfrm : Forall (wf_val Second) (fst (snd (expand_env_stack (expand_env_stack (env2s, (K2s, length K20))
                                          (vabs_stack env2s ip m' ey' retcl') Second) vxs m')))).
                     { apply (expand_sc env2s K2s (length K20) ip m' retcl' ey' vxs).
                       - exact (sc_env_get (d1++delay++fr::lS) Hef_sc ip (K2s, length K20) Hgfa).
                       - cbn [wf_res] in Hef_wf. exact Hef_wf.
                       - cbn [wf_res] in Hex_wf. exact Hex_wf. }
                     rewrite Eexp in Hfrm. simpl in Hfrm.
                     assert (Hsc_body : sc_env ((frlist',off')::st2)).
                     { apply stack_cons; [exact Hex_sc | exact Hfrm]. }
                     destruct (teval_stack k' (S (length st2)) ((frlist',off')::st2) env'_heap ey' retcl') as [rb stb] eqn:Ebody.
                     try rewrite E2 in Hstk. try rewrite E3 in Hstk. try rewrite Hgfa in Hstk.
                     try rewrite Eexp in Hstk. try rewrite Ebody in Hstk. cbn in Hstk.
                     pose proof (IH retcl' ey'
                        (expand_env (expand_env (Def H1 (K2++K20) (length K20)) (vabs (Def H1 (K2++K20) (length K20)) m' ey' retcl') Second) vx m')
                        (teval k' (expand_env (expand_env (Def H1 (K2++K20) (length K20)) (vabs (Def H1 (K2++K20) (length K20)) m' ey' retcl') Second) vx m') ey' retcl')
                        (frlist',off') st2 env'_heap rb ((frlist',off')::st2) nil stb eq_refl eq_refl Ebody Hbodyenv Hfc_body0 Hsc_body) as Hbody.
                     destruct Hbody as [Hbody_res [Hbody_sc [Hbody_wf Hbody_ext]]].
                     cbn [wf_res] in Hbody_wf.
                     destruct m'.
                     { (* m' = First *)
                       cbn in Eexp. injection Eexp as Heh Hfr Hoff.
                       subst env'_heap. subst frlist'. subst off'.
                       assert (Eb1 : teval_stack k' (S (@length (prod (list vl_stack) nat) st2)) ((@cons (prod (list vl_stack) nat) (@pair (list vl_stack) nat (@cons vl_stack (vabs_stack env2s ip First ey' retcl') K2s) (@length vl K20)) st2)) (@cons vl_stack vxs env2s) ey' retcl' = (rb, stb)) by exact Ebody.
                       rewrite Eb1 in Hstk. cbn in Hstk.
destruct n; destruct retcl'; cbn in *.
                     * (* n = First, retcl' = First *)
                       destruct rb as [[bvs|]|] eqn:Erb; cbn in *.
                       -- (* value *)
                          destruct (equiv_res_val_inv stb _ bvs Hbody_res) as [bve [Heq Hval]].
                          rewrite Heq. injection Hstk as Hvs Hso. subst v_stack. subst st_out.
                          split.
                          ++ apply e_res, e_val, (equiv_val_first_irrel stb bve bvs Hbody_wf Hval).
                          ++ split. { exact Hsc. }
                             split. { cbn [wf_res]. exact Hbody_wf. }
                             exists (@nil (stack_frame vl_stack)). reflexivity.
                       -- (* Some None *)
                          pose proof (equiv_res_somenone_inv stb _ Hbody_res) as Heq.
                          rewrite Heq. injection Hstk as Hvs Hso. subst v_stack. subst st_out.
                          split. { apply e_res, e_stuck. }
                          split. { exact Hsc. }
                          split. { cbn [wf_res]. exact I. }
                          exists (@nil (stack_frame vl_stack)). reflexivity.
                       -- (* None *)
                          pose proof (equiv_res_none_inv stb _ Hbody_res) as Heq.
                          rewrite Heq. injection Hstk as Hvs Hso. subst v_stack. subst st_out.
                          split. { apply e_time. }
                          split. { exact Hsc. }
                          split. { cbn [wf_res]. exact I. }
                          exists (@nil (stack_frame vl_stack)). reflexivity.
                     * (* n = First, retcl' = Second : stuck *)
                       cbn in *. injection Hstk as Hvs Hso. subst v_stack. subst st_out.
                       split. { apply e_res, e_stuck. }
                       split. { exact Hsc. }
                       split. { cbn [wf_res]. exact I. }
                       exists (@nil (stack_frame vl_stack)). reflexivity.
                     * (* n = Second, retcl' = First *)
                       destruct rb as [[bvs|]|] eqn:Erb; cbn in *.
                       -- (* value *)
                          destruct (equiv_res_val_inv stb _ bvs Hbody_res) as [bve [Heq Hval]].
                          rewrite Heq. injection Hstk as Hvs Hso. subst v_stack. subst st_out.
                          split.
                          ++ apply e_res, e_val, (equiv_val_first_irrel stb bve bvs Hbody_wf Hval).
                          ++ split. { exact Hsc. }
                             split. { cbn [wf_res]. apply wf_val_first_second; exact Hbody_wf. }
                             exists (@nil (stack_frame vl_stack)). reflexivity.
                       -- (* Some None *)
                          pose proof (equiv_res_somenone_inv stb _ Hbody_res) as Heq.
                          rewrite Heq. injection Hstk as Hvs Hso. subst v_stack. subst st_out.
                          split. { apply e_res, e_stuck. }
                          split. { exact Hsc. }
                          split. { cbn [wf_res]. exact I. }
                          exists (@nil (stack_frame vl_stack)). reflexivity.
                       -- (* None *)
                          pose proof (equiv_res_none_inv stb _ Hbody_res) as Heq.
                          rewrite Heq. injection Hstk as Hvs Hso. subst v_stack. subst st_out.
                          split. { apply e_time. }
                          split. { exact Hsc. }
                          split. { cbn [wf_res]. exact I. }
                          exists (@nil (stack_frame vl_stack)). reflexivity.
                     * (* n = Second, retcl' = Second *)
                       destruct rb as [[bvs|]|] eqn:Erb; cbn in *.
                       -- (* value : st_out = stb *)
                          destruct (equiv_res_val_inv stb _ bvs Hbody_res) as [bve [Heq Hval]].
                          rewrite Heq. injection Hstk as Hvs Hso. subst v_stack. subst st_out.
                          split.
                          ++ apply e_res, e_val, Hval.
                          ++ split. { exact Hbody_sc. }
                             split. { cbn [wf_res]. exact Hbody_wf. }
                             destruct Hbody_ext as [db Hdb].
                             exists (db ++ ((vabs_stack env2s ip First ey' Second :: K2s, length K20) :: (d2 ++ d1))).
                             rewrite Hdb. rewrite Hex_ext. repeat (cbn; rewrite <- app_assoc). reflexivity.
                       -- (* Some None *)
                          pose proof (equiv_res_somenone_inv stb _ Hbody_res) as Heq.
                          rewrite Heq. injection Hstk as Hvs Hso. subst v_stack. subst st_out.
                          split. { apply e_res, e_stuck. }
                          split. { exact Hsc. }
                          split. { cbn [wf_res]. exact I. }
                          exists (@nil (stack_frame vl_stack)). reflexivity.
                       -- (* None *)
                          pose proof (equiv_res_none_inv stb _ Hbody_res) as Heq.
                          rewrite Heq. injection Hstk as Hvs Hso. subst v_stack. subst st_out.
                          split. { apply e_time. }
                          split. { exact Hsc. }
                          split. { cbn [wf_res]. exact I. }
                          exists (@nil (stack_frame vl_stack)). reflexivity.

                     }
                     { (* m' = Second *)
                       cbn in Eexp. injection Eexp as Heh Hfr Hoff.
                       subst env'_heap. subst frlist'. subst off'.
                       assert (Eb2 : teval_stack k' (S (@length (prod (list vl_stack) nat) st2)) ((@cons (prod (list vl_stack) nat) (@pair (list vl_stack) nat (@cons vl_stack vxs (@cons vl_stack (vabs_stack env2s ip Second ey' retcl') K2s)) (@length vl K20)) st2)) env2s ey' retcl' = (rb, stb)) by exact Ebody.
                       rewrite Eb2 in Hstk. cbn in Hstk.
destruct n; destruct retcl'; cbn in *.
                     * (* n = First, retcl' = First *)
                       destruct rb as [[bvs|]|] eqn:Erb; cbn in *.
                       -- (* value *)
                          destruct (equiv_res_val_inv stb _ bvs Hbody_res) as [bve [Heq Hval]].
                          rewrite Heq. injection Hstk as Hvs Hso. subst v_stack. subst st_out.
                          split.
                          ++ apply e_res, e_val, (equiv_val_first_irrel stb bve bvs Hbody_wf Hval).
                          ++ split. { exact Hsc. }
                             split. { cbn [wf_res]. exact Hbody_wf. }
                             exists (@nil (stack_frame vl_stack)). reflexivity.
                       -- (* Some None *)
                          pose proof (equiv_res_somenone_inv stb _ Hbody_res) as Heq.
                          rewrite Heq. injection Hstk as Hvs Hso. subst v_stack. subst st_out.
                          split. { apply e_res, e_stuck. }
                          split. { exact Hsc. }
                          split. { cbn [wf_res]. exact I. }
                          exists (@nil (stack_frame vl_stack)). reflexivity.
                       -- (* None *)
                          pose proof (equiv_res_none_inv stb _ Hbody_res) as Heq.
                          rewrite Heq. injection Hstk as Hvs Hso. subst v_stack. subst st_out.
                          split. { apply e_time. }
                          split. { exact Hsc. }
                          split. { cbn [wf_res]. exact I. }
                          exists (@nil (stack_frame vl_stack)). reflexivity.
                     * (* n = First, retcl' = Second : stuck *)
                       cbn in *. injection Hstk as Hvs Hso. subst v_stack. subst st_out.
                       split. { apply e_res, e_stuck. }
                       split. { exact Hsc. }
                       split. { cbn [wf_res]. exact I. }
                       exists (@nil (stack_frame vl_stack)). reflexivity.
                     * (* n = Second, retcl' = First *)
                       destruct rb as [[bvs|]|] eqn:Erb; cbn in *.
                       -- (* value *)
                          destruct (equiv_res_val_inv stb _ bvs Hbody_res) as [bve [Heq Hval]].
                          rewrite Heq. injection Hstk as Hvs Hso. subst v_stack. subst st_out.
                          split.
                          ++ apply e_res, e_val, (equiv_val_first_irrel stb bve bvs Hbody_wf Hval).
                          ++ split. { exact Hsc. }
                             split. { cbn [wf_res]. apply wf_val_first_second; exact Hbody_wf. }
                             exists (@nil (stack_frame vl_stack)). reflexivity.
                       -- (* Some None *)
                          pose proof (equiv_res_somenone_inv stb _ Hbody_res) as Heq.
                          rewrite Heq. injection Hstk as Hvs Hso. subst v_stack. subst st_out.
                          split. { apply e_res, e_stuck. }
                          split. { exact Hsc. }
                          split. { cbn [wf_res]. exact I. }
                          exists (@nil (stack_frame vl_stack)). reflexivity.
                       -- (* None *)
                          pose proof (equiv_res_none_inv stb _ Hbody_res) as Heq.
                          rewrite Heq. injection Hstk as Hvs Hso. subst v_stack. subst st_out.
                          split. { apply e_time. }
                          split. { exact Hsc. }
                          split. { cbn [wf_res]. exact I. }
                          exists (@nil (stack_frame vl_stack)). reflexivity.
                     * (* n = Second, retcl' = Second *)
                       destruct rb as [[bvs|]|] eqn:Erb; cbn in *.
                       -- (* value : st_out = stb *)
                          destruct (equiv_res_val_inv stb _ bvs Hbody_res) as [bve [Heq Hval]].
                          rewrite Heq. injection Hstk as Hvs Hso. subst v_stack. subst st_out.
                          split.
                          ++ apply e_res, e_val, Hval.
                          ++ split. { exact Hbody_sc. }
                             split. { cbn [wf_res]. exact Hbody_wf. }
                             destruct Hbody_ext as [db Hdb].
                             exists (db ++ ((vxs :: vabs_stack env2s ip Second ey' Second :: K2s, length K20) :: (d2 ++ d1))).
                             rewrite Hdb. rewrite Hex_ext. repeat (cbn; rewrite <- app_assoc). reflexivity.
                       -- (* Some None *)
                          pose proof (equiv_res_somenone_inv stb _ Hbody_res) as Heq.
                          rewrite Heq. injection Hstk as Hvs Hso. subst v_stack. subst st_out.
                          split. { apply e_res, e_stuck. }
                          split. { exact Hsc. }
                          split. { cbn [wf_res]. exact I. }
                          exists (@nil (stack_frame vl_stack)). reflexivity.
                       -- (* None *)
                          pose proof (equiv_res_none_inv stb _ Hbody_res) as Heq.
                          rewrite Heq. injection Hstk as Hvs Hso. subst v_stack. subst st_out.
                          split. { apply e_time. }
                          split. { exact Hsc. }
                          split. { cbn [wf_res]. exact I. }
                          exists (@nil (stack_frame vl_stack)). reflexivity.

                     }
                   - (* ex stack = Some None *)
                     exfalso. apply equiv_res_Some in Hex_res. inversion Hex_res.
                   - (* ex stack = None *)
                     inversion Hex_res. }
                 { (* ex = Some None *)
                   pose proof (equiv_res_somenone_right st2 vxs1 Hex_res) as Heqx.
                   rewrite Heqx in Hstk.
                   destruct n; destruct retcl'; try rewrite E2 in Hstk; try rewrite E3 in Hstk; cbn in *.
                   + injection Hstk as Hvs Hso. subst v_stack. subst st_out. split. { apply e_res, e_stuck. }
                     split. { exact Hsc. } split. { cbn [wf_res]. exact I. } exists (@nil (stack_frame vl_stack)). reflexivity.
                   + injection Hstk as Hvs Hso. subst v_stack. subst st_out. split. { apply e_res, e_stuck. }
                     split. { exact Hsc. } split. { cbn [wf_res]. exact I. } exists (@nil (stack_frame vl_stack)). reflexivity.
                   + injection Hstk as Hvs Hso. subst v_stack. subst st_out. split. { apply e_res, e_stuck. }
                     split. { exact Hsc. } split. { cbn [wf_res]. exact I. } exists (@nil (stack_frame vl_stack)). reflexivity.
                   + injection Hstk as Hvs Hso. subst v_stack. subst st_out. split. { apply e_res, e_stuck. }
                     split. { exact Hsc. } split. { cbn [wf_res]. exact I. } exists (@nil (stack_frame vl_stack)). reflexivity. }
                 { (* ex = None *)
                   pose proof (equiv_res_none_right st2 vxs1 Hex_res) as Heqx.
                   rewrite Heqx in Hstk.
                   destruct n; destruct retcl'; try rewrite E2 in Hstk; try rewrite E3 in Hstk; cbn in *.
                   + injection Hstk as Hvs Hso. subst v_stack. subst st_out. split. { apply e_time. }
                     split. { exact Hsc. } split. { cbn [wf_res]. exact I. } exists (@nil (stack_frame vl_stack)). reflexivity.
                   + injection Hstk as Hvs Hso. subst v_stack. subst st_out. split. { apply e_res, e_stuck. }
                     split. { exact Hsc. } split. { cbn [wf_res]. exact I. } exists (@nil (stack_frame vl_stack)). reflexivity.
                   + injection Hstk as Hvs Hso. subst v_stack. subst st_out. split. { apply e_time. }
                     split. { exact Hsc. } split. { cbn [wf_res]. exact I. } exists (@nil (stack_frame vl_stack)). reflexivity.
                   + injection Hstk as Hvs Hso. subst v_stack. subst st_out. split. { apply e_time. }
                     split. { exact Hsc. } split. { cbn [wf_res]. exact I. } exists (@nil (stack_frame vl_stack)). reflexivity. }
        -- (* E2b = Some None *) exfalso. apply equiv_res_Some in Hef_res. inversion Hef_res.
        -- (* E2b = None *) inversion Hef_res.
      * (* E1 = Some None *)
        destruct vfs1 as [[vs|]|] eqn:E2b.
        -- exfalso. apply equiv_res_Some in Hef_res. inversion Hef_res.
        -- (* both stuck *)
           cbn in Hev, Hstk.
           subst v. injection Hstk as Hvs Hso. subst v_stack. subst st_out.
           split. { apply e_res, e_stuck. }
           split. { exact Hsc. }
           split. { cbn [wf_res]. exact I. }
           exists (@nil (stack_frame vl_stack)). reflexivity.
        -- exfalso. inversion Hef_res.
      * (* E1 = None *)
        destruct vfs1 as [[vs|]|] eqn:E2b.
        -- exfalso. inversion Hef_res.
        -- exfalso. inversion Hef_res.
        -- (* both None : timeout *)
           cbn in Hev, Hstk.
           subst v. injection Hstk as Hvs Hso. subst v_stack. subst st_out.
           split. { apply e_time. }
           split. { exact Hsc. }
           split. { cbn [wf_res]. exact I. }
           exists (@nil (stack_frame vl_stack)). reflexivity.

    + (* tabs *)
      destruct n; simpl in Hstk.
      * (* First *)
        destruct (equiv_env_inv (fr::lS) env env_heap fr Henv) as [H1 [H2 [H20 [H2s [Heqenv [Heqfr [Hf1 Hf2]]]]]]].
        subst env. subst fr.
        simpl in Hstk.
        injection Hstk as Hvs Hso. subst v_stack. subst st_out. subst v.
        pose proof (Forall2_length Hf2) as Hlen2.
        replace (length H20 + length H2s) with (length (H2 ++ H20))
          by (rewrite length_app; rewrite Hlen2; lia).
        split.
        -- apply e_res, e_val. eapply equiv_abs.
           ++ simpl. reflexivity.
           ++ eapply eqv_forall with (H1 := H1) (H1s := env_heap) (H2 := @nil vl) (H2s := @nil vl_stack) (H20 := H2 ++ H20).
              ** apply Forall2_impl with (R1 := fun v vs => equiv_val ((H2s,length H20)::lS) v vs)
                                          (R2 := fun v vs => equiv_val (delay ++ (H2s,length H20)::lS) v vs).
                 { intros a b Hb. exact (equiv_val_ext ((H2s,length H20)::lS) a b Hb delay). }
                 exact Hf1.
              ** apply Forall2_nil.
        -- split. { exact Hsc. }
           split. { cbn [wf_res]. apply wf_val_closureF with (tm:=ey) (class:=m) (idx:=length (H2 ++ H20)) (retcl:=retcl). exact Hfc. }
           exists (@nil (stack_frame vl_stack)). reflexivity.
      * (* Second *)
        destruct (equiv_env_inv (fr::lS) env env_heap fr Henv) as [H1 [H2 [H20 [H2s [Heqenv [Heqfr [Hf1 Hf2]]]]]]].
        subst env. subst fr.
        simpl in Hstk.
        injection Hstk as Hvs Hso. subst v_stack. subst st_out. subst v.
        split.
        -- apply e_res, e_val. eapply equiv_abs.
           ++ simpl. rewrite index_head. reflexivity.
           ++ eapply eqv_forall.
              ** apply Forall2_impl with (R1 := fun v vs => equiv_val ((H2s,length H20)::lS) v vs)
                                          (R2 := fun v vs => equiv_val (delay ++ (H2s,length H20)::lS) v vs).
                 { intros a b Hb. exact (equiv_val_ext ((H2s,length H20)::lS) a b Hb delay). }
                 exact Hf1.
              ** apply Forall2_impl with (R1 := fun v vs => equiv_val ((H2s,length H20)::lS) v vs)
                                          (R2 := fun v vs => equiv_val (delay ++ (H2s,length H20)::lS) v vs).
                 { intros a b Hb. exact (equiv_val_ext ((H2s,length H20)::lS) a b Hb delay). }
                 exact Hf2.
        -- split. { exact Hsc. }
           split. { cbn [wf_res]. apply wf_val_closureS with (tm:=ey) (class:=m) (i:=Si (length lS)) (retcl:=retcl). exact Hfc. }
           exists (@nil (stack_frame vl_stack)). reflexivity.
Qed.

Theorem teval_equiv : forall k n t env v lS lS' fr env_stack v_stack st,
     teval k env t n = v ->
     teval_stack k (length (fr::lS)) (lS' ++ fr::lS) env_stack t n = (v_stack, st) ->
     equiv_env (fr::lS) env (env_stack,fr) ->
     fc_env env_stack -> sc_env (lS' ++ fr::lS) ->
     equiv_res st v v_stack.
Proof.
  intros k n t env v lS lS' fr env_stack v_stack st Hev Hstk Henv Hfc Hsc.
  destruct (teval_equiv_aux k n t env v fr lS env_stack v_stack (lS' ++ fr :: lS) lS' st
              eq_refl Hev Hstk Henv Hfc Hsc) as [Hres [Hsce [Hwf Hext]]].
  exact Hres.
Qed.

