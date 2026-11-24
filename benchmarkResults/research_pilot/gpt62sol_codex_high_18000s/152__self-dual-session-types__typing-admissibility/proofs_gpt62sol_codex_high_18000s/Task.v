Require Import Language Sessions.

Local Lemma session_type_unfold s :
  s = match s with
      | SendTB n ts ss => SendTB n ts ss
      | RecvTB n ts ss => RecvTB n ts ss
      | EndTB => EndTB
      end.
Proof. destruct s; reflexivity. Qed.

Local Lemma dual_send n ts ss :
  dual (SendTB n ts ss) = RecvTB n ts (dual ∘ ss).
Proof. exact (session_type_unfold (dual (SendTB n ts ss))). Qed.

Local Lemma dual_recv n ts ss :
  dual (RecvTB n ts ss) = SendTB n ts (dual ∘ ss).
Proof. exact (session_type_unfold (dual (RecvTB n ts ss))). Qed.

Local Lemma dual_end : dual EndTB = EndTB.
Proof. exact (session_type_unfold (dual EndTB)). Qed.

Local Lemma dual_involutive s : dual (dual s) = s.
Proof.
  apply session_type_extensionality.
  revert s.
  cofix IH.
  intros [n ts ss | n ts ss |].
  - rewrite dual_send, dual_recv.
    apply cteq_SendT.
    + intro i. reflexivity.
    + intro i. exact (IH (ss i)).
  - rewrite dual_recv, dual_send.
    apply cteq_RecvT.
    + intro i. reflexivity.
    + intro i. exact (IH (ss i)).
  - rewrite !dual_end. exact cteq_EndT.
Qed.

Local Lemma type_unfold t :
  t = match t with
      | FunT l t1 t2 => FunT l t1 t2
      | UnitT => UnitT
      | PairT t1 t2 => PairT t1 t2
      | SumT n ts => SumT n ts
      end.
Proof. destruct t; reflexivity. Qed.

Local Lemma toL_send n ts ss :
  toL (SendTB n ts ss) =
  FunT Lin (SumT n (λ i, PairT (toL (dual (ss i))) (ts i))) UnitT.
Proof. exact (type_unfold (toL (SendTB n ts ss))). Qed.

Local Lemma toL_recv n ts ss :
  toL (RecvTB n ts ss) =
  FunT Lin UnitT (SumT n (λ i, PairT (toL (ss i)) (ts i))).
Proof. exact (type_unfold (toL (RecvTB n ts ss))). Qed.

Local Lemma toL_end : toL EndTB = FunT Lin UnitT UnitT.
Proof. exact (type_unfold (toL EndTB)). Qed.

Local Lemma toL_dual_shape s :
  ∃ a b, toL s = FunT Lin a b ∧ toL (dual s) = FunT Lin b a.
Proof.
  destruct s as [n ts ss | n ts ss |].
  - rewrite dual_send, toL_send, toL_recv.
    eexists _, _. split; reflexivity.
  - rewrite dual_recv, toL_recv, toL_send.
    eexists _, _. split; [reflexivity|].
    f_equal. f_equal.
    apply functional_extensionality. intro i.
    change (PairT (toL (dual (dual (ss i)))) (ts i) =
            PairT (toL (ss i)) (ts i)).
    rewrite dual_involutive. reflexivity.
  - rewrite dual_end, toL_end.
    exists UnitT, UnitT. split; reflexivity.
Qed.

Theorem ForkB_typed Γ σ e :
  typed Γ e (FunT Lin (toL (dual σ)) UnitT) ->
  typed Γ (ForkB e) (toL σ).
Proof.
  destruct (toL_dual_shape σ) as (a & b & H & Hdual).
  rewrite H, Hdual. intro He.
  apply Fork_typed. exact He.
Qed.

Local Lemma env_unr_empty : env_unr ∅.
Proof. intros x t H. simplify_map_eq. Qed.

Local Lemma env_split_empty_right Γ : env_split Γ Γ ∅.
Proof.
  split.
  - symmetry. apply map_union_empty.
  - intros x t1 t2 H1 H2. simplify_map_eq.
Qed.

Local Lemma env_bind_fresh Γ x t :
  Γ !! x = None -> env_bind (<[x := t]> Γ) x t Γ.
Proof.
  intro H. split; [reflexivity|].
  intros t' H'. rewrite H in H'. discriminate.
Qed.

Local Lemma typed_single_binding x t : typed (<[x := t]> ∅) (Var x) t.
Proof. apply Var_typed. exists ∅. split; [reflexivity|apply env_unr_empty]. Qed.

Local Lemma env_split_insert_left Γ Γ1 Γ2 x t :
  env_split Γ Γ1 Γ2 ->
  Γ2 !! x = None ->
  env_split (<[x := t]> Γ) (<[x := t]> Γ1) Γ2.
Proof.
  intros [-> Hdisj] Hfresh. split.
  - apply insert_union_l.
  - intros y t1 t2 H1 H2.
    destruct (decide (x = y)) as [->|Hne].
    + rewrite Hfresh in H2. discriminate.
    + rewrite (lookup_insert_ne Γ1 x y t Hne) in H1.
      exact (Hdisj y t1 t2 H1 H2).
Qed.

Local Lemma env_split_insert_right Γ Γ1 Γ2 x t :
  env_split Γ Γ1 Γ2 ->
  Γ1 !! x = None ->
  env_split (<[x := t]> Γ) Γ1 (<[x := t]> Γ2).
Proof.
  intros [-> Hdisj] Hfresh. split.
  - apply insert_union_r. exact Hfresh.
  - intros y t1 t2 H1 H2.
    destruct (decide (x = y)) as [->|Hne].
    + rewrite Hfresh in H1. discriminate.
    + rewrite (lookup_insert_ne Γ2 x y t Hne) in H2.
      exact (Hdisj y t1 t2 H1 H2).
Qed.

Theorem SendB_typed Γ Γ1 Γ2 e1 e2 n ts σs i :
  env_split Γ Γ1 Γ2 ->
  typed Γ1 e1 (toL (SendTB n ts σs)) ->
  typed Γ2 e2 (ts i) ->
  typed Γ (SendB e1 i e2) (toL (σs i)).
Proof.
  intros Hsplit He1 He2.
  destruct (toL_dual_shape (σs i)) as (a & b & H & Hdual).
  unfold SendB. rewrite H.
  eapply LetPair_typed with (Γ1 := Γ) (Γ2 := ∅).
  - apply env_split_empty_right.
  - exact (Pair_typed _ _ _ _ _ _ _ Hsplit He1 He2).
  - eapply Fun_typed.
    + apply env_bind_fresh. by simplify_map_eq.
    + discriminate.
    + eapply Fun_typed.
      * apply env_bind_fresh. by simplify_map_eq.
      * discriminate.
      * apply Fork_typed.
        eapply Fun_typed.
        -- apply env_bind_fresh. by simplify_map_eq.
        -- discriminate.
        -- eapply App_typed with (Γ1 := <["x" := toL (SendTB n ts σs)]> ∅).
           ++ apply env_split_insert_right.
              ** apply env_split_insert_right.
                 --- apply env_split_empty_right.
                 --- by simplify_map_eq.
              ** by simplify_map_eq.
           ++ rewrite <- toL_send. apply typed_single_binding.
           ++ eapply Sum_typed with (i := i).
              rewrite Hdual.
              eapply Pair_typed with (Γ1 := <["z" := FunT Lin b a]> ∅)
                                     (Γ2 := <["y" := ts i]> ∅).
              ** apply env_split_insert_left.
                 --- apply env_split_insert_right.
                     +++ apply env_split_empty_right.
                     +++ by simplify_map_eq.
                 --- by simplify_map_eq.
              ** apply typed_single_binding.
              ** apply typed_single_binding.
Qed.

Theorem RecvB_typed Γ e n ts σs :
  typed Γ e (toL (RecvTB n ts σs)) ->
  typed Γ (RecvB e) (SumT n (λ i, PairT (toL (σs i)) (ts i))).
Proof.
  rewrite toL_recv. intro He.
  eapply App_typed with (Γ1 := Γ) (Γ2 := ∅).
  - apply env_split_empty_right.
  - exact He.
  - apply Unit_typed. apply env_unr_empty.
Qed.

Theorem CloseB_typed Γ e :
  typed Γ e (toL EndTB) ->
  typed Γ (CloseB e) UnitT.
Proof.
  rewrite toL_end. intro He.
  eapply App_typed with (Γ1 := Γ) (Γ2 := ∅).
  - apply env_split_empty_right.
  - exact He.
  - apply Unit_typed. apply env_unr_empty.
Qed.
