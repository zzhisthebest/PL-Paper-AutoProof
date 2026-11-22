Require Import Language Sessions.

(* ------------------------------------------------------------------ *)
(* Environment lemmas                                                  *)
(* ------------------------------------------------------------------ *)

(* Coq's reduction only unfolds a cofixpoint when it is scrutinised by a
   match.  Consequently, facts about the interpretations of session types
   are established below through eta-expansions (see [type_eta] and
   [st_eta]) that expose the cofixpoints to a match. *)

Lemma env_lookup_empty (i : string) : (∅ : env) !! i = None.
Proof. apply lookup_empty. Qed.

Lemma env_lookup_insert (i j : string) (x : type) (m : env) :
  (<[i:=x]> m) !! j = (if decide (i = j) then Some x else m !! j).
Proof. apply lookup_insert. Qed.

Lemma env_union_empty_r (m : env) : m ∪ ∅ = m.
Proof. apply map_union_empty. Qed.

Lemma env_unr_empty : env_unr ∅.
Proof. intros x t H. rewrite env_lookup_empty in H. discriminate H. Qed.

Lemma env_split_empty_r (Γ : env) : env_split Γ Γ ∅.
Proof.
  split.
  - symmetry. apply env_union_empty_r.
  - intros i t1 t2 H1 H2. rewrite env_lookup_empty in H2. discriminate H2.
Qed.

Lemma env_unr_lookup_none (m : env) (y : string) :
  m !! y = None -> ∀ t', m !! y = Some t' -> unr t'.
Proof. intros Hm t' H. rewrite Hm in H. discriminate H. Qed.

Lemma env_unr_insert_ne (m : env) (x y : string) (t : type) :
  x ≠ y ->
  (∀ t', m !! y = Some t' -> unr t') ->
  ∀ t', (<[x := t]> m) !! y = Some t' -> unr t'.
Proof.
  intros Hne Hm t' H.
  rewrite env_lookup_insert in H.
  destruct (decide (x = y)) as [E|E]; [congruence |].
  apply Hm. exact H.
Qed.

Lemma env_var_self (x : string) (t : type) : env_var (<[x := t]> (∅ : env)) x t.
Proof. exists ∅. split; [reflexivity | apply env_unr_empty]. Qed.

Lemma disj_of_disjoint (Γ1 Γ2 : env) : Γ1 ##ₘ Γ2 -> disj Γ1 Γ2.
Proof.
  intros H i t1 t2 H1 H2.
  exfalso. exact (proj1 (map_disjoint_spec Γ1 Γ2) H i t1 t2 H1 H2).
Qed.

(* ------------------------------------------------------------------ *)
(* Unfolding of the session type interpretations                       *)
(* ------------------------------------------------------------------ *)

Lemma type_eta (t : type) :
  t = match t with
      | FunT l a b => FunT l a b
      | UnitT => UnitT
      | PairT a b => PairT a b
      | SumT n ts => SumT n ts
      end.
Proof. destruct t; reflexivity. Qed.

Lemma st_eta (σ : session_type) :
  σ = match σ with
      | SendTB n ts σs => SendTB n ts σs
      | RecvTB n ts σs => RecvTB n ts σs
      | EndTB => EndTB
      end.
Proof. destruct σ; reflexivity. Qed.

Lemma toL_Send n ts σs :
  toL (SendTB n ts σs) =
  FunT Lin (SumT n (fun i => PairT (toL (dual (σs i))) (ts i))) UnitT.
Proof. rewrite (type_eta (toL (SendTB n ts σs))). reflexivity. Qed.

Lemma toL_Recv n ts σs :
  toL (RecvTB n ts σs) =
  FunT Lin UnitT (SumT n (fun i => PairT (toL (σs i)) (ts i))).
Proof. rewrite (type_eta (toL (RecvTB n ts σs))). reflexivity. Qed.

Lemma toL_End : toL EndTB = FunT Lin UnitT UnitT.
Proof. rewrite (type_eta (toL EndTB)). reflexivity. Qed.

Lemma dual_Send n ts σs : dual (SendTB n ts σs) = RecvTB n ts (dual ∘ σs).
Proof. rewrite (st_eta (dual (SendTB n ts σs))). reflexivity. Qed.

Lemma dual_Recv n ts σs : dual (RecvTB n ts σs) = SendTB n ts (dual ∘ σs).
Proof. rewrite (st_eta (dual (RecvTB n ts σs))). reflexivity. Qed.

Lemma dual_End : dual EndTB = EndTB.
Proof. rewrite (st_eta (dual EndTB)). reflexivity. Qed.

Lemma toL_dual_Send n ts σs :
  toL (dual (SendTB n ts σs)) =
  FunT Lin UnitT (SumT n (fun i => PairT (toL (dual (σs i))) (ts i))).
Proof. rewrite dual_Send. rewrite toL_Recv. reflexivity. Qed.

Lemma toL_dual_Recv n ts σs :
  toL (dual (RecvTB n ts σs)) =
  FunT Lin (SumT n (fun i => PairT (toL (dual (dual (σs i)))) (ts i))) UnitT.
Proof. rewrite dual_Recv. rewrite (toL_Send n ts (dual ∘ σs)). reflexivity. Qed.

Lemma toL_dual_End : toL (dual EndTB) = FunT Lin UnitT UnitT.
Proof. rewrite dual_End. apply toL_End. Qed.

Lemma dual_dual_Send n ts σs :
  dual (dual (SendTB n ts σs)) = SendTB n ts (dual ∘ (dual ∘ σs)).
Proof. rewrite (st_eta (dual (dual (SendTB n ts σs)))). reflexivity. Qed.

Lemma dual_dual_Recv n ts σs :
  dual (dual (RecvTB n ts σs)) = RecvTB n ts (dual ∘ (dual ∘ σs)).
Proof. rewrite (st_eta (dual (dual (RecvTB n ts σs)))). reflexivity. Qed.

Lemma dual_dual_End : dual (dual EndTB) = EndTB.
Proof. rewrite (st_eta (dual (dual EndTB))). reflexivity. Qed.

Lemma dual_dual_equiv : ∀ σ : session_type, dual (dual σ) ≡ σ.
Proof.
  cofix IH. intros σ. destruct σ as [n ts σs | n ts σs | ].
  - rewrite (dual_dual_Send n ts σs).
    apply (cteq_SendT n ts ts (dual ∘ (dual ∘ σs)) σs
             (fun i => eq_refl) (fun i => IH (σs i))).
  - rewrite (dual_dual_Recv n ts σs).
    apply (cteq_RecvT n ts ts (dual ∘ (dual ∘ σs)) σs
             (fun i => eq_refl) (fun i => IH (σs i))).
  - rewrite dual_dual_End. apply cteq_EndT.
Qed.

Lemma dual_dual (σ : session_type) : dual (dual σ) = σ.
Proof. apply session_type_extensionality, dual_dual_equiv. Qed.

(* ------------------------------------------------------------------ *)
(* Derived typing rules                                                *)
(* ------------------------------------------------------------------ *)

Theorem ForkB_typed Γ σ e :
  typed Γ e (FunT Lin (toL (dual σ)) UnitT) ->
  typed Γ (ForkB e) (toL σ).
Proof.
  intros H. unfold ForkB.
  destruct σ as [n ts σs | n ts σs | ].
  - rewrite toL_Send.
    eapply Fork_typed with
        (t1 := SumT n (fun i => PairT (toL (dual (σs i))) (ts i))) (t2 := UnitT).
    rewrite toL_dual_Send in H. exact H.
  - rewrite toL_Recv.
    eapply Fork_typed with
        (t1 := UnitT) (t2 := SumT n (fun i => PairT (toL (σs i)) (ts i))).
    rewrite toL_dual_Recv in H.
    replace (SumT n (fun i => PairT (toL (dual (dual (σs i)))) (ts i)))
      with (SumT n (fun i => PairT (toL (σs i)) (ts i))) in H.
    + exact H.
    + apply f_equal. apply functional_extensionality. intro i.
      rewrite (dual_dual (σs i)). reflexivity.
  - rewrite toL_End.
    eapply Fork_typed with (t1 := UnitT) (t2 := UnitT).
    rewrite toL_dual_End in H. exact H.
Qed.

Theorem SendB_typed Γ Γ1 Γ2 e1 e2 n ts σs i :
  env_split Γ Γ1 Γ2 ->
  typed Γ1 e1 (toL (SendTB n ts σs)) ->
  typed Γ2 e2 (ts i) ->
  typed Γ (SendB e1 i e2) (toL (σs i)).
Proof.
  intros Hsplit H1 H2. unfold SendB.
  eapply LetPair_typed with (Γ1 := Γ) (Γ2 := ∅)
      (t1 := toL (SendTB n ts σs)) (t2 := ts i) (t := toL (σs i)).
  - apply env_split_empty_r.
  - eapply Pair_typed with (Γ1 := Γ1) (Γ2 := Γ2).
    + exact Hsplit.
    + exact H1.
    + exact H2.
  - eapply Fun_typed with
        (Γ' := <["x" := toL (SendTB n ts σs)]> (∅ : env))
        (t1 := toL (SendTB n ts σs))
        (t2 := FunT Lin (ts i) (toL (σs i))) (l := Lin).
    + split.
      * reflexivity.
      * apply env_unr_lookup_none, env_lookup_empty.
    + intros E; discriminate E.
    + eapply Fun_typed with
          (Γ' := <["y" := ts i]> (<["x" := toL (SendTB n ts σs)]> (∅ : env)))
          (t1 := ts i) (t2 := toL (σs i)) (l := Lin).
      * split.
        -- reflexivity.
        -- intros t' H.
           apply (env_unr_insert_ne ∅ "x" "y" (toL (SendTB n ts σs))).
           ++ intro E; discriminate E.
           ++ apply env_unr_lookup_none, env_lookup_empty.
           ++ exact H.
      * intros E; discriminate E.
      * eapply ForkB_typed.
        eapply Fun_typed with
            (Γ' := <["z" := toL (dual (σs i))]>
                     (<["y" := ts i]> (<["x" := toL (SendTB n ts σs)]> (∅ : env))))
            (t1 := toL (dual (σs i))) (t2 := UnitT) (l := Lin).
        -- split.
           ++ reflexivity.
           ++ intros t' H.
              apply (env_unr_insert_ne (<["x" := toL (SendTB n ts σs)]> (∅:env))
                       "y" "z" (ts i)).
              ** intro E; discriminate E.
              ** apply (env_unr_insert_ne ∅ "x" "z" (toL (SendTB n ts σs))).
                 --- intro E; discriminate E.
                 --- apply env_unr_lookup_none, env_lookup_empty.
              ** exact H.
        -- intros E; discriminate E.
        -- eapply App_typed with
              (Γ1 := <["x" := toL (SendTB n ts σs)]> (∅ : env))
              (Γ2 := <["z" := toL (dual (σs i))]> (<["y" := ts i]> (∅ : env)))
              (t1 := SumT n (fun j => PairT (toL (dual (σs j))) (ts j)))
              (t2 := UnitT) (l := Lin).
           ++ split.
              ** set_solver.
              ** apply disj_of_disjoint. set_solver.
           ++ rewrite <- (toL_Send n ts σs). eapply Var_typed. apply env_var_self.
           ++ eapply Sum_typed.
              ** eapply Pair_typed with
                   (Γ1 := <["z" := toL (dual (σs i))]> (∅ : env))
                   (Γ2 := <["y" := ts i]> (∅ : env))
                   (t1 := toL (dual (σs i))) (t2 := ts i).
                 --- split.
                     +++ set_solver.
                     +++ apply disj_of_disjoint. set_solver.
                 --- eapply Var_typed. apply env_var_self.
                 --- eapply Var_typed. apply env_var_self.
Qed.

Theorem RecvB_typed Γ e n ts σs :
  typed Γ e (toL (RecvTB n ts σs)) ->
  typed Γ (RecvB e) (SumT n (λ i, PairT (toL (σs i)) (ts i))).
Proof.
  intros H. unfold RecvB. rewrite toL_Recv in H.
  eapply App_typed with (Γ1 := Γ) (Γ2 := ∅) (t1 := UnitT)
    (t2 := SumT n (λ i, PairT (toL (σs i)) (ts i))) (l := Lin).
  - apply env_split_empty_r.
  - exact H.
  - apply Unit_typed. apply env_unr_empty.
Qed.

Theorem CloseB_typed Γ e :
  typed Γ e (toL EndTB) ->
  typed Γ (CloseB e) UnitT.
Proof.
  intros H. unfold CloseB. rewrite toL_End in H.
  eapply App_typed with (Γ1 := Γ) (Γ2 := ∅) (t1 := UnitT) (t2 := UnitT) (l := Lin).
  - apply env_split_empty_r.
  - exact H.
  - apply Unit_typed. apply env_unr_empty.
Qed.
