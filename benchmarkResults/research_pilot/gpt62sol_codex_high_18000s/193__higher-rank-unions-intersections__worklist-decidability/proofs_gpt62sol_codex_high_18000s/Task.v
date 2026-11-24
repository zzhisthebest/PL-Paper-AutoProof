Require Import Coq.Program.Equality.

Require Import Program.Tactics.

Require Import Metalib.Metatheory.

Require Import List.

Require Import uni.notations.

Require Import uni.algo_worklist.def_extra.

Open Scope aworklist_scope.

Open Scope dworklist_scope.

From Stdlib Require Import Arith Lia Wf_nat Lexicographic_Product Sorting.Permutation Wellfounded Relation_Operators.
Require Import uni.def_extra.

Lemma task_mem x S : AtomSetImpl.mem x S = true <-> x `in` S.
Proof. split; [apply AtomSetImpl.mem_2 | apply AtomSetImpl.mem_1]. Qed.

Lemma task_mem_false x S : AtomSetImpl.mem x S = false <-> x `notin` S.
Proof. destruct (AtomSetImpl.mem x S) eqn:E; rewrite <- task_mem; intuition congruence. Qed.

Lemma task_binds A (E : list (atom * A)) x a : binds x a E <-> List.In (x,a) E.
Proof. reflexivity. Qed.

Definition task_eq (x y : atom) : sumbool (x = y) (x <> y) := eq_var x y.
(* Split at the solved existential. The three parts are the worklist
   before its binding, the existential bindings moved before it, and the
   entries that remain after it. The substitution acts on the last part. *)
Fixpoint task_split (G : aworklist) (X : atom) (A : typ)
  : option (aworklist * aworklist * aworklist) :=
  match G with
  | aworklist_empty => None
  | aworklist_cons_var G Y abind_etvar_empty =>
      if task_eq Y X then Some (G, aworklist_empty, aworklist_empty)
      else match task_split G X A with
           | Some (P,M,K) =>
               if AtomSetImpl.mem Y (ftvar_in_typ A)
               then Some (P, awl_app M (aworklist_cons_var aworklist_empty Y abind_etvar_empty), K)
               else Some (P, M, aworklist_cons_var K Y abind_etvar_empty)
           | None => None
           end
  | aworklist_cons_var G Y b =>
      match task_split G X A with
      | Some (P,M,K) =>
          match b with
          | abind_var_typ _ => Some (P,M,aworklist_cons_var K Y b)
          | _ => if task_eq Y X then None
                 else if AtomSetImpl.mem Y (ftvar_in_typ A) then None
                 else Some (P,M,aworklist_cons_var K Y b)
          end
      | None => None
      end
  | aworklist_cons_work G w =>
      match task_split G X A with
      | Some (P,M,K) => Some (P,M,aworklist_cons_work K w)
      | None => None
      end
  end.

Lemma task_app_assoc A B C :
  awl_app (awl_app A B) C = awl_app A (awl_app B C).
Proof. induction A; simpl; congruence. Qed.

Lemma task_app_env A B :
  awl_to_aenv (awl_app A B) = awl_to_aenv A ++ awl_to_aenv B.
Proof. induction A; simpl; now try rewrite IHA. Qed.

Lemma task_split_insert C P X Y A :
  X `notin` dom (awl_to_aenv C) ->
  task_split (awl_app C (aworklist_cons_var (aworklist_cons_var P Y abind_etvar_empty)
                                                 X abind_etvar_empty)) X A =
    option_map (fun '(B,M,K) => (aworklist_cons_var B Y abind_etvar_empty,M,K))
      (task_split (awl_app C (aworklist_cons_var P X abind_etvar_empty)) X A).
Proof.
  induction C as [|C IHC Z a|C IHC w]; simpl; intros H.
  - destruct (task_eq X X); [reflexivity|congruence].
  - rewrite IHC by fsetdec. destruct a;
      repeat match goal with
      | |- context [task_eq ?x ?y] => destruct (task_eq x y); [subst; try solve [exfalso; fsetdec]|]
      | |- context [task_split ?G ?x ?A] => destruct (task_split G x A) as [ [ [? ?] ?]|]
      | |- context [AtomSetImpl.mem ?x ?S] => destruct (AtomSetImpl.mem x S)
      end; reflexivity.
  - rewrite IHC by fsetdec. destruct (task_split (awl_app C (aworklist_cons_var P X abind_etvar_empty)) X A) as [ [ [? ?] ?] | ]; reflexivity.
Qed.

Lemma task_split_complete G X A P K :
  aworklist_subst G X A P K -> uniq (awl_to_aenv G) ->
  exists B M, task_split G X A = Some (B,M,K) /\ P = awl_app M B.
Proof.
  intros H; induction H; intros U; simpl in *.
  - destruct (task_eq X X); [eauto|congruence].
  - destruct IHaworklist_subst as (base & M & -> & ->); [inversion U; auto|eauto].
  - destruct IHaworklist_subst as (B & M & -> & ->); [inversion U; auto|].
    rewrite (proj2 (task_mem_false _ _) H1).
    destruct (task_eq Y X); [congruence|eauto].
  - destruct IHaworklist_subst as (B & M & -> & ->); [inversion U; auto|].
    rewrite (proj2 (task_mem_false _ _) H1).
    destruct (task_eq Y X); [congruence|eauto].
  - destruct (IHaworklist_subst U) as (B & M & -> & ->); eauto.
  - destruct IHaworklist_subst as (B & M & -> & ->); [inversion U; auto|].
    rewrite (proj2 (task_mem_false _ _) H1).
    destruct (task_eq Y X); [congruence|eauto].
  - assert (U0 : uniq (awl_to_aenv Γ2 ++ (X,abind_etvar_empty) :: awl_to_aenv Γ1)).
    { rewrite task_app_env in U. exact (uniq_cons_1 _ _ _ _ U). }
    assert (FX : X `notin` dom (awl_to_aenv Γ2)) by (eapply fresh_mid_head; exact U0).
    assert (U' : uniq (awl_to_aenv
      (awl_app Γ2 (aworklist_cons_var (aworklist_cons_var Γ1 Y abind_etvar_empty) X abind_etvar_empty)))).
    { rewrite task_app_env in *. simpl in *.
      pose proof (uniq_cons_2 _ _ _ _ U) as FY.
      pose proof (fresh_mid_tail _ _ _ _ _ U0) as FXP.
      rewrite dom_app in FY; simpl in FY.
      apply uniq_insert_mid.
      - apply uniq_insert_mid.
        + exact (uniq_remove_mid _ (awl_to_aenv Γ2)
                   [(X,abind_etvar_empty)] (awl_to_aenv Γ1) U0).
        + fsetdec.
        + fsetdec.
      - exact FX.
      - simpl; fsetdec. }
    destruct (IHaworklist_subst U') as (B & M & HD & ->).
    rewrite task_split_insert in HD by assumption.
    destruct (task_split (awl_app Γ2 (aworklist_cons_var Γ1 X abind_etvar_empty)) X A)
      as [ [ [B' M'] K']|] eqn:ES; simpl in HD; try discriminate.
    inversion HD; subst.
    destruct (task_eq Y X); [congruence|].
    rewrite (proj2 (task_mem _ _) H1).
    do 2 eexists; split; [reflexivity|].
    now rewrite task_app_assoc.
Qed.

Lemma task_split_base G X A B M K :
  task_split G X A = Some (B,M,K) ->
  exists C, G = awl_app C (aworklist_cons_var B X abind_etvar_empty).
Proof.
  revert B M K; induction G as [|G IH Y b|G IH w]; intros B M K H; simpl in H.
  - discriminate.
  - destruct b; simpl in H.
    all: try (destruct (task_eq Y X) as [ -> | ?]; [try discriminate; injection H as <- <- <-;
               exists aworklist_empty; reflexivity|]).
    all: destruct (task_split G X A) as [ [ [P N] J]|] eqn:E; try discriminate.
    all: repeat match type of H with
         | context [task_eq ?x ?y] => destruct (task_eq x y); try discriminate
         | context [AtomSetImpl.mem ?x ?S] => destruct (AtomSetImpl.mem x S); try discriminate
         end.
    all: injection H as <- _ _; destruct (IH _ _ _ eq_refl) as [C ->];
         eexists (aworklist_cons_var C Y _); reflexivity.
  - destruct (task_split G X A) as [ [ [P N] J] | ]; try discriminate.
    injection H as <- _ _. destruct (IH _ _ _ eq_refl) as [C ->].
    exists (aworklist_cons_work C w); reflexivity.
Qed.

Lemma task_split_sound_aux C B X A P M K :
  X `notin` dom (awl_to_aenv C) ->
  task_split (awl_app C (aworklist_cons_var B X abind_etvar_empty)) X A = Some (P,M,K) ->
  aworklist_subst (awl_app C (aworklist_cons_var B X abind_etvar_empty)) X A (awl_app M P) K.
Proof.
  revert B P M K; induction C as [|C IH Y b|C IH w]; intros B P M K F H; simpl in *.
  - destruct (task_eq X X); [injection H as <- <- <-; constructor|congruence].
  - assert (FX : X `notin` dom (awl_to_aenv C)) by fsetdec.
    assert (NE : Y <> X) by (intro; subst; fsetdec).
    destruct b; simpl in H; try (destruct (task_eq Y X); [contradiction|]).
    all: destruct (task_split (awl_app C (aworklist_cons_var B X abind_etvar_empty)) X A)
           as [ [ [Q N] J]|] eqn:E; try discriminate.
    all: try (destruct (task_eq Y X); [contradiction|]).
    all: try (match type of H with context [AtomSetImpl.mem ?z ?s] => destruct (AtomSetImpl.mem z s) eqn:FV; try discriminate end).
    all: injection H as <- <- <-.
    + apply a_ws__tvar_stay; [eapply IH; eassumption|exact NE|now apply task_mem_false].
    + apply a_ws__stvar_stay; [eapply IH; eassumption|exact NE|now apply task_mem_false].
    + rewrite task_app_assoc.
      apply a_ws__etvar_move; [|exact NE|now apply task_mem].
      eapply IH; [exact FX|rewrite task_split_insert, E by assumption; reflexivity].
    + apply a_ws__etvar_stay; [eapply IH; eassumption|exact NE|now apply task_mem_false].
    + apply a_ws__var_stay; eapply IH; eassumption.
  - destruct (task_split (awl_app C (aworklist_cons_var B X abind_etvar_empty)) X A)
      as [ [ [Q N] J]|] eqn:E; try discriminate.
    injection H as <- <- <-. apply a_ws__work_stay. eapply IH; eassumption.
Qed.

Lemma task_split_sound G X A P M K :
  uniq (awl_to_aenv G) ->
  task_split G X A = Some (P,M,K) ->
  aworklist_subst G X A (awl_app M P) K.
Proof.
  intros U H. destruct (task_split_base _ _ _ _ _ _ H) as [C ->].
  apply task_split_sound_aux; [|assumption].
  rewrite task_app_env in U. eapply fresh_mid_head; exact U.
Qed.

(* Monotypes have rank zero. An arrow above a positive-rank component
   contributes one more, so replacing an existential by a monotype
   preserves the rank of every type in which it occurs. *)
Fixpoint task_type_rank (R : atoms) (A : typ) : nat :=
  match A with
  | typ_unit => 0
  | typ_var_b _ => 1
  | typ_var_f X => if AtomSetImpl.mem X R then 1 else 0
  | typ_bot | typ_top => 1
  | typ_all A => S (task_type_rank R A)
  | typ_intersection A B | typ_union A B => S (task_type_rank R A + task_type_rank R B)
  | typ_arrow A B => match task_type_rank R A + task_type_rank R B with
                     | 0 => 0 | S n => S (S n) end
  end.

Fixpoint task_head_rank (A : typ) : nat :=
  match A with
  | typ_bot => 9
  | typ_all A => 8 + task_head_rank A
  | typ_union A B | typ_intersection A B => 8 + task_head_rank A + task_head_rank B
  | _ => 8
  end.

Fixpoint task_exp_rank (e : exp) : nat :=
  match e with
  | exp_abs e | exp_tabs e | exp_tapp e _ | exp_anno e _ => S (task_exp_rank e)
  | exp_app e e' => S (task_exp_rank e + task_exp_rank e')
  | _ => 1
  end.

Lemma task_exp_rank_positive e : 0 < task_exp_rank e.
Proof. destruct e; simpl; lia. Qed.

Fixpoint task_type_dom G : atoms :=
  match G with
  | aworklist_empty => empty
  | aworklist_cons_var G X (abind_var_typ _) => task_type_dom G
  | aworklist_cons_var G X _ => add X (task_type_dom G)
  | aworklist_cons_work G _ => task_type_dom G
  end.

Fixpoint task_scoped D G : Prop :=
  match G with
  | aworklist_empty => True
  | aworklist_cons_var G X b =>
      task_scoped D G /\ ftvar_in_abind b [<=] union D (task_type_dom G)
  | aworklist_cons_work G w =>
      task_scoped D G /\ ftvar_in_work w [<=] union D (task_type_dom G)
  end.

Fixpoint task_colors (R : atoms) G : Prop :=
  match G with
  | aworklist_empty => True
  | aworklist_cons_var G X b => task_colors R G /\
      match b with
      | abind_tvar_empty | abind_etvar_empty => X `notin` R
      | abind_stvar_empty => X `in` R
      | abind_var_typ _ => True
      end
  | aworklist_cons_work G _ => task_colors R G
  end.

Fixpoint task_rigids G : atoms :=
  match G with
  | aworklist_empty => empty
  | aworklist_cons_var G X abind_stvar_empty => add X (task_rigids G)
  | aworklist_cons_var G _ _ | aworklist_cons_work G _ => task_rigids G
  end.

Lemma task_rigids_dom G : task_rigids G [<=] dom (awl_to_aenv G).
Proof. induction G; simpl; try destruct ab; simpl in *; fsetdec. Qed.

Lemma task_colors_extend G R X :
  X `notin` dom (awl_to_aenv G) -> task_colors R G -> task_colors (add X R) G.
Proof.
  induction G as [|G IH Y b|G IH w]; simpl; auto.
  intros F [H0 H1]; split; [apply IH; [fsetdec|exact H0]|].
  destruct b; simpl in *; try fsetdec.
Qed.

Lemma task_colors_init G : uniq (awl_to_aenv G) -> task_colors (task_rigids G) G.
Proof.
  induction G as [|G IH X b|G IH w]; simpl; auto.
  intros U; pose proof (uniq_cons_1 _ _ _ _ U) as U0.
  pose proof (uniq_cons_2 _ _ _ _ U) as F.
  specialize (IH U0); pose proof (task_rigids_dom G).
  destruct b; simpl; try solve [split; [exact IH|intuition fsetdec]].
  split; [now apply task_colors_extend|fsetdec].
Qed.
(* Renaming acts on both namespaces and their binding keys. Swaps are
   enough to transport any cofinite premise to a chosen fresh tuple. *)
Fixpoint task_rename_typ (f : atom -> atom) (t : typ) : typ :=
  match t with
  | typ_unit => typ_unit
  | typ_top => typ_top
  | typ_bot => typ_bot
  | typ_var_b n1 => typ_var_b n1
  | typ_var_f x1 => typ_var_f (f x1)
  | typ_arrow t1 t2 => typ_arrow (task_rename_typ f t1) (task_rename_typ f t2)
  | typ_all t1 => typ_all (task_rename_typ f t1)
  | typ_union t1 t2 => typ_union (task_rename_typ f t1) (task_rename_typ f t2)
  | typ_intersection t1 t2 => typ_intersection (task_rename_typ f t1) (task_rename_typ f t2)
  end.

Fixpoint task_rename_exp (f : atom -> atom) (t : exp) : exp :=
  match t with
  | exp_unit => exp_unit
  | exp_var_b n1 => exp_var_b n1
  | exp_var_f x1 => exp_var_f (f x1)
  | exp_abs e1 => exp_abs (task_rename_exp f e1)
  | exp_app e1 e2 => exp_app (task_rename_exp f e1) (task_rename_exp f e2)
  | exp_tabs e1 => exp_tabs (task_rename_exp f e1)
  | exp_tapp e1 t2 => exp_tapp (task_rename_exp f e1) (task_rename_typ f t2)
  | exp_anno e1 t2 => exp_anno (task_rename_exp f e1) (task_rename_typ f t2)
  end.

Fixpoint task_rename_conts (f : atom -> atom) (t : conts) : conts :=
  match t with
  | conts_infabs c1 => conts_infabs (task_rename_contd f c1)
  | conts_inftapp t1 c2 => conts_inftapp (task_rename_typ f t1) (task_rename_conts f c2)
  | conts_inftappunion t1 t2 c3 => conts_inftappunion (task_rename_typ f t1) (task_rename_typ f t2) (task_rename_conts f c3)
  | conts_unioninftapp t1 c2 => conts_unioninftapp (task_rename_typ f t1) (task_rename_conts f c2)
  | conts_sub t1 => conts_sub (task_rename_typ f t1)
  end
with task_rename_contd (f : atom -> atom) (t : contd) : contd :=
  match t with
  | contd_infabsunion t1 c2 => contd_infabsunion (task_rename_typ f t1) (task_rename_contd f c2)
  | contd_infapp e1 c2 => contd_infapp (task_rename_exp f e1) (task_rename_conts f c2)
  | contd_unioninfabs t1 t2 c3 => contd_unioninfabs (task_rename_typ f t1) (task_rename_typ f t2) (task_rename_contd f c3)
  end.

Definition task_rename_abind (f : atom -> atom) (t : abind) : abind :=
  match t with
  | abind_tvar_empty => abind_tvar_empty
  | abind_stvar_empty => abind_stvar_empty
  | abind_etvar_empty => abind_etvar_empty
  | abind_var_typ t1 => abind_var_typ (task_rename_typ f t1)
  end.

Definition task_rename_work (f : atom -> atom) (t : work) : work :=
  match t with
  | work_infer e1 c2 => work_infer (task_rename_exp f e1) (task_rename_conts f c2)
  | work_check e1 t2 => work_check (task_rename_exp f e1) (task_rename_typ f t2)
  | work_infabs t1 c2 => work_infabs (task_rename_typ f t1) (task_rename_contd f c2)
  | work_infabsunion t1 t2 t3 c4 => work_infabsunion (task_rename_typ f t1) (task_rename_typ f t2) (task_rename_typ f t3) (task_rename_contd f c4)
  | work_infapp t1 t2 e3 c4 => work_infapp (task_rename_typ f t1) (task_rename_typ f t2) (task_rename_exp f e3) (task_rename_conts f c4)
  | work_inftapp t1 t2 c3 => work_inftapp (task_rename_typ f t1) (task_rename_typ f t2) (task_rename_conts f c3)
  | work_sub t1 t2 => work_sub (task_rename_typ f t1) (task_rename_typ f t2)
  | work_inftappunion t1 t2 t3 c4 => work_inftappunion (task_rename_typ f t1) (task_rename_typ f t2) (task_rename_typ f t3) (task_rename_conts f c4)
  | work_unioninftapp t1 t2 c3 => work_unioninftapp (task_rename_typ f t1) (task_rename_typ f t2) (task_rename_conts f c3)
  | work_unioninfabs t1 t2 t3 t4 c5 => work_unioninfabs (task_rename_typ f t1) (task_rename_typ f t2) (task_rename_typ f t3) (task_rename_typ f t4) (task_rename_contd f c5)
  | work_applys c1 t2 => work_applys (task_rename_conts f c1) (task_rename_typ f t2)
  | work_applyd c1 t2 t3 => work_applyd (task_rename_contd f c1) (task_rename_typ f t2) (task_rename_typ f t3)
  end.

Fixpoint task_rename_aworklist (f : atom -> atom) (t : aworklist) : aworklist :=
  match t with
  | aworklist_empty => aworklist_empty
  | aworklist_cons_var G1 x2 b3 => aworklist_cons_var (task_rename_aworklist f G1) (f x2) (task_rename_abind f b3)
  | aworklist_cons_work G1 w2 => aworklist_cons_work (task_rename_aworklist f G1) (task_rename_work f w2)
  end.

Fixpoint task_names_typ (t : typ) : atoms :=
  match t with
  | typ_unit => empty
  | typ_top => empty
  | typ_bot => empty
  | typ_var_b n1 => empty
  | typ_var_f x1 => (singleton x1)
  | typ_arrow t1 t2 => (task_names_typ t1) `union` (task_names_typ t2)
  | typ_all t1 => (task_names_typ t1)
  | typ_union t1 t2 => (task_names_typ t1) `union` (task_names_typ t2)
  | typ_intersection t1 t2 => (task_names_typ t1) `union` (task_names_typ t2)
  end.

Fixpoint task_names_exp (t : exp) : atoms :=
  match t with
  | exp_unit => empty
  | exp_var_b n1 => empty
  | exp_var_f x1 => (singleton x1)
  | exp_abs e1 => (task_names_exp e1)
  | exp_app e1 e2 => (task_names_exp e1) `union` (task_names_exp e2)
  | exp_tabs e1 => (task_names_exp e1)
  | exp_tapp e1 t2 => (task_names_exp e1) `union` (task_names_typ t2)
  | exp_anno e1 t2 => (task_names_exp e1) `union` (task_names_typ t2)
  end.

Fixpoint task_names_conts (t : conts) : atoms :=
  match t with
  | conts_infabs c1 => (task_names_contd c1)
  | conts_inftapp t1 c2 => (task_names_typ t1) `union` (task_names_conts c2)
  | conts_inftappunion t1 t2 c3 => (task_names_typ t1) `union` (task_names_typ t2) `union` (task_names_conts c3)
  | conts_unioninftapp t1 c2 => (task_names_typ t1) `union` (task_names_conts c2)
  | conts_sub t1 => (task_names_typ t1)
  end
with task_names_contd (t : contd) : atoms :=
  match t with
  | contd_infabsunion t1 c2 => (task_names_typ t1) `union` (task_names_contd c2)
  | contd_infapp e1 c2 => (task_names_exp e1) `union` (task_names_conts c2)
  | contd_unioninfabs t1 t2 c3 => (task_names_typ t1) `union` (task_names_typ t2) `union` (task_names_contd c3)
  end.

Definition task_names_abind (t : abind) : atoms :=
  match t with
  | abind_tvar_empty => empty
  | abind_stvar_empty => empty
  | abind_etvar_empty => empty
  | abind_var_typ t1 => (task_names_typ t1)
  end.

Definition task_names_work (t : work) : atoms :=
  match t with
  | work_infer e1 c2 => (task_names_exp e1) `union` (task_names_conts c2)
  | work_check e1 t2 => (task_names_exp e1) `union` (task_names_typ t2)
  | work_infabs t1 c2 => (task_names_typ t1) `union` (task_names_contd c2)
  | work_infabsunion t1 t2 t3 c4 => (task_names_typ t1) `union` (task_names_typ t2) `union` (task_names_typ t3) `union` (task_names_contd c4)
  | work_infapp t1 t2 e3 c4 => (task_names_typ t1) `union` (task_names_typ t2) `union` (task_names_exp e3) `union` (task_names_conts c4)
  | work_inftapp t1 t2 c3 => (task_names_typ t1) `union` (task_names_typ t2) `union` (task_names_conts c3)
  | work_sub t1 t2 => (task_names_typ t1) `union` (task_names_typ t2)
  | work_inftappunion t1 t2 t3 c4 => (task_names_typ t1) `union` (task_names_typ t2) `union` (task_names_typ t3) `union` (task_names_conts c4)
  | work_unioninftapp t1 t2 c3 => (task_names_typ t1) `union` (task_names_typ t2) `union` (task_names_conts c3)
  | work_unioninfabs t1 t2 t3 t4 c5 => (task_names_typ t1) `union` (task_names_typ t2) `union` (task_names_typ t3) `union` (task_names_typ t4) `union` (task_names_contd c5)
  | work_applys c1 t2 => (task_names_conts c1) `union` (task_names_typ t2)
  | work_applyd c1 t2 t3 => (task_names_contd c1) `union` (task_names_typ t2) `union` (task_names_typ t3)
  end.

Fixpoint task_names_aworklist (t : aworklist) : atoms :=
  match t with
  | aworklist_empty => empty
  | aworklist_cons_var G1 x2 b3 => (task_names_aworklist G1) `union` (singleton x2) `union` (task_names_abind b3)
  | aworklist_cons_work G1 w2 => (task_names_aworklist G1) `union` (task_names_work w2)
  end.

Definition task_involution (f : atom -> atom) := forall x, f (f x) = x.

Lemma task_inj f : task_involution f -> forall x y, f x = f y -> x = y.
Proof. intros I x y E. now rewrite <- (I x), <- (I y), E. Qed.

Definition task_swap (a b x : atom) : atom :=
  if task_eq x a then b else if task_eq x b then a else x.

Lemma task_swap_involution a b : task_involution (task_swap a b).
Proof.
  intro x; unfold task_swap.
  destruct (task_eq x a) as [ ->|F].
  - destruct (task_eq b a) as [ -> | ?]; [reflexivity|].
    destruct (task_eq b b); congruence.
  - destruct (task_eq x b) as [ ->|?].
    + destruct (task_eq a a); congruence.
    + destruct (task_eq x a), (task_eq x b); congruence.
Qed.

Lemma task_swap_left a b : task_swap a b a = b.
Proof. unfold task_swap; destruct (task_eq a a); congruence. Qed.

Lemma task_swap_fixed a b x : x <> a -> x <> b -> task_swap a b x = x.
Proof. unfold task_swap; destruct (task_eq x a), (task_eq x b); congruence. Qed.

Definition task_list_set (xs : list atom) : atoms := fold_right add empty xs.
Definition task_image (f : atom -> atom) (S : atoms) :=
  task_list_set (List.map f (AtomSetImpl.elements S)).

Lemma task_list_set_in x xs : x `in` task_list_set xs <-> List.In x xs.
Proof. induction xs; simpl in *; [fsetdec|rewrite <- IHxs; fsetdec]. Qed.

Lemma task_image_in f x S : x `in` S -> f x `in` task_image f S.
Proof.
  intros H. apply task_list_set_in, in_map. apply AtomSetImpl.elements_1 in H.
  apply InA_alt in H as [y [E H]]; now subst.
Qed.

Lemma task_rename_typ_open f A : forall k B,
  task_rename_typ f (open_typ_wrt_typ_rec k B A) =
  open_typ_wrt_typ_rec k (task_rename_typ f B) (task_rename_typ f A).
Proof.
  induction A; intros; simpl; try congruence.
  destruct (lt_eq_lt_dec n k) as [ [] | ]; reflexivity.
Qed.

Lemma task_rename_exp_open_exp f e : forall k v,
  task_rename_exp f (open_exp_wrt_exp_rec k v e) =
  open_exp_wrt_exp_rec k (task_rename_exp f v) (task_rename_exp f e).
Proof.
  induction e; intros; simpl; try congruence.
  destruct (lt_eq_lt_dec n k) as [ [] | ]; reflexivity.
Qed.

Lemma task_rename_exp_open_typ f e : forall k A,
  task_rename_exp f (open_exp_wrt_typ_rec k A e) =
  open_exp_wrt_typ_rec k (task_rename_typ f A) (task_rename_exp f e).
Proof. induction e; intros; simpl; rewrite ?task_rename_typ_open; congruence. Qed.

Lemma task_rename_subst_typ f (I : task_involution f) A X B :
  task_rename_typ f (subst_typ_in_typ A X B) =
  subst_typ_in_typ (task_rename_typ f A) (f X) (task_rename_typ f B).
Proof.
  induction B; simpl; try congruence.
  repeat match goal with |- context [if ?test then _ else _] => destruct test end;
    simpl; try congruence; exfalso; eauto using task_inj.
Qed.

Lemma task_rename_subst_exp f (I : task_involution f) A X e :
  task_rename_exp f (subst_typ_in_exp A X e) =
  subst_typ_in_exp (task_rename_typ f A) (f X) (task_rename_exp f e).
Proof. induction e; simpl; rewrite ?task_rename_subst_typ by exact I; congruence. Qed.

Scheme task_conts_ind := Induction for conts Sort Prop
  with task_contd_ind := Induction for contd Sort Prop.
Combined Scheme task_cont_ind from task_conts_ind, task_contd_ind.

Lemma task_rename_subst_cont f (I : task_involution f) A X :
  (forall c, task_rename_conts f (subst_typ_in_conts A X c) =
    subst_typ_in_conts (task_rename_typ f A) (f X) (task_rename_conts f c)) /\
  (forall c, task_rename_contd f (subst_typ_in_contd A X c) =
    subst_typ_in_contd (task_rename_typ f A) (f X) (task_rename_contd f c)).
Proof.
  apply task_cont_ind; intros; simpl;
    rewrite ?task_rename_subst_typ, ?task_rename_subst_exp by exact I; congruence.
Qed.

Lemma task_rename_subst_awl f (I : task_involution f) A X G :
  task_rename_aworklist f (subst_typ_in_aworklist A X G) =
  subst_typ_in_aworklist (task_rename_typ f A) (f X) (task_rename_aworklist f G).
Proof.
  destruct (task_rename_subst_cont f I A X) as [HS HD].
  induction G; simpl; [reflexivity|destruct ab|destruct w];
    simpl; rewrite ?HS, ?HD, ?task_rename_subst_typ, ?task_rename_subst_exp by exact I; congruence.
Qed.

Lemma task_rename_app f G H :
  task_rename_aworklist f (awl_app G H) =
  awl_app (task_rename_aworklist f G) (task_rename_aworklist f H).
Proof. induction G; simpl; congruence. Qed.

Lemma task_rename_ftvar f (I : task_involution f) X A :
  f X `in` ftvar_in_typ (task_rename_typ f A) <-> X `in` ftvar_in_typ A.
Proof.
  induction A; simpl; try fsetdec.
  assert (f X = f X0 <-> X = X0) by (split; [eauto using task_inj|congruence]).
  fsetdec.
Qed.
Lemma task_rename_typ_fixed (f : atom -> atom) :
  (forall t, (forall x, x `in` task_names_typ t -> f x = x) -> task_rename_typ f t = t).
Proof.

  intro t; induction t; intros; simpl in *; f_equal; try reflexivity;
    first [solve [auto using task_swap_fixed] |
      solve [apply H; fsetdec] |
      match goal with
      | IH : (forall x, x `in` _ -> _) -> _ = _, F : forall x, x `in` _ -> _ |- _ =>
          apply IH; intros; apply F; fsetdec
      | F : forall x, x `in` _ -> _ |- _ =>
          first [fail];
          intros; apply F; fsetdec
      end].
Qed.

Lemma task_rename_typ_invol f (I : task_involution f) :
  (forall t, task_rename_typ f (task_rename_typ f t) = t).
Proof.
  intro t; induction t; intros; simpl; rewrite ?I; congruence.
Qed.

Lemma task_rename_exp_fixed (f : atom -> atom) :
  (forall t, (forall x, x `in` task_names_exp t -> f x = x) -> task_rename_exp f t = t).
Proof.

  intro t; induction t; intros; simpl in *; f_equal; try reflexivity;
    first [solve [auto using task_rename_typ_fixed, task_swap_fixed] |
      solve [apply H; fsetdec] |
      match goal with
      | IH : (forall x, x `in` _ -> _) -> _ = _, F : forall x, x `in` _ -> _ |- _ =>
          apply IH; intros; apply F; fsetdec
      | F : forall x, x `in` _ -> _ |- _ =>
          first [apply task_rename_typ_fixed | fail];
          intros; apply F; fsetdec
      end].
Qed.

Lemma task_rename_exp_invol f (I : task_involution f) :
  (forall t, task_rename_exp f (task_rename_exp f t) = t).
Proof.
  intro t; induction t; intros; simpl; rewrite ?task_rename_typ_invol by exact I; rewrite ?I; congruence.
Qed.

Lemma task_rename_conts_fixed (f : atom -> atom) :
  (forall t, (forall x, x `in` task_names_conts t -> f x = x) -> task_rename_conts f t = t) /\
  (forall t, (forall x, x `in` task_names_contd t -> f x = x) -> task_rename_contd f t = t).
Proof.

  apply task_cont_ind; intros; simpl in *; f_equal; try reflexivity;
    first [solve [auto using task_rename_exp_fixed, task_rename_typ_fixed, task_swap_fixed] |
      solve [apply H; fsetdec] |
      match goal with
      | IH : (forall x, x `in` _ -> _) -> _ = _, F : forall x, x `in` _ -> _ |- _ =>
          apply IH; intros; apply F; fsetdec
      | F : forall x, x `in` _ -> _ |- _ =>
          first [apply task_rename_exp_fixed | apply task_rename_typ_fixed | fail];
          intros; apply F; fsetdec
      end].
Qed.

Lemma task_rename_conts_invol f (I : task_involution f) :
  (forall t, task_rename_conts f (task_rename_conts f t) = t) /\
  (forall t, task_rename_contd f (task_rename_contd f t) = t).
Proof.
  apply task_cont_ind; intros; simpl; rewrite ?task_rename_exp_invol, ?task_rename_typ_invol by exact I; rewrite ?I; congruence.
Qed.

Lemma task_rename_abind_fixed (f : atom -> atom) :
  (forall t, (forall x, x `in` task_names_abind t -> f x = x) -> task_rename_abind f t = t).
Proof.

  intro t; destruct t; intros; simpl in *; f_equal; try reflexivity;
    first [solve [auto using task_rename_typ_fixed, task_swap_fixed] |
      solve [apply H; fsetdec] |
      match goal with
      | IH : (forall x, x `in` _ -> _) -> _ = _, F : forall x, x `in` _ -> _ |- _ =>
          apply IH; intros; apply F; fsetdec
      | F : forall x, x `in` _ -> _ |- _ =>
          first [apply task_rename_typ_fixed | fail];
          intros; apply F; fsetdec
      end].
Qed.

Lemma task_rename_abind_invol f (I : task_involution f) :
  (forall t, task_rename_abind f (task_rename_abind f t) = t).
Proof.
  intro t; destruct t; intros; simpl; rewrite ?task_rename_typ_invol by exact I; rewrite ?I; congruence.
Qed.

Lemma task_rename_work_fixed (f : atom -> atom) :
  (forall t, (forall x, x `in` task_names_work t -> f x = x) -> task_rename_work f t = t).
Proof.
  destruct (task_rename_conts_fixed f) as [HS HD].
  intro t; destruct t; intros; simpl in *; f_equal; try reflexivity;
    first [solve [auto using task_rename_exp_fixed, task_rename_typ_fixed, HS, HD, task_swap_fixed] |
      solve [apply H; fsetdec] |
      match goal with
      | IH : (forall x, x `in` _ -> _) -> _ = _, F : forall x, x `in` _ -> _ |- _ =>
          apply IH; intros; apply F; fsetdec
      | F : forall x, x `in` _ -> _ |- _ =>
          first [apply task_rename_exp_fixed | apply task_rename_typ_fixed | apply HS | apply HD | fail];
          intros; apply F; fsetdec
      end].
Qed.

Lemma task_rename_work_invol f (I : task_involution f) :
  (forall t, task_rename_work f (task_rename_work f t) = t).
Proof.
  destruct (task_rename_conts_invol f I) as [HS HD].
  intro t; destruct t; intros; simpl; rewrite ?task_rename_contd_invol, ?task_rename_conts_invol, ?task_rename_exp_invol, ?task_rename_typ_invol by exact I; rewrite ?HS, ?HD, ?I; congruence.
Qed.

Lemma task_rename_aworklist_fixed (f : atom -> atom) :
  (forall G, (forall x, x `in` task_names_aworklist G -> f x = x) -> task_rename_aworklist f G = G).
Proof.

  intro G; induction G; intros; simpl in *; f_equal; try reflexivity;
    first [solve [auto using task_rename_abind_fixed, task_rename_work_fixed, task_swap_fixed] |
      solve [apply H; fsetdec] |
      match goal with
      | IH : (forall x, x `in` _ -> _) -> _ = _, F : forall x, x `in` _ -> _ |- _ =>
          apply IH; intros; apply F; fsetdec
      | F : forall x, x `in` _ -> _ |- _ =>
          first [apply task_rename_abind_fixed | apply task_rename_work_fixed | fail];
          intros; apply F; fsetdec
      end].
Qed.

Lemma task_rename_aworklist_invol f (I : task_involution f) :
  (forall G, task_rename_aworklist f (task_rename_aworklist f G) = G).
Proof.
  intro G; induction G; intros; simpl; rewrite ?task_rename_abind_invol, ?task_rename_work_invol by exact I; rewrite ?I; congruence.
Qed.

Lemma task_rename_binds f G X b :
  binds X b (awl_to_aenv G) ->
  binds (f X) (task_rename_abind f b) (awl_to_aenv (task_rename_aworklist f G)).
Proof.
  induction G as [|G IH Y c|G IH w]; rewrite !task_binds in *; simpl; auto.
  intros [E|H]; [inversion E; auto|right; apply IH; exact H].
Qed.

Lemma task_rename_mono f G A :
  a_mono_typ (awl_to_aenv G) A ->
  a_mono_typ (awl_to_aenv (task_rename_aworklist f G)) (task_rename_typ f A).
Proof.
  remember (awl_to_aenv G) as E. induction 1; subst; simpl; try solve [constructor; auto].
  - apply a_mono_typ__tvar. exact (task_rename_binds f G X abind_tvar_empty H).
  - apply a_mono_typ__etvar. exact (task_rename_binds f G X abind_etvar_empty H).
Qed.

Lemma task_rename_lc f (I : task_involution f) A : lc_typ A -> lc_typ (task_rename_typ f A).
Proof.
  induction 1; simpl; try solve [constructor; auto].
  apply lc_typ_all; intro y.
  match goal with IH : forall x, lc_typ (task_rename_typ f _) |- _ =>
    specialize (IH (f y))
  end.
  unfold open_typ_wrt_typ in *.
  rewrite task_rename_typ_open in *; simpl in *; rewrite I in *; assumption.
Qed.

Lemma task_rename_wneq f (I : task_involution f) G A :
  a_wneq_all (awl_to_aenv G) A ->
  a_wneq_all (awl_to_aenv (task_rename_aworklist f G)) (task_rename_typ f A).
Proof.
  remember (awl_to_aenv G) as E. induction 1; subst; simpl;
    eauto using a_wneq_all, task_rename_lc.
  - apply a_wneq_all__tvar. exact (task_rename_binds f G X abind_tvar_empty H).
  - apply a_wneq_all__etvar. exact (task_rename_binds f G X abind_etvar_empty H).
Qed.

Lemma task_rename_awl_subst f (I : task_involution f) G X A P K :
  aworklist_subst G X A P K ->
  aworklist_subst (task_rename_aworklist f G) (f X) (task_rename_typ f A)
    (task_rename_aworklist f P) (task_rename_aworklist f K).
Proof.
  induction 1; simpl; rewrite ?task_rename_app;
    try solve [econstructor; eauto; rewrite task_rename_ftvar by exact I; assumption].
  all: eauto using aworklist_subst, task_inj.
  all: first [apply a_ws__tvar_stay|apply a_ws__stvar_stay|apply a_ws__etvar_stay|apply a_ws__etvar_move];
      eauto using task_inj; try now rewrite task_rename_ftvar by exact I.
  now rewrite task_rename_app in IHaworklist_subst.
Qed.

Lemma task_rename_apply_s f cs A w : apply_conts cs A w ->
  apply_conts (task_rename_conts f cs) (task_rename_typ f A) (task_rename_work f w).
Proof. destruct 1; simpl; constructor. Qed.

Lemma task_rename_apply_d f cd A B w : apply_contd cd A B w ->
  apply_contd (task_rename_contd f cd) (task_rename_typ f A) (task_rename_typ f B) (task_rename_work f w).
Proof. destruct 1; simpl; constructor. Qed.

Lemma task_notin_image f (I : task_involution f) L x :
  x `notin` task_image f L -> f x `notin` L.
Proof. intros H F. apply H. pose proof (task_image_in f _ _ F) as E. now rewrite I in E. Qed.

Local Ltac task_rename_normalize H :=
  let I := match goal with I : task_involution _ |- _ => I end in
  let f := match type of I with task_involution ?f => f end in
  let SI := constr:(proj1 (task_rename_conts_invol f I)) in
  let DI := constr:(proj2 (task_rename_conts_invol f I)) in
  unfold open_typ_wrt_typ, open_exp_wrt_typ, open_exp_wrt_exp in H;
  repeat (progress (cbn in H;
    rewrite ?task_rename_app, ?task_rename_subst_awl,
      ?task_rename_exp_open_exp, ?task_rename_exp_open_typ, ?task_rename_typ_open,
      ?task_rename_typ_invol, ?task_rename_exp_invol, ?task_rename_work_invol,
      ?task_rename_aworklist_invol, ?SI, ?DI in H by assumption));
  try match goal with I : task_involution ?f |- _ => rewrite ?I in H end.

Lemma task_rename_no_mono f (I : task_involution f) G A :
  ~ a_mono_typ (awl_to_aenv G) A ->
  ~ a_mono_typ (awl_to_aenv (task_rename_aworklist f G)) (task_rename_typ f A).
Proof.
  intros N H. apply N. apply (task_rename_mono f _ _) in H.
  now rewrite task_rename_aworklist_invol, task_rename_typ_invol in H.
Qed.

Local Ltac task_fresh_transport f I :=
  repeat match goal with
  | |- _ `notin` union _ _ => apply notin_union
  | |- f ?x `notin` ?L =>
      first [apply (task_notin_image f I); fsetdec
        | solve [intro E; assert (f x <> f x) by
             (intro; fsetdec); congruence]
        | solve [let F := fresh in
            assert (F : forall a b, f a = f b -> a = b) by exact (task_inj f I);
            match goal with
            | |- f ?x `notin` singleton (f ?y) =>
                assert (x <> y) by (intro; subst; fsetdec);
                assert (f x <> f y) by eauto; fsetdec
            end]]
  end.

Local Ltac task_transport_assumption f I :=
  match goal with
  | HS : aworklist_subst _ _ _ _ _ |- _ =>
      let HS' := fresh "SwappedSubstitution" in
      pose proof (task_rename_awl_subst f I _ _ _ _ _ HS) as HS';
      task_rename_normalize HS';
      repeat rewrite ?task_rename_aworklist_invol, ?task_rename_typ_invol in HS' by exact I
  end.

Local Ltac task_rename_binder f I L :=
  intros y Fy;
  match goal with
  | IH : forall X, X `notin` L -> a_wl_red (task_rename_aworklist f _) |- _ =>
      let H := fresh "Renamed" in
      pose proof (IH (f y) (task_notin_image f I L y Fy)) as H;
      task_rename_normalize H; exact H
  end.

Local Ltac task_rename_three f I L :=
  intros y Fy u Fu v Fv;
  let E := fresh "FreshU" in let F := fresh "FreshV" in
  assert (E : f u `notin` union L (singleton (f y))) by (task_fresh_transport f I);
  assert (F : f v `notin` union (union L (singleton (f y))) (singleton (f u)))
    by (task_fresh_transport f I);
  let H := fresh "Renamed" in
  first [
    match goal with
    | IH : forall x, x `notin` L -> _ |- _ =>
      pose proof (IH (f y) (task_notin_image f I L y Fy) (f u) E (f v) ltac:(fsetdec)) as H;
      task_rename_normalize H; exact H
    end
  | intros P K HS; task_transport_assumption f I;
    match goal with
    | IH : forall x, x `notin` L -> _ |- _ =>
      pose proof (IH (f y) (task_notin_image f I L y Fy) (f u) E (f v) ltac:(fsetdec)
                    (task_rename_aworklist f P) (task_rename_aworklist f K) ltac:(eassumption)) as H;
      task_rename_normalize H; exact H
    end].

Local Ltac task_rename_two_substs f I L :=
  intros y Fy u Fu P K HS;
  let E := fresh "FreshU" in
  assert (E : f u `notin` union L (singleton (f y))) by (task_fresh_transport f I);
  task_transport_assumption f I;
  match goal with
  | IH : forall x, x `notin` L -> _ |- _ =>
      let H := fresh "Renamed" in
      pose proof (IH (f y) (task_notin_image f I L y Fy) (f u) E
                    (task_rename_aworklist f P) (task_rename_aworklist f K) ltac:(eassumption)) as H;
      task_rename_normalize H; exact H
  end.

Local Ltac task_bind_rename f :=
  match goal with H : binds ?X ?b (awl_to_aenv ?G) |- _ =>
    exact (task_rename_binds f G X b H)
  end.

Local Ltac task_guard_rename f I :=
  first [task_bind_rename f
  | match goal with H : a_mono_typ (awl_to_aenv ?G) ?A -> False |- _ =>
      exact (task_rename_no_mono f I G A H)
    end
  | eauto using task_rename_wneq].

Lemma task_rename_red f (I : task_involution f) G :
  a_wl_red G -> a_wl_red (task_rename_aworklist f G).
Proof.
  induction 1; simpl.
  - apply a_wl_red__empty; assumption || idtac.
  - apply a_wl_red__gc_var; assumption || idtac.
  - apply a_wl_red__sub_top; assumption || idtac.
  - apply a_wl_red__sub_bot; assumption || idtac.
  - apply a_wl_red__sub_unit; assumption || idtac.
  - apply a_wl_red__sub_tvar; assumption || idtac.
  - apply a_wl_red__subarrow; assumption || idtac.
  - eapply a_wl_red__sub_alll with (L := task_image f L);
      try solve [task_guard_rename f I].
    task_rename_binder f I L.
  - eapply a_wl_red__sub_all with (L := task_image f L);
      try solve [task_guard_rename f I].
    task_rename_binder f I L.
  - eapply a_wl_red__sub_arrow1 with (L := task_image f L);
      try solve [task_guard_rename f I].
    task_rename_two_substs f I L.
  - eapply a_wl_red__sub_arrow2 with (L := task_image f L);
      try solve [task_guard_rename f I].
    task_rename_two_substs f I L.
  - eapply a_wl_red__sub_etvarmono1.
    + task_bind_rename f.
    + eapply task_rename_mono; eassumption.
    + now rewrite task_rename_ftvar by exact I.
    + eapply task_rename_awl_subst; eassumption.
    + match goal with H : a_wl_red (task_rename_aworklist f _) |- _ =>
        task_rename_normalize H; exact H
      end.
  - eapply a_wl_red__sub_etvarmono2.
    + task_bind_rename f.
    + eapply task_rename_mono; eassumption.
    + now rewrite task_rename_ftvar by exact I.
    + eapply task_rename_awl_subst; eassumption.
    + match goal with H : a_wl_red (task_rename_aworklist f _) |- _ =>
        task_rename_normalize H; exact H
      end.
  - apply a_wl_red__sub_intersection1; assumption || idtac.
  - apply a_wl_red__sub_intersection2; assumption || idtac.
  - apply a_wl_red__sub_intersection3; assumption || idtac.
  - apply a_wl_red__sub_union1; assumption || idtac.
  - apply a_wl_red__sub_union2; assumption || idtac.
  - apply a_wl_red__sub_union3; assumption || idtac.
  - apply a_wl_red__chk_sub; assumption || idtac.
  - eapply a_wl_red__chk_absarrow with (L := task_image f L);
      try solve [task_guard_rename f I].
    task_rename_binder f I L.
  - eapply a_wl_red__chk_absetvar with (L := task_image f L);
      try solve [task_guard_rename f I].
    task_rename_three f I L.
  - eapply a_wl_red__chk_abstop with (L := task_image f L);
      try solve [task_guard_rename f I].
    task_rename_binder f I L.
  - apply a_wl_red__chk_inter; assumption || idtac.
  - apply a_wl_red__chk_union1; assumption || idtac.
  - apply a_wl_red__chk_union2; assumption || idtac.
  - eapply a_wl_red__inf_var; [task_bind_rename f|eassumption].
  - apply a_wl_red__inf_anno; assumption || idtac.
  - eapply a_wl_red__inf_tabs with (L := task_image f L);
      try solve [task_guard_rename f I].
    task_rename_binder f I L.
  - eapply a_wl_red__inf_abs_mono with (L := task_image f L);
      try solve [task_guard_rename f I].
    task_rename_three f I L.
  - apply a_wl_red__inf_unit; assumption || idtac.
  - apply a_wl_red__inf_app; assumption || idtac.
  - apply a_wl_red__infapp; assumption || idtac.
  - apply a_wl_red__infabs_arr; assumption || idtac.
  - apply a_wl_red__infabs_bot; assumption || idtac.
  - eapply a_wl_red__infabs_all with (L := task_image f L);
      try solve [task_guard_rename f I].
    task_rename_binder f I L.
  - apply a_wl_red__infabs_inter1; assumption || idtac.
  - apply a_wl_red__infabs_inter2; assumption || idtac.
  - apply a_wl_red__infabs_union; assumption || idtac.
  - apply a_wl_red__infabsunion; assumption || idtac.
  - apply a_wl_red__unioninfabs; assumption || idtac.
  - eapply a_wl_red__infabs_etvar with (L := task_image f L);
      try solve [task_guard_rename f I].
    task_rename_two_substs f I L.
  - apply a_wl_red__inf_tapp; assumption || idtac.
  - apply a_wl_red__inftapp_all.
    match goal with H : a_wl_red (task_rename_aworklist f _) |- _ =>
      task_rename_normalize H; exact H
    end.
  - apply a_wl_red__inftapp_bot; assumption || idtac.
  - apply a_wl_red__inftapp_inter1; assumption || idtac.
  - apply a_wl_red__inftapp_inter2; assumption || idtac.
  - apply a_wl_red__inftapp_union; assumption || idtac.
  - apply a_wl_red__inftappunion; assumption || idtac.
  - apply a_wl_red__unioninftapp; assumption || idtac.
  - eapply a_wl_red__applys; [eapply task_rename_apply_s; eassumption|eassumption].
  - eapply a_wl_red__applyd; [eapply task_rename_apply_d; eassumption|eassumption].
Qed.

Lemma task_in_add x y S : x `in` add y S <-> x = y \/ x `in` S.
Proof. fsetdec. Qed.

Lemma task_in_union x A B : x `in` union A B <-> x `in` A \/ x `in` B.
Proof. fsetdec. Qed.

Lemma task_in_singleton x y : x `in` singleton y <-> x = y.
Proof. fsetdec. Qed.

Local Ltac task_atomic :=
  repeat progress (rewrite ?task_in_add, ?task_in_union, ?task_in_singleton in *);
  intuition congruence.

(* Choose names outside the support of the whole worklist. A disjoint
   intermediate tuple lets each swap fix the other two coordinates. *)
Definition task_fresh3 S (a b c : atom) :=
  a `notin` S /\ b `notin` add a S /\ c `notin` add b (add a S).

Lemma task_pick3 S : sig (fun t : atom * atom * atom => let '(a,b,c) := t in task_fresh3 S a b c).
Proof.
  destruct (atom_fresh S) as [a Fa].
  destruct (atom_fresh (add a S)) as [b Fb].
  destruct (atom_fresh (add b (add a S))) as [c Fc].
  exists (a,b,c). repeat split; assumption.
Defined.

Definition task_stable S (P : atom -> atom -> atom -> Prop) :=
  forall f, task_involution f -> (forall x, x `in` S -> f x = x) ->
    forall a b c, P a b c -> P (f a) (f b) (f c).

Lemma task_stable_disjoint S P a b c u v w :
  task_stable S P -> task_fresh3 S a b c ->
  task_fresh3 (add c (add b (add a S))) u v w ->
  P a b c -> P u v w.
Proof.
  intros Stable [Fa [Fb Fc]] [Fu [Fv Fw]] H.
  assert (FS : forall p q, p `notin` S -> q `notin` S ->
               forall x, x `in` S -> task_swap p q x = x).
  { intros; apply task_swap_fixed; task_atomic. }
  pose proof (Stable (task_swap a u) (task_swap_involution _ _)
      (FS a u Fa ltac:(task_atomic)) a b c H) as H1.
  rewrite task_swap_left in H1.
  repeat (rewrite task_swap_fixed in H1 by (task_atomic)).
  pose proof (Stable (task_swap b v) (task_swap_involution _ _)
      (FS b v ltac:(task_atomic) ltac:(task_atomic)) u b c H1) as H2.
  rewrite task_swap_left in H2.
  repeat (rewrite task_swap_fixed in H2 by (task_atomic)).
  pose proof (Stable (task_swap c w) (task_swap_involution _ _)
      (FS c w ltac:(task_atomic) ltac:(task_atomic)) u v c H2) as H3.
  rewrite task_swap_left in H3.
  repeat (rewrite task_swap_fixed in H3 by (task_atomic)).
  exact H3.
Qed.

Lemma task_stable_fresh S P a b c u v w :
  task_stable S P -> task_fresh3 S a b c -> task_fresh3 S u v w ->
  P a b c -> P u v w.
Proof.
  intros Stable F F' H.
  destruct (task_pick3 (add w (add v (add u (add c (add b (add a S)))))))
    as [ [ [x y] z] [Fx [Fy Fz]]].
  pose proof (task_stable_disjoint S P a b c x y z Stable F
      ltac:(repeat split; task_atomic) H) as H'.
  apply (task_stable_disjoint S P x y z u v w Stable).
  - repeat split; task_atomic.
  - destruct F' as [? [? ?]]. repeat split; task_atomic.
  - exact H'.
Qed.

Lemma task_stable_intro S P a b c :
  task_stable S P -> task_fresh3 S a b c -> P a b c ->
  forall u v w, task_fresh3 S u v w -> P u v w.
Proof. intros Stable F H u v w F'. exact (task_stable_fresh S P a b c u v w Stable F F' H). Qed.

Lemma task_stable_elim S P a b c :
  task_stable S P -> task_fresh3 S a b c ->
  (exists L, forall u v w, task_fresh3 L u v w -> P u v w) -> P a b c.
Proof.
  intros Stable F [L H].
  destruct (task_pick3 (union S L)) as [ [ [u v] w] [Fu [Fv Fw]]].
  eapply (task_stable_fresh S P u v w a b c); [exact Stable| |exact F|apply H];
    repeat split; task_atomic.
Qed.

Definition task_names_state R G := union R (task_names_aworklist G).

Lemma task_names_dom G : dom (awl_to_aenv G) [<=] task_names_aworklist G.
Proof. induction G; simpl in *; fsetdec. Qed.

Definition task_abind_eq : forall a b : abind, sumbool (a = b) (a <> b).
Proof. decide equality; decide equality; try apply Nat.eq_dec; apply task_eq. Defined.

Definition task_binding_dec G x b : sumbool (binds x b (awl_to_aenv G)) (~ binds x b (awl_to_aenv G)) :=
  binds_dec _ x b _ task_abind_eq.

Fixpoint task_mono_dec G A : sumbool (a_mono_typ (awl_to_aenv G) A) (~ a_mono_typ (awl_to_aenv G) A).
Proof.
  destruct A; try solve [constructor; constructor | right; inversion 1].
  - destruct (task_binding_dec G X abind_tvar_empty), (task_binding_dec G X abind_etvar_empty);
      first [left; solve [eauto using a_mono_typ] | right; inversion 1; contradiction].
  - destruct (task_mono_dec G A1), (task_mono_dec G A2);
      first [left; solve [eauto using a_mono_typ] | right; inversion 1; contradiction].
Defined.

Fixpoint task_closed (k : nat) (A : typ) : bool :=
  match A with
  | typ_var_b n => Nat.ltb n k
  | typ_all A => task_closed (S k) A
  | typ_arrow A B | typ_union A B | typ_intersection A B =>
      andb (task_closed k A) (task_closed k B)
  | _ => true
  end.

Lemma task_closed_open A : forall d k x, k <= d ->
  task_closed d (open_typ_wrt_typ_rec k (typ_var_f x) A) = task_closed (S d) A.
Proof.
  induction A; intros; simpl; try congruence;
    try solve [rewrite IHA by lia; reflexivity];
    try solve [rewrite IHA1, IHA2 by lia; reflexivity].
  destruct (lt_eq_lt_dec n k) as [ [E | E] | E]; simpl.
  - change (Nat.ltb n d = Nat.ltb n (S d)).
    assert (E1 : Nat.ltb n d = true) by (apply Nat.ltb_lt; lia).
    assert (E2 : Nat.ltb n (S d) = true) by (apply Nat.ltb_lt; lia).
    congruence.
  - symmetry. apply Nat.ltb_lt; lia.
  - change (Nat.ltb (n-1) d = Nat.ltb n (S d)).
    destruct (Nat.ltb (n-1) d) eqn:E1, (Nat.ltb n (S d)) eqn:E2;
      try reflexivity; apply Nat.ltb_ge in E1 || apply Nat.ltb_lt in E1;
      apply Nat.ltb_ge in E2 || apply Nat.ltb_lt in E2; lia.
Qed.

Lemma task_lc_closed A : lc_typ A -> task_closed 0 A = true.
Proof.
  induction 1; simpl; try congruence; try solve [now rewrite IHlc_typ1, IHlc_typ2].
  destruct (atom_fresh empty) as [X _].
  match goal with H : forall x, task_closed 0 _ = true |- _ => specialize (H X);
      unfold open_typ_wrt_typ in H; rewrite task_closed_open in H by lia; exact H end.
Qed.

Lemma task_size_open A : forall k x,
  size_typ (open_typ_wrt_typ_rec k (typ_var_f x) A) = size_typ A.
Proof. induction A; intros; simpl; try congruence; destruct (lt_eq_lt_dec n k) as [ [] | ]; reflexivity. Qed.

Lemma task_closed_lc A : task_closed 0 A = true -> lc_typ A.
Proof.
  induction A using (well_founded_induction (well_founded_ltof _ size_typ)).
  destruct A; simpl; intro E; try discriminate; try solve [constructor].
  all: try solve [apply Bool.andb_true_iff in E as [E1 E2]; constructor; apply H; first [unfold ltof; simpl; lia|assumption]].
  apply lc_typ_all; intro X; apply H.
  - unfold ltof, open_typ_wrt_typ. rewrite task_size_open. simpl; lia.
  - unfold open_typ_wrt_typ. now rewrite task_closed_open by lia.
Qed.

Definition task_lc_dec A : sumbool (lc_typ A) (~ lc_typ A).
Proof.
  destruct (task_closed 0 A) eqn:E.
  - left; now apply task_closed_lc.
  - right; intro H; apply task_lc_closed in H; congruence.
Defined.

Fixpoint task_wneq_dec G A : sumbool (a_wneq_all (awl_to_aenv G) A) (~ a_wneq_all (awl_to_aenv G) A).
Proof.
  destruct A; try solve [constructor; constructor | right; inversion 1].
  - destruct (task_binding_dec G X abind_tvar_empty), (task_binding_dec G X abind_etvar_empty);
      first [left; solve [eauto using a_wneq_all] | right; inversion 1; contradiction].
  - destruct (task_lc_dec A1), (task_lc_dec A2);
      first [left; solve [eauto using a_wneq_all] | right; inversion 1; contradiction].
  - destruct (task_lc_dec A1), (task_lc_dec A2), (task_wneq_dec G A1), (task_wneq_dec G A2);
      first [left; solve [eauto using a_wneq_all] | right; inversion 1; contradiction].
  - destruct (task_wneq_dec G A1), (task_wneq_dec G A2);
      first [left; solve [eauto using a_wneq_all] | right; inversion 1; contradiction].
Defined.

Definition task_solution G X A :=
  option_map (fun '(B,M,K) =>
    awl_app (subst_typ_in_aworklist A X K) (awl_app M B)) (task_split G X A).

Lemma task_solution_spec G X A T :
  uniq (awl_to_aenv G) ->
  (task_solution G X A = Some T <->
    exists P K, aworklist_subst G X A P K /\
                T = awl_app (subst_typ_in_aworklist A X K) P).
Proof.
  intros U; split.
  - unfold task_solution.
    destruct (task_split G X A) as [ [ [B M] K]|] eqn:E; try discriminate.
    inversion 1; subst. exists (awl_app M B), K.
    split; [eapply task_split_sound; eassumption|reflexivity].
  - intros [P [K [H ->]]].
    destruct (task_split_complete _ _ _ _ _ H U) as [B [M [E ->]]].
    unfold task_solution. now rewrite E.
Qed.

Definition task_new_holes G a b :=
  aworklist_cons_var (aworklist_cons_var G a abind_etvar_empty) b abind_etvar_empty.
Definition task_arrow a b := typ_arrow (typ_var_f a) (typ_var_f b).

Lemma task_solution_red G X A (F : aworklist -> aworklist) :
  uniq (awl_to_aenv G) ->
  a_wl_red (match task_solution G X A with Some T => F T | None => aworklist_empty end) <->
  (forall P K, aworklist_subst G X A P K ->
    a_wl_red (F (awl_app (subst_typ_in_aworklist A X K) P))).
Proof.
  intro U; destruct (task_solution G X A) as [T|] eqn:E; split.
  - intros H P K S.
    assert (task_solution G X A = Some (awl_app (subst_typ_in_aworklist A X K) P))
      by (apply task_solution_spec; eauto).
    congruence.
  - intros H. apply task_solution_spec in E as [P [K [S ->]]]; auto.
  - intros _ P K S.
    assert (task_solution G X A = Some (awl_app (subst_typ_in_aworklist A X K) P))
      by (apply task_solution_spec; eauto).
    congruence.
  - intros; constructor.
Qed.

Lemma task_subst_top_work G w X A P K :
  aworklist_subst (aworklist_cons_work G w) X A P K <->
  exists J, K = aworklist_cons_work J w /\ aworklist_subst G X A P J.
Proof.
  split; [inversion 1; eauto|intros [J [ -> H]]; now constructor].
Qed.

Lemma task_subst_top_term G x T X A P K :
  aworklist_subst (aworklist_cons_var G x (abind_var_typ T)) X A P K <->
  exists J, K = aworklist_cons_var J x (abind_var_typ T) /\ aworklist_subst G X A P J.
Proof.
  split; [inversion 1; eauto|intros [J [ -> H]]; now constructor].
Qed.

Lemma task_red_arrow G A1 A2 B1 B2 :
  a_wl_red (aworklist_cons_work G (work_sub (typ_arrow A1 A2) (typ_arrow B1 B2))) <->
  a_wl_red (aworklist_cons_work (aworklist_cons_work G (work_sub B1 A1)) (work_sub A2 B2)).
Proof. split; [inversion 1; assumption|apply a_wl_red__subarrow]. Qed.

Lemma task_red_infabs_arrow G A B cd :
  a_wl_red (aworklist_cons_work G (work_infabs (typ_arrow A B) cd)) <->
  a_wl_red (aworklist_cons_work G (work_applyd cd A B)).
Proof. split; [inversion 1; assumption|apply a_wl_red__infabs_arr]. Qed.

Lemma task_subst_same_var X A : subst_typ_in_typ A X (typ_var_f X) = A.
Proof. simpl; match goal with |- context [if ?t then _ else _] => destruct t; congruence end. Qed.

Lemma task_subst_other_var X Y A : Y <> X -> subst_typ_in_typ A X (typ_var_f Y) = typ_var_f Y.
Proof. simpl; match goal with |- context [if ?t then _ else _] => destruct t; congruence end. Qed.

Definition task_apply_s cs A :=
  match cs with
  | conts_infabs cd => work_infabs A cd
  | conts_inftapp B cs => work_inftapp A B cs
  | conts_inftappunion A2 B cs => work_inftappunion A A2 B cs
  | conts_unioninftapp B cs => work_unioninftapp B A cs
  | conts_sub B => work_sub A B
  end.

Definition task_apply_d cd A B :=
  match cd with
  | contd_infabsunion C cd => work_infabsunion A B C cd
  | contd_infapp e cs => work_infapp A B e cs
  | contd_unioninfabs C D cd => work_unioninfabs C D A B cd
  end.

Lemma task_apply_s_spec cs A w : apply_conts cs A w <-> w = task_apply_s cs A.
Proof. split; [destruct 1; reflexivity|intros ->; destruct cs; constructor]. Qed.

Lemma task_apply_d_spec cd A B w : apply_contd cd A B w <-> w = task_apply_d cd A B.
Proof. split; [destruct 1; reflexivity|intros ->; destruct cd; constructor]. Qed.

Fixpoint task_env_types (E : aenv) : atoms :=
  match E with
  | nil => empty
  | (x, abind_var_typ _) :: E => task_env_types E
  | (x, _) :: E => add x (task_env_types E)
  end.

Lemma task_type_dom_env G : task_type_dom G = task_env_types (awl_to_aenv G).
Proof. induction G; simpl; try destruct ab; simpl; congruence. Qed.

Lemma task_type_dom_app A B :
  task_type_dom (awl_app A B) [=] union (task_type_dom A) (task_type_dom B).
Proof. induction A; simpl; try destruct ab; simpl in *; fsetdec. Qed.

Lemma task_ft_open A : forall k X,
  ftvar_in_typ A [<=] ftvar_in_typ (open_typ_wrt_typ_rec k (typ_var_f X) A) /\
  ftvar_in_typ (open_typ_wrt_typ_rec k (typ_var_f X) A) [<=] add X (ftvar_in_typ A).
Proof.
  induction A; intros; simpl; try solve [specialize (IHA k X); intuition fsetdec];
    try solve [specialize (IHA (S k) X); intuition fsetdec];
    try (specialize (IHA1 k X); specialize (IHA2 k X));
    try solve [intuition fsetdec].
  destruct (lt_eq_lt_dec n k) as [ [] | ]; simpl; split; fsetdec.
Qed.

Lemma task_ft_exp_typ_open e : forall k X,
  ftvar_in_exp e [<=] ftvar_in_exp (open_exp_wrt_typ_rec k (typ_var_f X) e) /\
  ftvar_in_exp (open_exp_wrt_typ_rec k (typ_var_f X) e) [<=] add X (ftvar_in_exp e).
Proof.
  induction e; intros; simpl; try solve [specialize (IHe k X); intuition fsetdec];
    try solve [specialize (IHe (S k) X); intuition fsetdec];
    try (specialize (IHe k X));
    try (specialize (IHe1 k X); specialize (IHe2 k X));
    try match goal with A : typ |- _ => pose proof (task_ft_open A k X) end;
    intuition fsetdec.
Qed.

Lemma task_ft_exp_exp_open e : forall k x,
  ftvar_in_exp (open_exp_wrt_exp_rec k (exp_var_f x) e) [=] ftvar_in_exp e.
Proof.
  induction e; intros; simpl; try solve [specialize (IHe k x); fsetdec];
    try solve [specialize (IHe (S k) x); fsetdec];
    try (specialize (IHe1 k x); specialize (IHe2 k x)); try solve [fsetdec].
  destruct (lt_eq_lt_dec n k) as [ [] | ]; simpl; fsetdec.
Qed.

Lemma task_env_types_binds E X b :
  binds X b E -> (forall T, b <> abind_var_typ T) -> X `in` task_env_types E.
Proof.
  induction E as [|[Y B] E IH]; rewrite task_binds; simpl; try tauto.
  intros [EQ|F] H.
  - inversion EQ; subst; destruct b; simpl; try fsetdec. exfalso; eapply H; reflexivity.
  - specialize (IH F H). destruct B; simpl in *; fsetdec.
Qed.

Lemma task_wf_type_scope E A : a_wf_typ E A -> ftvar_in_typ A [<=] task_env_types E.
Proof.
  induction 1; simpl; try solve [fsetdec].
  all: try solve [pose proof (task_env_types_binds _ _ _ H ltac:(discriminate)); fsetdec].
  destruct (atom_fresh (union L (ftvar_in_typ A))) as [X F].
  match goal with IH : forall X, X `notin` L -> _ [<=] _ |- _ =>
    specialize (IH X ltac:(fsetdec))
  end.
  unfold open_typ_wrt_typ in *; simpl in *.
  destruct (task_ft_open A 0 X). fsetdec.
Qed.

Lemma task_wf_exp_scope E e : a_wf_exp E e -> ftvar_in_exp e [<=] task_env_types E.
Proof.
  induction 1; simpl in *; try solve [fsetdec].
  - destruct (atom_fresh L) as [x F].
    match goal with IH : forall x, x `notin` L -> _ [<=] _ |- _ => specialize (IH x F) end.
    unfold open_exp_wrt_exp in *; simpl in *.
    pose proof (task_ft_exp_exp_open e 0 x). fsetdec.
  - destruct (atom_fresh (union L (union (ftvar_in_exp e) (ftvar_in_typ A)))) as [X F].
    match goal with IH : forall X, X `notin` L -> _ [<=] _ |- _ =>
      specialize (IH X ltac:(fsetdec))
    end.
    unfold open_exp_wrt_typ, open_typ_wrt_typ in *; simpl in *.
    destruct (task_ft_open A 0 X), (task_ft_exp_typ_open e 0 X); fsetdec.
  - pose proof (task_wf_type_scope _ _ H); fsetdec.
  - pose proof (task_wf_type_scope _ _ H); fsetdec.
Qed.

Scheme task_wf_conts_ind := Induction for a_wf_conts Sort Prop
  with task_wf_contd_ind := Induction for a_wf_contd Sort Prop.
Combined Scheme task_wf_cont_ind from task_wf_conts_ind, task_wf_contd_ind.

Lemma task_wf_cont_scope :
  (forall E c, a_wf_conts E c -> ftvar_in_conts c [<=] task_env_types E) /\
  (forall E c, a_wf_contd E c -> ftvar_in_contd c [<=] task_env_types E).
Proof.
  apply task_wf_cont_ind; intros; simpl in *;
    repeat match goal with
    | H : a_wf_typ _ _ |- _ => apply task_wf_type_scope in H
    | H : a_wf_exp _ _ |- _ => apply task_wf_exp_scope in H
    end; simpl in *; fsetdec.
Qed.

Lemma task_wf_work_scope E w : a_wf_work E w -> ftvar_in_work w [<=] task_env_types E.
Proof.
  destruct task_wf_cont_scope as [HS HD].
  destruct 1; simpl in *;
    repeat match goal with
    | H : a_wf_typ _ _ |- _ => apply task_wf_type_scope in H
    | H : a_wf_exp _ _ |- _ => apply task_wf_exp_scope in H
    | H : a_wf_conts _ _ |- _ => apply HS in H
    | H : a_wf_contd _ _ |- _ => apply HD in H
    end; simpl in *; fsetdec.
Qed.

Lemma task_wf_twl_init G :
  a_wf_twl G -> uniq (awl_to_aenv G) /\ task_scoped empty G.
Proof.
  induction 1; simpl in *; intuition auto using uniq_cons, uniq_nil.
  all: rewrite task_type_dom_env;
    repeat match goal with
    | H : a_wf_typ _ _ |- _ => apply task_wf_type_scope in H
    | H : a_wf_work _ _ |- _ => apply task_wf_work_scope in H
    end; fsetdec.
Qed.

Lemma task_wf_wl_init G :
  a_wf_wl G -> uniq (awl_to_aenv G) /\ task_scoped empty G.
Proof.
  induction 1; simpl in *; eauto using task_wf_twl_init;
    intuition auto using uniq_cons, uniq_nil.
  all: rewrite task_type_dom_env;
    repeat match goal with H : a_wf_typ _ _ |- _ => apply task_wf_type_scope in H end; fsetdec.
Qed.

Lemma task_scoped_mono D E G :
  D [<=] E -> task_scoped D G -> task_scoped E G.
Proof. induction G; simpl in *; intuition fsetdec. Qed.

Lemma task_scoped_app D A B :
  task_scoped D (awl_app A B) <->
  task_scoped D B /\ task_scoped (union D (task_type_dom B)) A.
Proof.
  induction A; simpl; [tauto| |];
    rewrite IHA; pose proof (task_type_dom_app A B);
    intuition fsetdec.
Qed.

Lemma task_colors_app R A B :
  task_colors R (awl_app A B) <-> task_colors R A /\ task_colors R B.
Proof. induction A; simpl in *; tauto. Qed.

Lemma task_ft_subst_typ A X B :
  ftvar_in_typ (subst_typ_in_typ A X B) [<=]
    union (remove X (ftvar_in_typ B)) (ftvar_in_typ A).
Proof.
  induction B; simpl in *; try fsetdec.
  destruct (X0 == X); subst; simpl; fsetdec.
Qed.

Lemma task_ft_subst_exp A X e :
  ftvar_in_exp (subst_typ_in_exp A X e) [<=]
    union (remove X (ftvar_in_exp e)) (ftvar_in_typ A).
Proof.
  induction e; simpl in *; try match goal with B : typ |- _ => pose proof (task_ft_subst_typ A X B) end;
    fsetdec.
Qed.

Lemma task_ft_subst_cont A X :
  (forall c, ftvar_in_conts (subst_typ_in_conts A X c) [<=]
    union (remove X (ftvar_in_conts c)) (ftvar_in_typ A)) /\
  (forall c, ftvar_in_contd (subst_typ_in_contd A X c) [<=]
    union (remove X (ftvar_in_contd c)) (ftvar_in_typ A)).
Proof.
  apply task_cont_ind; intros; simpl;
    repeat match goal with
    | |- context [ftvar_in_typ (subst_typ_in_typ A X ?T)] =>
        tryif (match goal with H : ftvar_in_typ (subst_typ_in_typ A X T) [<=] _ |- _ => idtac end) then fail else pose proof (task_ft_subst_typ A X T)
    | |- context [ftvar_in_exp (subst_typ_in_exp A X ?e)] =>
        tryif (match goal with H : ftvar_in_exp (subst_typ_in_exp A X e) [<=] _ |- _ => idtac end) then fail else pose proof (task_ft_subst_exp A X e)
    end; simpl in *; fsetdec.
Qed.

Lemma task_ft_subst_work A X w :
  ftvar_in_work (subst_typ_in_work A X w) [<=]
    union (remove X (ftvar_in_work w)) (ftvar_in_typ A).
Proof.
  destruct (task_ft_subst_cont A X) as [HS HD].
  destruct w; simpl;
    repeat match goal with
    | |- context [ftvar_in_typ (subst_typ_in_typ A X ?T)] =>
        tryif (match goal with H : ftvar_in_typ (subst_typ_in_typ A X T) [<=] _ |- _ => idtac end) then fail else pose proof (task_ft_subst_typ A X T)
    | |- context [ftvar_in_exp (subst_typ_in_exp A X ?e)] =>
        tryif (match goal with H : ftvar_in_exp (subst_typ_in_exp A X e) [<=] _ |- _ => idtac end) then fail else pose proof (task_ft_subst_exp A X e)
    | |- context [ftvar_in_conts (subst_typ_in_conts A X ?c)] =>
        tryif (match goal with H : ftvar_in_conts (subst_typ_in_conts A X c) [<=] _ |- _ => idtac end) then fail else pose proof (HS c)
    | |- context [ftvar_in_contd (subst_typ_in_contd A X ?c)] =>
        tryif (match goal with H : ftvar_in_contd (subst_typ_in_contd A X c) [<=] _ |- _ => idtac end) then fail else pose proof (HD c)
    end; simpl in *; fsetdec.
Qed.

Fixpoint task_lookup G X : list typ :=
  match G with
  | aworklist_empty => nil
  | aworklist_cons_work G _ => task_lookup G X
  | aworklist_cons_var G Y (abind_var_typ A) =>
      if task_eq X Y then A :: task_lookup G X else task_lookup G X
  | aworklist_cons_var G _ _ => task_lookup G X
  end.

Lemma task_lookup_spec G X A :
  List.In A (task_lookup G X) <-> binds X (abind_var_typ A) (awl_to_aenv G).
Proof.
  induction G as [|G IH Y d|G IH w]; simpl; try apply IH; try tauto.
  rewrite task_binds in *. destruct d; simpl; try rewrite IH; try (intuition congruence).
  destruct (task_eq X Y); subst; simpl; rewrite ?IH, ?pair_equal_spec.
  - assert (E : abind_var_typ A0 = abind_var_typ A <-> A0 = A) by (split; congruence).
    rewrite E; tauto.
  - intuition congruence.
Qed.

(* The finite search uses one fresh tuple per worklist. For existential
   arrow instantiation it combines substitution with the ensuing
   arrow decomposition or continuation application. *)
Inductive task_step (a b c : atom) : aworklist -> aworklist -> Prop :=
  | task_step__gc_var : forall (G:aworklist) (X:atom) (d:abind),
      task_step a b c (aworklist_cons_var G X d) G
  | task_step__sub_top : forall (G:aworklist) (A:typ),
      task_step a b c (aworklist_cons_work G (work_sub A typ_top)) G
  | task_step__sub_bot : forall (G:aworklist) (A:typ),
      task_step a b c (aworklist_cons_work G (work_sub typ_bot A)) G
  | task_step__sub_unit : forall (G:aworklist),
      task_step a b c (aworklist_cons_work G (work_sub typ_unit typ_unit)) G
  | task_step__sub_tvar : forall (G:aworklist) (X:atom) (Y:atom),
      (X = Y) ->
      task_step a b c (aworklist_cons_work G (work_sub (typ_var_f X) (typ_var_f Y))) G
  | task_step__subarrow : forall (G:aworklist) (A:typ) (B:typ) (C:typ) (D:typ),
      task_step a b c (aworklist_cons_work G (work_sub (typ_arrow A B) (typ_arrow C D))) (aworklist_cons_work (aworklist_cons_work G (work_sub C A)) (work_sub B D))
  | task_step__sub_alll : forall (G:aworklist) (A:typ) (B:typ),
      (a_wneq_all (awl_to_aenv G) B) ->
      task_step a b c (aworklist_cons_work G (work_sub (typ_all A) B)) (aworklist_cons_work (aworklist_cons_var G a abind_etvar_empty) (work_sub (open_typ_wrt_typ A (typ_var_f a)) B))
  | task_step__sub_all : forall (G:aworklist) (A:typ) (B:typ),
      task_step a b c (aworklist_cons_work G (work_sub (typ_all A) (typ_all B))) (aworklist_cons_work (aworklist_cons_var G c abind_stvar_empty) (work_sub (open_typ_wrt_typ A (typ_var_f c)) (open_typ_wrt_typ B (typ_var_f c))))
  | task_step__sub_arrow1 : forall (G:aworklist) (X:atom) (A:typ) (B:typ),
      (binds X abind_etvar_empty (awl_to_aenv G)) ->
      (~ (a_mono_typ (awl_to_aenv G) (typ_arrow A B))) ->
      task_step a b c (aworklist_cons_work G (work_sub (typ_var_f X) (typ_arrow A B))) (match (task_solution (task_new_holes G a b) X (task_arrow a b)) with Some T => (aworklist_cons_work (aworklist_cons_work T (work_sub (subst_typ_in_typ (task_arrow a b) X A) (typ_var_f a))) (work_sub (typ_var_f b) (subst_typ_in_typ (task_arrow a b) X B))) | None => aworklist_empty end)
  | task_step__sub_arrow2 : forall (G:aworklist) (A:typ) (B:typ) (X:atom),
      (binds X abind_etvar_empty (awl_to_aenv G)) ->
      (~ (a_mono_typ (awl_to_aenv G) (typ_arrow A B))) ->
      task_step a b c (aworklist_cons_work G (work_sub (typ_arrow A B) (typ_var_f X))) (match (task_solution (task_new_holes G a b) X (task_arrow a b)) with Some T => (aworklist_cons_work (aworklist_cons_work T (work_sub (typ_var_f a) (subst_typ_in_typ (task_arrow a b) X A))) (work_sub (subst_typ_in_typ (task_arrow a b) X B) (typ_var_f b))) | None => aworklist_empty end)
  | task_step__sub_etvarmono1 : forall (G:aworklist) (A:typ) (X:atom) (T:aworklist),
      (binds X abind_etvar_empty (awl_to_aenv G)) ->
      (a_mono_typ (awl_to_aenv G) A) ->
      (X `notin` ftvar_in_typ A) ->
      (task_solution G X A = Some T) ->
      task_step a b c (aworklist_cons_work G (work_sub A (typ_var_f X))) T
  | task_step__sub_etvarmono2 : forall (G:aworklist) (X:atom) (A:typ) (T:aworklist),
      (binds X abind_etvar_empty (awl_to_aenv G)) ->
      (a_mono_typ (awl_to_aenv G) A) ->
      (X `notin` ftvar_in_typ A) ->
      (task_solution G X A = Some T) ->
      task_step a b c (aworklist_cons_work G (work_sub (typ_var_f X) A)) T
  | task_step__sub_intersection1 : forall (G:aworklist) (A:typ) (B:typ) (C:typ),
      task_step a b c (aworklist_cons_work G (work_sub A (typ_intersection B C))) (aworklist_cons_work (aworklist_cons_work G (work_sub A B)) (work_sub A C))
  | task_step__sub_intersection2 : forall (G:aworklist) (A:typ) (B:typ) (C:typ),
      task_step a b c (aworklist_cons_work G (work_sub (typ_intersection A B) C)) (aworklist_cons_work G (work_sub A C))
  | task_step__sub_intersection3 : forall (G:aworklist) (A:typ) (B:typ) (C:typ),
      task_step a b c (aworklist_cons_work G (work_sub (typ_intersection A B) C)) (aworklist_cons_work G (work_sub B C))
  | task_step__sub_union1 : forall (G:aworklist) (A:typ) (B:typ) (C:typ),
      task_step a b c (aworklist_cons_work G (work_sub A (typ_union B C))) (aworklist_cons_work G (work_sub A B))
  | task_step__sub_union2 : forall (G:aworklist) (A:typ) (B:typ) (C:typ),
      task_step a b c (aworklist_cons_work G (work_sub A (typ_union B C))) (aworklist_cons_work G (work_sub A C))
  | task_step__sub_union3 : forall (G:aworklist) (A:typ) (B:typ) (C:typ),
      task_step a b c (aworklist_cons_work G (work_sub (typ_union A B) C)) (aworklist_cons_work (aworklist_cons_work G (work_sub A C)) (work_sub B C))
  | task_step__chk_sub : forall (G:aworklist) (e:exp) (A:typ),
      task_step a b c (aworklist_cons_work G (work_check e A)) (aworklist_cons_work G (work_infer e (conts_sub A)))
  | task_step__chk_absarrow : forall (G:aworklist) (e:exp) (A:typ) (B:typ),
      task_step a b c (aworklist_cons_work G (work_check (exp_abs e) (typ_arrow A B))) (aworklist_cons_work (aworklist_cons_var G c (abind_var_typ A)) (work_check (open_exp_wrt_exp e (exp_var_f c)) B))
  | task_step__chk_absetvar : forall (G:aworklist) (e:exp) (X:atom),
      (binds X abind_etvar_empty (awl_to_aenv G)) ->
      task_step a b c (aworklist_cons_work G (work_check (exp_abs e) (typ_var_f X))) (match (task_solution (task_new_holes G a b) X (task_arrow a b)) with Some T => (aworklist_cons_work (aworklist_cons_var T c (abind_var_typ (typ_var_f a))) (work_check (subst_typ_in_exp (task_arrow a b) X (open_exp_wrt_exp e (exp_var_f c))) (typ_var_f b))) | None => aworklist_empty end)
  | task_step__chk_abstop : forall (G:aworklist) (e:exp),
      task_step a b c (aworklist_cons_work G (work_check (exp_abs e) typ_top)) (aworklist_cons_work (aworklist_cons_var G c (abind_var_typ typ_bot)) (work_check (open_exp_wrt_exp e (exp_var_f c)) typ_top))
  | task_step__chk_inter : forall (G:aworklist) (e:exp) (A:typ) (B:typ),
      task_step a b c (aworklist_cons_work G (work_check e (typ_intersection A B))) (aworklist_cons_work (aworklist_cons_work G (work_check e A)) (work_check e B))
  | task_step__chk_union1 : forall (G:aworklist) (e:exp) (A:typ) (B:typ),
      task_step a b c (aworklist_cons_work G (work_check e (typ_union A B))) (aworklist_cons_work G (work_check e A))
  | task_step__chk_union2 : forall (G:aworklist) (e:exp) (A:typ) (B:typ),
      task_step a b c (aworklist_cons_work G (work_check e (typ_union A B))) (aworklist_cons_work G (work_check e B))
  | task_step__inf_var : forall (G:aworklist) (X:atom) (cs:conts) (A:typ),
      (binds X (abind_var_typ A) (awl_to_aenv G)) ->
      task_step a b c (aworklist_cons_work G (work_infer (exp_var_f X) cs)) (aworklist_cons_work G (work_applys cs A))
  | task_step__inf_anno : forall (G:aworklist) (e:exp) (A:typ) (cs:conts),
      task_step a b c (aworklist_cons_work G (work_infer (exp_anno e A) cs)) (aworklist_cons_work (aworklist_cons_work G (work_applys cs A)) (work_check e A))
  | task_step__inf_tabs : forall (G:aworklist) (e:exp) (A:typ) (cs:conts),
      task_step a b c (aworklist_cons_work G (work_infer (exp_tabs (exp_anno e A)) cs)) (aworklist_cons_work (aworklist_cons_var (aworklist_cons_work G (work_applys cs (typ_all A))) a abind_tvar_empty) (work_check (open_exp_wrt_typ e (typ_var_f a)) (open_typ_wrt_typ A (typ_var_f a))))
  | task_step__inf_abs_mono : forall (G:aworklist) (e:exp) (cs:conts),
      task_step a b c (aworklist_cons_work G (work_infer (exp_abs e) cs)) (aworklist_cons_work (aworklist_cons_var (aworklist_cons_work (task_new_holes G a b) (work_applys cs (task_arrow a b))) c (abind_var_typ (typ_var_f a))) (work_check (open_exp_wrt_exp e (exp_var_f c)) (typ_var_f b)))
  | task_step__inf_unit : forall (G:aworklist) (cs:conts),
      task_step a b c (aworklist_cons_work G (work_infer exp_unit cs)) (aworklist_cons_work G (work_applys cs typ_unit))
  | task_step__inf_app : forall (G:aworklist) (e:exp) (f:exp) (cs:conts),
      task_step a b c (aworklist_cons_work G (work_infer (exp_app e f) cs)) (aworklist_cons_work G (work_infer e (conts_infabs (contd_infapp f cs))))
  | task_step__infapp : forall (G:aworklist) (A:typ) (B:typ) (e:exp) (cs:conts),
      task_step a b c (aworklist_cons_work G (work_infapp A B e cs)) (aworklist_cons_work (aworklist_cons_work G (work_applys cs B)) (work_check e A))
  | task_step__infabs_arr : forall (G:aworklist) (A:typ) (B:typ) (cd:contd),
      task_step a b c (aworklist_cons_work G (work_infabs (typ_arrow A B) cd)) (aworklist_cons_work G (work_applyd cd A B))
  | task_step__infabs_bot : forall (G:aworklist) (cd:contd),
      task_step a b c (aworklist_cons_work G (work_infabs typ_bot cd)) (aworklist_cons_work G (work_infabs (typ_arrow typ_top typ_bot) cd))
  | task_step__infabs_all : forall (G:aworklist) (A:typ) (cd:contd),
      task_step a b c (aworklist_cons_work G (work_infabs (typ_all A) cd)) (aworklist_cons_work (aworklist_cons_var G a abind_etvar_empty) (work_infabs (open_typ_wrt_typ A (typ_var_f a)) cd))
  | task_step__infabs_inter1 : forall (G:aworklist) (A:typ) (B:typ) (cd:contd),
      task_step a b c (aworklist_cons_work G (work_infabs (typ_intersection A B) cd)) (aworklist_cons_work G (work_infabs A cd))
  | task_step__infabs_inter2 : forall (G:aworklist) (A:typ) (B:typ) (cd:contd),
      task_step a b c (aworklist_cons_work G (work_infabs (typ_intersection A B) cd)) (aworklist_cons_work G (work_infabs B cd))
  | task_step__infabs_union : forall (G:aworklist) (A:typ) (B:typ) (cd:contd),
      task_step a b c (aworklist_cons_work G (work_infabs (typ_union A B) cd)) (aworklist_cons_work G (work_infabs A (contd_infabsunion B cd)))
  | task_step__infabsunion : forall (G:aworklist) (A:typ) (B:typ) (C:typ) (cd:contd),
      task_step a b c (aworklist_cons_work G (work_infabsunion A B C cd)) (aworklist_cons_work G (work_infabs C (contd_unioninfabs A B cd)))
  | task_step__unioninfabs : forall (G:aworklist) (A:typ) (B:typ) (C:typ) (D:typ) (cd:contd),
      task_step a b c (aworklist_cons_work G (work_unioninfabs A B C D cd)) (aworklist_cons_work G (work_applyd cd (typ_intersection A C) (typ_union B D)))
  | task_step__infabs_etvar : forall (G:aworklist) (X:atom) (cd:contd),
      (binds X abind_etvar_empty (awl_to_aenv G)) ->
      task_step a b c (aworklist_cons_work G (work_infabs (typ_var_f X) cd)) (match (task_solution (task_new_holes G a b) X (task_arrow a b)) with Some T => (aworklist_cons_work T (work_applyd (subst_typ_in_contd (task_arrow a b) X cd) (typ_var_f a) (typ_var_f b))) | None => aworklist_empty end)
  | task_step__inf_tapp : forall (G:aworklist) (e:exp) (A:typ) (cs:conts),
      task_step a b c (aworklist_cons_work G (work_infer (exp_tapp e A) cs)) (aworklist_cons_work G (work_infer e (conts_inftapp A cs)))
  | task_step__inftapp_all : forall (G:aworklist) (A:typ) (B:typ) (cs:conts),
      task_step a b c (aworklist_cons_work G (work_inftapp (typ_all A) B cs)) (aworklist_cons_work G (work_applys cs (open_typ_wrt_typ A B)))
  | task_step__inftapp_bot : forall (G:aworklist) (B:typ) (cs:conts),
      task_step a b c (aworklist_cons_work G (work_inftapp typ_bot B cs)) (aworklist_cons_work G (work_applys cs typ_bot))
  | task_step__inftapp_inter1 : forall (G:aworklist) (A:typ) (B:typ) (C:typ) (cs:conts),
      task_step a b c (aworklist_cons_work G (work_inftapp (typ_intersection A B) C cs)) (aworklist_cons_work G (work_inftapp A C cs))
  | task_step__inftapp_inter2 : forall (G:aworklist) (A:typ) (B:typ) (C:typ) (cs:conts),
      task_step a b c (aworklist_cons_work G (work_inftapp (typ_intersection A B) C cs)) (aworklist_cons_work G (work_inftapp B C cs))
  | task_step__inftapp_union : forall (G:aworklist) (A:typ) (B:typ) (C:typ) (cs:conts),
      task_step a b c (aworklist_cons_work G (work_inftapp (typ_union A B) C cs)) (aworklist_cons_work G (work_inftapp A C (conts_inftappunion B C cs)))
  | task_step__inftappunion : forall (G:aworklist) (A:typ) (B:typ) (C:typ) (cs:conts),
      task_step a b c (aworklist_cons_work G (work_inftappunion A B C cs)) (aworklist_cons_work G (work_inftapp B C (conts_unioninftapp A cs)))
  | task_step__unioninftapp : forall (G:aworklist) (A:typ) (B:typ) (cs:conts),
      task_step a b c (aworklist_cons_work G (work_unioninftapp A B cs)) (aworklist_cons_work G (work_applys cs (typ_union A B)))
  | task_step__applys : forall (G:aworklist) (cs:conts) (A:typ),
      task_step a b c (aworklist_cons_work G (work_applys cs A)) (aworklist_cons_work G (task_apply_s cs A))
  | task_step__applyd : forall (G:aworklist) (cd:contd) (A:typ) (B:typ),
      task_step a b c (aworklist_cons_work G (work_applyd cd A B)) (aworklist_cons_work G (task_apply_d cd A B)).

Definition task_list_gc_var (a b c : atom) (G : aworklist) : list aworklist :=
  match G with
  | aworklist_cons_var G X d => G :: nil
  | _ => nil
  end.

Definition task_list_sub_top (a b c : atom) (G : aworklist) : list aworklist :=
  match G with
  | aworklist_cons_work G (work_sub A typ_top) => G :: nil
  | _ => nil
  end.

Definition task_list_sub_bot (a b c : atom) (G : aworklist) : list aworklist :=
  match G with
  | aworklist_cons_work G (work_sub typ_bot A) => G :: nil
  | _ => nil
  end.

Definition task_list_sub_unit (a b c : atom) (G : aworklist) : list aworklist :=
  match G with
  | aworklist_cons_work G (work_sub typ_unit typ_unit) => G :: nil
  | _ => nil
  end.

Definition task_list_sub_tvar (a b c : atom) (G : aworklist) : list aworklist :=
  match G with
  | aworklist_cons_work G (work_sub (typ_var_f X) (typ_var_f Y)) => if task_eq X Y then G :: nil else nil
  | _ => nil
  end.

Definition task_list_subarrow (a b c : atom) (G : aworklist) : list aworklist :=
  match G with
  | aworklist_cons_work G (work_sub (typ_arrow A B) (typ_arrow C D)) => (aworklist_cons_work (aworklist_cons_work G (work_sub C A)) (work_sub B D)) :: nil
  | _ => nil
  end.

Definition task_list_sub_alll (a b c : atom) (G : aworklist) : list aworklist :=
  match G with
  | aworklist_cons_work G (work_sub (typ_all A) B) => if task_wneq_dec G B then (aworklist_cons_work (aworklist_cons_var G a abind_etvar_empty) (work_sub (open_typ_wrt_typ A (typ_var_f a)) B)) :: nil else nil
  | _ => nil
  end.

Definition task_list_sub_all (a b c : atom) (G : aworklist) : list aworklist :=
  match G with
  | aworklist_cons_work G (work_sub (typ_all A) (typ_all B)) => (aworklist_cons_work (aworklist_cons_var G c abind_stvar_empty) (work_sub (open_typ_wrt_typ A (typ_var_f c)) (open_typ_wrt_typ B (typ_var_f c)))) :: nil
  | _ => nil
  end.

Definition task_list_sub_arrow1 (a b c : atom) (G : aworklist) : list aworklist :=
  match G with
  | aworklist_cons_work G (work_sub (typ_var_f X) (typ_arrow A B)) => if task_binding_dec G X abind_etvar_empty then if task_mono_dec G (typ_arrow A B) then nil else (match (task_solution (task_new_holes G a b) X (task_arrow a b)) with Some T => (aworklist_cons_work (aworklist_cons_work T (work_sub (subst_typ_in_typ (task_arrow a b) X A) (typ_var_f a))) (work_sub (typ_var_f b) (subst_typ_in_typ (task_arrow a b) X B))) | None => aworklist_empty end) :: nil else nil
  | _ => nil
  end.

Definition task_list_sub_arrow2 (a b c : atom) (G : aworklist) : list aworklist :=
  match G with
  | aworklist_cons_work G (work_sub (typ_arrow A B) (typ_var_f X)) => if task_binding_dec G X abind_etvar_empty then if task_mono_dec G (typ_arrow A B) then nil else (match (task_solution (task_new_holes G a b) X (task_arrow a b)) with Some T => (aworklist_cons_work (aworklist_cons_work T (work_sub (typ_var_f a) (subst_typ_in_typ (task_arrow a b) X A))) (work_sub (subst_typ_in_typ (task_arrow a b) X B) (typ_var_f b))) | None => aworklist_empty end) :: nil else nil
  | _ => nil
  end.

Definition task_list_sub_etvarmono1 (a b c : atom) (G : aworklist) : list aworklist :=
  match G with
  | aworklist_cons_work G (work_sub A (typ_var_f X)) => if task_binding_dec G X abind_etvar_empty then if task_mono_dec G A then if AtomSetImpl.mem X (ftvar_in_typ A) then nil else match task_solution G X A with Some T => T :: nil | None => nil end else nil else nil
  | _ => nil
  end.

Definition task_list_sub_etvarmono2 (a b c : atom) (G : aworklist) : list aworklist :=
  match G with
  | aworklist_cons_work G (work_sub (typ_var_f X) A) => if task_binding_dec G X abind_etvar_empty then if task_mono_dec G A then if AtomSetImpl.mem X (ftvar_in_typ A) then nil else match task_solution G X A with Some T => T :: nil | None => nil end else nil else nil
  | _ => nil
  end.

Definition task_list_sub_intersection1 (a b c : atom) (G : aworklist) : list aworklist :=
  match G with
  | aworklist_cons_work G (work_sub A (typ_intersection B C)) => (aworklist_cons_work (aworklist_cons_work G (work_sub A B)) (work_sub A C)) :: nil
  | _ => nil
  end.

Definition task_list_sub_intersection2 (a b c : atom) (G : aworklist) : list aworklist :=
  match G with
  | aworklist_cons_work G (work_sub (typ_intersection A B) C) => (aworklist_cons_work G (work_sub A C)) :: nil
  | _ => nil
  end.

Definition task_list_sub_intersection3 (a b c : atom) (G : aworklist) : list aworklist :=
  match G with
  | aworklist_cons_work G (work_sub (typ_intersection A B) C) => (aworklist_cons_work G (work_sub B C)) :: nil
  | _ => nil
  end.

Definition task_list_sub_union1 (a b c : atom) (G : aworklist) : list aworklist :=
  match G with
  | aworklist_cons_work G (work_sub A (typ_union B C)) => (aworklist_cons_work G (work_sub A B)) :: nil
  | _ => nil
  end.

Definition task_list_sub_union2 (a b c : atom) (G : aworklist) : list aworklist :=
  match G with
  | aworklist_cons_work G (work_sub A (typ_union B C)) => (aworklist_cons_work G (work_sub A C)) :: nil
  | _ => nil
  end.

Definition task_list_sub_union3 (a b c : atom) (G : aworklist) : list aworklist :=
  match G with
  | aworklist_cons_work G (work_sub (typ_union A B) C) => (aworklist_cons_work (aworklist_cons_work G (work_sub A C)) (work_sub B C)) :: nil
  | _ => nil
  end.

Definition task_list_chk_sub (a b c : atom) (G : aworklist) : list aworklist :=
  match G with
  | aworklist_cons_work G (work_check e A) => (aworklist_cons_work G (work_infer e (conts_sub A))) :: nil
  | _ => nil
  end.

Definition task_list_chk_absarrow (a b c : atom) (G : aworklist) : list aworklist :=
  match G with
  | aworklist_cons_work G (work_check (exp_abs e) (typ_arrow A B)) => (aworklist_cons_work (aworklist_cons_var G c (abind_var_typ A)) (work_check (open_exp_wrt_exp e (exp_var_f c)) B)) :: nil
  | _ => nil
  end.

Definition task_list_chk_absetvar (a b c : atom) (G : aworklist) : list aworklist :=
  match G with
  | aworklist_cons_work G (work_check (exp_abs e) (typ_var_f X)) => if task_binding_dec G X abind_etvar_empty then (match (task_solution (task_new_holes G a b) X (task_arrow a b)) with Some T => (aworklist_cons_work (aworklist_cons_var T c (abind_var_typ (typ_var_f a))) (work_check (subst_typ_in_exp (task_arrow a b) X (open_exp_wrt_exp e (exp_var_f c))) (typ_var_f b))) | None => aworklist_empty end) :: nil else nil
  | _ => nil
  end.

Definition task_list_chk_abstop (a b c : atom) (G : aworklist) : list aworklist :=
  match G with
  | aworklist_cons_work G (work_check (exp_abs e) typ_top) => (aworklist_cons_work (aworklist_cons_var G c (abind_var_typ typ_bot)) (work_check (open_exp_wrt_exp e (exp_var_f c)) typ_top)) :: nil
  | _ => nil
  end.

Definition task_list_chk_inter (a b c : atom) (G : aworklist) : list aworklist :=
  match G with
  | aworklist_cons_work G (work_check e (typ_intersection A B)) => (aworklist_cons_work (aworklist_cons_work G (work_check e A)) (work_check e B)) :: nil
  | _ => nil
  end.

Definition task_list_chk_union1 (a b c : atom) (G : aworklist) : list aworklist :=
  match G with
  | aworklist_cons_work G (work_check e (typ_union A B)) => (aworklist_cons_work G (work_check e A)) :: nil
  | _ => nil
  end.

Definition task_list_chk_union2 (a b c : atom) (G : aworklist) : list aworklist :=
  match G with
  | aworklist_cons_work G (work_check e (typ_union A B)) => (aworklist_cons_work G (work_check e B)) :: nil
  | _ => nil
  end.

Definition task_list_inf_var (a b c : atom) (G : aworklist) : list aworklist :=
  match G with
  | aworklist_cons_work G (work_infer (exp_var_f X) cs) => List.map (fun A => (aworklist_cons_work G (work_applys cs A))) (task_lookup G X)
  | _ => nil
  end.

Definition task_list_inf_anno (a b c : atom) (G : aworklist) : list aworklist :=
  match G with
  | aworklist_cons_work G (work_infer (exp_anno e A) cs) => (aworklist_cons_work (aworklist_cons_work G (work_applys cs A)) (work_check e A)) :: nil
  | _ => nil
  end.

Definition task_list_inf_tabs (a b c : atom) (G : aworklist) : list aworklist :=
  match G with
  | aworklist_cons_work G (work_infer (exp_tabs (exp_anno e A)) cs) => (aworklist_cons_work (aworklist_cons_var (aworklist_cons_work G (work_applys cs (typ_all A))) a abind_tvar_empty) (work_check (open_exp_wrt_typ e (typ_var_f a)) (open_typ_wrt_typ A (typ_var_f a)))) :: nil
  | _ => nil
  end.

Definition task_list_inf_abs_mono (a b c : atom) (G : aworklist) : list aworklist :=
  match G with
  | aworklist_cons_work G (work_infer (exp_abs e) cs) => (aworklist_cons_work (aworklist_cons_var (aworklist_cons_work (task_new_holes G a b) (work_applys cs (task_arrow a b))) c (abind_var_typ (typ_var_f a))) (work_check (open_exp_wrt_exp e (exp_var_f c)) (typ_var_f b))) :: nil
  | _ => nil
  end.

Definition task_list_inf_unit (a b c : atom) (G : aworklist) : list aworklist :=
  match G with
  | aworklist_cons_work G (work_infer exp_unit cs) => (aworklist_cons_work G (work_applys cs typ_unit)) :: nil
  | _ => nil
  end.

Definition task_list_inf_app (a b c : atom) (G : aworklist) : list aworklist :=
  match G with
  | aworklist_cons_work G (work_infer (exp_app e f) cs) => (aworklist_cons_work G (work_infer e (conts_infabs (contd_infapp f cs)))) :: nil
  | _ => nil
  end.

Definition task_list_infapp (a b c : atom) (G : aworklist) : list aworklist :=
  match G with
  | aworklist_cons_work G (work_infapp A B e cs) => (aworklist_cons_work (aworklist_cons_work G (work_applys cs B)) (work_check e A)) :: nil
  | _ => nil
  end.

Definition task_list_infabs_arr (a b c : atom) (G : aworklist) : list aworklist :=
  match G with
  | aworklist_cons_work G (work_infabs (typ_arrow A B) cd) => (aworklist_cons_work G (work_applyd cd A B)) :: nil
  | _ => nil
  end.

Definition task_list_infabs_bot (a b c : atom) (G : aworklist) : list aworklist :=
  match G with
  | aworklist_cons_work G (work_infabs typ_bot cd) => (aworklist_cons_work G (work_infabs (typ_arrow typ_top typ_bot) cd)) :: nil
  | _ => nil
  end.

Definition task_list_infabs_all (a b c : atom) (G : aworklist) : list aworklist :=
  match G with
  | aworklist_cons_work G (work_infabs (typ_all A) cd) => (aworklist_cons_work (aworklist_cons_var G a abind_etvar_empty) (work_infabs (open_typ_wrt_typ A (typ_var_f a)) cd)) :: nil
  | _ => nil
  end.

Definition task_list_infabs_inter1 (a b c : atom) (G : aworklist) : list aworklist :=
  match G with
  | aworklist_cons_work G (work_infabs (typ_intersection A B) cd) => (aworklist_cons_work G (work_infabs A cd)) :: nil
  | _ => nil
  end.

Definition task_list_infabs_inter2 (a b c : atom) (G : aworklist) : list aworklist :=
  match G with
  | aworklist_cons_work G (work_infabs (typ_intersection A B) cd) => (aworklist_cons_work G (work_infabs B cd)) :: nil
  | _ => nil
  end.

Definition task_list_infabs_union (a b c : atom) (G : aworklist) : list aworklist :=
  match G with
  | aworklist_cons_work G (work_infabs (typ_union A B) cd) => (aworklist_cons_work G (work_infabs A (contd_infabsunion B cd))) :: nil
  | _ => nil
  end.

Definition task_list_infabsunion (a b c : atom) (G : aworklist) : list aworklist :=
  match G with
  | aworklist_cons_work G (work_infabsunion A B C cd) => (aworklist_cons_work G (work_infabs C (contd_unioninfabs A B cd))) :: nil
  | _ => nil
  end.

Definition task_list_unioninfabs (a b c : atom) (G : aworklist) : list aworklist :=
  match G with
  | aworklist_cons_work G (work_unioninfabs A B C D cd) => (aworklist_cons_work G (work_applyd cd (typ_intersection A C) (typ_union B D))) :: nil
  | _ => nil
  end.

Definition task_list_infabs_etvar (a b c : atom) (G : aworklist) : list aworklist :=
  match G with
  | aworklist_cons_work G (work_infabs (typ_var_f X) cd) => if task_binding_dec G X abind_etvar_empty then (match (task_solution (task_new_holes G a b) X (task_arrow a b)) with Some T => (aworklist_cons_work T (work_applyd (subst_typ_in_contd (task_arrow a b) X cd) (typ_var_f a) (typ_var_f b))) | None => aworklist_empty end) :: nil else nil
  | _ => nil
  end.

Definition task_list_inf_tapp (a b c : atom) (G : aworklist) : list aworklist :=
  match G with
  | aworklist_cons_work G (work_infer (exp_tapp e A) cs) => (aworklist_cons_work G (work_infer e (conts_inftapp A cs))) :: nil
  | _ => nil
  end.

Definition task_list_inftapp_all (a b c : atom) (G : aworklist) : list aworklist :=
  match G with
  | aworklist_cons_work G (work_inftapp (typ_all A) B cs) => (aworklist_cons_work G (work_applys cs (open_typ_wrt_typ A B))) :: nil
  | _ => nil
  end.

Definition task_list_inftapp_bot (a b c : atom) (G : aworklist) : list aworklist :=
  match G with
  | aworklist_cons_work G (work_inftapp typ_bot B cs) => (aworklist_cons_work G (work_applys cs typ_bot)) :: nil
  | _ => nil
  end.

Definition task_list_inftapp_inter1 (a b c : atom) (G : aworklist) : list aworklist :=
  match G with
  | aworklist_cons_work G (work_inftapp (typ_intersection A B) C cs) => (aworklist_cons_work G (work_inftapp A C cs)) :: nil
  | _ => nil
  end.

Definition task_list_inftapp_inter2 (a b c : atom) (G : aworklist) : list aworklist :=
  match G with
  | aworklist_cons_work G (work_inftapp (typ_intersection A B) C cs) => (aworklist_cons_work G (work_inftapp B C cs)) :: nil
  | _ => nil
  end.

Definition task_list_inftapp_union (a b c : atom) (G : aworklist) : list aworklist :=
  match G with
  | aworklist_cons_work G (work_inftapp (typ_union A B) C cs) => (aworklist_cons_work G (work_inftapp A C (conts_inftappunion B C cs))) :: nil
  | _ => nil
  end.

Definition task_list_inftappunion (a b c : atom) (G : aworklist) : list aworklist :=
  match G with
  | aworklist_cons_work G (work_inftappunion A B C cs) => (aworklist_cons_work G (work_inftapp B C (conts_unioninftapp A cs))) :: nil
  | _ => nil
  end.

Definition task_list_unioninftapp (a b c : atom) (G : aworklist) : list aworklist :=
  match G with
  | aworklist_cons_work G (work_unioninftapp A B cs) => (aworklist_cons_work G (work_applys cs (typ_union A B))) :: nil
  | _ => nil
  end.

Definition task_list_applys (a b c : atom) (G : aworklist) : list aworklist :=
  match G with
  | aworklist_cons_work G (work_applys cs A) => (aworklist_cons_work G (task_apply_s cs A)) :: nil
  | _ => nil
  end.

Definition task_list_applyd (a b c : atom) (G : aworklist) : list aworklist :=
  match G with
  | aworklist_cons_work G (work_applyd cd A B) => (aworklist_cons_work G (task_apply_d cd A B)) :: nil
  | _ => nil
  end.

(* Enumerate all applicable alternatives, including overlapping
   subtyping rules. A term lookup can contribute one successor per binding. *)
Definition task_successors a b c G : list aworklist :=
  List.concat (
    task_list_gc_var a b c G ::
    task_list_sub_top a b c G ::
    task_list_sub_bot a b c G ::
    task_list_sub_unit a b c G ::
    task_list_sub_tvar a b c G ::
    task_list_subarrow a b c G ::
    task_list_sub_alll a b c G ::
    task_list_sub_all a b c G ::
    task_list_sub_arrow1 a b c G ::
    task_list_sub_arrow2 a b c G ::
    task_list_sub_etvarmono1 a b c G ::
    task_list_sub_etvarmono2 a b c G ::
    task_list_sub_intersection1 a b c G ::
    task_list_sub_intersection2 a b c G ::
    task_list_sub_intersection3 a b c G ::
    task_list_sub_union1 a b c G ::
    task_list_sub_union2 a b c G ::
    task_list_sub_union3 a b c G ::
    task_list_chk_sub a b c G ::
    task_list_chk_absarrow a b c G ::
    task_list_chk_absetvar a b c G ::
    task_list_chk_abstop a b c G ::
    task_list_chk_inter a b c G ::
    task_list_chk_union1 a b c G ::
    task_list_chk_union2 a b c G ::
    task_list_inf_var a b c G ::
    task_list_inf_anno a b c G ::
    task_list_inf_tabs a b c G ::
    task_list_inf_abs_mono a b c G ::
    task_list_inf_unit a b c G ::
    task_list_inf_app a b c G ::
    task_list_infapp a b c G ::
    task_list_infabs_arr a b c G ::
    task_list_infabs_bot a b c G ::
    task_list_infabs_all a b c G ::
    task_list_infabs_inter1 a b c G ::
    task_list_infabs_inter2 a b c G ::
    task_list_infabs_union a b c G ::
    task_list_infabsunion a b c G ::
    task_list_unioninfabs a b c G ::
    task_list_infabs_etvar a b c G ::
    task_list_inf_tapp a b c G ::
    task_list_inftapp_all a b c G ::
    task_list_inftapp_bot a b c G ::
    task_list_inftapp_inter1 a b c G ::
    task_list_inftapp_inter2 a b c G ::
    task_list_inftapp_union a b c G ::
    task_list_inftappunion a b c G ::
    task_list_unioninftapp a b c G ::
    task_list_applys a b c G ::
    task_list_applyd a b c G :: nil).

Definition task_entry := (atom * abind + work)%type.

Fixpoint task_entries G : list task_entry :=
  match G with
  | aworklist_empty => nil
  | aworklist_cons_var G x b => inl (x,b) :: task_entries G
  | aworklist_cons_work G w => inr w :: task_entries G
  end.

Lemma task_entries_app G H : task_entries (awl_app G H) = task_entries G ++ task_entries H.
Proof. induction G; simpl; now try rewrite IHG. Qed.

Lemma task_split_perm G X A P K :
  aworklist_subst G X A P K ->
  Permutation (task_entries G) (inl (X,abind_etvar_empty) :: task_entries K ++ task_entries P).
Proof.
  induction 1; simpl; try reflexivity.
  all: try solve [eapply Permutation_trans; [apply perm_skip; eassumption|apply perm_swap]].
  eapply Permutation_trans; [|exact IHaworklist_subst].
  rewrite !task_entries_app; simpl.
  pose proof (Permutation_middle (task_entries Γ2 ++ [inl (X,abind_etvar_empty)])
                                  (task_entries Γ1) (inl (Y,abind_etvar_empty))) as P.
  rewrite <- !List.app_assoc in P. exact P.
Qed.

Definition task_entry_bindings (e : task_entry) : list (atom * abind) :=
  match e with inl b => [b] | inr _ => nil end.

Lemma task_entries_env G : flat_map task_entry_bindings (task_entries G) = awl_to_aenv G.
Proof. induction G; simpl; now try rewrite IHG. Qed.

Lemma task_split_perm_env G X A P K :
  aworklist_subst G X A P K ->
  Permutation (awl_to_aenv G) ((X,abind_etvar_empty) :: awl_to_aenv K ++ awl_to_aenv P).
Proof.
  intro H; pose proof (task_split_perm _ _ _ _ _ H) as E.
  apply (Permutation_flat_map task_entry_bindings) in E.
  rewrite !task_entries_env in E.
  simpl in E. now rewrite flat_map_app, !task_entries_env in E.
Qed.

Lemma task_dom_map x E : x `in` dom E <-> List.In x (List.map (@fst atom abind) E).
Proof.
  induction E as [|[a b] E IH]; simpl; [fsetdec|rewrite <- IH; fsetdec].
Qed.

Lemma task_uniq_nodup E : uniq E <-> NoDup (List.map (@fst atom abind) E).
Proof.
  induction E as [| [a b] E IH]; simpl.
  - split; constructor.
  - rewrite uniq_cons_iff, NoDup_cons_iff, IH, <- task_dom_map. tauto.
Qed.

Lemma task_perm_uniq (E F : aenv) : Permutation E F -> uniq E -> uniq F.
Proof.
  intros HP H. apply task_uniq_nodup in H. apply task_uniq_nodup.
  eapply Permutation_NoDup; [apply Permutation_map; exact HP|exact H].
Qed.

Lemma task_types_in_env E X :
  X `in` task_env_types E <->
    binds X abind_tvar_empty E \/ binds X abind_etvar_empty E \/ binds X abind_stvar_empty E.
Proof.
  induction E as [|[Y b] E IH].
  - simpl; rewrite !task_binds; simpl; fsetdec.
  - destruct b; rewrite !task_binds in *; simpl in *; rewrite ?task_in_add, IH;
      intuition congruence.
Qed.

Lemma task_env_after_subst A X G Y b :
  (b = abind_etvar_empty \/ b = abind_tvar_empty \/ b = abind_stvar_empty) ->
  binds Y b (awl_to_aenv (subst_typ_in_aworklist A X G)) <-> binds Y b (awl_to_aenv G).
Proof.
  intro E; destruct E as [ -> | [ -> |  ->]]; induction G as [|G IH Z d|G IH w];
    rewrite !task_binds in *; simpl; try tauto;
    destruct d; simpl; rewrite IH; intuition congruence.
Qed.

Lemma task_dom_after_subst A X G :
  dom (awl_to_aenv (subst_typ_in_aworklist A X G)) = dom (awl_to_aenv G).
Proof. induction G; simpl; congruence. Qed.

Lemma task_tdom_after_subst A X G :
  task_type_dom (subst_typ_in_aworklist A X G) = task_type_dom G.
Proof. induction G; simpl; try destruct ab; simpl; congruence. Qed.

Lemma task_uniq_after_subst A X G :
  uniq (awl_to_aenv G) -> uniq (awl_to_aenv (subst_typ_in_aworklist A X G)).
Proof.
  induction G; simpl; auto. rewrite !uniq_cons_iff, task_dom_after_subst. tauto.
Qed.

Lemma task_split_dom G X A P K :
  aworklist_subst G X A P K ->
  task_type_dom G [=] add X (task_type_dom (awl_app K P)).
Proof.
  intros H; pose proof (task_split_perm_env _ _ _ _ _ H) as E.
  rewrite !task_type_dom_env, task_app_env. intro Y.
  rewrite task_types_in_env, task_in_add, task_types_in_env.
  repeat rewrite task_binds.
  assert (Hperm : forall a, List.In a (awl_to_aenv G) <->
    List.In a ((X,abind_etvar_empty) :: awl_to_aenv K ++ awl_to_aenv P)).
  { intro; split; eauto using Permutation_in, Permutation_sym. }
  rewrite !Hperm. simpl. rewrite !pair_equal_spec. intuition congruence.
Qed.

Lemma task_solution_dom G X A T :
  uniq (awl_to_aenv G) -> task_solution G X A = Some T ->
  task_type_dom G [=] add X (task_type_dom T).
Proof.
  intros U E. apply task_solution_spec in E as [P [K [S ->]]]; auto.
  pose proof (task_split_dom _ _ _ _ _ S).
  pose proof (task_type_dom_app K P).
  pose proof (task_type_dom_app (subst_typ_in_aworklist A X K) P).
  rewrite task_tdom_after_subst in *. fsetdec.
Qed.

Lemma task_colors_binds R G :
  task_colors R G <->
  (forall X, binds X abind_stvar_empty (awl_to_aenv G) -> X `in` R) /\
  (forall X, binds X abind_tvar_empty (awl_to_aenv G) -> X `notin` R) /\
  (forall X, binds X abind_etvar_empty (awl_to_aenv G) -> X `notin` R).
Proof.
  induction G as [|G IH Y d|G IH w]; simpl.
  - split; [intros _; repeat split; intros X H; inversion H|tauto].
  - rewrite IH. clear IH. destruct d; unfold binds; simpl; firstorder congruence.
  - exact IH.
Qed.

Lemma task_solution_uniq_color R G X A T :
  uniq (awl_to_aenv G) -> task_colors R G -> task_solution G X A = Some T ->
  uniq (awl_to_aenv T) /\ task_colors R T.
Proof.
  intros U C E. apply task_solution_spec in E as [P [K [HS ->]]]; auto.
  pose proof (task_split_perm_env _ _ _ _ _ HS) as J.
  assert (V := task_perm_uniq _ _ J U).
  apply uniq_cons_1 in V. split.
  - rewrite task_app_env. apply uniq_app_iff in V as [U1 [U2 D]].
    apply uniq_app_4; auto using task_uniq_after_subst.
    unfold disjoint in *. now rewrite task_dom_after_subst.
  - assert (Keep : forall y b,
       (b = abind_etvar_empty \/ b = abind_tvar_empty \/ b = abind_stvar_empty) ->
       binds y b (awl_to_aenv (awl_app (subst_typ_in_aworklist A X K) P)) ->
       binds y b (awl_to_aenv G)).
    { intros y b HB H. rewrite task_app_env, binds_app_iff in H.
      rewrite task_env_after_subst in H by exact HB.
      apply task_binds; eapply Permutation_in; [apply Permutation_sym; exact J|].
      simpl; right; apply in_or_app. now rewrite !task_binds in H. }
    apply task_colors_binds in C as [CS [CT CE]].
    apply task_colors_binds; repeat split; intros y H.
    + apply CS, Keep; auto.
    + apply CT, Keep; auto.
    + apply CE, Keep; auto.
Qed.

Lemma task_subst_scope_rel G X A P K :
  aworklist_subst G X A P K ->
  task_scoped empty G ->
  ftvar_in_typ A [<=] task_type_dom G ->
  X `notin` ftvar_in_typ A ->
  task_scoped empty (awl_app (subst_typ_in_aworklist A X K) P).
Proof.
  intros HS. induction HS; intros Scoped F NX; simpl in *; try tauto.
  - destruct Scoped as [HG HB]. split.
    + apply IHHS; assumption.
    + pose proof (task_split_dom _ _ _ _ _ HS) as D.
      pose proof (task_type_dom_app Γ2 Γ1).
      pose proof (task_type_dom_app (subst_typ_in_aworklist A X Γ2) Γ1).
      rewrite task_tdom_after_subst in *.
      pose proof (task_ft_subst_typ A X B). fsetdec.
  - destruct Scoped as [HG HB]. split; [apply IHHS; [assumption|fsetdec|assumption]|fsetdec].
  - destruct Scoped as [HG HB]. split; [apply IHHS; [assumption|fsetdec|assumption]|fsetdec].
  - destruct Scoped as [HG HW]. split.
    + apply IHHS; assumption.
    + pose proof (task_split_dom _ _ _ _ _ HS) as D.
      pose proof (task_type_dom_app Γ2 Γ1).
      pose proof (task_type_dom_app (subst_typ_in_aworklist A X Γ2) Γ1).
      rewrite task_tdom_after_subst in *.
      pose proof (task_ft_subst_work A X w). fsetdec.
  - destruct Scoped as [HG HB]. split; [apply IHHS; [assumption|fsetdec|assumption]|fsetdec].
  - apply IHHS; [| |assumption].
    + destruct Scoped as [Scoped _].
      apply task_scoped_app in Scoped as [H1 H2].
      apply task_scoped_app; split.
      * simpl in *; intuition fsetdec.
      * eapply task_scoped_mono; [|exact H2]; simpl; fsetdec.
    + intros y HY. specialize (F y HY).
      pose proof (task_type_dom_app Γ2 (aworklist_cons_var Γ1 X abind_etvar_empty) y) as D1.
      pose proof (task_type_dom_app Γ2
        (aworklist_cons_var (aworklist_cons_var Γ1 Y abind_etvar_empty) X abind_etvar_empty) y) as D2.
      cbn [task_type_dom] in D1,D2.
      clear -F D1 D2; task_atomic.
Qed.

Lemma task_solution_scope G X A T :
  uniq (awl_to_aenv G) -> task_scoped empty G ->
  ftvar_in_typ A [<=] task_type_dom G -> X `notin` ftvar_in_typ A ->
  task_solution G X A = Some T -> task_scoped empty T.
Proof.
  intros U H F NX E. apply task_solution_spec in E as [P [K [HS ->]]]; auto.
  eapply task_subst_scope_rel; eassumption.
Qed.

Lemma task_list_sound_gc_var a b c G T :
  List.In T (task_list_gc_var a b c G) -> task_step a b c G T.
Proof.
  intros E.
  destruct G as [ | G X d | skip0 skip1]; cbn [task_list_gc_var] in E; try contradiction.
  destruct E as [ <-|[]].
  eapply task_step__gc_var; try eassumption.
Qed.

Lemma task_list_sound_sub_top a b c G T :
  List.In T (task_list_sub_top a b c G) -> task_step a b c G T.
Proof.
  intros E.
  destruct G as [ | skip0 skip1 skip2 | G arg3]; cbn [task_list_sub_top] in E; try contradiction.
  destruct arg3 as [skip4 skip5 | skip6 skip7 | skip8 skip9 | skip10 skip11 skip12 skip13 | skip14 skip15 skip16 skip17 | skip18 skip19 skip20 | A arg21 | skip22 skip23 skip24 skip25 | skip26 skip27 skip28 | skip29 skip30 skip31 skip32 skip33 | skip34 skip35 | skip36 skip37 skip38]; cbn [task_list_sub_top] in E; try contradiction.
  destruct arg21 as [ |  |  | skip39 | skip40 | skip41 skip42 | skip43 | skip44 skip45 | skip46 skip47]; cbn [task_list_sub_top] in E; try contradiction.
  destruct E as [ <-|[]].
  eapply task_step__sub_top; try eassumption.
Qed.

Lemma task_list_sound_sub_bot a b c G T :
  List.In T (task_list_sub_bot a b c G) -> task_step a b c G T.
Proof.
  intros E.
  destruct G as [ | skip0 skip1 skip2 | G arg3]; cbn [task_list_sub_bot] in E; try contradiction.
  destruct arg3 as [skip4 skip5 | skip6 skip7 | skip8 skip9 | skip10 skip11 skip12 skip13 | skip14 skip15 skip16 skip17 | skip18 skip19 skip20 | arg21 A | skip22 skip23 skip24 skip25 | skip26 skip27 skip28 | skip29 skip30 skip31 skip32 skip33 | skip34 skip35 | skip36 skip37 skip38]; cbn [task_list_sub_bot] in E; try contradiction.
  destruct arg21 as [ |  |  | skip39 | skip40 | skip41 skip42 | skip43 | skip44 skip45 | skip46 skip47]; cbn [task_list_sub_bot] in E; try contradiction.
  destruct E as [ <-|[]].
  eapply task_step__sub_bot; try eassumption.
Qed.

Lemma task_list_sound_sub_unit a b c G T :
  List.In T (task_list_sub_unit a b c G) -> task_step a b c G T.
Proof.
  intros E.
  destruct G as [ | skip0 skip1 skip2 | G arg3]; cbn [task_list_sub_unit] in E; try contradiction.
  destruct arg3 as [skip4 skip5 | skip6 skip7 | skip8 skip9 | skip10 skip11 skip12 skip13 | skip14 skip15 skip16 skip17 | skip18 skip19 skip20 | arg21 arg22 | skip23 skip24 skip25 skip26 | skip27 skip28 skip29 | skip30 skip31 skip32 skip33 skip34 | skip35 skip36 | skip37 skip38 skip39]; cbn [task_list_sub_unit] in E; try contradiction.
  destruct arg21 as [ |  |  | skip40 | skip41 | skip42 skip43 | skip44 | skip45 skip46 | skip47 skip48]; cbn [task_list_sub_unit] in E; try contradiction.
  destruct arg22 as [ |  |  | skip49 | skip50 | skip51 skip52 | skip53 | skip54 skip55 | skip56 skip57]; cbn [task_list_sub_unit] in E; try contradiction.
  destruct E as [ <-|[]].
  eapply task_step__sub_unit; try eassumption.
Qed.

Lemma task_list_sound_sub_tvar a b c G T :
  List.In T (task_list_sub_tvar a b c G) -> task_step a b c G T.
Proof.
  intros E.
  destruct G as [ | skip0 skip1 skip2 | G arg3]; cbn [task_list_sub_tvar] in E; try contradiction.
  destruct arg3 as [skip4 skip5 | skip6 skip7 | skip8 skip9 | skip10 skip11 skip12 skip13 | skip14 skip15 skip16 skip17 | skip18 skip19 skip20 | arg21 arg22 | skip23 skip24 skip25 skip26 | skip27 skip28 skip29 | skip30 skip31 skip32 skip33 skip34 | skip35 skip36 | skip37 skip38 skip39]; cbn [task_list_sub_tvar] in E; try contradiction.
  destruct arg21 as [ |  |  | skip40 | X | skip41 skip42 | skip43 | skip44 skip45 | skip46 skip47]; cbn [task_list_sub_tvar] in E; try contradiction.
  destruct arg22 as [ |  |  | skip48 | Y | skip49 skip50 | skip51 | skip52 skip53 | skip54 skip55]; cbn [task_list_sub_tvar] in E; try contradiction.
  destruct (task_eq X Y) as [Guard0 | Guard0]; try contradiction.
  destruct E as [ <-|[]].
  eapply task_step__sub_tvar; try eassumption.
Qed.

Lemma task_list_sound_subarrow a b c G T :
  List.In T (task_list_subarrow a b c G) -> task_step a b c G T.
Proof.
  intros E.
  destruct G as [ | skip0 skip1 skip2 | G arg3]; cbn [task_list_subarrow] in E; try contradiction.
  destruct arg3 as [skip4 skip5 | skip6 skip7 | skip8 skip9 | skip10 skip11 skip12 skip13 | skip14 skip15 skip16 skip17 | skip18 skip19 skip20 | arg21 arg22 | skip23 skip24 skip25 skip26 | skip27 skip28 skip29 | skip30 skip31 skip32 skip33 skip34 | skip35 skip36 | skip37 skip38 skip39]; cbn [task_list_subarrow] in E; try contradiction.
  destruct arg21 as [ |  |  | skip40 | skip41 | A B | skip42 | skip43 skip44 | skip45 skip46]; cbn [task_list_subarrow] in E; try contradiction.
  destruct arg22 as [ |  |  | skip47 | skip48 | C D | skip49 | skip50 skip51 | skip52 skip53]; cbn [task_list_subarrow] in E; try contradiction.
  destruct E as [ <-|[]].
  eapply task_step__subarrow; try eassumption.
Qed.

Lemma task_list_sound_sub_alll a b c G T :
  List.In T (task_list_sub_alll a b c G) -> task_step a b c G T.
Proof.
  intros E.
  destruct G as [ | skip0 skip1 skip2 | G arg3]; cbn [task_list_sub_alll] in E; try contradiction.
  destruct arg3 as [skip4 skip5 | skip6 skip7 | skip8 skip9 | skip10 skip11 skip12 skip13 | skip14 skip15 skip16 skip17 | skip18 skip19 skip20 | arg21 B | skip22 skip23 skip24 skip25 | skip26 skip27 skip28 | skip29 skip30 skip31 skip32 skip33 | skip34 skip35 | skip36 skip37 skip38]; cbn [task_list_sub_alll] in E; try contradiction.
  destruct arg21 as [ |  |  | skip39 | skip40 | skip41 skip42 | A | skip43 skip44 | skip45 skip46]; cbn [task_list_sub_alll] in E; try contradiction.
  destruct (task_wneq_dec G B) as [Guard0 | Guard0]; try contradiction.
  destruct E as [ <-|[]].
  eapply task_step__sub_alll; try eassumption.
Qed.

Lemma task_list_sound_sub_all a b c G T :
  List.In T (task_list_sub_all a b c G) -> task_step a b c G T.
Proof.
  intros E.
  destruct G as [ | skip0 skip1 skip2 | G arg3]; cbn [task_list_sub_all] in E; try contradiction.
  destruct arg3 as [skip4 skip5 | skip6 skip7 | skip8 skip9 | skip10 skip11 skip12 skip13 | skip14 skip15 skip16 skip17 | skip18 skip19 skip20 | arg21 arg22 | skip23 skip24 skip25 skip26 | skip27 skip28 skip29 | skip30 skip31 skip32 skip33 skip34 | skip35 skip36 | skip37 skip38 skip39]; cbn [task_list_sub_all] in E; try contradiction.
  destruct arg21 as [ |  |  | skip40 | skip41 | skip42 skip43 | A | skip44 skip45 | skip46 skip47]; cbn [task_list_sub_all] in E; try contradiction.
  destruct arg22 as [ |  |  | skip48 | skip49 | skip50 skip51 | B | skip52 skip53 | skip54 skip55]; cbn [task_list_sub_all] in E; try contradiction.
  destruct E as [ <-|[]].
  eapply task_step__sub_all; try eassumption.
Qed.

Lemma task_list_sound_sub_arrow1 a b c G T :
  List.In T (task_list_sub_arrow1 a b c G) -> task_step a b c G T.
Proof.
  intros E.
  destruct G as [ | skip0 skip1 skip2 | G arg3]; cbn [task_list_sub_arrow1] in E; try contradiction.
  destruct arg3 as [skip4 skip5 | skip6 skip7 | skip8 skip9 | skip10 skip11 skip12 skip13 | skip14 skip15 skip16 skip17 | skip18 skip19 skip20 | arg21 arg22 | skip23 skip24 skip25 skip26 | skip27 skip28 skip29 | skip30 skip31 skip32 skip33 skip34 | skip35 skip36 | skip37 skip38 skip39]; cbn [task_list_sub_arrow1] in E; try contradiction.
  destruct arg21 as [ |  |  | skip40 | X | skip41 skip42 | skip43 | skip44 skip45 | skip46 skip47]; cbn [task_list_sub_arrow1] in E; try contradiction.
  destruct arg22 as [ |  |  | skip48 | skip49 | A B | skip50 | skip51 skip52 | skip53 skip54]; cbn [task_list_sub_arrow1] in E; try contradiction.
  destruct (task_binding_dec G X abind_etvar_empty) as [Guard0 | Guard0]; try contradiction.
  destruct (task_mono_dec G (typ_arrow A B)) as [Guard1 | Guard1]; try contradiction.
  destruct E as [ <-|[]].
  eapply task_step__sub_arrow1; try eassumption.
Qed.

Lemma task_list_sound_sub_arrow2 a b c G T :
  List.In T (task_list_sub_arrow2 a b c G) -> task_step a b c G T.
Proof.
  intros E.
  destruct G as [ | skip0 skip1 skip2 | G arg3]; cbn [task_list_sub_arrow2] in E; try contradiction.
  destruct arg3 as [skip4 skip5 | skip6 skip7 | skip8 skip9 | skip10 skip11 skip12 skip13 | skip14 skip15 skip16 skip17 | skip18 skip19 skip20 | arg21 arg22 | skip23 skip24 skip25 skip26 | skip27 skip28 skip29 | skip30 skip31 skip32 skip33 skip34 | skip35 skip36 | skip37 skip38 skip39]; cbn [task_list_sub_arrow2] in E; try contradiction.
  destruct arg21 as [ |  |  | skip40 | skip41 | A B | skip42 | skip43 skip44 | skip45 skip46]; cbn [task_list_sub_arrow2] in E; try contradiction.
  destruct arg22 as [ |  |  | skip47 | X | skip48 skip49 | skip50 | skip51 skip52 | skip53 skip54]; cbn [task_list_sub_arrow2] in E; try contradiction.
  destruct (task_binding_dec G X abind_etvar_empty) as [Guard0 | Guard0]; try contradiction.
  destruct (task_mono_dec G (typ_arrow A B)) as [Guard1 | Guard1]; try contradiction.
  destruct E as [ <-|[]].
  eapply task_step__sub_arrow2; try eassumption.
Qed.

Lemma task_list_sound_sub_etvarmono1 a b c G T :
  List.In T (task_list_sub_etvarmono1 a b c G) -> task_step a b c G T.
Proof.
  intros E.
  destruct G as [ | skip0 skip1 skip2 | G arg3]; cbn [task_list_sub_etvarmono1] in E; try contradiction.
  destruct arg3 as [skip4 skip5 | skip6 skip7 | skip8 skip9 | skip10 skip11 skip12 skip13 | skip14 skip15 skip16 skip17 | skip18 skip19 skip20 | A arg21 | skip22 skip23 skip24 skip25 | skip26 skip27 skip28 | skip29 skip30 skip31 skip32 skip33 | skip34 skip35 | skip36 skip37 skip38]; cbn [task_list_sub_etvarmono1] in E; try contradiction.
  destruct arg21 as [ |  |  | skip39 | X | skip40 skip41 | skip42 | skip43 skip44 | skip45 skip46]; cbn [task_list_sub_etvarmono1] in E; try contradiction.
  destruct (task_binding_dec G X abind_etvar_empty) as [Guard0 | Guard0]; try contradiction.
  destruct (task_mono_dec G A) as [Guard1 | Guard1]; try contradiction.
  destruct (AtomSetImpl.mem X (ftvar_in_typ A)) eqn:Guard2; try contradiction.
  destruct (task_solution G X A) as [T0|] eqn:S; try contradiction.
  destruct E as [ <-|[]].
  eapply task_step__sub_etvarmono1; try eassumption.
  now apply task_mem_false.
Qed.

Lemma task_list_sound_sub_etvarmono2 a b c G T :
  List.In T (task_list_sub_etvarmono2 a b c G) -> task_step a b c G T.
Proof.
  intros E.
  destruct G as [ | skip0 skip1 skip2 | G arg3]; cbn [task_list_sub_etvarmono2] in E; try contradiction.
  destruct arg3 as [skip4 skip5 | skip6 skip7 | skip8 skip9 | skip10 skip11 skip12 skip13 | skip14 skip15 skip16 skip17 | skip18 skip19 skip20 | arg21 A | skip22 skip23 skip24 skip25 | skip26 skip27 skip28 | skip29 skip30 skip31 skip32 skip33 | skip34 skip35 | skip36 skip37 skip38]; cbn [task_list_sub_etvarmono2] in E; try contradiction.
  destruct arg21 as [ |  |  | skip39 | X | skip40 skip41 | skip42 | skip43 skip44 | skip45 skip46]; cbn [task_list_sub_etvarmono2] in E; try contradiction.
  destruct (task_binding_dec G X abind_etvar_empty) as [Guard0 | Guard0]; try contradiction.
  destruct (task_mono_dec G A) as [Guard1 | Guard1]; try contradiction.
  destruct (AtomSetImpl.mem X (ftvar_in_typ A)) eqn:Guard2; try contradiction.
  destruct (task_solution G X A) as [T0|] eqn:S; try contradiction.
  destruct E as [ <-|[]].
  eapply task_step__sub_etvarmono2; try eassumption.
  now apply task_mem_false.
Qed.

Lemma task_list_sound_sub_intersection1 a b c G T :
  List.In T (task_list_sub_intersection1 a b c G) -> task_step a b c G T.
Proof.
  intros E.
  destruct G as [ | skip0 skip1 skip2 | G arg3]; cbn [task_list_sub_intersection1] in E; try contradiction.
  destruct arg3 as [skip4 skip5 | skip6 skip7 | skip8 skip9 | skip10 skip11 skip12 skip13 | skip14 skip15 skip16 skip17 | skip18 skip19 skip20 | A arg21 | skip22 skip23 skip24 skip25 | skip26 skip27 skip28 | skip29 skip30 skip31 skip32 skip33 | skip34 skip35 | skip36 skip37 skip38]; cbn [task_list_sub_intersection1] in E; try contradiction.
  destruct arg21 as [ |  |  | skip39 | skip40 | skip41 skip42 | skip43 | skip44 skip45 | B C]; cbn [task_list_sub_intersection1] in E; try contradiction.
  destruct E as [ <-|[]].
  eapply task_step__sub_intersection1; try eassumption.
Qed.

Lemma task_list_sound_sub_intersection2 a b c G T :
  List.In T (task_list_sub_intersection2 a b c G) -> task_step a b c G T.
Proof.
  intros E.
  destruct G as [ | skip0 skip1 skip2 | G arg3]; cbn [task_list_sub_intersection2] in E; try contradiction.
  destruct arg3 as [skip4 skip5 | skip6 skip7 | skip8 skip9 | skip10 skip11 skip12 skip13 | skip14 skip15 skip16 skip17 | skip18 skip19 skip20 | arg21 C | skip22 skip23 skip24 skip25 | skip26 skip27 skip28 | skip29 skip30 skip31 skip32 skip33 | skip34 skip35 | skip36 skip37 skip38]; cbn [task_list_sub_intersection2] in E; try contradiction.
  destruct arg21 as [ |  |  | skip39 | skip40 | skip41 skip42 | skip43 | skip44 skip45 | A B]; cbn [task_list_sub_intersection2] in E; try contradiction.
  destruct E as [ <-|[]].
  eapply task_step__sub_intersection2; try eassumption.
Qed.

Lemma task_list_sound_sub_intersection3 a b c G T :
  List.In T (task_list_sub_intersection3 a b c G) -> task_step a b c G T.
Proof.
  intros E.
  destruct G as [ | skip0 skip1 skip2 | G arg3]; cbn [task_list_sub_intersection3] in E; try contradiction.
  destruct arg3 as [skip4 skip5 | skip6 skip7 | skip8 skip9 | skip10 skip11 skip12 skip13 | skip14 skip15 skip16 skip17 | skip18 skip19 skip20 | arg21 C | skip22 skip23 skip24 skip25 | skip26 skip27 skip28 | skip29 skip30 skip31 skip32 skip33 | skip34 skip35 | skip36 skip37 skip38]; cbn [task_list_sub_intersection3] in E; try contradiction.
  destruct arg21 as [ |  |  | skip39 | skip40 | skip41 skip42 | skip43 | skip44 skip45 | A B]; cbn [task_list_sub_intersection3] in E; try contradiction.
  destruct E as [ <-|[]].
  eapply task_step__sub_intersection3; try eassumption.
Qed.

Lemma task_list_sound_sub_union1 a b c G T :
  List.In T (task_list_sub_union1 a b c G) -> task_step a b c G T.
Proof.
  intros E.
  destruct G as [ | skip0 skip1 skip2 | G arg3]; cbn [task_list_sub_union1] in E; try contradiction.
  destruct arg3 as [skip4 skip5 | skip6 skip7 | skip8 skip9 | skip10 skip11 skip12 skip13 | skip14 skip15 skip16 skip17 | skip18 skip19 skip20 | A arg21 | skip22 skip23 skip24 skip25 | skip26 skip27 skip28 | skip29 skip30 skip31 skip32 skip33 | skip34 skip35 | skip36 skip37 skip38]; cbn [task_list_sub_union1] in E; try contradiction.
  destruct arg21 as [ |  |  | skip39 | skip40 | skip41 skip42 | skip43 | B C | skip44 skip45]; cbn [task_list_sub_union1] in E; try contradiction.
  destruct E as [ <-|[]].
  eapply task_step__sub_union1; try eassumption.
Qed.

Lemma task_list_sound_sub_union2 a b c G T :
  List.In T (task_list_sub_union2 a b c G) -> task_step a b c G T.
Proof.
  intros E.
  destruct G as [ | skip0 skip1 skip2 | G arg3]; cbn [task_list_sub_union2] in E; try contradiction.
  destruct arg3 as [skip4 skip5 | skip6 skip7 | skip8 skip9 | skip10 skip11 skip12 skip13 | skip14 skip15 skip16 skip17 | skip18 skip19 skip20 | A arg21 | skip22 skip23 skip24 skip25 | skip26 skip27 skip28 | skip29 skip30 skip31 skip32 skip33 | skip34 skip35 | skip36 skip37 skip38]; cbn [task_list_sub_union2] in E; try contradiction.
  destruct arg21 as [ |  |  | skip39 | skip40 | skip41 skip42 | skip43 | B C | skip44 skip45]; cbn [task_list_sub_union2] in E; try contradiction.
  destruct E as [ <-|[]].
  eapply task_step__sub_union2; try eassumption.
Qed.

Lemma task_list_sound_sub_union3 a b c G T :
  List.In T (task_list_sub_union3 a b c G) -> task_step a b c G T.
Proof.
  intros E.
  destruct G as [ | skip0 skip1 skip2 | G arg3]; cbn [task_list_sub_union3] in E; try contradiction.
  destruct arg3 as [skip4 skip5 | skip6 skip7 | skip8 skip9 | skip10 skip11 skip12 skip13 | skip14 skip15 skip16 skip17 | skip18 skip19 skip20 | arg21 C | skip22 skip23 skip24 skip25 | skip26 skip27 skip28 | skip29 skip30 skip31 skip32 skip33 | skip34 skip35 | skip36 skip37 skip38]; cbn [task_list_sub_union3] in E; try contradiction.
  destruct arg21 as [ |  |  | skip39 | skip40 | skip41 skip42 | skip43 | A B | skip44 skip45]; cbn [task_list_sub_union3] in E; try contradiction.
  destruct E as [ <-|[]].
  eapply task_step__sub_union3; try eassumption.
Qed.

Lemma task_list_sound_chk_sub a b c G T :
  List.In T (task_list_chk_sub a b c G) -> task_step a b c G T.
Proof.
  intros E.
  destruct G as [ | skip0 skip1 skip2 | G arg3]; cbn [task_list_chk_sub] in E; try contradiction.
  destruct arg3 as [skip4 skip5 | e A | skip6 skip7 | skip8 skip9 skip10 skip11 | skip12 skip13 skip14 skip15 | skip16 skip17 skip18 | skip19 skip20 | skip21 skip22 skip23 skip24 | skip25 skip26 skip27 | skip28 skip29 skip30 skip31 skip32 | skip33 skip34 | skip35 skip36 skip37]; cbn [task_list_chk_sub] in E; try contradiction.
  destruct E as [ <-|[]].
  eapply task_step__chk_sub; try eassumption.
Qed.

Lemma task_list_sound_chk_absarrow a b c G T :
  List.In T (task_list_chk_absarrow a b c G) -> task_step a b c G T.
Proof.
  intros E.
  destruct G as [ | skip0 skip1 skip2 | G arg3]; cbn [task_list_chk_absarrow] in E; try contradiction.
  destruct arg3 as [skip4 skip5 | arg6 arg7 | skip8 skip9 | skip10 skip11 skip12 skip13 | skip14 skip15 skip16 skip17 | skip18 skip19 skip20 | skip21 skip22 | skip23 skip24 skip25 skip26 | skip27 skip28 skip29 | skip30 skip31 skip32 skip33 skip34 | skip35 skip36 | skip37 skip38 skip39]; cbn [task_list_chk_absarrow] in E; try contradiction.
  destruct arg6 as [ | skip40 | skip41 | e | skip42 skip43 | skip44 | skip45 skip46 | skip47 skip48]; cbn [task_list_chk_absarrow] in E; try contradiction.
  destruct arg7 as [ |  |  | skip49 | skip50 | A B | skip51 | skip52 skip53 | skip54 skip55]; cbn [task_list_chk_absarrow] in E; try contradiction.
  destruct E as [ <-|[]].
  eapply task_step__chk_absarrow; try eassumption.
Qed.

Lemma task_list_sound_chk_absetvar a b c G T :
  List.In T (task_list_chk_absetvar a b c G) -> task_step a b c G T.
Proof.
  intros E.
  destruct G as [ | skip0 skip1 skip2 | G arg3]; cbn [task_list_chk_absetvar] in E; try contradiction.
  destruct arg3 as [skip4 skip5 | arg6 arg7 | skip8 skip9 | skip10 skip11 skip12 skip13 | skip14 skip15 skip16 skip17 | skip18 skip19 skip20 | skip21 skip22 | skip23 skip24 skip25 skip26 | skip27 skip28 skip29 | skip30 skip31 skip32 skip33 skip34 | skip35 skip36 | skip37 skip38 skip39]; cbn [task_list_chk_absetvar] in E; try contradiction.
  destruct arg6 as [ | skip40 | skip41 | e | skip42 skip43 | skip44 | skip45 skip46 | skip47 skip48]; cbn [task_list_chk_absetvar] in E; try contradiction.
  destruct arg7 as [ |  |  | skip49 | X | skip50 skip51 | skip52 | skip53 skip54 | skip55 skip56]; cbn [task_list_chk_absetvar] in E; try contradiction.
  destruct (task_binding_dec G X abind_etvar_empty) as [Guard0 | Guard0]; try contradiction.
  destruct E as [ <-|[]].
  eapply task_step__chk_absetvar; try eassumption.
Qed.

Lemma task_list_sound_chk_abstop a b c G T :
  List.In T (task_list_chk_abstop a b c G) -> task_step a b c G T.
Proof.
  intros E.
  destruct G as [ | skip0 skip1 skip2 | G arg3]; cbn [task_list_chk_abstop] in E; try contradiction.
  destruct arg3 as [skip4 skip5 | arg6 arg7 | skip8 skip9 | skip10 skip11 skip12 skip13 | skip14 skip15 skip16 skip17 | skip18 skip19 skip20 | skip21 skip22 | skip23 skip24 skip25 skip26 | skip27 skip28 skip29 | skip30 skip31 skip32 skip33 skip34 | skip35 skip36 | skip37 skip38 skip39]; cbn [task_list_chk_abstop] in E; try contradiction.
  destruct arg6 as [ | skip40 | skip41 | e | skip42 skip43 | skip44 | skip45 skip46 | skip47 skip48]; cbn [task_list_chk_abstop] in E; try contradiction.
  destruct arg7 as [ |  |  | skip49 | skip50 | skip51 skip52 | skip53 | skip54 skip55 | skip56 skip57]; cbn [task_list_chk_abstop] in E; try contradiction.
  destruct E as [ <-|[]].
  eapply task_step__chk_abstop; try eassumption.
Qed.

Lemma task_list_sound_chk_inter a b c G T :
  List.In T (task_list_chk_inter a b c G) -> task_step a b c G T.
Proof.
  intros E.
  destruct G as [ | skip0 skip1 skip2 | G arg3]; cbn [task_list_chk_inter] in E; try contradiction.
  destruct arg3 as [skip4 skip5 | e arg6 | skip7 skip8 | skip9 skip10 skip11 skip12 | skip13 skip14 skip15 skip16 | skip17 skip18 skip19 | skip20 skip21 | skip22 skip23 skip24 skip25 | skip26 skip27 skip28 | skip29 skip30 skip31 skip32 skip33 | skip34 skip35 | skip36 skip37 skip38]; cbn [task_list_chk_inter] in E; try contradiction.
  destruct arg6 as [ |  |  | skip39 | skip40 | skip41 skip42 | skip43 | skip44 skip45 | A B]; cbn [task_list_chk_inter] in E; try contradiction.
  destruct E as [ <-|[]].
  eapply task_step__chk_inter; try eassumption.
Qed.

Lemma task_list_sound_chk_union1 a b c G T :
  List.In T (task_list_chk_union1 a b c G) -> task_step a b c G T.
Proof.
  intros E.
  destruct G as [ | skip0 skip1 skip2 | G arg3]; cbn [task_list_chk_union1] in E; try contradiction.
  destruct arg3 as [skip4 skip5 | e arg6 | skip7 skip8 | skip9 skip10 skip11 skip12 | skip13 skip14 skip15 skip16 | skip17 skip18 skip19 | skip20 skip21 | skip22 skip23 skip24 skip25 | skip26 skip27 skip28 | skip29 skip30 skip31 skip32 skip33 | skip34 skip35 | skip36 skip37 skip38]; cbn [task_list_chk_union1] in E; try contradiction.
  destruct arg6 as [ |  |  | skip39 | skip40 | skip41 skip42 | skip43 | A B | skip44 skip45]; cbn [task_list_chk_union1] in E; try contradiction.
  destruct E as [ <-|[]].
  eapply task_step__chk_union1; try eassumption.
Qed.

Lemma task_list_sound_chk_union2 a b c G T :
  List.In T (task_list_chk_union2 a b c G) -> task_step a b c G T.
Proof.
  intros E.
  destruct G as [ | skip0 skip1 skip2 | G arg3]; cbn [task_list_chk_union2] in E; try contradiction.
  destruct arg3 as [skip4 skip5 | e arg6 | skip7 skip8 | skip9 skip10 skip11 skip12 | skip13 skip14 skip15 skip16 | skip17 skip18 skip19 | skip20 skip21 | skip22 skip23 skip24 skip25 | skip26 skip27 skip28 | skip29 skip30 skip31 skip32 skip33 | skip34 skip35 | skip36 skip37 skip38]; cbn [task_list_chk_union2] in E; try contradiction.
  destruct arg6 as [ |  |  | skip39 | skip40 | skip41 skip42 | skip43 | A B | skip44 skip45]; cbn [task_list_chk_union2] in E; try contradiction.
  destruct E as [ <-|[]].
  eapply task_step__chk_union2; try eassumption.
Qed.

Lemma task_list_sound_inf_var a b c G T :
  List.In T (task_list_inf_var a b c G) -> task_step a b c G T.
Proof.
  intros E.
  destruct G as [ | skip0 skip1 skip2 | G arg3]; cbn [task_list_inf_var] in E; try contradiction.
  destruct arg3 as [arg4 cs | skip5 skip6 | skip7 skip8 | skip9 skip10 skip11 skip12 | skip13 skip14 skip15 skip16 | skip17 skip18 skip19 | skip20 skip21 | skip22 skip23 skip24 skip25 | skip26 skip27 skip28 | skip29 skip30 skip31 skip32 skip33 | skip34 skip35 | skip36 skip37 skip38]; cbn [task_list_inf_var] in E; try contradiction.
  destruct arg4 as [ | skip39 | X | skip40 | skip41 skip42 | skip43 | skip44 skip45 | skip46 skip47]; cbn [task_list_inf_var] in E; try contradiction.
  apply in_map_iff in E as [A [ <- B]].
  apply task_step__inf_var. now apply task_lookup_spec.
Qed.

Lemma task_list_sound_inf_anno a b c G T :
  List.In T (task_list_inf_anno a b c G) -> task_step a b c G T.
Proof.
  intros E.
  destruct G as [ | skip0 skip1 skip2 | G arg3]; cbn [task_list_inf_anno] in E; try contradiction.
  destruct arg3 as [arg4 cs | skip5 skip6 | skip7 skip8 | skip9 skip10 skip11 skip12 | skip13 skip14 skip15 skip16 | skip17 skip18 skip19 | skip20 skip21 | skip22 skip23 skip24 skip25 | skip26 skip27 skip28 | skip29 skip30 skip31 skip32 skip33 | skip34 skip35 | skip36 skip37 skip38]; cbn [task_list_inf_anno] in E; try contradiction.
  destruct arg4 as [ | skip39 | skip40 | skip41 | skip42 skip43 | skip44 | skip45 skip46 | e A]; cbn [task_list_inf_anno] in E; try contradiction.
  destruct E as [ <-|[]].
  eapply task_step__inf_anno; try eassumption.
Qed.

Lemma task_list_sound_inf_tabs a b c G T :
  List.In T (task_list_inf_tabs a b c G) -> task_step a b c G T.
Proof.
  intros E.
  destruct G as [ | skip0 skip1 skip2 | G arg3]; cbn [task_list_inf_tabs] in E; try contradiction.
  destruct arg3 as [arg4 cs | skip5 skip6 | skip7 skip8 | skip9 skip10 skip11 skip12 | skip13 skip14 skip15 skip16 | skip17 skip18 skip19 | skip20 skip21 | skip22 skip23 skip24 skip25 | skip26 skip27 skip28 | skip29 skip30 skip31 skip32 skip33 | skip34 skip35 | skip36 skip37 skip38]; cbn [task_list_inf_tabs] in E; try contradiction.
  destruct arg4 as [ | skip39 | skip40 | skip41 | skip42 skip43 | arg44 | skip45 skip46 | skip47 skip48]; cbn [task_list_inf_tabs] in E; try contradiction.
  destruct arg44 as [ | skip49 | skip50 | skip51 | skip52 skip53 | skip54 | skip55 skip56 | e A]; cbn [task_list_inf_tabs] in E; try contradiction.
  destruct E as [ <-|[]].
  eapply task_step__inf_tabs; try eassumption.
Qed.

Lemma task_list_sound_inf_abs_mono a b c G T :
  List.In T (task_list_inf_abs_mono a b c G) -> task_step a b c G T.
Proof.
  intros E.
  destruct G as [ | skip0 skip1 skip2 | G arg3]; cbn [task_list_inf_abs_mono] in E; try contradiction.
  destruct arg3 as [arg4 cs | skip5 skip6 | skip7 skip8 | skip9 skip10 skip11 skip12 | skip13 skip14 skip15 skip16 | skip17 skip18 skip19 | skip20 skip21 | skip22 skip23 skip24 skip25 | skip26 skip27 skip28 | skip29 skip30 skip31 skip32 skip33 | skip34 skip35 | skip36 skip37 skip38]; cbn [task_list_inf_abs_mono] in E; try contradiction.
  destruct arg4 as [ | skip39 | skip40 | e | skip41 skip42 | skip43 | skip44 skip45 | skip46 skip47]; cbn [task_list_inf_abs_mono] in E; try contradiction.
  destruct E as [ <-|[]].
  eapply task_step__inf_abs_mono; try eassumption.
Qed.

Lemma task_list_sound_inf_unit a b c G T :
  List.In T (task_list_inf_unit a b c G) -> task_step a b c G T.
Proof.
  intros E.
  destruct G as [ | skip0 skip1 skip2 | G arg3]; cbn [task_list_inf_unit] in E; try contradiction.
  destruct arg3 as [arg4 cs | skip5 skip6 | skip7 skip8 | skip9 skip10 skip11 skip12 | skip13 skip14 skip15 skip16 | skip17 skip18 skip19 | skip20 skip21 | skip22 skip23 skip24 skip25 | skip26 skip27 skip28 | skip29 skip30 skip31 skip32 skip33 | skip34 skip35 | skip36 skip37 skip38]; cbn [task_list_inf_unit] in E; try contradiction.
  destruct arg4 as [ | skip39 | skip40 | skip41 | skip42 skip43 | skip44 | skip45 skip46 | skip47 skip48]; cbn [task_list_inf_unit] in E; try contradiction.
  destruct E as [ <-|[]].
  eapply task_step__inf_unit; try eassumption.
Qed.

Lemma task_list_sound_inf_app a b c G T :
  List.In T (task_list_inf_app a b c G) -> task_step a b c G T.
Proof.
  intros E.
  destruct G as [ | skip0 skip1 skip2 | G arg3]; cbn [task_list_inf_app] in E; try contradiction.
  destruct arg3 as [arg4 cs | skip5 skip6 | skip7 skip8 | skip9 skip10 skip11 skip12 | skip13 skip14 skip15 skip16 | skip17 skip18 skip19 | skip20 skip21 | skip22 skip23 skip24 skip25 | skip26 skip27 skip28 | skip29 skip30 skip31 skip32 skip33 | skip34 skip35 | skip36 skip37 skip38]; cbn [task_list_inf_app] in E; try contradiction.
  destruct arg4 as [ | skip39 | skip40 | skip41 | e f | skip42 | skip43 skip44 | skip45 skip46]; cbn [task_list_inf_app] in E; try contradiction.
  destruct E as [ <-|[]].
  eapply task_step__inf_app; try eassumption.
Qed.

Lemma task_list_sound_infapp a b c G T :
  List.In T (task_list_infapp a b c G) -> task_step a b c G T.
Proof.
  intros E.
  destruct G as [ | skip0 skip1 skip2 | G arg3]; cbn [task_list_infapp] in E; try contradiction.
  destruct arg3 as [skip4 skip5 | skip6 skip7 | skip8 skip9 | skip10 skip11 skip12 skip13 | A B e cs | skip14 skip15 skip16 | skip17 skip18 | skip19 skip20 skip21 skip22 | skip23 skip24 skip25 | skip26 skip27 skip28 skip29 skip30 | skip31 skip32 | skip33 skip34 skip35]; cbn [task_list_infapp] in E; try contradiction.
  destruct E as [ <-|[]].
  eapply task_step__infapp; try eassumption.
Qed.

Lemma task_list_sound_infabs_arr a b c G T :
  List.In T (task_list_infabs_arr a b c G) -> task_step a b c G T.
Proof.
  intros E.
  destruct G as [ | skip0 skip1 skip2 | G arg3]; cbn [task_list_infabs_arr] in E; try contradiction.
  destruct arg3 as [skip4 skip5 | skip6 skip7 | arg8 cd | skip9 skip10 skip11 skip12 | skip13 skip14 skip15 skip16 | skip17 skip18 skip19 | skip20 skip21 | skip22 skip23 skip24 skip25 | skip26 skip27 skip28 | skip29 skip30 skip31 skip32 skip33 | skip34 skip35 | skip36 skip37 skip38]; cbn [task_list_infabs_arr] in E; try contradiction.
  destruct arg8 as [ |  |  | skip39 | skip40 | A B | skip41 | skip42 skip43 | skip44 skip45]; cbn [task_list_infabs_arr] in E; try contradiction.
  destruct E as [ <-|[]].
  eapply task_step__infabs_arr; try eassumption.
Qed.

Lemma task_list_sound_infabs_bot a b c G T :
  List.In T (task_list_infabs_bot a b c G) -> task_step a b c G T.
Proof.
  intros E.
  destruct G as [ | skip0 skip1 skip2 | G arg3]; cbn [task_list_infabs_bot] in E; try contradiction.
  destruct arg3 as [skip4 skip5 | skip6 skip7 | arg8 cd | skip9 skip10 skip11 skip12 | skip13 skip14 skip15 skip16 | skip17 skip18 skip19 | skip20 skip21 | skip22 skip23 skip24 skip25 | skip26 skip27 skip28 | skip29 skip30 skip31 skip32 skip33 | skip34 skip35 | skip36 skip37 skip38]; cbn [task_list_infabs_bot] in E; try contradiction.
  destruct arg8 as [ |  |  | skip39 | skip40 | skip41 skip42 | skip43 | skip44 skip45 | skip46 skip47]; cbn [task_list_infabs_bot] in E; try contradiction.
  destruct E as [ <-|[]].
  eapply task_step__infabs_bot; try eassumption.
Qed.

Lemma task_list_sound_infabs_all a b c G T :
  List.In T (task_list_infabs_all a b c G) -> task_step a b c G T.
Proof.
  intros E.
  destruct G as [ | skip0 skip1 skip2 | G arg3]; cbn [task_list_infabs_all] in E; try contradiction.
  destruct arg3 as [skip4 skip5 | skip6 skip7 | arg8 cd | skip9 skip10 skip11 skip12 | skip13 skip14 skip15 skip16 | skip17 skip18 skip19 | skip20 skip21 | skip22 skip23 skip24 skip25 | skip26 skip27 skip28 | skip29 skip30 skip31 skip32 skip33 | skip34 skip35 | skip36 skip37 skip38]; cbn [task_list_infabs_all] in E; try contradiction.
  destruct arg8 as [ |  |  | skip39 | skip40 | skip41 skip42 | A | skip43 skip44 | skip45 skip46]; cbn [task_list_infabs_all] in E; try contradiction.
  destruct E as [ <-|[]].
  eapply task_step__infabs_all; try eassumption.
Qed.

Lemma task_list_sound_infabs_inter1 a b c G T :
  List.In T (task_list_infabs_inter1 a b c G) -> task_step a b c G T.
Proof.
  intros E.
  destruct G as [ | skip0 skip1 skip2 | G arg3]; cbn [task_list_infabs_inter1] in E; try contradiction.
  destruct arg3 as [skip4 skip5 | skip6 skip7 | arg8 cd | skip9 skip10 skip11 skip12 | skip13 skip14 skip15 skip16 | skip17 skip18 skip19 | skip20 skip21 | skip22 skip23 skip24 skip25 | skip26 skip27 skip28 | skip29 skip30 skip31 skip32 skip33 | skip34 skip35 | skip36 skip37 skip38]; cbn [task_list_infabs_inter1] in E; try contradiction.
  destruct arg8 as [ |  |  | skip39 | skip40 | skip41 skip42 | skip43 | skip44 skip45 | A B]; cbn [task_list_infabs_inter1] in E; try contradiction.
  destruct E as [ <-|[]].
  eapply task_step__infabs_inter1; try eassumption.
Qed.

Lemma task_list_sound_infabs_inter2 a b c G T :
  List.In T (task_list_infabs_inter2 a b c G) -> task_step a b c G T.
Proof.
  intros E.
  destruct G as [ | skip0 skip1 skip2 | G arg3]; cbn [task_list_infabs_inter2] in E; try contradiction.
  destruct arg3 as [skip4 skip5 | skip6 skip7 | arg8 cd | skip9 skip10 skip11 skip12 | skip13 skip14 skip15 skip16 | skip17 skip18 skip19 | skip20 skip21 | skip22 skip23 skip24 skip25 | skip26 skip27 skip28 | skip29 skip30 skip31 skip32 skip33 | skip34 skip35 | skip36 skip37 skip38]; cbn [task_list_infabs_inter2] in E; try contradiction.
  destruct arg8 as [ |  |  | skip39 | skip40 | skip41 skip42 | skip43 | skip44 skip45 | A B]; cbn [task_list_infabs_inter2] in E; try contradiction.
  destruct E as [ <-|[]].
  eapply task_step__infabs_inter2; try eassumption.
Qed.

Lemma task_list_sound_infabs_union a b c G T :
  List.In T (task_list_infabs_union a b c G) -> task_step a b c G T.
Proof.
  intros E.
  destruct G as [ | skip0 skip1 skip2 | G arg3]; cbn [task_list_infabs_union] in E; try contradiction.
  destruct arg3 as [skip4 skip5 | skip6 skip7 | arg8 cd | skip9 skip10 skip11 skip12 | skip13 skip14 skip15 skip16 | skip17 skip18 skip19 | skip20 skip21 | skip22 skip23 skip24 skip25 | skip26 skip27 skip28 | skip29 skip30 skip31 skip32 skip33 | skip34 skip35 | skip36 skip37 skip38]; cbn [task_list_infabs_union] in E; try contradiction.
  destruct arg8 as [ |  |  | skip39 | skip40 | skip41 skip42 | skip43 | A B | skip44 skip45]; cbn [task_list_infabs_union] in E; try contradiction.
  destruct E as [ <-|[]].
  eapply task_step__infabs_union; try eassumption.
Qed.

Lemma task_list_sound_infabsunion a b c G T :
  List.In T (task_list_infabsunion a b c G) -> task_step a b c G T.
Proof.
  intros E.
  destruct G as [ | skip0 skip1 skip2 | G arg3]; cbn [task_list_infabsunion] in E; try contradiction.
  destruct arg3 as [skip4 skip5 | skip6 skip7 | skip8 skip9 | A B C cd | skip10 skip11 skip12 skip13 | skip14 skip15 skip16 | skip17 skip18 | skip19 skip20 skip21 skip22 | skip23 skip24 skip25 | skip26 skip27 skip28 skip29 skip30 | skip31 skip32 | skip33 skip34 skip35]; cbn [task_list_infabsunion] in E; try contradiction.
  destruct E as [ <-|[]].
  eapply task_step__infabsunion; try eassumption.
Qed.

Lemma task_list_sound_unioninfabs a b c G T :
  List.In T (task_list_unioninfabs a b c G) -> task_step a b c G T.
Proof.
  intros E.
  destruct G as [ | skip0 skip1 skip2 | G arg3]; cbn [task_list_unioninfabs] in E; try contradiction.
  destruct arg3 as [skip4 skip5 | skip6 skip7 | skip8 skip9 | skip10 skip11 skip12 skip13 | skip14 skip15 skip16 skip17 | skip18 skip19 skip20 | skip21 skip22 | skip23 skip24 skip25 skip26 | skip27 skip28 skip29 | A B C D cd | skip30 skip31 | skip32 skip33 skip34]; cbn [task_list_unioninfabs] in E; try contradiction.
  destruct E as [ <-|[]].
  eapply task_step__unioninfabs; try eassumption.
Qed.

Lemma task_list_sound_infabs_etvar a b c G T :
  List.In T (task_list_infabs_etvar a b c G) -> task_step a b c G T.
Proof.
  intros E.
  destruct G as [ | skip0 skip1 skip2 | G arg3]; cbn [task_list_infabs_etvar] in E; try contradiction.
  destruct arg3 as [skip4 skip5 | skip6 skip7 | arg8 cd | skip9 skip10 skip11 skip12 | skip13 skip14 skip15 skip16 | skip17 skip18 skip19 | skip20 skip21 | skip22 skip23 skip24 skip25 | skip26 skip27 skip28 | skip29 skip30 skip31 skip32 skip33 | skip34 skip35 | skip36 skip37 skip38]; cbn [task_list_infabs_etvar] in E; try contradiction.
  destruct arg8 as [ |  |  | skip39 | X | skip40 skip41 | skip42 | skip43 skip44 | skip45 skip46]; cbn [task_list_infabs_etvar] in E; try contradiction.
  destruct (task_binding_dec G X abind_etvar_empty) as [Guard0 | Guard0]; try contradiction.
  destruct E as [ <-|[]].
  eapply task_step__infabs_etvar; try eassumption.
Qed.

Lemma task_list_sound_inf_tapp a b c G T :
  List.In T (task_list_inf_tapp a b c G) -> task_step a b c G T.
Proof.
  intros E.
  destruct G as [ | skip0 skip1 skip2 | G arg3]; cbn [task_list_inf_tapp] in E; try contradiction.
  destruct arg3 as [arg4 cs | skip5 skip6 | skip7 skip8 | skip9 skip10 skip11 skip12 | skip13 skip14 skip15 skip16 | skip17 skip18 skip19 | skip20 skip21 | skip22 skip23 skip24 skip25 | skip26 skip27 skip28 | skip29 skip30 skip31 skip32 skip33 | skip34 skip35 | skip36 skip37 skip38]; cbn [task_list_inf_tapp] in E; try contradiction.
  destruct arg4 as [ | skip39 | skip40 | skip41 | skip42 skip43 | skip44 | e A | skip45 skip46]; cbn [task_list_inf_tapp] in E; try contradiction.
  destruct E as [ <-|[]].
  eapply task_step__inf_tapp; try eassumption.
Qed.

Lemma task_list_sound_inftapp_all a b c G T :
  List.In T (task_list_inftapp_all a b c G) -> task_step a b c G T.
Proof.
  intros E.
  destruct G as [ | skip0 skip1 skip2 | G arg3]; cbn [task_list_inftapp_all] in E; try contradiction.
  destruct arg3 as [skip4 skip5 | skip6 skip7 | skip8 skip9 | skip10 skip11 skip12 skip13 | skip14 skip15 skip16 skip17 | arg18 B cs | skip19 skip20 | skip21 skip22 skip23 skip24 | skip25 skip26 skip27 | skip28 skip29 skip30 skip31 skip32 | skip33 skip34 | skip35 skip36 skip37]; cbn [task_list_inftapp_all] in E; try contradiction.
  destruct arg18 as [ |  |  | skip38 | skip39 | skip40 skip41 | A | skip42 skip43 | skip44 skip45]; cbn [task_list_inftapp_all] in E; try contradiction.
  destruct E as [ <-|[]].
  eapply task_step__inftapp_all; try eassumption.
Qed.

Lemma task_list_sound_inftapp_bot a b c G T :
  List.In T (task_list_inftapp_bot a b c G) -> task_step a b c G T.
Proof.
  intros E.
  destruct G as [ | skip0 skip1 skip2 | G arg3]; cbn [task_list_inftapp_bot] in E; try contradiction.
  destruct arg3 as [skip4 skip5 | skip6 skip7 | skip8 skip9 | skip10 skip11 skip12 skip13 | skip14 skip15 skip16 skip17 | arg18 B cs | skip19 skip20 | skip21 skip22 skip23 skip24 | skip25 skip26 skip27 | skip28 skip29 skip30 skip31 skip32 | skip33 skip34 | skip35 skip36 skip37]; cbn [task_list_inftapp_bot] in E; try contradiction.
  destruct arg18 as [ |  |  | skip38 | skip39 | skip40 skip41 | skip42 | skip43 skip44 | skip45 skip46]; cbn [task_list_inftapp_bot] in E; try contradiction.
  destruct E as [ <-|[]].
  eapply task_step__inftapp_bot; try eassumption.
Qed.

Lemma task_list_sound_inftapp_inter1 a b c G T :
  List.In T (task_list_inftapp_inter1 a b c G) -> task_step a b c G T.
Proof.
  intros E.
  destruct G as [ | skip0 skip1 skip2 | G arg3]; cbn [task_list_inftapp_inter1] in E; try contradiction.
  destruct arg3 as [skip4 skip5 | skip6 skip7 | skip8 skip9 | skip10 skip11 skip12 skip13 | skip14 skip15 skip16 skip17 | arg18 C cs | skip19 skip20 | skip21 skip22 skip23 skip24 | skip25 skip26 skip27 | skip28 skip29 skip30 skip31 skip32 | skip33 skip34 | skip35 skip36 skip37]; cbn [task_list_inftapp_inter1] in E; try contradiction.
  destruct arg18 as [ |  |  | skip38 | skip39 | skip40 skip41 | skip42 | skip43 skip44 | A B]; cbn [task_list_inftapp_inter1] in E; try contradiction.
  destruct E as [ <-|[]].
  eapply task_step__inftapp_inter1; try eassumption.
Qed.

Lemma task_list_sound_inftapp_inter2 a b c G T :
  List.In T (task_list_inftapp_inter2 a b c G) -> task_step a b c G T.
Proof.
  intros E.
  destruct G as [ | skip0 skip1 skip2 | G arg3]; cbn [task_list_inftapp_inter2] in E; try contradiction.
  destruct arg3 as [skip4 skip5 | skip6 skip7 | skip8 skip9 | skip10 skip11 skip12 skip13 | skip14 skip15 skip16 skip17 | arg18 C cs | skip19 skip20 | skip21 skip22 skip23 skip24 | skip25 skip26 skip27 | skip28 skip29 skip30 skip31 skip32 | skip33 skip34 | skip35 skip36 skip37]; cbn [task_list_inftapp_inter2] in E; try contradiction.
  destruct arg18 as [ |  |  | skip38 | skip39 | skip40 skip41 | skip42 | skip43 skip44 | A B]; cbn [task_list_inftapp_inter2] in E; try contradiction.
  destruct E as [ <-|[]].
  eapply task_step__inftapp_inter2; try eassumption.
Qed.

Lemma task_list_sound_inftapp_union a b c G T :
  List.In T (task_list_inftapp_union a b c G) -> task_step a b c G T.
Proof.
  intros E.
  destruct G as [ | skip0 skip1 skip2 | G arg3]; cbn [task_list_inftapp_union] in E; try contradiction.
  destruct arg3 as [skip4 skip5 | skip6 skip7 | skip8 skip9 | skip10 skip11 skip12 skip13 | skip14 skip15 skip16 skip17 | arg18 C cs | skip19 skip20 | skip21 skip22 skip23 skip24 | skip25 skip26 skip27 | skip28 skip29 skip30 skip31 skip32 | skip33 skip34 | skip35 skip36 skip37]; cbn [task_list_inftapp_union] in E; try contradiction.
  destruct arg18 as [ |  |  | skip38 | skip39 | skip40 skip41 | skip42 | A B | skip43 skip44]; cbn [task_list_inftapp_union] in E; try contradiction.
  destruct E as [ <-|[]].
  eapply task_step__inftapp_union; try eassumption.
Qed.

Lemma task_list_sound_inftappunion a b c G T :
  List.In T (task_list_inftappunion a b c G) -> task_step a b c G T.
Proof.
  intros E.
  destruct G as [ | skip0 skip1 skip2 | G arg3]; cbn [task_list_inftappunion] in E; try contradiction.
  destruct arg3 as [skip4 skip5 | skip6 skip7 | skip8 skip9 | skip10 skip11 skip12 skip13 | skip14 skip15 skip16 skip17 | skip18 skip19 skip20 | skip21 skip22 | A B C cs | skip23 skip24 skip25 | skip26 skip27 skip28 skip29 skip30 | skip31 skip32 | skip33 skip34 skip35]; cbn [task_list_inftappunion] in E; try contradiction.
  destruct E as [ <-|[]].
  eapply task_step__inftappunion; try eassumption.
Qed.

Lemma task_list_sound_unioninftapp a b c G T :
  List.In T (task_list_unioninftapp a b c G) -> task_step a b c G T.
Proof.
  intros E.
  destruct G as [ | skip0 skip1 skip2 | G arg3]; cbn [task_list_unioninftapp] in E; try contradiction.
  destruct arg3 as [skip4 skip5 | skip6 skip7 | skip8 skip9 | skip10 skip11 skip12 skip13 | skip14 skip15 skip16 skip17 | skip18 skip19 skip20 | skip21 skip22 | skip23 skip24 skip25 skip26 | A B cs | skip27 skip28 skip29 skip30 skip31 | skip32 skip33 | skip34 skip35 skip36]; cbn [task_list_unioninftapp] in E; try contradiction.
  destruct E as [ <-|[]].
  eapply task_step__unioninftapp; try eassumption.
Qed.

Lemma task_list_sound_applys a b c G T :
  List.In T (task_list_applys a b c G) -> task_step a b c G T.
Proof.
  intros E.
  destruct G as [ | skip0 skip1 skip2 | G arg3]; cbn [task_list_applys] in E; try contradiction.
  destruct arg3 as [skip4 skip5 | skip6 skip7 | skip8 skip9 | skip10 skip11 skip12 skip13 | skip14 skip15 skip16 skip17 | skip18 skip19 skip20 | skip21 skip22 | skip23 skip24 skip25 skip26 | skip27 skip28 skip29 | skip30 skip31 skip32 skip33 skip34 | cs A | skip35 skip36 skip37]; cbn [task_list_applys] in E; try contradiction.
  destruct E as [ <-|[]].
  eapply task_step__applys; try eassumption.
Qed.

Lemma task_list_sound_applyd a b c G T :
  List.In T (task_list_applyd a b c G) -> task_step a b c G T.
Proof.
  intros E.
  destruct G as [ | skip0 skip1 skip2 | G arg3]; cbn [task_list_applyd] in E; try contradiction.
  destruct arg3 as [skip4 skip5 | skip6 skip7 | skip8 skip9 | skip10 skip11 skip12 skip13 | skip14 skip15 skip16 skip17 | skip18 skip19 skip20 | skip21 skip22 | skip23 skip24 skip25 skip26 | skip27 skip28 skip29 | skip30 skip31 skip32 skip33 skip34 | skip35 skip36 | cd A B]; cbn [task_list_applyd] in E; try contradiction.
  destruct E as [ <-|[]].
  eapply task_step__applyd; try eassumption.
Qed.

Lemma task_successors_sound a b c G T :
  List.In T (task_successors a b c G) -> task_step a b c G T.
Proof.
  unfold task_successors.
  repeat rewrite concat_cons, in_app_iff.

  intros [H0|[H1|[H2|[H3|[H4|[H5|[H6|[H7|[H8|[H9|[H10|[H11|[H12|[H13|[H14|[H15|[H16|[H17|[H18|[H19|[H20|[H21|[H22|[H23|[H24|[H25|[H26|[H27|[H28|[H29|[H30|[H31|[H32|[H33|[H34|[H35|[H36|[H37|[H38|[H39|[H40|[H41|[H42|[H43|[H44|[H45|[H46|[H47|[H48|[H49|[H50|[]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]].
  - now apply task_list_sound_gc_var in H0.
  - now apply task_list_sound_sub_top in H1.
  - now apply task_list_sound_sub_bot in H2.
  - now apply task_list_sound_sub_unit in H3.
  - now apply task_list_sound_sub_tvar in H4.
  - now apply task_list_sound_subarrow in H5.
  - now apply task_list_sound_sub_alll in H6.
  - now apply task_list_sound_sub_all in H7.
  - now apply task_list_sound_sub_arrow1 in H8.
  - now apply task_list_sound_sub_arrow2 in H9.
  - now apply task_list_sound_sub_etvarmono1 in H10.
  - now apply task_list_sound_sub_etvarmono2 in H11.
  - now apply task_list_sound_sub_intersection1 in H12.
  - now apply task_list_sound_sub_intersection2 in H13.
  - now apply task_list_sound_sub_intersection3 in H14.
  - now apply task_list_sound_sub_union1 in H15.
  - now apply task_list_sound_sub_union2 in H16.
  - now apply task_list_sound_sub_union3 in H17.
  - now apply task_list_sound_chk_sub in H18.
  - now apply task_list_sound_chk_absarrow in H19.
  - now apply task_list_sound_chk_absetvar in H20.
  - now apply task_list_sound_chk_abstop in H21.
  - now apply task_list_sound_chk_inter in H22.
  - now apply task_list_sound_chk_union1 in H23.
  - now apply task_list_sound_chk_union2 in H24.
  - now apply task_list_sound_inf_var in H25.
  - now apply task_list_sound_inf_anno in H26.
  - now apply task_list_sound_inf_tabs in H27.
  - now apply task_list_sound_inf_abs_mono in H28.
  - now apply task_list_sound_inf_unit in H29.
  - now apply task_list_sound_inf_app in H30.
  - now apply task_list_sound_infapp in H31.
  - now apply task_list_sound_infabs_arr in H32.
  - now apply task_list_sound_infabs_bot in H33.
  - now apply task_list_sound_infabs_all in H34.
  - now apply task_list_sound_infabs_inter1 in H35.
  - now apply task_list_sound_infabs_inter2 in H36.
  - now apply task_list_sound_infabs_union in H37.
  - now apply task_list_sound_infabsunion in H38.
  - now apply task_list_sound_unioninfabs in H39.
  - now apply task_list_sound_infabs_etvar in H40.
  - now apply task_list_sound_inf_tapp in H41.
  - now apply task_list_sound_inftapp_all in H42.
  - now apply task_list_sound_inftapp_bot in H43.
  - now apply task_list_sound_inftapp_inter1 in H44.
  - now apply task_list_sound_inftapp_inter2 in H45.
  - now apply task_list_sound_inftapp_union in H46.
  - now apply task_list_sound_inftappunion in H47.
  - now apply task_list_sound_unioninftapp in H48.
  - now apply task_list_sound_applys in H49.
  - now apply task_list_sound_applyd in H50.
Qed.

Lemma task_successors_complete a b c G T :
  task_step a b c G T -> List.In T (task_successors a b c G).
Proof.
  destruct 1; unfold task_successors; apply in_concat.
  - exists (task_list_gc_var a b c (aworklist_cons_var G X d)); split.
    + cbn [List.In]. left; reflexivity.
    + cbn [task_list_gc_var].
      now left.
  - exists (task_list_sub_top a b c (aworklist_cons_work G (work_sub A typ_top))); split.
    + cbn [List.In]. do 1 right. left; reflexivity.
    + cbn [task_list_sub_top].
      now left.
  - exists (task_list_sub_bot a b c (aworklist_cons_work G (work_sub typ_bot A))); split.
    + cbn [List.In]. do 2 right. left; reflexivity.
    + cbn [task_list_sub_bot].
      now left.
  - exists (task_list_sub_unit a b c (aworklist_cons_work G (work_sub typ_unit typ_unit))); split.
    + cbn [List.In]. do 3 right. left; reflexivity.
    + cbn [task_list_sub_unit].
      now left.
  - exists (task_list_sub_tvar a b c (aworklist_cons_work G (work_sub (typ_var_f X) (typ_var_f Y)))); split.
    + cbn [List.In]. do 4 right. left; reflexivity.
    + cbn [task_list_sub_tvar].
      destruct (task_eq X Y); try contradiction.
      now left.
  - exists (task_list_subarrow a b c (aworklist_cons_work G (work_sub (typ_arrow A B) (typ_arrow C D)))); split.
    + cbn [List.In]. do 5 right. left; reflexivity.
    + cbn [task_list_subarrow].
      now left.
  - exists (task_list_sub_alll a b c (aworklist_cons_work G (work_sub (typ_all A) B))); split.
    + cbn [List.In]. do 6 right. left; reflexivity.
    + cbn [task_list_sub_alll].
      destruct (task_wneq_dec G B); try contradiction.
      now left.
  - exists (task_list_sub_all a b c (aworklist_cons_work G (work_sub (typ_all A) (typ_all B)))); split.
    + cbn [List.In]. do 7 right. left; reflexivity.
    + cbn [task_list_sub_all].
      now left.
  - exists (task_list_sub_arrow1 a b c (aworklist_cons_work G (work_sub (typ_var_f X) (typ_arrow A B)))); split.
    + cbn [List.In]. do 8 right. left; reflexivity.
    + cbn [task_list_sub_arrow1].
      destruct (task_binding_dec G X abind_etvar_empty); try contradiction.
      destruct (task_mono_dec G (typ_arrow A B)); try contradiction.
      now left.
  - exists (task_list_sub_arrow2 a b c (aworklist_cons_work G (work_sub (typ_arrow A B) (typ_var_f X)))); split.
    + cbn [List.In]. do 9 right. left; reflexivity.
    + cbn [task_list_sub_arrow2].
      destruct (task_binding_dec G X abind_etvar_empty); try contradiction.
      destruct (task_mono_dec G (typ_arrow A B)); try contradiction.
      now left.
  - exists (task_list_sub_etvarmono1 a b c (aworklist_cons_work G (work_sub A (typ_var_f X)))); split.
    + cbn [List.In]. do 10 right. left; reflexivity.
    + cbn [task_list_sub_etvarmono1].
      destruct (task_binding_dec G X abind_etvar_empty); try contradiction.
      destruct (task_mono_dec G A); try contradiction.
      rewrite (proj2 (task_mem_false X (ftvar_in_typ A)) ltac:(assumption)).
      match goal with E : task_solution _ _ _ = Some _ |- _ => rewrite E end.
      now left.
  - exists (task_list_sub_etvarmono2 a b c (aworklist_cons_work G (work_sub (typ_var_f X) A))); split.
    + cbn [List.In]. do 11 right. left; reflexivity.
    + cbn [task_list_sub_etvarmono2].
      destruct (task_binding_dec G X abind_etvar_empty); try contradiction.
      destruct (task_mono_dec G A); try contradiction.
      rewrite (proj2 (task_mem_false X (ftvar_in_typ A)) ltac:(assumption)).
      match goal with E : task_solution _ _ _ = Some _ |- _ => rewrite E end.
      now left.
  - exists (task_list_sub_intersection1 a b c (aworklist_cons_work G (work_sub A (typ_intersection B C)))); split.
    + cbn [List.In]. do 12 right. left; reflexivity.
    + cbn [task_list_sub_intersection1].
      now left.
  - exists (task_list_sub_intersection2 a b c (aworklist_cons_work G (work_sub (typ_intersection A B) C))); split.
    + cbn [List.In]. do 13 right. left; reflexivity.
    + cbn [task_list_sub_intersection2].
      now left.
  - exists (task_list_sub_intersection3 a b c (aworklist_cons_work G (work_sub (typ_intersection A B) C))); split.
    + cbn [List.In]. do 14 right. left; reflexivity.
    + cbn [task_list_sub_intersection3].
      now left.
  - exists (task_list_sub_union1 a b c (aworklist_cons_work G (work_sub A (typ_union B C)))); split.
    + cbn [List.In]. do 15 right. left; reflexivity.
    + cbn [task_list_sub_union1].
      now left.
  - exists (task_list_sub_union2 a b c (aworklist_cons_work G (work_sub A (typ_union B C)))); split.
    + cbn [List.In]. do 16 right. left; reflexivity.
    + cbn [task_list_sub_union2].
      now left.
  - exists (task_list_sub_union3 a b c (aworklist_cons_work G (work_sub (typ_union A B) C))); split.
    + cbn [List.In]. do 17 right. left; reflexivity.
    + cbn [task_list_sub_union3].
      now left.
  - exists (task_list_chk_sub a b c (aworklist_cons_work G (work_check e A))); split.
    + cbn [List.In]. do 18 right. left; reflexivity.
    + cbn [task_list_chk_sub].
      now left.
  - exists (task_list_chk_absarrow a b c (aworklist_cons_work G (work_check (exp_abs e) (typ_arrow A B)))); split.
    + cbn [List.In]. do 19 right. left; reflexivity.
    + cbn [task_list_chk_absarrow].
      now left.
  - exists (task_list_chk_absetvar a b c (aworklist_cons_work G (work_check (exp_abs e) (typ_var_f X)))); split.
    + cbn [List.In]. do 20 right. left; reflexivity.
    + cbn [task_list_chk_absetvar].
      destruct (task_binding_dec G X abind_etvar_empty); try contradiction.
      now left.
  - exists (task_list_chk_abstop a b c (aworklist_cons_work G (work_check (exp_abs e) typ_top))); split.
    + cbn [List.In]. do 21 right. left; reflexivity.
    + cbn [task_list_chk_abstop].
      now left.
  - exists (task_list_chk_inter a b c (aworklist_cons_work G (work_check e (typ_intersection A B)))); split.
    + cbn [List.In]. do 22 right. left; reflexivity.
    + cbn [task_list_chk_inter].
      now left.
  - exists (task_list_chk_union1 a b c (aworklist_cons_work G (work_check e (typ_union A B)))); split.
    + cbn [List.In]. do 23 right. left; reflexivity.
    + cbn [task_list_chk_union1].
      now left.
  - exists (task_list_chk_union2 a b c (aworklist_cons_work G (work_check e (typ_union A B)))); split.
    + cbn [List.In]. do 24 right. left; reflexivity.
    + cbn [task_list_chk_union2].
      now left.
  - exists (task_list_inf_var a b c (aworklist_cons_work G (work_infer (exp_var_f X) cs))); split.
    + cbn [List.In]. do 25 right. left; reflexivity.
    + cbn [task_list_inf_var].
      apply in_map_iff. exists A. split; [reflexivity|now apply task_lookup_spec].
  - exists (task_list_inf_anno a b c (aworklist_cons_work G (work_infer (exp_anno e A) cs))); split.
    + cbn [List.In]. do 26 right. left; reflexivity.
    + cbn [task_list_inf_anno].
      now left.
  - exists (task_list_inf_tabs a b c (aworklist_cons_work G (work_infer (exp_tabs (exp_anno e A)) cs))); split.
    + cbn [List.In]. do 27 right. left; reflexivity.
    + cbn [task_list_inf_tabs].
      now left.
  - exists (task_list_inf_abs_mono a b c (aworklist_cons_work G (work_infer (exp_abs e) cs))); split.
    + cbn [List.In]. do 28 right. left; reflexivity.
    + cbn [task_list_inf_abs_mono].
      now left.
  - exists (task_list_inf_unit a b c (aworklist_cons_work G (work_infer exp_unit cs))); split.
    + cbn [List.In]. do 29 right. left; reflexivity.
    + cbn [task_list_inf_unit].
      now left.
  - exists (task_list_inf_app a b c (aworklist_cons_work G (work_infer (exp_app e f) cs))); split.
    + cbn [List.In]. do 30 right. left; reflexivity.
    + cbn [task_list_inf_app].
      now left.
  - exists (task_list_infapp a b c (aworklist_cons_work G (work_infapp A B e cs))); split.
    + cbn [List.In]. do 31 right. left; reflexivity.
    + cbn [task_list_infapp].
      now left.
  - exists (task_list_infabs_arr a b c (aworklist_cons_work G (work_infabs (typ_arrow A B) cd))); split.
    + cbn [List.In]. do 32 right. left; reflexivity.
    + cbn [task_list_infabs_arr].
      now left.
  - exists (task_list_infabs_bot a b c (aworklist_cons_work G (work_infabs typ_bot cd))); split.
    + cbn [List.In]. do 33 right. left; reflexivity.
    + cbn [task_list_infabs_bot].
      now left.
  - exists (task_list_infabs_all a b c (aworklist_cons_work G (work_infabs (typ_all A) cd))); split.
    + cbn [List.In]. do 34 right. left; reflexivity.
    + cbn [task_list_infabs_all].
      now left.
  - exists (task_list_infabs_inter1 a b c (aworklist_cons_work G (work_infabs (typ_intersection A B) cd))); split.
    + cbn [List.In]. do 35 right. left; reflexivity.
    + cbn [task_list_infabs_inter1].
      now left.
  - exists (task_list_infabs_inter2 a b c (aworklist_cons_work G (work_infabs (typ_intersection A B) cd))); split.
    + cbn [List.In]. do 36 right. left; reflexivity.
    + cbn [task_list_infabs_inter2].
      now left.
  - exists (task_list_infabs_union a b c (aworklist_cons_work G (work_infabs (typ_union A B) cd))); split.
    + cbn [List.In]. do 37 right. left; reflexivity.
    + cbn [task_list_infabs_union].
      now left.
  - exists (task_list_infabsunion a b c (aworklist_cons_work G (work_infabsunion A B C cd))); split.
    + cbn [List.In]. do 38 right. left; reflexivity.
    + cbn [task_list_infabsunion].
      now left.
  - exists (task_list_unioninfabs a b c (aworklist_cons_work G (work_unioninfabs A B C D cd))); split.
    + cbn [List.In]. do 39 right. left; reflexivity.
    + cbn [task_list_unioninfabs].
      now left.
  - exists (task_list_infabs_etvar a b c (aworklist_cons_work G (work_infabs (typ_var_f X) cd))); split.
    + cbn [List.In]. do 40 right. left; reflexivity.
    + cbn [task_list_infabs_etvar].
      destruct (task_binding_dec G X abind_etvar_empty); try contradiction.
      now left.
  - exists (task_list_inf_tapp a b c (aworklist_cons_work G (work_infer (exp_tapp e A) cs))); split.
    + cbn [List.In]. do 41 right. left; reflexivity.
    + cbn [task_list_inf_tapp].
      now left.
  - exists (task_list_inftapp_all a b c (aworklist_cons_work G (work_inftapp (typ_all A) B cs))); split.
    + cbn [List.In]. do 42 right. left; reflexivity.
    + cbn [task_list_inftapp_all].
      now left.
  - exists (task_list_inftapp_bot a b c (aworklist_cons_work G (work_inftapp typ_bot B cs))); split.
    + cbn [List.In]. do 43 right. left; reflexivity.
    + cbn [task_list_inftapp_bot].
      now left.
  - exists (task_list_inftapp_inter1 a b c (aworklist_cons_work G (work_inftapp (typ_intersection A B) C cs))); split.
    + cbn [List.In]. do 44 right. left; reflexivity.
    + cbn [task_list_inftapp_inter1].
      now left.
  - exists (task_list_inftapp_inter2 a b c (aworklist_cons_work G (work_inftapp (typ_intersection A B) C cs))); split.
    + cbn [List.In]. do 45 right. left; reflexivity.
    + cbn [task_list_inftapp_inter2].
      now left.
  - exists (task_list_inftapp_union a b c (aworklist_cons_work G (work_inftapp (typ_union A B) C cs))); split.
    + cbn [List.In]. do 46 right. left; reflexivity.
    + cbn [task_list_inftapp_union].
      now left.
  - exists (task_list_inftappunion a b c (aworklist_cons_work G (work_inftappunion A B C cs))); split.
    + cbn [List.In]. do 47 right. left; reflexivity.
    + cbn [task_list_inftappunion].
      now left.
  - exists (task_list_unioninftapp a b c (aworklist_cons_work G (work_unioninftapp A B cs))); split.
    + cbn [List.In]. do 48 right. left; reflexivity.
    + cbn [task_list_unioninftapp].
      now left.
  - exists (task_list_applys a b c (aworklist_cons_work G (work_applys cs A))); split.
    + cbn [List.In]. do 49 right. left; reflexivity.
    + cbn [task_list_applys].
      now left.
  - exists (task_list_applyd a b c (aworklist_cons_work G (work_applyd cd A B))); split.
    + cbn [List.In]. do 50 right. left; reflexivity.
    + cbn [task_list_applyd].
      now left.
Qed.

Lemma task_fresh_new_holes R G w a b c :
  uniq (awl_to_aenv G) ->
  task_fresh3 (task_names_state R (aworklist_cons_work G w)) a b c ->
  uniq (awl_to_aenv (task_new_holes G a b)).
Proof.
  intros U [Fa [Fb Fc]].
  unfold task_names_state in Fa,Fb; simpl in Fa,Fb.
  pose proof (task_names_dom G) as D.
  change (uniq ((b,abind_etvar_empty) :: (a,abind_etvar_empty) :: awl_to_aenv G)).
  apply uniq_cons.
  - apply uniq_cons; [exact U|fsetdec].
  - simpl; fsetdec.
Qed.

Local Ltac task_rewrite_fixed H :=
  repeat match goal with
  | E : task_rename_aworklist _ _ = _ |- _ => progress rewrite ?E in H
  | E : task_rename_typ _ _ = _ |- _ => progress rewrite ?E in H
  | E : task_rename_exp _ _ = _ |- _ => progress rewrite ?E in H
  | E : task_rename_conts _ _ = _ |- _ => progress rewrite ?E in H
  | E : task_rename_contd _ _ = _ |- _ => progress rewrite ?E in H
  | E : ?f ?x = ?x |- _ => is_var f; is_var x; progress rewrite ?E in H
  end.

Definition task_cof_sub_alll G A B (a b c : atom) : Prop :=
  a_wl_red (aworklist_cons_work (aworklist_cons_var G a abind_etvar_empty) (work_sub (open_typ_wrt_typ A (typ_var_f a)) B)).

Lemma task_cof_sub_alll_stable R G A B :
  task_stable (task_names_state R (aworklist_cons_work G (work_sub (typ_all A) B))) (task_cof_sub_alll G A B).
Proof.
  unfold task_stable, task_names_state, task_cof_sub_alll, task_arrow, task_new_holes.
  intros p I Fixed a b c H.
  assert (Fix_G : task_rename_aworklist p G = G) by (apply task_rename_aworklist_fixed; intros; apply Fixed; simpl; fsetdec).
  assert (Fix_A : task_rename_typ p A = A) by (apply task_rename_typ_fixed; intros; apply Fixed; simpl; fsetdec).
  assert (Fix_B : task_rename_typ p B = B) by (apply task_rename_typ_fixed; intros; apply Fixed; simpl; fsetdec).
  apply (task_rename_red p I) in H.
  task_rename_normalize H; task_rewrite_fixed H; exact H.
Qed.

Lemma task_cof_sub_alll_choices R G A B a b c :
  task_fresh3 (task_names_state R (aworklist_cons_work G (work_sub (typ_all A) B))) a b c ->
  ((exists L, forall a, a `notin` L -> task_cof_sub_alll G A B a b c) <-> task_cof_sub_alll G A B a b c).
Proof.
  intro F. split.
  - intros [L H]. eapply task_stable_elim; [apply task_cof_sub_alll_stable|exact F|].
    exists L. intros u v w [Fu [Fv Fw]].
    exact (H u ltac:(task_atomic)).
  - intro H.
    exists (task_names_state R (aworklist_cons_work G (work_sub (typ_all A) B))).
    intros u Fu.
    destruct (task_pick3 (add u (task_names_state R (aworklist_cons_work G (work_sub (typ_all A) B))))) as [ [ [v w] p] [F1 [F2 F3]]].
    eapply (task_stable_intro (task_names_state R (aworklist_cons_work G (work_sub (typ_all A) B))) (task_cof_sub_alll G A B) a b c ltac:(apply task_cof_sub_alll_stable) F H u v w);
      repeat split; task_atomic.
Qed.

Definition task_cof_sub_all G A B (a b c : atom) : Prop :=
  a_wl_red (aworklist_cons_work (aworklist_cons_var G c abind_stvar_empty) (work_sub (open_typ_wrt_typ A (typ_var_f c)) (open_typ_wrt_typ B (typ_var_f c)))).

Lemma task_cof_sub_all_stable R G A B :
  task_stable (task_names_state R (aworklist_cons_work G (work_sub (typ_all A) (typ_all B)))) (task_cof_sub_all G A B).
Proof.
  unfold task_stable, task_names_state, task_cof_sub_all, task_arrow, task_new_holes.
  intros p I Fixed a b c H.
  assert (Fix_G : task_rename_aworklist p G = G) by (apply task_rename_aworklist_fixed; intros; apply Fixed; simpl; fsetdec).
  assert (Fix_A : task_rename_typ p A = A) by (apply task_rename_typ_fixed; intros; apply Fixed; simpl; fsetdec).
  assert (Fix_B : task_rename_typ p B = B) by (apply task_rename_typ_fixed; intros; apply Fixed; simpl; fsetdec).
  apply (task_rename_red p I) in H.
  task_rename_normalize H; task_rewrite_fixed H; exact H.
Qed.

Lemma task_cof_sub_all_choices R G A B a b c :
  task_fresh3 (task_names_state R (aworklist_cons_work G (work_sub (typ_all A) (typ_all B)))) a b c ->
  ((exists L, forall c, c `notin` L -> task_cof_sub_all G A B a b c) <-> task_cof_sub_all G A B a b c).
Proof.
  intro F. split.
  - intros [L H]. eapply task_stable_elim; [apply task_cof_sub_all_stable|exact F|].
    exists L. intros u v w [Fu [Fv Fw]].
    exact (H w ltac:(task_atomic)).
  - intro H.
    exists (task_names_state R (aworklist_cons_work G (work_sub (typ_all A) (typ_all B)))).
    intros w Fw.
    destruct (task_pick3 (add w (task_names_state R (aworklist_cons_work G (work_sub (typ_all A) (typ_all B)))))) as [ [ [u v] p] [F1 [F2 F3]]].
    eapply (task_stable_intro (task_names_state R (aworklist_cons_work G (work_sub (typ_all A) (typ_all B)))) (task_cof_sub_all G A B) a b c ltac:(apply task_cof_sub_all_stable) F H u v w);
      repeat split; task_atomic.
Qed.

Definition task_cof_sub_arrow1 G X A B (a b c : atom) : Prop :=
  forall P K, aworklist_subst (aworklist_cons_work (task_new_holes G a b) (work_sub (typ_var_f X) (typ_arrow A B))) X (task_arrow a b) P K ->
    a_wl_red (awl_app (subst_typ_in_aworklist (task_arrow a b) X K) P).

Lemma task_cof_sub_arrow1_stable R G X A B :
  task_stable (task_names_state R (aworklist_cons_work G (work_sub (typ_var_f X) (typ_arrow A B)))) (task_cof_sub_arrow1 G X A B).
Proof.
  unfold task_stable, task_names_state, task_cof_sub_arrow1, task_arrow, task_new_holes.
  intros p I Fixed a b c H.
  assert (Fix_G : task_rename_aworklist p G = G) by (apply task_rename_aworklist_fixed; intros; apply Fixed; simpl; fsetdec).
  assert (Fix_X : p X = X) by (apply Fixed; simpl; fsetdec).
  assert (Fix_A : task_rename_typ p A = A) by (apply task_rename_typ_fixed; intros; apply Fixed; simpl; fsetdec).
  assert (Fix_B : task_rename_typ p B = B) by (apply task_rename_typ_fixed; intros; apply Fixed; simpl; fsetdec).
  intros P K HS.
  pose proof (task_rename_awl_subst p I _ _ _ _ _ HS) as H'.
  task_rename_normalize H'; task_rewrite_fixed H'.
  specialize (H (task_rename_aworklist p P) (task_rename_aworklist p K) H').
  apply (task_rename_red p I) in H.
  task_rename_normalize H; task_rewrite_fixed H; exact H.
Qed.

Lemma task_cof_sub_arrow1_compact R G X A B a b c :
  uniq (awl_to_aenv G) -> task_fresh3 (task_names_state R (aworklist_cons_work G (work_sub (typ_var_f X) (typ_arrow A B)))) a b c ->
  (task_cof_sub_arrow1 G X A B a b c <-> a_wl_red (match (task_solution (task_new_holes G a b) X (task_arrow a b)) with Some T => (aworklist_cons_work (aworklist_cons_work T (work_sub (subst_typ_in_typ (task_arrow a b) X A) (typ_var_f a))) (work_sub (typ_var_f b) (subst_typ_in_typ (task_arrow a b) X B))) | None => aworklist_empty end)).
Proof.
  intros U Fresh.
  pose proof (task_fresh_new_holes R G (work_sub (typ_var_f X) (typ_arrow A B)) a b c U Fresh) as U'.
  unfold task_cof_sub_arrow1.
  assert (Fa : a <> X) by (destruct Fresh as [F _]; unfold task_names_state in F; simpl in F; intro; subst; fsetdec).
  assert (Fb : b <> X) by (destruct Fresh as [_ [F _]]; unfold task_names_state in F; simpl in F; intro; subst; fsetdec).
  pose proof (task_solution_red (task_new_holes G a b) X (task_arrow a b)
    (fun T => (aworklist_cons_work (aworklist_cons_work T (work_sub (subst_typ_in_typ (task_arrow a b) X A) (typ_var_f a))) (work_sub (typ_var_f b) (subst_typ_in_typ (task_arrow a b) X B)))) U') as Equiv.
  apply iff_sym in Equiv. rewrite <- Equiv.
  split; intros H P K HS.
  - specialize (H P (aworklist_cons_work K (work_sub (typ_var_f X) (typ_arrow A B))) ltac:(repeat constructor; exact HS)).
    cbn [subst_typ_in_aworklist subst_typ_in_work subst_typ_in_abind awl_app] in H.
    rewrite task_subst_same_var in H. apply task_red_arrow in H. exact H.
  - apply task_subst_top_work in HS as [J [ -> HS]].
    specialize (H P J HS).
    cbn [subst_typ_in_aworklist subst_typ_in_work subst_typ_in_abind awl_app].
    rewrite task_subst_same_var. now apply task_red_arrow.
Qed.

Lemma task_cof_sub_arrow1_choices R G X A B a b c :
  task_fresh3 (task_names_state R (aworklist_cons_work G (work_sub (typ_var_f X) (typ_arrow A B)))) a b c ->
  ((exists L, forall a, a `notin` L -> forall b, b `notin` (union L (singleton a)) -> task_cof_sub_arrow1 G X A B a b c) <-> task_cof_sub_arrow1 G X A B a b c).
Proof.
  intro F. split.
  - intros [L H]. eapply task_stable_elim; [apply task_cof_sub_arrow1_stable|exact F|].
    exists L. intros u v w [Fu [Fv Fw]].
    exact (H u ltac:(task_atomic) v ltac:(task_atomic)).
  - intro H.
    exists (task_names_state R (aworklist_cons_work G (work_sub (typ_var_f X) (typ_arrow A B)))).
    intros u Fu v Fv.
    destruct (task_pick3 (add v (add u (task_names_state R (aworklist_cons_work G (work_sub (typ_var_f X) (typ_arrow A B))))))) as [ [ [w p] q] [F1 [F2 F3]]].
    eapply (task_stable_intro (task_names_state R (aworklist_cons_work G (work_sub (typ_var_f X) (typ_arrow A B)))) (task_cof_sub_arrow1 G X A B) a b c ltac:(apply task_cof_sub_arrow1_stable) F H u v w);
      repeat split; task_atomic.
Qed.

Definition task_cof_sub_arrow2 G A B X (a b c : atom) : Prop :=
  forall P K, aworklist_subst (aworklist_cons_work (task_new_holes G a b) (work_sub (typ_arrow A B) (typ_var_f X))) X (task_arrow a b) P K ->
    a_wl_red (awl_app (subst_typ_in_aworklist (task_arrow a b) X K) P).

Lemma task_cof_sub_arrow2_stable R G A B X :
  task_stable (task_names_state R (aworklist_cons_work G (work_sub (typ_arrow A B) (typ_var_f X)))) (task_cof_sub_arrow2 G A B X).
Proof.
  unfold task_stable, task_names_state, task_cof_sub_arrow2, task_arrow, task_new_holes.
  intros p I Fixed a b c H.
  assert (Fix_G : task_rename_aworklist p G = G) by (apply task_rename_aworklist_fixed; intros; apply Fixed; simpl; fsetdec).
  assert (Fix_A : task_rename_typ p A = A) by (apply task_rename_typ_fixed; intros; apply Fixed; simpl; fsetdec).
  assert (Fix_B : task_rename_typ p B = B) by (apply task_rename_typ_fixed; intros; apply Fixed; simpl; fsetdec).
  assert (Fix_X : p X = X) by (apply Fixed; simpl; fsetdec).
  intros P K HS.
  pose proof (task_rename_awl_subst p I _ _ _ _ _ HS) as H'.
  task_rename_normalize H'; task_rewrite_fixed H'.
  specialize (H (task_rename_aworklist p P) (task_rename_aworklist p K) H').
  apply (task_rename_red p I) in H.
  task_rename_normalize H; task_rewrite_fixed H; exact H.
Qed.

Lemma task_cof_sub_arrow2_compact R G A B X a b c :
  uniq (awl_to_aenv G) -> task_fresh3 (task_names_state R (aworklist_cons_work G (work_sub (typ_arrow A B) (typ_var_f X)))) a b c ->
  (task_cof_sub_arrow2 G A B X a b c <-> a_wl_red (match (task_solution (task_new_holes G a b) X (task_arrow a b)) with Some T => (aworklist_cons_work (aworklist_cons_work T (work_sub (typ_var_f a) (subst_typ_in_typ (task_arrow a b) X A))) (work_sub (subst_typ_in_typ (task_arrow a b) X B) (typ_var_f b))) | None => aworklist_empty end)).
Proof.
  intros U Fresh.
  pose proof (task_fresh_new_holes R G (work_sub (typ_arrow A B) (typ_var_f X)) a b c U Fresh) as U'.
  unfold task_cof_sub_arrow2.
  assert (Fa : a <> X) by (destruct Fresh as [F _]; unfold task_names_state in F; simpl in F; intro; subst; fsetdec).
  assert (Fb : b <> X) by (destruct Fresh as [_ [F _]]; unfold task_names_state in F; simpl in F; intro; subst; fsetdec).
  pose proof (task_solution_red (task_new_holes G a b) X (task_arrow a b)
    (fun T => (aworklist_cons_work (aworklist_cons_work T (work_sub (typ_var_f a) (subst_typ_in_typ (task_arrow a b) X A))) (work_sub (subst_typ_in_typ (task_arrow a b) X B) (typ_var_f b)))) U') as Equiv.
  apply iff_sym in Equiv. rewrite <- Equiv.
  split; intros H P K HS.
  - specialize (H P (aworklist_cons_work K (work_sub (typ_arrow A B) (typ_var_f X))) ltac:(repeat constructor; exact HS)).
    cbn [subst_typ_in_aworklist subst_typ_in_work subst_typ_in_abind awl_app] in H.
    rewrite task_subst_same_var in H. apply task_red_arrow in H. exact H.
  - apply task_subst_top_work in HS as [J [ -> HS]].
    specialize (H P J HS).
    cbn [subst_typ_in_aworklist subst_typ_in_work subst_typ_in_abind awl_app].
    rewrite task_subst_same_var. now apply task_red_arrow.
Qed.

Lemma task_cof_sub_arrow2_choices R G A B X a b c :
  task_fresh3 (task_names_state R (aworklist_cons_work G (work_sub (typ_arrow A B) (typ_var_f X)))) a b c ->
  ((exists L, forall a, a `notin` L -> forall b, b `notin` (union L (singleton a)) -> task_cof_sub_arrow2 G A B X a b c) <-> task_cof_sub_arrow2 G A B X a b c).
Proof.
  intro F. split.
  - intros [L H]. eapply task_stable_elim; [apply task_cof_sub_arrow2_stable|exact F|].
    exists L. intros u v w [Fu [Fv Fw]].
    exact (H u ltac:(task_atomic) v ltac:(task_atomic)).
  - intro H.
    exists (task_names_state R (aworklist_cons_work G (work_sub (typ_arrow A B) (typ_var_f X)))).
    intros u Fu v Fv.
    destruct (task_pick3 (add v (add u (task_names_state R (aworklist_cons_work G (work_sub (typ_arrow A B) (typ_var_f X))))))) as [ [ [w p] q] [F1 [F2 F3]]].
    eapply (task_stable_intro (task_names_state R (aworklist_cons_work G (work_sub (typ_arrow A B) (typ_var_f X)))) (task_cof_sub_arrow2 G A B X) a b c ltac:(apply task_cof_sub_arrow2_stable) F H u v w);
      repeat split; task_atomic.
Qed.

Definition task_cof_chk_absarrow G e A B (a b c : atom) : Prop :=
  a_wl_red (aworklist_cons_work (aworklist_cons_var G c (abind_var_typ A)) (work_check (open_exp_wrt_exp e (exp_var_f c)) B)).

Lemma task_cof_chk_absarrow_stable R G e A B :
  task_stable (task_names_state R (aworklist_cons_work G (work_check (exp_abs e) (typ_arrow A B)))) (task_cof_chk_absarrow G e A B).
Proof.
  unfold task_stable, task_names_state, task_cof_chk_absarrow, task_arrow, task_new_holes.
  intros p I Fixed a b c H.
  assert (Fix_G : task_rename_aworklist p G = G) by (apply task_rename_aworklist_fixed; intros; apply Fixed; simpl; fsetdec).
  assert (Fix_e : task_rename_exp p e = e) by (apply task_rename_exp_fixed; intros; apply Fixed; simpl; fsetdec).
  assert (Fix_A : task_rename_typ p A = A) by (apply task_rename_typ_fixed; intros; apply Fixed; simpl; fsetdec).
  assert (Fix_B : task_rename_typ p B = B) by (apply task_rename_typ_fixed; intros; apply Fixed; simpl; fsetdec).
  apply (task_rename_red p I) in H.
  task_rename_normalize H; task_rewrite_fixed H; exact H.
Qed.

Lemma task_cof_chk_absarrow_choices R G e A B a b c :
  task_fresh3 (task_names_state R (aworklist_cons_work G (work_check (exp_abs e) (typ_arrow A B)))) a b c ->
  ((exists L, forall c, c `notin` L -> task_cof_chk_absarrow G e A B a b c) <-> task_cof_chk_absarrow G e A B a b c).
Proof.
  intro F. split.
  - intros [L H]. eapply task_stable_elim; [apply task_cof_chk_absarrow_stable|exact F|].
    exists L. intros u v w [Fu [Fv Fw]].
    exact (H w ltac:(task_atomic)).
  - intro H.
    exists (task_names_state R (aworklist_cons_work G (work_check (exp_abs e) (typ_arrow A B)))).
    intros w Fw.
    destruct (task_pick3 (add w (task_names_state R (aworklist_cons_work G (work_check (exp_abs e) (typ_arrow A B)))))) as [ [ [u v] p] [F1 [F2 F3]]].
    eapply (task_stable_intro (task_names_state R (aworklist_cons_work G (work_check (exp_abs e) (typ_arrow A B)))) (task_cof_chk_absarrow G e A B) a b c ltac:(apply task_cof_chk_absarrow_stable) F H u v w);
      repeat split; task_atomic.
Qed.

Definition task_cof_chk_absetvar G e X (a b c : atom) : Prop :=
  forall P K, aworklist_subst (aworklist_cons_work (aworklist_cons_var (task_new_holes G a b) c (abind_var_typ (typ_var_f a))) (work_check (open_exp_wrt_exp e (exp_var_f c)) (typ_var_f b))) X (task_arrow a b) P K ->
    a_wl_red (awl_app (subst_typ_in_aworklist (task_arrow a b) X K) P).

Lemma task_cof_chk_absetvar_stable R G e X :
  task_stable (task_names_state R (aworklist_cons_work G (work_check (exp_abs e) (typ_var_f X)))) (task_cof_chk_absetvar G e X).
Proof.
  unfold task_stable, task_names_state, task_cof_chk_absetvar, task_arrow, task_new_holes.
  intros p I Fixed a b c H.
  assert (Fix_G : task_rename_aworklist p G = G) by (apply task_rename_aworklist_fixed; intros; apply Fixed; simpl; fsetdec).
  assert (Fix_e : task_rename_exp p e = e) by (apply task_rename_exp_fixed; intros; apply Fixed; simpl; fsetdec).
  assert (Fix_X : p X = X) by (apply Fixed; simpl; fsetdec).
  intros P K HS.
  pose proof (task_rename_awl_subst p I _ _ _ _ _ HS) as H'.
  task_rename_normalize H'; task_rewrite_fixed H'.
  specialize (H (task_rename_aworklist p P) (task_rename_aworklist p K) H').
  apply (task_rename_red p I) in H.
  task_rename_normalize H; task_rewrite_fixed H; exact H.
Qed.

Lemma task_cof_chk_absetvar_compact R G e X a b c :
  uniq (awl_to_aenv G) -> task_fresh3 (task_names_state R (aworklist_cons_work G (work_check (exp_abs e) (typ_var_f X)))) a b c ->
  (task_cof_chk_absetvar G e X a b c <-> a_wl_red (match (task_solution (task_new_holes G a b) X (task_arrow a b)) with Some T => (aworklist_cons_work (aworklist_cons_var T c (abind_var_typ (typ_var_f a))) (work_check (subst_typ_in_exp (task_arrow a b) X (open_exp_wrt_exp e (exp_var_f c))) (typ_var_f b))) | None => aworklist_empty end)).
Proof.
  intros U Fresh.
  pose proof (task_fresh_new_holes R G (work_check (exp_abs e) (typ_var_f X)) a b c U Fresh) as U'.
  unfold task_cof_chk_absetvar.
  assert (Fa : a <> X) by (destruct Fresh as [F _]; unfold task_names_state in F; simpl in F; intro; subst; fsetdec).
  assert (Fb : b <> X) by (destruct Fresh as [_ [F _]]; unfold task_names_state in F; simpl in F; intro; subst; fsetdec).
  pose proof (task_solution_red (task_new_holes G a b) X (task_arrow a b)
    (fun T => (aworklist_cons_work (aworklist_cons_var T c (abind_var_typ (typ_var_f a))) (work_check (subst_typ_in_exp (task_arrow a b) X (open_exp_wrt_exp e (exp_var_f c))) (typ_var_f b)))) U') as Equiv.
  apply iff_sym in Equiv. rewrite <- Equiv.
  split; intros H P K HS.
  - specialize (H P (aworklist_cons_work (aworklist_cons_var K c (abind_var_typ (typ_var_f a))) (work_check (open_exp_wrt_exp e (exp_var_f c)) (typ_var_f b))) ltac:(repeat constructor; exact HS)).
    cbn [subst_typ_in_aworklist subst_typ_in_work subst_typ_in_abind awl_app] in H.
    rewrite !task_subst_other_var in H by congruence. exact H.
  - apply task_subst_top_work in HS as [J [ -> HS]].
    apply task_subst_top_term in HS as [K [ -> HS]].
    specialize (H P K HS).
    cbn [subst_typ_in_aworklist subst_typ_in_work subst_typ_in_abind awl_app].
    rewrite !task_subst_other_var by congruence. exact H.
Qed.

Lemma task_cof_chk_absetvar_choices R G e X a b c :
  task_fresh3 (task_names_state R (aworklist_cons_work G (work_check (exp_abs e) (typ_var_f X)))) a b c ->
  ((exists L, forall c, c `notin` L -> forall a, a `notin` (union L (singleton c)) -> forall b, b `notin` (union L (union (singleton c) (singleton a))) -> task_cof_chk_absetvar G e X a b c) <-> task_cof_chk_absetvar G e X a b c).
Proof.
  intro F. split.
  - intros [L H]. eapply task_stable_elim; [apply task_cof_chk_absetvar_stable|exact F|].
    exists L. intros u v w [Fu [Fv Fw]].
    exact (H w ltac:(task_atomic) u ltac:(task_atomic) v ltac:(task_atomic)).
  - intro H.
    exists (task_names_state R (aworklist_cons_work G (work_check (exp_abs e) (typ_var_f X)))).
    intros w Fw u Fu v Fv.
    eapply (task_stable_intro (task_names_state R (aworklist_cons_work G (work_check (exp_abs e) (typ_var_f X)))) (task_cof_chk_absetvar G e X) a b c ltac:(apply task_cof_chk_absetvar_stable) F H u v w);
      repeat split; task_atomic.
Qed.

Definition task_cof_chk_abstop G e (a b c : atom) : Prop :=
  a_wl_red (aworklist_cons_work (aworklist_cons_var G c (abind_var_typ typ_bot)) (work_check (open_exp_wrt_exp e (exp_var_f c)) typ_top)).

Lemma task_cof_chk_abstop_stable R G e :
  task_stable (task_names_state R (aworklist_cons_work G (work_check (exp_abs e) typ_top))) (task_cof_chk_abstop G e).
Proof.
  unfold task_stable, task_names_state, task_cof_chk_abstop, task_arrow, task_new_holes.
  intros p I Fixed a b c H.
  assert (Fix_G : task_rename_aworklist p G = G) by (apply task_rename_aworklist_fixed; intros; apply Fixed; simpl; fsetdec).
  assert (Fix_e : task_rename_exp p e = e) by (apply task_rename_exp_fixed; intros; apply Fixed; simpl; fsetdec).
  apply (task_rename_red p I) in H.
  task_rename_normalize H; task_rewrite_fixed H; exact H.
Qed.

Lemma task_cof_chk_abstop_choices R G e a b c :
  task_fresh3 (task_names_state R (aworklist_cons_work G (work_check (exp_abs e) typ_top))) a b c ->
  ((exists L, forall c, c `notin` L -> task_cof_chk_abstop G e a b c) <-> task_cof_chk_abstop G e a b c).
Proof.
  intro F. split.
  - intros [L H]. eapply task_stable_elim; [apply task_cof_chk_abstop_stable|exact F|].
    exists L. intros u v w [Fu [Fv Fw]].
    exact (H w ltac:(task_atomic)).
  - intro H.
    exists (task_names_state R (aworklist_cons_work G (work_check (exp_abs e) typ_top))).
    intros w Fw.
    destruct (task_pick3 (add w (task_names_state R (aworklist_cons_work G (work_check (exp_abs e) typ_top))))) as [ [ [u v] p] [F1 [F2 F3]]].
    eapply (task_stable_intro (task_names_state R (aworklist_cons_work G (work_check (exp_abs e) typ_top))) (task_cof_chk_abstop G e) a b c ltac:(apply task_cof_chk_abstop_stable) F H u v w);
      repeat split; task_atomic.
Qed.

Definition task_cof_inf_tabs G e A cs (a b c : atom) : Prop :=
  a_wl_red (aworklist_cons_work (aworklist_cons_var (aworklist_cons_work G (work_applys cs (typ_all A))) a abind_tvar_empty) (work_check (open_exp_wrt_typ e (typ_var_f a)) (open_typ_wrt_typ A (typ_var_f a)))).

Lemma task_cof_inf_tabs_stable R G e A cs :
  task_stable (task_names_state R (aworklist_cons_work G (work_infer (exp_tabs (exp_anno e A)) cs))) (task_cof_inf_tabs G e A cs).
Proof.
  unfold task_stable, task_names_state, task_cof_inf_tabs, task_arrow, task_new_holes.
  intros p I Fixed a b c H.
  assert (Fix_G : task_rename_aworklist p G = G) by (apply task_rename_aworklist_fixed; intros; apply Fixed; simpl; fsetdec).
  assert (Fix_e : task_rename_exp p e = e) by (apply task_rename_exp_fixed; intros; apply Fixed; simpl; fsetdec).
  assert (Fix_A : task_rename_typ p A = A) by (apply task_rename_typ_fixed; intros; apply Fixed; simpl; fsetdec).
  assert (Fix_cs : task_rename_conts p cs = cs) by (apply (proj1 (task_rename_conts_fixed p)); intros; apply Fixed; simpl; fsetdec).
  apply (task_rename_red p I) in H.
  task_rename_normalize H; task_rewrite_fixed H; exact H.
Qed.

Lemma task_cof_inf_tabs_choices R G e A cs a b c :
  task_fresh3 (task_names_state R (aworklist_cons_work G (work_infer (exp_tabs (exp_anno e A)) cs))) a b c ->
  ((exists L, forall a, a `notin` L -> task_cof_inf_tabs G e A cs a b c) <-> task_cof_inf_tabs G e A cs a b c).
Proof.
  intro F. split.
  - intros [L H]. eapply task_stable_elim; [apply task_cof_inf_tabs_stable|exact F|].
    exists L. intros u v w [Fu [Fv Fw]].
    exact (H u ltac:(task_atomic)).
  - intro H.
    exists (task_names_state R (aworklist_cons_work G (work_infer (exp_tabs (exp_anno e A)) cs))).
    intros u Fu.
    destruct (task_pick3 (add u (task_names_state R (aworklist_cons_work G (work_infer (exp_tabs (exp_anno e A)) cs))))) as [ [ [v w] p] [F1 [F2 F3]]].
    eapply (task_stable_intro (task_names_state R (aworklist_cons_work G (work_infer (exp_tabs (exp_anno e A)) cs))) (task_cof_inf_tabs G e A cs) a b c ltac:(apply task_cof_inf_tabs_stable) F H u v w);
      repeat split; task_atomic.
Qed.

Definition task_cof_inf_abs_mono G e cs (a b c : atom) : Prop :=
  a_wl_red (aworklist_cons_work (aworklist_cons_var (aworklist_cons_work (task_new_holes G a b) (work_applys cs (task_arrow a b))) c (abind_var_typ (typ_var_f a))) (work_check (open_exp_wrt_exp e (exp_var_f c)) (typ_var_f b))).

Lemma task_cof_inf_abs_mono_stable R G e cs :
  task_stable (task_names_state R (aworklist_cons_work G (work_infer (exp_abs e) cs))) (task_cof_inf_abs_mono G e cs).
Proof.
  unfold task_stable, task_names_state, task_cof_inf_abs_mono, task_arrow, task_new_holes.
  intros p I Fixed a b c H.
  assert (Fix_G : task_rename_aworklist p G = G) by (apply task_rename_aworklist_fixed; intros; apply Fixed; simpl; fsetdec).
  assert (Fix_e : task_rename_exp p e = e) by (apply task_rename_exp_fixed; intros; apply Fixed; simpl; fsetdec).
  assert (Fix_cs : task_rename_conts p cs = cs) by (apply (proj1 (task_rename_conts_fixed p)); intros; apply Fixed; simpl; fsetdec).
  apply (task_rename_red p I) in H.
  task_rename_normalize H; task_rewrite_fixed H; exact H.
Qed.

Lemma task_cof_inf_abs_mono_choices R G e cs a b c :
  task_fresh3 (task_names_state R (aworklist_cons_work G (work_infer (exp_abs e) cs))) a b c ->
  ((exists L, forall c, c `notin` L -> forall a, a `notin` (union L (singleton c)) -> forall b, b `notin` (union L (union (singleton c) (singleton a))) -> task_cof_inf_abs_mono G e cs a b c) <-> task_cof_inf_abs_mono G e cs a b c).
Proof.
  intro F. split.
  - intros [L H]. eapply task_stable_elim; [apply task_cof_inf_abs_mono_stable|exact F|].
    exists L. intros u v w [Fu [Fv Fw]].
    exact (H w ltac:(task_atomic) u ltac:(task_atomic) v ltac:(task_atomic)).
  - intro H.
    exists (task_names_state R (aworklist_cons_work G (work_infer (exp_abs e) cs))).
    intros w Fw u Fu v Fv.
    eapply (task_stable_intro (task_names_state R (aworklist_cons_work G (work_infer (exp_abs e) cs))) (task_cof_inf_abs_mono G e cs) a b c ltac:(apply task_cof_inf_abs_mono_stable) F H u v w);
      repeat split; task_atomic.
Qed.

Definition task_cof_infabs_all G A cd (a b c : atom) : Prop :=
  a_wl_red (aworklist_cons_work (aworklist_cons_var G a abind_etvar_empty) (work_infabs (open_typ_wrt_typ A (typ_var_f a)) cd)).

Lemma task_cof_infabs_all_stable R G A cd :
  task_stable (task_names_state R (aworklist_cons_work G (work_infabs (typ_all A) cd))) (task_cof_infabs_all G A cd).
Proof.
  unfold task_stable, task_names_state, task_cof_infabs_all, task_arrow, task_new_holes.
  intros p I Fixed a b c H.
  assert (Fix_G : task_rename_aworklist p G = G) by (apply task_rename_aworklist_fixed; intros; apply Fixed; simpl; fsetdec).
  assert (Fix_A : task_rename_typ p A = A) by (apply task_rename_typ_fixed; intros; apply Fixed; simpl; fsetdec).
  assert (Fix_cd : task_rename_contd p cd = cd) by (apply (proj2 (task_rename_conts_fixed p)); intros; apply Fixed; simpl; fsetdec).
  apply (task_rename_red p I) in H.
  task_rename_normalize H; task_rewrite_fixed H; exact H.
Qed.

Lemma task_cof_infabs_all_choices R G A cd a b c :
  task_fresh3 (task_names_state R (aworklist_cons_work G (work_infabs (typ_all A) cd))) a b c ->
  ((exists L, forall a, a `notin` L -> task_cof_infabs_all G A cd a b c) <-> task_cof_infabs_all G A cd a b c).
Proof.
  intro F. split.
  - intros [L H]. eapply task_stable_elim; [apply task_cof_infabs_all_stable|exact F|].
    exists L. intros u v w [Fu [Fv Fw]].
    exact (H u ltac:(task_atomic)).
  - intro H.
    exists (task_names_state R (aworklist_cons_work G (work_infabs (typ_all A) cd))).
    intros u Fu.
    destruct (task_pick3 (add u (task_names_state R (aworklist_cons_work G (work_infabs (typ_all A) cd))))) as [ [ [v w] p] [F1 [F2 F3]]].
    eapply (task_stable_intro (task_names_state R (aworklist_cons_work G (work_infabs (typ_all A) cd))) (task_cof_infabs_all G A cd) a b c ltac:(apply task_cof_infabs_all_stable) F H u v w);
      repeat split; task_atomic.
Qed.

Definition task_cof_infabs_etvar G X cd (a b c : atom) : Prop :=
  forall P K, aworklist_subst (aworklist_cons_work (task_new_holes G a b) (work_infabs (task_arrow a b) cd)) X (task_arrow a b) P K ->
    a_wl_red (awl_app (subst_typ_in_aworklist (task_arrow a b) X K) P).

Lemma task_cof_infabs_etvar_stable R G X cd :
  task_stable (task_names_state R (aworklist_cons_work G (work_infabs (typ_var_f X) cd))) (task_cof_infabs_etvar G X cd).
Proof.
  unfold task_stable, task_names_state, task_cof_infabs_etvar, task_arrow, task_new_holes.
  intros p I Fixed a b c H.
  assert (Fix_G : task_rename_aworklist p G = G) by (apply task_rename_aworklist_fixed; intros; apply Fixed; simpl; fsetdec).
  assert (Fix_X : p X = X) by (apply Fixed; simpl; fsetdec).
  assert (Fix_cd : task_rename_contd p cd = cd) by (apply (proj2 (task_rename_conts_fixed p)); intros; apply Fixed; simpl; fsetdec).
  intros P K HS.
  pose proof (task_rename_awl_subst p I _ _ _ _ _ HS) as H'.
  task_rename_normalize H'; task_rewrite_fixed H'.
  specialize (H (task_rename_aworklist p P) (task_rename_aworklist p K) H').
  apply (task_rename_red p I) in H.
  task_rename_normalize H; task_rewrite_fixed H; exact H.
Qed.

Lemma task_subst_arrow_fresh X a b :
  a <> X -> b <> X ->
  subst_typ_in_typ (task_arrow a b) X (task_arrow a b) = task_arrow a b.
Proof.
  intros Fa Fb. change (typ_arrow
    (subst_typ_in_typ (task_arrow a b) X (typ_var_f a))
    (subst_typ_in_typ (task_arrow a b) X (typ_var_f b)) = task_arrow a b).
  now rewrite !task_subst_other_var.
Qed.

Lemma task_cof_infabs_etvar_compact R G X cd a b c :
  uniq (awl_to_aenv G) -> task_fresh3 (task_names_state R (aworklist_cons_work G (work_infabs (typ_var_f X) cd))) a b c ->
  (task_cof_infabs_etvar G X cd a b c <-> a_wl_red (match (task_solution (task_new_holes G a b) X (task_arrow a b)) with Some T => (aworklist_cons_work T (work_applyd (subst_typ_in_contd (task_arrow a b) X cd) (typ_var_f a) (typ_var_f b))) | None => aworklist_empty end)).
Proof.
  intros U Fresh.
  pose proof (task_fresh_new_holes R G (work_infabs (typ_var_f X) cd) a b c U Fresh) as U'.
  unfold task_cof_infabs_etvar.
  assert (Fa : a <> X) by (destruct Fresh as [F _]; unfold task_names_state in F; simpl in F; intro; subst; fsetdec).
  assert (Fb : b <> X) by (destruct Fresh as [_ [F _]]; unfold task_names_state in F; simpl in F; intro; subst; fsetdec).
  pose proof (task_solution_red (task_new_holes G a b) X (task_arrow a b)
    (fun T => (aworklist_cons_work T (work_applyd (subst_typ_in_contd (task_arrow a b) X cd) (typ_var_f a) (typ_var_f b)))) U') as Equiv.
  apply iff_sym in Equiv. rewrite <- Equiv.
  split; intros H P K HS.
  - specialize (H P (aworklist_cons_work K (work_infabs (task_arrow a b) cd)) ltac:(repeat constructor; exact HS)).
    cbn [subst_typ_in_aworklist subst_typ_in_work subst_typ_in_abind awl_app] in H.
    rewrite (task_subst_arrow_fresh X a b Fa Fb) in H. now apply task_red_infabs_arrow in H.
  - apply task_subst_top_work in HS as [J [ -> HS]].
    specialize (H P J HS).
    cbn [subst_typ_in_aworklist subst_typ_in_work subst_typ_in_abind awl_app].
    rewrite (task_subst_arrow_fresh X a b Fa Fb). now apply task_red_infabs_arrow.
Qed.

Lemma task_cof_infabs_etvar_choices R G X cd a b c :
  task_fresh3 (task_names_state R (aworklist_cons_work G (work_infabs (typ_var_f X) cd))) a b c ->
  ((exists L, forall a, a `notin` L -> forall b, b `notin` (union L (singleton a)) -> task_cof_infabs_etvar G X cd a b c) <-> task_cof_infabs_etvar G X cd a b c).
Proof.
  intro F. split.
  - intros [L H]. eapply task_stable_elim; [apply task_cof_infabs_etvar_stable|exact F|].
    exists L. intros u v w [Fu [Fv Fw]].
    exact (H u ltac:(task_atomic) v ltac:(task_atomic)).
  - intro H.
    exists (task_names_state R (aworklist_cons_work G (work_infabs (typ_var_f X) cd))).
    intros u Fu v Fv.
    destruct (task_pick3 (add v (add u (task_names_state R (aworklist_cons_work G (work_infabs (typ_var_f X) cd)))))) as [ [ [w p] q] [F1 [F2 F3]]].
    eapply (task_stable_intro (task_names_state R (aworklist_cons_work G (work_infabs (typ_var_f X) cd))) (task_cof_infabs_etvar G X cd) a b c ltac:(apply task_cof_infabs_etvar_stable) F H u v w);
      repeat split; task_atomic.
Qed.


(* The search steps preserve and reflect successful reduction.
   The cofinite premises are discharged by the fresh tuple lemmas. *)
Lemma task_step_red R a b c G T :
  task_step a b c G T -> uniq (awl_to_aenv G) ->
  task_fresh3 (task_names_state R G) a b c -> a_wl_red T -> a_wl_red G.
Proof.
  destruct 1; intros U Fresh Red.
  - now apply a_wl_red__gc_var.
  - now apply a_wl_red__sub_top.
  - now apply a_wl_red__sub_bot.
  - now apply a_wl_red__sub_unit.
  - subst. now apply a_wl_red__sub_tvar.
  - now apply a_wl_red__subarrow.
  - change (task_cof_sub_alll G A B a b c) in Red.
    apply (proj2 (task_cof_sub_alll_choices R G A B a b c Fresh)) in Red as [L Premise].
    eapply a_wl_red__sub_alll with (L := L); try eassumption; exact Premise.
  - change (task_cof_sub_all G A B a b c) in Red.
    apply (proj2 (task_cof_sub_all_choices R G A B a b c Fresh)) in Red as [L Premise].
    eapply a_wl_red__sub_all with (L := L); try eassumption; exact Premise.
  - apply (proj2 (task_cof_sub_arrow1_compact R G X A B a b c U Fresh)) in Red.
    apply (proj2 (task_cof_sub_arrow1_choices R G X A B a b c Fresh)) in Red as [L Premise].
    eapply a_wl_red__sub_arrow1 with (L := L); try eassumption; exact Premise.
  - apply (proj2 (task_cof_sub_arrow2_compact R G A B X a b c U Fresh)) in Red.
    apply (proj2 (task_cof_sub_arrow2_choices R G A B X a b c Fresh)) in Red as [L Premise].
    eapply a_wl_red__sub_arrow2 with (L := L); try eassumption; exact Premise.
  - match goal with HS : task_solution _ _ _ = Some _ |- _ =>
      apply task_solution_spec in HS as [P [K [HS ->]]]; [|exact U]
    end.
    eapply a_wl_red__sub_etvarmono1; eassumption.
  - match goal with HS : task_solution _ _ _ = Some _ |- _ =>
      apply task_solution_spec in HS as [P [K [HS ->]]]; [|exact U]
    end.
    eapply a_wl_red__sub_etvarmono2; eassumption.
  - now apply a_wl_red__sub_intersection1.
  - now apply a_wl_red__sub_intersection2.
  - now apply a_wl_red__sub_intersection3.
  - now apply a_wl_red__sub_union1.
  - now apply a_wl_red__sub_union2.
  - now apply a_wl_red__sub_union3.
  - now apply a_wl_red__chk_sub.
  - change (task_cof_chk_absarrow G e A B a b c) in Red.
    apply (proj2 (task_cof_chk_absarrow_choices R G e A B a b c Fresh)) in Red as [L Premise].
    eapply a_wl_red__chk_absarrow with (L := L); try eassumption; exact Premise.
  - apply (proj2 (task_cof_chk_absetvar_compact R G e X a b c U Fresh)) in Red.
    apply (proj2 (task_cof_chk_absetvar_choices R G e X a b c Fresh)) in Red as [L Premise].
    eapply a_wl_red__chk_absetvar with (L := L); try eassumption; exact Premise.
  - change (task_cof_chk_abstop G e a b c) in Red.
    apply (proj2 (task_cof_chk_abstop_choices R G e a b c Fresh)) in Red as [L Premise].
    eapply a_wl_red__chk_abstop with (L := L); try eassumption; exact Premise.
  - now apply a_wl_red__chk_inter.
  - now apply a_wl_red__chk_union1.
  - now apply a_wl_red__chk_union2.
  - eapply a_wl_red__inf_var; eassumption.
  - now apply a_wl_red__inf_anno.
  - change (task_cof_inf_tabs G e A cs a b c) in Red.
    apply (proj2 (task_cof_inf_tabs_choices R G e A cs a b c Fresh)) in Red as [L Premise].
    eapply a_wl_red__inf_tabs with (L := L); try eassumption; exact Premise.
  - change (task_cof_inf_abs_mono G e cs a b c) in Red.
    apply (proj2 (task_cof_inf_abs_mono_choices R G e cs a b c Fresh)) in Red as [L Premise].
    eapply a_wl_red__inf_abs_mono with (L := L); try eassumption; exact Premise.
  - now apply a_wl_red__inf_unit.
  - now apply a_wl_red__inf_app.
  - now apply a_wl_red__infapp.
  - now apply a_wl_red__infabs_arr.
  - now apply a_wl_red__infabs_bot.
  - change (task_cof_infabs_all G A cd a b c) in Red.
    apply (proj2 (task_cof_infabs_all_choices R G A cd a b c Fresh)) in Red as [L Premise].
    eapply a_wl_red__infabs_all with (L := L); try eassumption; exact Premise.
  - now apply a_wl_red__infabs_inter1.
  - now apply a_wl_red__infabs_inter2.
  - now apply a_wl_red__infabs_union.
  - now apply a_wl_red__infabsunion.
  - now apply a_wl_red__unioninfabs.
  - apply (proj2 (task_cof_infabs_etvar_compact R G X cd a b c U Fresh)) in Red.
    apply (proj2 (task_cof_infabs_etvar_choices R G X cd a b c Fresh)) in Red as [L Premise].
    eapply a_wl_red__infabs_etvar with (L := L); try eassumption; exact Premise.
  - now apply a_wl_red__inf_tapp.
  - now apply a_wl_red__inftapp_all.
  - now apply a_wl_red__inftapp_bot.
  - now apply a_wl_red__inftapp_inter1.
  - now apply a_wl_red__inftapp_inter2.
  - now apply a_wl_red__inftapp_union.
  - now apply a_wl_red__inftappunion.
  - now apply a_wl_red__unioninftapp.
  - eapply a_wl_red__applys; [apply task_apply_s_spec; reflexivity|exact Red].
  - eapply a_wl_red__applyd; [apply task_apply_d_spec; reflexivity|exact Red].
Qed.

Lemma task_red_step R a b c G :
  a_wl_red G -> uniq (awl_to_aenv G) ->
  task_fresh3 (task_names_state R G) a b c ->
  G = aworklist_empty \/ exists T, task_step a b c G T /\ a_wl_red T.
Proof.
  destruct 1; intros U Fresh; cbn [awl_to_aenv] in U.
  - left; reflexivity.
  - right; eexists; split; [eapply task_step__gc_var; try assumption; try reflexivity|eassumption].
  - right; eexists; split; [eapply task_step__sub_top; try assumption; try reflexivity|eassumption].
  - right; eexists; split; [eapply task_step__sub_bot; try assumption; try reflexivity|eassumption].
  - right; eexists; split; [eapply task_step__sub_unit; try assumption; try reflexivity|eassumption].
  - right; eexists; split; [eapply task_step__sub_tvar; try assumption; try reflexivity|eassumption].
  - right; eexists; split; [eapply task_step__subarrow; try assumption; try reflexivity|eassumption].
  - right; eexists; split; [apply task_step__sub_alll; try assumption|].

    apply (proj1 (task_cof_sub_alll_choices R _ _ _ a b c Fresh)).
    exists L. eassumption.
  - right; eexists; split; [apply task_step__sub_all; try assumption|].

    apply (proj1 (task_cof_sub_all_choices R _ _ _ a b c Fresh)).
    exists L. eassumption.
  - right; eexists; split; [apply task_step__sub_arrow1; try assumption|].
    apply (proj1 (task_cof_sub_arrow1_compact R _ _ _ _ a b c U Fresh)).
    apply (proj1 (task_cof_sub_arrow1_choices R _ _ _ _ a b c Fresh)).
    exists L. eassumption.
  - right; eexists; split; [apply task_step__sub_arrow2; try assumption|].
    apply (proj1 (task_cof_sub_arrow2_compact R _ _ _ _ a b c U Fresh)).
    apply (proj1 (task_cof_sub_arrow2_choices R _ _ _ _ a b c Fresh)).
    exists L. eassumption.
  - right; eexists; split; [eapply task_step__sub_etvarmono1; try eassumption|eassumption].
    apply task_solution_spec; [exact U|]. do 2 eexists; split; [eassumption|reflexivity].
  - right; eexists; split; [eapply task_step__sub_etvarmono2; try eassumption|eassumption].
    apply task_solution_spec; [exact U|]. do 2 eexists; split; [eassumption|reflexivity].
  - right; eexists; split; [eapply task_step__sub_intersection1; try assumption; try reflexivity|eassumption].
  - right; eexists; split; [eapply task_step__sub_intersection2; try assumption; try reflexivity|eassumption].
  - right; eexists; split; [eapply task_step__sub_intersection3; try assumption; try reflexivity|eassumption].
  - right; eexists; split; [eapply task_step__sub_union1; try assumption; try reflexivity|eassumption].
  - right; eexists; split; [eapply task_step__sub_union2; try assumption; try reflexivity|eassumption].
  - right; eexists; split; [eapply task_step__sub_union3; try assumption; try reflexivity|eassumption].
  - right; eexists; split; [eapply task_step__chk_sub; try assumption; try reflexivity|eassumption].
  - right; eexists; split; [apply task_step__chk_absarrow; try assumption|].

    apply (proj1 (task_cof_chk_absarrow_choices R _ _ _ _ a b c Fresh)).
    exists L. eassumption.
  - right; eexists; split; [apply task_step__chk_absetvar; try assumption|].
    apply (proj1 (task_cof_chk_absetvar_compact R _ _ _ a b c U Fresh)).
    apply (proj1 (task_cof_chk_absetvar_choices R _ _ _ a b c Fresh)).
    exists L. eassumption.
  - right; eexists; split; [apply task_step__chk_abstop; try assumption|].

    apply (proj1 (task_cof_chk_abstop_choices R _ _ a b c Fresh)).
    exists L. eassumption.
  - right; eexists; split; [eapply task_step__chk_inter; try assumption; try reflexivity|eassumption].
  - right; eexists; split; [eapply task_step__chk_union1; try assumption; try reflexivity|eassumption].
  - right; eexists; split; [eapply task_step__chk_union2; try assumption; try reflexivity|eassumption].
  - right; eexists; split; [eapply task_step__inf_var; eassumption|eassumption].
  - right; eexists; split; [eapply task_step__inf_anno; try assumption; try reflexivity|eassumption].
  - right; eexists; split; [apply task_step__inf_tabs; try assumption|].

    apply (proj1 (task_cof_inf_tabs_choices R _ _ _ _ a b c Fresh)).
    exists L. eassumption.
  - right; eexists; split; [apply task_step__inf_abs_mono; try assumption|].

    apply (proj1 (task_cof_inf_abs_mono_choices R _ _ _ a b c Fresh)).
    exists L. eassumption.
  - right; eexists; split; [eapply task_step__inf_unit; try assumption; try reflexivity|eassumption].
  - right; eexists; split; [eapply task_step__inf_app; try assumption; try reflexivity|eassumption].
  - right; eexists; split; [eapply task_step__infapp; try assumption; try reflexivity|eassumption].
  - right; eexists; split; [eapply task_step__infabs_arr; try assumption; try reflexivity|eassumption].
  - right; eexists; split; [eapply task_step__infabs_bot; try assumption; try reflexivity|eassumption].
  - right; eexists; split; [apply task_step__infabs_all; try assumption|].

    apply (proj1 (task_cof_infabs_all_choices R _ _ _ a b c Fresh)).
    exists L. eassumption.
  - right; eexists; split; [eapply task_step__infabs_inter1; try assumption; try reflexivity|eassumption].
  - right; eexists; split; [eapply task_step__infabs_inter2; try assumption; try reflexivity|eassumption].
  - right; eexists; split; [eapply task_step__infabs_union; try assumption; try reflexivity|eassumption].
  - right; eexists; split; [eapply task_step__infabsunion; try assumption; try reflexivity|eassumption].
  - right; eexists; split; [eapply task_step__unioninfabs; try assumption; try reflexivity|eassumption].
  - right; eexists; split; [apply task_step__infabs_etvar; try assumption|].
    apply (proj1 (task_cof_infabs_etvar_compact R _ _ _ a b c U Fresh)).
    apply (proj1 (task_cof_infabs_etvar_choices R _ _ _ a b c Fresh)).
    exists L. eassumption.
  - right; eexists; split; [eapply task_step__inf_tapp; try assumption; try reflexivity|eassumption].
  - right; eexists; split; [eapply task_step__inftapp_all; try assumption; try reflexivity|eassumption].
  - right; eexists; split; [eapply task_step__inftapp_bot; try assumption; try reflexivity|eassumption].
  - right; eexists; split; [eapply task_step__inftapp_inter1; try assumption; try reflexivity|eassumption].
  - right; eexists; split; [eapply task_step__inftapp_inter2; try assumption; try reflexivity|eassumption].
  - right; eexists; split; [eapply task_step__inftapp_union; try assumption; try reflexivity|eassumption].
  - right; eexists; split; [eapply task_step__inftappunion; try assumption; try reflexivity|eassumption].
  - right; eexists; split; [eapply task_step__unioninftapp; try assumption; try reflexivity|eassumption].
  - match goal with H : apply_conts _ _ _ |- _ =>
      apply task_apply_s_spec in H; subst
    end.
    right; eexists; split; [apply task_step__applys|eassumption].
  - match goal with H : apply_contd _ _ _ _ |- _ =>
      apply task_apply_d_spec in H; subst
    end.
    right; eexists; split; [apply task_step__applyd|eassumption].
Qed.

Lemma task_rank_mono R G A :
  task_colors R G -> a_mono_typ (awl_to_aenv G) A -> task_type_rank R A = 0.
Proof.
  intro C. apply task_colors_binds in C as [CS [CT CE]]. clear CS.
  generalize dependent (awl_to_aenv G). intros E CT CE H.
  induction H; simpl; auto.
  - rewrite (proj2 (task_mem_false _ _) (CT _ H)); reflexivity.
  - rewrite (proj2 (task_mem_false _ _) (CE _ H)); reflexivity.
  - rewrite IHa_mono_typ1, IHa_mono_typ2 by assumption; reflexivity.
Qed.

Lemma task_rank_zero R G A :
  task_colors R G -> ftvar_in_typ A [<=] task_type_dom G ->
  task_type_rank R A = 0 -> a_mono_typ (awl_to_aenv G) A.
Proof.
  intro C. apply task_colors_binds in C as [CS [CT CE]].
  induction A; simpl; intros F H; try discriminate; try solve [constructor].
  - assert (X `in` task_type_dom G) by fsetdec.
    rewrite task_type_dom_env in H0.
    apply task_types_in_env in H0 as [T|[T|T]].
    + now apply a_mono_typ__tvar.
    + now apply a_mono_typ__etvar.
    + rewrite (proj2 (task_mem _ _) (CS _ T)) in H; discriminate.
  - destruct (task_type_rank R A1 + task_type_rank R A2) eqn:E; try discriminate.
    constructor; [apply IHA1|apply IHA2]; try fsetdec; lia.
Qed.

Lemma task_rank_fresh R A x :
  x `notin` ftvar_in_typ A ->
  task_type_rank (add x R) A = task_type_rank R A.
Proof.
  induction A; simpl; intro F; try reflexivity;
    try solve [rewrite IHA by fsetdec; reflexivity];
    try solve [rewrite IHA1, IHA2 by fsetdec; reflexivity].
  destruct (AtomSetImpl.mem X R) eqn:E.
  - apply task_mem in E. assert (X `in` add x R) by fsetdec.
    now rewrite (proj2 (task_mem _ _) H).
  - apply task_mem_false in E. assert (X `notin` add x R) by fsetdec.
    now rewrite (proj2 (task_mem_false _ _) H).
Qed.

Lemma task_rank_subst R T X A :
  X `notin` R -> task_type_rank R T = 0 ->
  task_type_rank R (subst_typ_in_typ T X A) = task_type_rank R A.
Proof.
  intros F Z; induction A; simpl; try reflexivity;
    try solve [rewrite IHA; reflexivity];
    try solve [rewrite IHA1, IHA2; reflexivity].
  destruct (X0 == X); subst; simpl; auto.
  now rewrite (proj2 (task_mem_false _ _) F).
Qed.

Lemma task_head_rank_subst R T X A :
  task_type_rank R T = 0 ->
  task_head_rank (subst_typ_in_typ T X A) = task_head_rank A.
Proof.
  intro Z; induction A; simpl; try reflexivity;
    try solve [rewrite IHA; reflexivity];
    try solve [rewrite IHA1, IHA2; reflexivity].
  destruct (X0 == X); simpl; auto.
  destruct T; simpl in Z; discriminate || reflexivity.
Qed.

Lemma task_rank_open R A : forall k x,
  task_type_rank R (open_typ_wrt_typ_rec k (typ_var_f x) A) <= task_type_rank R A.
Proof.
  induction A; intros; simpl; try lia.
  - destruct (lt_eq_lt_dec n k) as [ [] | ]; simpl; try lia.
    destruct (AtomSetImpl.mem x R); lia.
  - specialize (IHA1 k x); specialize (IHA2 k x).
    destruct (task_type_rank R A1 + task_type_rank R A2) eqn:E;
    destruct (task_type_rank R (open_typ_wrt_typ_rec k (typ_var_f x) A1) +
              task_type_rank R (open_typ_wrt_typ_rec k (typ_var_f x) A2)) eqn:D; lia.
  - specialize (IHA (S k) x); lia.
  - specialize (IHA1 k x); specialize (IHA2 k x); lia.
  - specialize (IHA1 k x); specialize (IHA2 k x); lia.
Qed.

Lemma task_head_rank_open A : forall k x,
  task_head_rank (open_typ_wrt_typ_rec k (typ_var_f x) A) = task_head_rank A.
Proof.
  induction A; intros; simpl; rewrite ?IHA, ?IHA1, ?IHA2; try reflexivity.
  destruct (lt_eq_lt_dec n k) as [ [] | ]; reflexivity.
Qed.

Lemma task_exp_rank_subst T X e :
  task_exp_rank (subst_typ_in_exp T X e) = task_exp_rank e.
Proof. induction e; simpl; congruence. Qed.

Lemma task_exp_rank_open_e e : forall k x,
  task_exp_rank (open_exp_wrt_exp_rec k (exp_var_f x) e) = task_exp_rank e.
Proof. induction e; intros; simpl; try congruence; destruct (lt_eq_lt_dec n k) as [ [] | ]; reflexivity. Qed.

Lemma task_exp_rank_open_t e : forall k A,
  task_exp_rank (open_exp_wrt_typ_rec k A e) = task_exp_rank e.
Proof. induction e; intros; simpl; congruence. Qed.

Definition task_at (k i n : nat) := if Nat.eq_dec k i then n else 0.
Definition task_check_index e := 3 * task_exp_rank e + 1.
Definition task_infer_index e := 3 * task_exp_rank e.
Definition task_argument_index e := 3 * task_exp_rank e + 2.

(* The highest changed coefficient decreases when a term is processed
   or a continuation starts a new type-processing stage. Checking
   coefficients use powers of three to pay for intersection splitting. *)
Fixpoint task_primary_s k cs :=
  match cs with
  | conts_infabs cd => task_at k 0 1 + task_primary_d k cd
  | conts_inftapp _ cs => task_at k 0 1 + task_primary_s k cs
  | conts_inftappunion _ _ cs | conts_unioninftapp _ cs => task_primary_s k cs
  | conts_sub _ => task_at k 0 1
  end
with task_primary_d k cd :=
  match cd with
  | contd_infapp e cs => task_at k (task_argument_index e) 1 + task_primary_s k cs
  | contd_infabsunion _ cd | contd_unioninfabs _ _ cd => task_primary_d k cd
  end.

Definition task_primary_work R k w :=
  match w with
  | work_check e A => task_at k (task_check_index e) (3 ^ task_type_rank R A)
  | work_infer e cs => task_at k (task_infer_index e) 1 + task_primary_s k cs
  | work_infapp _ _ e cs => task_at k (task_argument_index e) 1 + task_primary_s k cs
  | work_applys cs _ | work_inftapp _ _ cs | work_inftappunion _ _ _ cs
  | work_unioninftapp _ _ cs => task_primary_s k cs
  | work_applyd cd _ _ | work_infabs _ cd | work_infabsunion _ _ _ cd
  | work_unioninfabs _ _ _ _ cd => task_primary_d k cd
  | work_sub _ _ => 0
  end.

Fixpoint task_abs_cost cd :=
  match cd with
  | contd_infabsunion B cd => task_head_rank B + 4 + task_abs_cost cd
  | contd_unioninfabs _ _ cd => 2 + task_abs_cost cd
  | contd_infapp _ _ => 1
  end.

Fixpoint task_tapp_cost cs :=
  match cs with
  | conts_inftappunion B _ cs => task_head_rank B + 4 + task_tapp_cost cs
  | conts_unioninftapp _ cs => 2 + task_tapp_cost cs
  | _ => 0
  end.

(* Within a type-processing stage, count the unfinished branches.
   Subtyping uses the nonmonomorphic type rank. Existential count and
   ordinary size supply the final two components of the measure. *)
Definition task_secondary_work R w :=
  match w with
  | work_sub A B => 3 ^ (task_type_rank R A + task_type_rank R B) - 1
  | work_infabs A cd => task_head_rank A + task_abs_cost cd
  | work_infabsunion _ _ B cd => task_head_rank B + 3 + task_abs_cost cd
  | work_unioninfabs _ _ _ _ cd => 1 + task_abs_cost cd
  | work_applyd cd _ _ => task_abs_cost cd
  | work_inftapp A _ cs => task_head_rank A + task_tapp_cost cs
  | work_inftappunion _ B _ cs => task_head_rank B + 3 + task_tapp_cost cs
  | work_unioninftapp _ _ cs => 1 + task_tapp_cost cs
  | work_applys cs _ => task_tapp_cost cs
  | _ => 0
  end.

Definition task_zero_bind (_ : abind) := 0.
Definition task_zero_work (_ : work) := 0.
Definition task_etvar_weight b :=
  match b with abind_etvar_empty => 1 | _ => 0 end.

Fixpoint task_sum (B : abind -> nat) (W : work -> nat) G :=
  match G with
  | aworklist_empty => 0
  | aworklist_cons_var G _ b => task_sum B W G + B b
  | aworklist_cons_work G w => task_sum B W G + W w
  end.

Definition task_primary R G k := task_sum task_zero_bind (task_primary_work R k) G.
Definition task_secondary R G := task_sum task_zero_bind (task_secondary_work R) G.
Definition task_holes G := task_sum task_etvar_weight task_zero_work G.
Definition task_size G := task_sum (fun _ => 1) size_work G.

Lemma task_sum_app V W G H :
  task_sum V W (awl_app G H) = task_sum V W G + task_sum V W H.
Proof. induction G; simpl; lia. Qed.

Lemma task_sum_subst V W A X G :
  (forall b, V (subst_typ_in_abind A X b) = V b) ->
  (forall w, W (subst_typ_in_work A X w) = W w) ->
  task_sum V W (subst_typ_in_aworklist A X G) = task_sum V W G.
Proof. intros VB VW; induction G; simpl; rewrite ?VB, ?VW; lia. Qed.

Lemma task_sum_entries V W G :
  task_sum V W G =
  fold_right (fun s n => match s with inl (_,b) => V b + n | inr w => W w + n end) 0 (task_entries G).
Proof. induction G; simpl in *; lia. Qed.

Lemma task_sum_perm (V : abind -> nat) (W : work -> nat) (l m : list task_entry) :
  Permutation l m ->
  fold_right (fun s n => match s with inl (_,b) => V b + n | inr w => W w + n end) 0 l =
  fold_right (fun s n => match s with inl (_,b) => V b + n | inr w => W w + n end) 0 m.
Proof.
  induction 1 as [|u p q E IH|u v p|p q r E1 IH1 E2 IH2]; simpl.
  - reflexivity.
  - destruct u as [[x b]|w]; simpl; now rewrite IH.
  - destruct u as [[x b]|w], v as [[y c]|w']; simpl; lia.
  - congruence.
Qed.

Lemma task_sum_solution V W G A X T :
  uniq (awl_to_aenv G) -> task_solution G X A = Some T ->
  (forall b, V (subst_typ_in_abind A X b) = V b) ->
  (forall w, W (subst_typ_in_work A X w) = W w) ->
  task_sum V W G = task_sum V W T + V abind_etvar_empty.
Proof.
  intros U E VB VW. apply task_solution_spec in E as [P [K [HS ->]]]; auto.
  pose proof (task_split_perm _ _ _ _ _ HS) as HP.
  apply (task_sum_perm V W) in HP.
  rewrite <- task_sum_entries in HP; simpl in HP.
  rewrite <- task_entries_app, <- task_sum_entries in HP.
  rewrite !task_sum_app in *. rewrite task_sum_subst by assumption. lia.
Qed.

Lemma task_primary_cont_subst k T X :
  (forall c, task_primary_s k (subst_typ_in_conts T X c) = task_primary_s k c) /\
  (forall c, task_primary_d k (subst_typ_in_contd T X c) = task_primary_d k c).
Proof.
  apply task_cont_ind; intros; simpl; unfold task_argument_index;
    rewrite ?task_exp_rank_subst; congruence.
Qed.

Lemma task_primary_subst R T X k w :
  X `notin` R -> task_type_rank R T = 0 ->
  task_primary_work R k (subst_typ_in_work T X w) = task_primary_work R k w.
Proof.
  intros NX Z; destruct (task_primary_cont_subst k T X) as [HS HD].
  destruct w; simpl;
    rewrite ?HS, ?HD, ?task_rank_subst by assumption;
    unfold task_check_index, task_infer_index, task_argument_index;
    rewrite ?task_exp_rank_subst; reflexivity.
Qed.

Lemma task_secondary_subst R T X w :
  X `notin` R -> task_type_rank R T = 0 ->
  task_secondary_work R (subst_typ_in_work T X w) = task_secondary_work R w.
Proof.
  intros NX Z.
  assert (HS : forall c, task_tapp_cost (subst_typ_in_conts T X c) = task_tapp_cost c)
    by (induction c; simpl; rewrite ?(task_head_rank_subst R T X _ Z); congruence).
  assert (HD : forall c, task_abs_cost (subst_typ_in_contd T X c) = task_abs_cost c)
    by (induction c; simpl; rewrite ?(task_head_rank_subst R T X _ Z); congruence).
  destruct w; simpl; rewrite ?HS, ?HD, ?task_rank_subst, ?(task_head_rank_subst R T X _ Z) by assumption; reflexivity.
Qed.

Lemma task_holes_solution G T X A :
  uniq (awl_to_aenv G) -> task_solution G X A = Some T -> task_holes G = S (task_holes T).
Proof.
  intros U E. unfold task_holes.
  pose proof (task_sum_solution task_etvar_weight task_zero_work G A X T U E ltac:(destruct b; reflexivity) ltac:(reflexivity)).
  simpl in H; lia.
Qed.

Definition task_poly_less (p q : nat -> nat) :=
  exists k, p k < q k /\ forall j, k < j -> p j = q j.

Fixpoint task_poly_lex (n : nat) (p q : nat -> nat) : Prop :=
  match n with
  | 0 => False
  | S n => p n < q n \/ (p n = q n /\ task_poly_lex n p q)
  end.

Lemma task_poly_lex_wf n : well_founded (task_poly_lex n).
Proof.
  induction n.
  - intro p; constructor; contradiction.
  - apply (wf_incl _ (task_poly_lex (S n)) (fun p q => slexprod nat (nat -> nat) lt (task_poly_lex n)
                                      (p n,p) (q n,q))).
    + intros p q [H|[E H]].
      * now apply left_slex.
      * rewrite E. now apply right_slex.
    + apply wf_inverse_image, wf_slexprod; [apply lt_wf|exact IHn].
Qed.

Definition task_bounded n p := forall k, n <= k -> p k = 0.

Definition task_low_rank R G := (task_secondary R G, (task_holes G, task_size G)).
Definition task_low_lt := slexprod nat (nat * nat) lt (slexprod nat nat lt lt).

Lemma task_low_wf : well_founded task_low_lt.
Proof. unfold task_low_lt. repeat apply wf_slexprod; apply lt_wf. Qed.

Lemma task_primary_fresh R x G :
  x `notin` task_names_aworklist G ->
  forall k, task_primary (add x R) G k = task_primary R G k.
Proof.
  induction G as [|G IH Y d|G IH w]; intros F k; [reflexivity| |].
  - change (task_primary (add x R) G k + 0 = task_primary R G k + 0).
    rewrite IH; [reflexivity|simpl in F; fsetdec].
  - change (task_primary (add x R) G k + task_primary_work (add x R) k w =
            task_primary R G k + task_primary_work R k w).
    rewrite IH by (simpl in F; fsetdec).
    destruct w; cbn [task_primary_work task_names_aworklist task_names_work] in *; try reflexivity.
    now rewrite task_rank_fresh by fsetdec.
Qed.

Lemma task_secondary_fresh R x G :
  x `notin` task_names_aworklist G ->
  task_secondary (add x R) G = task_secondary R G.
Proof.
  induction G as [|G IH Y d|G IH w]; intros F; [reflexivity| |].
  - change (task_secondary (add x R) G + 0 = task_secondary R G + 0).
    rewrite IH; [reflexivity|simpl in F; fsetdec].
  - change (task_secondary (add x R) G + task_secondary_work (add x R) w =
            task_secondary R G + task_secondary_work R w).
    rewrite IH by (simpl in F; fsetdec).
    destruct w; cbn [task_secondary_work task_names_aworklist task_names_work] in *; try reflexivity.
    now rewrite !task_rank_fresh by fsetdec.
Qed.

Lemma task_at_eq i v : task_at i i v = v.
Proof. unfold task_at; destruct (Nat.eq_dec i i); congruence. Qed.

Lemma task_at_neq k i v : k <> i -> task_at k i v = 0.
Proof. unfold task_at; destruct (Nat.eq_dec k i); congruence. Qed.

Lemma task_pow_pos n : 0 < 3 ^ n.
Proof. pose proof (Nat.pow_nonzero 3 n ltac:(lia)). lia. Qed.

Lemma task_pow_pair m n k :
  m <= k -> n <= k -> 3^m + 3^n < 3^(S k).
Proof.
  intros.
  pose proof (Nat.pow_le_mono_r 3 m k ltac:(lia) H).
  pose proof (Nat.pow_le_mono_r 3 n k ltac:(lia) H0).
  pose proof (task_pow_pos k). simpl; lia.
Qed.

Lemma task_pow_step m n :
  m < n -> 3^m - 1 < 3^n - 1.
Proof. intro H; pose proof (Nat.pow_lt_mono_r 3 m n ltac:(lia) H); pose proof (task_pow_pos m); lia. Qed.

Lemma task_arrow_rank_nonmono R A B :
  task_type_rank R A + task_type_rank R B > 0 ->
  task_type_rank R (typ_arrow A B) = S (task_type_rank R A + task_type_rank R B).
Proof. simpl; destruct (_ + _); lia. Qed.

Lemma task_arrow_rank_zero R A B :
  task_type_rank R (typ_arrow A B) = 0 <->
  task_type_rank R A = 0 /\ task_type_rank R B = 0.
Proof. simpl; destruct (_ + _) eqn:E; lia. Qed.

Lemma task_arrow_rank_lb R A B :
  task_type_rank R A + task_type_rank R B <= task_type_rank R (typ_arrow A B).
Proof. simpl; destruct (_ + _); lia. Qed.

Lemma task_secondary_sub_arrow R A B C D :
  0 < task_type_rank R (typ_arrow A B) + task_type_rank R (typ_arrow C D) ->
  task_secondary_work R (work_sub C A) + task_secondary_work R (work_sub B D) <
    task_secondary_work R (work_sub (typ_arrow A B) (typ_arrow C D)).
Proof.
  intro Srank.
  change (3^(task_type_rank R C + task_type_rank R A)-1 +
          (3^(task_type_rank R B + task_type_rank R D)-1) <
          3^(task_type_rank R (typ_arrow A B) + task_type_rank R (typ_arrow C D))-1).
  pose proof (task_arrow_rank_lb R A B) as L.
  pose proof (task_arrow_rank_lb R C D) as M.
  assert (H : task_type_rank R A + task_type_rank R B +
              (task_type_rank R C + task_type_rank R D) <
              task_type_rank R (typ_arrow A B) + task_type_rank R (typ_arrow C D)).
  { destruct (Nat.eq_dec (task_type_rank R A + task_type_rank R B) 0);
    [|rewrite task_arrow_rank_nonmono by lia; lia].
    destruct (Nat.eq_dec (task_type_rank R C + task_type_rank R D) 0);
    [|rewrite (task_arrow_rank_nonmono R C D) by lia; lia].
    assert (U : task_type_rank R (typ_arrow A B) = 0) by (apply task_arrow_rank_zero; lia).
    assert (V : task_type_rank R (typ_arrow C D) = 0) by (apply task_arrow_rank_zero; lia).
    lia. }
  remember (task_type_rank R (typ_arrow A B) + task_type_rank R (typ_arrow C D)) as N.
  destruct N as [ | N]; [lia|].
  pose proof (task_pow_pair (task_type_rank R C + task_type_rank R A)
    (task_type_rank R B + task_type_rank R D) N ltac:(lia) ltac:(lia)).
  pose proof (task_pow_pos (task_type_rank R C + task_type_rank R A)).
  pose proof (task_pow_pos (task_type_rank R B + task_type_rank R D)).
  lia.
Qed.

Lemma task_bounded_at i v : task_bounded (S i) (fun k => task_at k i v).
Proof. intros k F. apply task_at_neq; lia. Qed.

Lemma task_bounded_zero n : task_bounded n (fun _ => 0).
Proof. red; auto. Qed.

Lemma task_bounded_sum n m p q :
  task_bounded n p -> task_bounded m q ->
  task_bounded (Nat.max n m) (fun i => p i + q i).
Proof. intros F G k H; rewrite F, G; lia. Qed.

Lemma task_bounded_cont :
  (forall cs, exists n, task_bounded n (fun i => task_primary_s i cs)) /\
  (forall cd, exists n, task_bounded n (fun i => task_primary_d i cd)).
Proof.
  apply task_cont_ind; intros; cbn [task_primary_s task_primary_d].
  all: repeat match goal with E : exists _, _ |- _ => destruct E end.
  all: first [solve [eexists; eassumption]|solve [eexists; apply task_bounded_at]|eexists; eapply task_bounded_sum; [apply task_bounded_at|eassumption]].
Qed.

Lemma task_bounded_work R w : exists n, task_bounded n (fun i => task_primary_work R i w).
Proof.
  destruct task_bounded_cont as [HS HD].
  destruct w; unfold task_primary_work;
    try solve [apply HS|apply HD|eexists; apply task_bounded_at|exists 0; apply task_bounded_zero].
  all: match goal with cs : conts |- _ =>
    let n := fresh "bound" in let B := fresh "bounded" in
    destruct (HS cs) as [n B];
    eexists; eapply task_bounded_sum; [apply task_bounded_at|exact B]
  end.
Qed.

Lemma task_bounded_wl R G : exists n, task_bounded n (task_primary R G).
Proof.
  induction G as [|G [n F] x b|G [n F] w].
  - exists 0; red; auto.
  - exists n; intros k H; unfold task_primary; simpl; unfold task_zero_bind; rewrite Nat.add_0_r; apply F; exact H.
  - destruct (task_bounded_work R w) as [m B].
    exists (Nat.max n m); apply task_bounded_sum; assumption.
Qed.

Definition task_vector n (p : nat -> nat) := List.map p (seq 0 n).

Lemma task_vector_nth n p k :
  k < n -> nth k (task_vector n p) 0 = p k.
Proof.
  intro H. unfold task_vector.
  rewrite (nth_indep (List.map p (seq 0 n)) 0 (p 0)) by (rewrite length_map, length_seq; assumption).
  rewrite map_nth, seq_nth by assumption. reflexivity.
Qed.

Definition task_vector_lt n (p q : list nat) :=
  task_poly_lex n (fun k => nth k p 0) (fun k => nth k q 0).

Lemma task_vector_wf n : well_founded (task_vector_lt n).
Proof. unfold task_vector_lt. apply wf_inverse_image, task_poly_lex_wf. Qed.

Lemma task_vector_drop n p q :
  task_bounded n q -> task_poly_less p q ->
  task_bounded n p /\ task_vector_lt n (task_vector n p) (task_vector n q).
Proof.
  intros B [k [L E]].
  assert (K : k < n) by (destruct (le_lt_dec n k); [specialize (B k l); lia|lia]).
  split; [intros j F; rewrite E by lia; auto|].
  unfold task_vector_lt.
  assert (H : forall m, m <= n -> k < m ->
       task_poly_lex m (fun j => nth j (task_vector n p) 0)
                      (fun j => nth j (task_vector n q) 0)).
  { induction m; simpl; intros P Q; [lia|].
    rewrite !task_vector_nth by lia.
    destruct (Nat.eq_dec m k) as [ -> | N]; [now left|].
    right; split; [apply E; lia|apply IHm; lia]. }
  auto.
Qed.

Definition task_world := (atoms * aworklist)%type.
Definition task_measure n (state : task_world) :=
  (task_vector n (task_primary (fst state) (snd state)), task_low_rank (fst state) (snd state)).

Definition task_search_order n x y :=
  slexprod (list nat) (nat * (nat * nat)) (task_vector_lt n) task_low_lt
    (task_measure n x) (task_measure n y).

Lemma task_search_wf n : well_founded (task_search_order n).
Proof. unfold task_search_order. apply wf_inverse_image, wf_slexprod; [apply task_vector_wf|apply task_low_wf]. Qed.

Lemma task_ft_open_any A : forall k T,
  ftvar_in_typ (open_typ_wrt_typ_rec k T A) [<=] union (ftvar_in_typ A) (ftvar_in_typ T).
Proof.
  induction A; intros; simpl; try solve [fsetdec];
    try solve [specialize (IHA (S k) T); fsetdec];
    try solve [specialize (IHA1 k T); specialize (IHA2 k T); fsetdec].
  destruct (lt_eq_lt_dec n k) as [ [] | ]; simpl; fsetdec.
Qed.

Lemma task_type_subst_dom G X A T :
  uniq (awl_to_aenv G) -> task_solution G X A = Some T ->
  dom (awl_to_aenv T) [<=] dom (awl_to_aenv G).
Proof.
  intros U E. apply task_solution_spec in E as [P [K [HS ->]]]; auto.
  pose proof (task_split_perm_env _ _ _ _ _ HS) as J.
  rewrite task_app_env, dom_app, task_dom_after_subst.
  intros y H. apply task_dom_map.
  eapply Permutation_in; [apply Permutation_map, Permutation_sym; exact J|].
  simpl; right. rewrite List.map_app, in_app_iff, <- !task_dom_map. fsetdec.
Qed.

Lemma task_scope_lookup G x A :
  task_scoped empty G -> binds x (abind_var_typ A) (awl_to_aenv G) ->
  ftvar_in_typ A [<=] task_type_dom G.
Proof.
  induction G; simpl; rewrite !task_binds in *; simpl in *; try tauto.
  intros [HS F] [E|B].
  - inversion E; subst; simpl in *; fsetdec.
  - pose proof (IHG HS B). destruct ab; simpl in *; fsetdec.
Qed.

Lemma task_expansion_valid R R0 G w a b c X T :
  uniq (awl_to_aenv G) -> task_scoped empty G -> task_colors R G ->
  a `notin` R -> b `notin` R ->
  task_fresh3 (task_names_state R0 (aworklist_cons_work G w)) a b c ->
  X `in` task_names_work w ->
  task_solution (task_new_holes G a b) X (task_arrow a b) = Some T ->
  uniq (awl_to_aenv T) /\ task_scoped empty T /\ task_colors R T /\
  task_type_dom (task_new_holes G a b) [=] add X (task_type_dom T) /\
  c `notin` dom (awl_to_aenv T) /\
  ftvar_in_typ (task_arrow a b) [<=] task_type_dom T /\
  X `notin` ftvar_in_typ (task_arrow a b).
Proof.
  intros U S C Fa Fb F FX E.
  assert (UN : uniq (awl_to_aenv (task_new_holes G a b))) by (eapply task_fresh_new_holes; eassumption).
  assert (SN : task_scoped empty (task_new_holes G a b)) by (simpl; intuition fsetdec).
  assert (CN : task_colors R (task_new_holes G a b)) by (simpl; tauto).
  pose proof (task_solution_uniq_color _ _ _ _ _ UN CN E) as [UT CT].
  pose proof (task_solution_dom _ _ _ _ UN E) as D.
  pose proof (task_type_subst_dom _ _ _ _ UN E) as DT.
  assert (NX : X `notin` ftvar_in_typ (task_arrow a b)).
  { destruct F as [F1 [F2 F3]]. clear -F1 F2 FX.
    unfold task_names_state in *. simpl in *. task_atomic. }
  assert (FP : ftvar_in_typ (task_arrow a b) [<=] task_type_dom (task_new_holes G a b)) by (simpl; fsetdec).
  pose proof (task_solution_scope _ _ _ _ UN SN FP NX E) as ST.
  assert (Fc : c `notin` dom (awl_to_aenv T)).
  { destruct F as [F1 [F2 F3]]. unfold task_names_state in *. simpl in *.
    pose proof (task_names_dom G) as N. clear -DT N F3; fsetdec. }
  refine (conj UT (conj ST (conj CT (conj D (conj Fc (conj _ NX)))))).
  intros x Hin. pose proof (FP _ Hin) as H.
  apply D in H. apply task_in_add in H as [->|H]; [contradiction|exact H].
Qed.

Definition task_valid R G :=
  uniq (awl_to_aenv G) /\ task_scoped empty G /\ task_colors R G.

Local Ltac task_open_scope :=
  unfold open_typ_wrt_typ, open_exp_wrt_typ, open_exp_wrt_exp in *;
  repeat match goal with
  | |- context [ftvar_in_typ (open_typ_wrt_typ_rec ?k ?T ?A)] =>
      tryif (match goal with H : ftvar_in_typ (open_typ_wrt_typ_rec k T A) [<=] _ |- _ => idtac end) then fail else pose proof (task_ft_open_any A k T)
  | |- context [ftvar_in_exp (open_exp_wrt_typ_rec ?k (typ_var_f ?X) ?e)] =>
      tryif (match goal with H : ftvar_in_exp (open_exp_wrt_typ_rec k (typ_var_f X) e) [<=] _ |- _ => idtac end) then fail else pose proof (proj2 (task_ft_exp_typ_open e k X))
  | |- context [ftvar_in_exp (open_exp_wrt_exp_rec ?k (exp_var_f ?x) ?e)] =>
      tryif (match goal with H : ftvar_in_exp (open_exp_wrt_exp_rec k (exp_var_f x) e) [=] _ |- _ => idtac end) then fail else pose proof (task_ft_exp_exp_open e k x)
  end.

Lemma task_elim_empty x : x `notin` empty.
Proof. fsetdec. Qed.

Lemma task_mem_remove x y D : x `in` remove y D <-> x <> y /\ x `in` D.
Proof.
  split.
  - intro H; split.
    + intro E; eapply AtomSetImpl.remove_1; [symmetry; exact E|exact H].
    + eapply AtomSetImpl.remove_3; eassumption.
  - intros [N H]; apply AtomSetImpl.remove_2; [congruence|exact H].
Qed.

Local Ltac task_pointwise :=
  let x := fresh "X" in
  intros x ?;
  repeat match goal with
  | H : _ [<=] _ |- _ => specialize (H x)
  | H : _ [=] _ |- _ => specialize (H x)
  end;
  repeat progress (rewrite ?task_in_add, ?task_in_union, ?task_in_singleton, ?task_mem_remove in *);
  repeat (let H := fresh in
    match goal with
    | |- context [x `in` empty] =>
        tryif (match goal with _ : x `notin` empty |- _ => idtac end)
        then fail else pose proof (task_elim_empty x) as H
    | _ : context [x `in` empty] |- _ =>
        tryif (match goal with _ : x `notin` empty |- _ => idtac end)
        then fail else pose proof (task_elim_empty x) as H
    end);
  task_atomic.

Lemma task_fresh_environment R G a b c :
  task_fresh3 (task_names_state R G) a b c ->
  a `notin` dom (awl_to_aenv G) /\
  b `notin` add a (dom (awl_to_aenv G)) /\
  c `notin` add b (add a (dom (awl_to_aenv G))) /\
  a `notin` add c R /\ b `notin` add c R /\ c `in` add c R.
Proof.
  intros [A [B C]]. pose proof (task_names_dom G) as D.
  unfold task_names_state in *. repeat split.
  - intro E; apply D in E; task_atomic.
  - rewrite task_in_add; intros [E|E]; [task_atomic|apply D in E; task_atomic].
  - rewrite !task_in_add; intros [E|[E|E]]; try solve [task_atomic].
    apply D in E; task_atomic.
  - task_atomic.
  - task_atomic.
  - task_atomic.
Qed.

Local Ltac task_valid_simpl :=
  cbn [task_scoped awl_to_aenv task_type_dom task_colors
    ftvar_in_work ftvar_in_abind ftvar_in_typ ftvar_in_exp ftvar_in_conts ftvar_in_contd] in *.

Local Ltac task_small_scope :=
  lazymatch goal with |- _ [<=] _ => idtac end;
  repeat match goal with
  | H : task_fresh3 _ _ _ _ |- _ => clear H
  | H : uniq _ |- _ => clear H
  | H : task_scoped _ _ |- _ => clear H
  | H : task_colors _ _ |- _ => clear H
  | H : _ `in` _ -> False |- _ => clear H
  | H : _ `in` _ |- _ => clear H
  | H : binds _ _ _ |- _ => clear H
  end;
  task_open_scope;
  cbn [ftvar_in_typ ftvar_in_exp] in *;
  task_pointwise.

Local Ltac task_preservation_goals :=
  repeat split;
  first [assumption
  | solve [apply uniq_nil]
  | solve [repeat apply uniq_cons; try assumption; simpl in *; task_atomic]
  | solve [task_small_scope]
  | solve [task_atomic]].

(* The search needs unique binding keys, type-variable scope, and
   agreement between the rigid-name set and the binding kinds. *)
Lemma task_step_preserves R a b c G T :
  task_step a b c G T -> task_valid R G ->
  task_fresh3 (task_names_state R G) a b c ->
  task_valid (add c R) T.
Proof.
  destruct 1; intros [U [S C0]] F.
  all: lazymatch type of F with task_fresh3 (task_names_state ?R ?Src) ?a ?b ?c =>
      pose proof (task_fresh_environment R Src a b c F) as [Fa [Fb [Fc [CA [CB CC]]]]];
      assert (FD : c `notin` dom (awl_to_aenv Src)) by task_atomic;
      pose proof (task_colors_extend Src R c FD C0) as Colors;
      clear C0 FD
    end.
  all: unfold task_valid; task_valid_simpl.
  all: destruct S as [SG SW]; try destruct Colors as [Colors CD].
  all: try solve [pose proof (uniq_cons_1 _ _ _ _ U); repeat split; assumption].
  all: try solve [task_preservation_goals].
  all: try solve [
    match goal with E : task_solution ?G ?X ?A = Some ?T |- _ =>
      pose proof (task_solution_uniq_color (add c R) G X A T U Colors E) as [U1 C1];
      assert (FV : ftvar_in_typ A [<=] task_type_dom G) by (clear -SW; fsetdec);
      pose proof (task_solution_scope G X A T U SG FV ltac:(eassumption) E) as S1;
      exact (conj U1 (conj S1 C1))
    end].
  all: try solve [
    match goal with H : binds ?x (abind_var_typ ?A) (awl_to_aenv ?G) |- _ =>
       pose proof (task_scope_lookup G x A SG H)
    end; task_preservation_goals].
  all: try solve [
    match goal with |- context [task_apply_s ?cs _] => destruct cs
      | |- context [task_apply_d ?cd _ _] => destruct cd end;
    cbn [task_apply_s task_apply_d] in *; task_valid_simpl; task_preservation_goals].
  all: try solve [unfold task_new_holes; task_valid_simpl; task_preservation_goals].
  all: try (lazymatch goal with
  | |- context [task_solution (task_new_holes ?G ?a ?b) ?X (task_arrow ?a ?b)] =>
      destruct (task_solution (task_new_holes G a b) X (task_arrow a b)) as [T|] eqn:Sol;
      [|simpl; repeat split; try constructor; exact I]
  end).
  all: try (lazymatch type of F with
  | task_fresh3 (task_names_state ?R (aworklist_cons_work ?G ?w)) ?a ?b ?c =>
    match goal with Sol : task_solution (task_new_holes G a b) ?X (task_arrow a b) = Some ?T |- _ =>
      pose proof (task_expansion_valid (add c R) R G w a b c X T
        U SG Colors CA CB F ltac:(simpl; fsetdec) Sol)
        as [UT [ST [CT [DT [FT [FA NX]]]]]]
    end
  end).
  all: task_valid_simpl.
  all: repeat match goal with
  | |- context [ftvar_in_typ (subst_typ_in_typ ?T ?X ?A)] =>
      tryif (match goal with H : ftvar_in_typ (subst_typ_in_typ T X A) [<=] _ |- _ => idtac end)
      then fail else pose proof (task_ft_subst_typ T X A)
  | |- context [ftvar_in_exp (subst_typ_in_exp ?T ?X ?e)] =>
      tryif (match goal with H : ftvar_in_exp (subst_typ_in_exp T X e) [<=] _ |- _ => idtac end)
      then fail else pose proof (task_ft_subst_exp T X e)
  | |- context [ftvar_in_contd (subst_typ_in_contd ?T ?X ?cd)] =>
      tryif (match goal with H : ftvar_in_contd (subst_typ_in_contd T X cd) [<=] _ |- _ => idtac end)
      then fail else pose proof (proj2 (task_ft_subst_cont T X) cd)
  end.
  all: try match goal with
  | |- context [subst_typ_in_exp _ _ (open_exp_wrt_exp ?e (exp_var_f ?z))] =>
      pose proof (task_ft_exp_exp_open e 0 z)
  end.
  all: cbn [task_new_holes task_type_dom task_arrow ftvar_in_typ ftvar_in_work] in *.
  all: repeat split.
  all: try solve [assumption | apply uniq_nil |
    repeat apply uniq_cons; try assumption; simpl in *; task_atomic |
    task_small_scope | task_atomic].
Qed.

Lemma task_etvar_color R G X :
  task_colors R G -> binds X abind_etvar_empty (awl_to_aenv G) -> X `notin` R.
Proof. intros C B; apply task_colors_binds in C as [_ [_ CE]]; auto. Qed.

Lemma task_arrow_zero R a b :
  a `notin` R -> b `notin` R -> task_type_rank R (task_arrow a b) = 0.
Proof.
  intros Fa Fb; simpl; rewrite (proj2 (task_mem_false _ _) Fa), (proj2 (task_mem_false _ _) Fb); reflexivity.
Qed.

Lemma task_solution_ranks R G A X T :
  uniq (awl_to_aenv G) -> task_solution G X A = Some T ->
  X `notin` R -> task_type_rank R A = 0 ->
  (forall k, task_primary R G k = task_primary R T k) /\
  task_secondary R G = task_secondary R T /\
  task_holes G = S (task_holes T).
Proof.
  intros U E F Z. split; [intro k|split].
  - pose proof (task_sum_solution task_zero_bind (task_primary_work R k) _ _ _ _ U E
      ltac:(reflexivity) ltac:(intro; apply task_primary_subst; assumption)) as H.
    unfold task_primary, task_zero_bind in *. lia.
  - pose proof (task_sum_solution task_zero_bind (task_secondary_work R) _ _ _ _ U E
      ltac:(reflexivity) ltac:(intro; apply task_secondary_subst; assumption)) as H.
    unfold task_secondary, task_zero_bind in *. lia.
  - eapply task_holes_solution; eassumption.
Qed.

Lemma task_new_holes_ranks R G X a b T :
  uniq (awl_to_aenv (task_new_holes G a b)) ->
  task_solution (task_new_holes G a b) X (task_arrow a b) = Some T ->
  X `notin` R -> task_type_rank R (task_arrow a b) = 0 ->
  (forall k, task_primary R G k = task_primary R T k) /\ task_secondary R G = task_secondary R T.
Proof.
  intros U E NX Z.
  destruct (task_solution_ranks _ _ _ _ _ U E NX Z) as [P [S H]].
  split.
  - intro k; specialize (P k).
    change (task_primary R G k + 0 + 0 = task_primary R T k) in P; lia.
  - change (task_secondary R G + 0 + 0 = task_secondary R T) in S; lia.
Qed.

Lemma task_work_size_positive w : size_work w > 0.
Proof. destruct w; simpl; lia. Qed.

Lemma task_low_pop R G w :
  task_low_lt (task_low_rank R G) (task_low_rank R (aworklist_cons_work G w)).
Proof.
  unfold task_low_lt, task_low_rank.
  destruct (Nat.eq_dec (task_secondary_work R w) 0).
  - unfold task_secondary at 2; cbn [task_sum].
    rewrite e, Nat.add_0_r.
    apply right_slex.
    unfold task_holes at 2; cbn [task_sum task_zero_work]; rewrite Nat.add_0_r.
    apply right_slex.
    change (task_size G < task_size G + size_work w). pose proof (task_work_size_positive w); lia.
  - apply left_slex. change (task_secondary R G < task_secondary R G + task_secondary_work R w). lia.
Qed.

Lemma task_low_empty R G :
  task_size G > 0 -> task_low_lt (task_low_rank R aworklist_empty) (task_low_rank R G).
Proof.
  intro F. unfold task_low_lt, task_low_rank.
  change (slexprod nat (nat * nat) lt (slexprod nat nat lt lt)
            (0,(0,0)) (task_secondary R G,(task_holes G,task_size G))).
  destruct (Nat.eq_dec (task_secondary R G) 0) as [E|N].
  - rewrite E; apply right_slex. destruct (Nat.eq_dec (task_holes G) 0) as [D|M].
    + rewrite D; apply right_slex; exact F.
    + apply left_slex; lia.
  - apply left_slex; lia.
Qed.

Lemma task_bounded_nonzero n p :
  task_bounded n p ->
  (forall k, p k = 0) \/ task_poly_less (fun _ => 0) p.
Proof.
  induction n; intro B.
  - left; intro k; apply B; lia.
  - destruct (Nat.eq_dec (p n) 0) as [E|L].
    + apply IHn. intros k F. destruct (Nat.eq_dec n k) as [ -> | N]; [exact E|apply B; lia].
    + right. exists n; split; [lia|intros; symmetry; apply B; lia].
Qed.

Lemma task_empty_decrease R G :
  task_size G > 0 ->
  task_poly_less (task_primary R aworklist_empty) (task_primary R G) \/
    (forall k, task_primary R aworklist_empty k = task_primary R G k) /\
    task_low_lt (task_low_rank R aworklist_empty) (task_low_rank R G).
Proof.
  intro H. destruct (task_bounded_wl R G) as [n B].
  destruct (task_bounded_nonzero n _ B) as [E | D]; [right; split|left; exact D].
  - intro k; symmetry; apply E.
  - now apply task_low_empty.
Qed.

Local Ltac task_simpl_p :=
  unfold task_primary;
  cbn [task_sum task_zero_bind task_primary_work task_primary_s task_primary_d task_new_holes];
  try unfold task_zero_bind;
  unfold open_typ_wrt_typ, open_exp_wrt_typ, open_exp_wrt_exp;
  unfold task_check_index, task_infer_index, task_argument_index in *;
  rewrite ?task_exp_rank_subst, ?task_exp_rank_open_t, ?task_exp_rank_open_e;
  cbn [task_exp_rank] in *; cbn [task_type_rank];
  repeat match goal with
  | |- context [task_exp_rank ?e] =>
      tryif (match goal with _ : 0 < task_exp_rank e |- _ => idtac end) then fail else pose proof (task_exp_rank_positive e)
  end;
  rewrite ?task_at_eq;
  repeat match goal with
  | |- context [task_at ?k ?i ?n] => rewrite (task_at_neq k i n) by lia
  end.

Local Ltac task_same_p :=
  let i := fresh "index" in intro i; task_simpl_p;
  try match goal with H : forall k, task_primary _ _ k = task_primary _ _ k |- _ =>
    specialize (H i); unfold task_primary, task_zero_bind in H
  end;
  rewrite ?(proj1 (task_primary_cont_subst i _ _)), ?(proj2 (task_primary_cont_subst i _ _));
  lia.

Local Ltac task_compare_prefix k :=
  try match goal with H : forall i, task_primary _ _ i = task_primary _ _ i |- _ =>
    let E := fresh "Prefix" in
    pose proof (H k) as E;
    unfold task_primary, task_zero_bind, task_check_index, task_infer_index,
      task_argument_index in E;
    cbn [task_exp_rank] in E
  end.

Local Ltac task_pivot i :=
  left; exists i; split;
  [task_simpl_p; task_compare_prefix i
  | let j := fresh "index" in
    intros j Above; task_simpl_p; task_compare_prefix j].

Local Ltac task_calc_s :=
  unfold task_secondary;
  cbn [task_secondary_work task_sum task_zero_bind task_abs_cost task_tapp_cost task_head_rank task_new_holes];
  try unfold task_zero_bind;
  unfold open_typ_wrt_typ in *;
  rewrite ?task_head_rank_open; repeat rewrite Nat.add_0_r.

Local Ltac task_s_drop :=
  right; split; [task_same_p|apply left_slex; task_calc_s; lia].

Local Ltac task_sub_smaller :=
  right; split; [task_same_p|apply left_slex; task_calc_s];
  match goal with
  | |- ?t + (3^?a - 1) < ?t + (3^?b - 1) =>
      let H := fresh in
      assert (H : a < b) by
        (cbn [task_type_rank];
         repeat match goal with |- context [task_type_rank ?R (open_typ_wrt_typ_rec ?k (typ_var_f ?x) ?A)] =>
           tryif (match goal with _ : task_type_rank R (open_typ_wrt_typ_rec k (typ_var_f x) A) <= _ |- _ => idtac end) then fail else pose proof (task_rank_open R A k x)
         end; lia);
      pose proof (task_pow_step a b H); lia
  end.

Local Ltac task_sub_split :=
  right; split; [task_same_p|apply left_slex; task_calc_s];
  match goal with
  | |- _ + (3^?a - 1) + (3^?b - 1) < _ + (3^?d - 1) =>
    let Bound := fresh in
    let H := fresh in
    assert (Bound : exists n, d = S n /\ a <= n /\ b <= n) by
      (cbn [task_type_rank]; rewrite ?Nat.add_succ_l, ?Nat.add_succ_r; eexists; repeat split; try reflexivity; try lia);
    destruct Bound as [n [E [L M]]];
    rewrite E; pose proof (task_pow_pair a b n L M);
    pose proof (task_pow_pos a); pose proof (task_pow_pos b); lia
  end.

Lemma task_step_rank_fixed R R0 a b c G T :
  task_step a b c G T -> task_valid R G ->
  task_fresh3 (task_names_state R0 G) a b c ->
  a `notin` R -> b `notin` R ->
  task_poly_less (task_primary R T) (task_primary R G) \/
    (forall k, task_primary R T k = task_primary R G k) /\
    task_low_lt (task_low_rank R T) (task_low_rank R G).
Proof.
  destruct 1; intros [U [S C0]] F Fa Fb.
  - right; split; [task_same_p|].
    unfold task_low_rank, task_low_lt, task_secondary; cbn [task_sum]; unfold task_zero_bind; rewrite Nat.add_0_r.
    apply right_slex. unfold task_holes. cbn [task_sum].
    destruct d; unfold task_etvar_weight; try rewrite Nat.add_0_r;
      first [apply left_slex; lia | apply right_slex;
        change (task_size G < task_size G + 1); lia].
  - right; split; [task_same_p|apply task_low_pop].
  - right; split; [task_same_p|apply task_low_pop].
  - right; split; [task_same_p|apply task_low_pop].
  - right; split; [task_same_p|apply task_low_pop].
  - right; split; [task_same_p|].
    destruct (Nat.eq_dec (task_type_rank R (typ_arrow A B) + task_type_rank R (typ_arrow C D)) 0) as [Z|N].
    + assert (Z1 : task_type_rank R (typ_arrow A B) = 0) by lia.
      assert (Z2 : task_type_rank R (typ_arrow C D) = 0) by lia.
      apply task_arrow_rank_zero in Z1 as [ZA ZB].
      apply task_arrow_rank_zero in Z2 as [ZC ZD].
      unfold task_low_rank, task_low_lt; task_calc_s.
      rewrite ZA, ZB, ZC, ZD, Z. simpl Nat.pow; repeat rewrite Nat.add_0_r.
      apply right_slex.
      cbn [task_holes task_sum task_zero_work]; repeat rewrite Nat.add_0_r.
      apply right_slex.
      cbn [task_size task_sum size_work size_typ]; lia.
    + apply left_slex. pose proof (task_secondary_sub_arrow R A B C D ltac:(lia)).
      cbn [task_secondary_work] in H. task_calc_s. lia.
  - task_sub_smaller.
  - task_sub_smaller.
  - pose proof (task_etvar_color R G X C0 ltac:(assumption)) as NX.
    pose proof (task_arrow_zero R a b Fa Fb) as Z.
    pose proof (task_fresh_new_holes R0 G _ a b c U F) as UN.
    destruct (task_solution (task_new_holes G a b) X (task_arrow a b)) as [T|] eqn:E.
    2: { apply task_empty_decrease. cbn [task_size task_sum].
         pose proof (task_work_size_positive (work_sub (typ_var_f X) (typ_arrow A B))); lia. }
    pose proof (task_new_holes_ranks R G X a b T UN E NX Z) as [PR SR].
    assert (Rank : 0 < task_type_rank R (typ_arrow A B)).
    { apply Nat.neq_0_lt_0; intro N; match goal with H : ~ a_mono_typ _ _ |- _ => apply H end.
      eapply task_rank_zero; [exact C0| |exact N]. simpl in S |- *; intuition fsetdec. }
    right; split; [task_same_p|apply left_slex].
    task_calc_s. unfold task_secondary, task_zero_bind in SR.
    assert (ZA : task_type_rank R (typ_var_f a) = 0)
      by (simpl; now rewrite (proj2 (task_mem_false _ _) Fa)).
    assert (ZB : task_type_rank R (typ_var_f b) = 0)
      by (simpl; now rewrite (proj2 (task_mem_false _ _) Fb)).
    assert (ZX : task_type_rank R (typ_var_f X) = 0)
      by (simpl; now rewrite (proj2 (task_mem_false _ _) NX)).
    pose proof (task_arrow_rank_lb R A B).
    assert (RB : 0 < task_type_rank R A + task_type_rank R B).
    { destruct (Nat.eq_dec (task_type_rank R A + task_type_rank R B) 0); [|lia].
      assert (task_type_rank R (typ_arrow A B) = 0) by (apply task_arrow_rank_zero; lia).
      lia. }
    rewrite ZA, ZB, ZX, (task_arrow_rank_nonmono _ _ _ RB).
    rewrite !task_rank_subst by assumption.
    pose proof (task_pow_pair (task_type_rank R A) (task_type_rank R B)
      (task_type_rank R A + task_type_rank R B) ltac:(lia) ltac:(lia)).
    pose proof (task_pow_pos (task_type_rank R A)).
    pose proof (task_pow_pos (task_type_rank R B)).
    repeat rewrite Nat.add_0_r in *; cbn [Nat.add] in *; lia.
  - pose proof (task_etvar_color R G X C0 ltac:(assumption)) as NX.
    pose proof (task_arrow_zero R a b Fa Fb) as Z.
    pose proof (task_fresh_new_holes R0 G _ a b c U F) as UN.
    destruct (task_solution (task_new_holes G a b) X (task_arrow a b)) as [T|] eqn:E.
    2: { apply task_empty_decrease. cbn [task_size task_sum].
         pose proof (task_work_size_positive (work_sub (typ_arrow A B) (typ_var_f X))); lia. }
    pose proof (task_new_holes_ranks R G X a b T UN E NX Z) as [PR SR].
    assert (Rank : 0 < task_type_rank R (typ_arrow A B)).
    { apply Nat.neq_0_lt_0; intro N; match goal with H : ~ a_mono_typ _ _ |- _ => apply H end.
      eapply task_rank_zero; [exact C0| |exact N]. simpl in S |- *; intuition fsetdec. }
    right; split; [task_same_p|apply left_slex].
    task_calc_s. unfold task_secondary, task_zero_bind in SR.
    assert (ZA : task_type_rank R (typ_var_f a) = 0)
      by (simpl; now rewrite (proj2 (task_mem_false _ _) Fa)).
    assert (ZB : task_type_rank R (typ_var_f b) = 0)
      by (simpl; now rewrite (proj2 (task_mem_false _ _) Fb)).
    assert (ZX : task_type_rank R (typ_var_f X) = 0)
      by (simpl; now rewrite (proj2 (task_mem_false _ _) NX)).
    pose proof (task_arrow_rank_lb R A B).
    assert (RB : 0 < task_type_rank R A + task_type_rank R B).
    { destruct (Nat.eq_dec (task_type_rank R A + task_type_rank R B) 0); [|lia].
      assert (task_type_rank R (typ_arrow A B) = 0) by (apply task_arrow_rank_zero; lia).
      lia. }
    rewrite ZA, ZB, ZX, (task_arrow_rank_nonmono _ _ _ RB).
    rewrite !task_rank_subst by assumption.
    pose proof (task_pow_pair (task_type_rank R A) (task_type_rank R B)
      (task_type_rank R A + task_type_rank R B) ltac:(lia) ltac:(lia)).
    pose proof (task_pow_pos (task_type_rank R A)).
    pose proof (task_pow_pos (task_type_rank R B)).
    repeat rewrite Nat.add_0_r in *; cbn [Nat.add] in *; lia.
  - pose proof (task_etvar_color R G X C0 ltac:(assumption)) as NX.
    pose proof (task_rank_mono R G A C0 ltac:(assumption)) as Z.
    match goal with E : task_solution _ _ _ = Some _ |- _ =>
      pose proof (task_solution_ranks R G A X T U E NX Z) as [P [D Holes]]
    end.
    right; split; [task_same_p|].
    unfold task_low_rank, task_low_lt, task_secondary in *.
    cbn [task_sum task_secondary_work].
    assert (ZX : task_type_rank R (typ_var_f X) = 0)
      by (simpl; now rewrite (proj2 (task_mem_false _ _) NX)).
    rewrite Z, ZX; simpl Nat.pow; repeat rewrite Nat.add_0_r.
    rewrite D.
    apply right_slex, left_slex. unfold task_holes in *. cbn [task_sum task_zero_work]; lia.
  - pose proof (task_etvar_color R G X C0 ltac:(assumption)) as NX.
    pose proof (task_rank_mono R G A C0 ltac:(assumption)) as Z.
    match goal with E : task_solution _ _ _ = Some _ |- _ =>
      pose proof (task_solution_ranks R G A X T U E NX Z) as [P [D Holes]]
    end.
    right; split; [task_same_p|].
    unfold task_low_rank, task_low_lt, task_secondary in *.
    cbn [task_sum task_secondary_work].
    assert (ZX : task_type_rank R (typ_var_f X) = 0)
      by (simpl; now rewrite (proj2 (task_mem_false _ _) NX)).
    rewrite Z, ZX; simpl Nat.pow; repeat rewrite Nat.add_0_r.
    rewrite D.
    apply right_slex, left_slex. unfold task_holes in *. cbn [task_sum task_zero_work]; lia.
  - task_sub_split.
  - task_sub_smaller.
  - task_sub_smaller.
  - task_sub_smaller.
  - task_sub_smaller.
  - task_sub_split.
  - task_pivot (task_check_index e); try lia.
    match goal with |- context [3 ^ ?n] => pose proof (task_pow_pos n); lia end.
  - task_pivot (task_check_index (exp_abs e)); try lia.
    match goal with |- context [3 ^ ?n] => pose proof (task_pow_pos n); lia end.
  - pose proof (task_etvar_color R G X C0 ltac:(assumption)) as NX.
    pose proof (task_arrow_zero R a b Fa Fb) as Z.
    pose proof (task_fresh_new_holes R0 G _ a b c U F) as UN.
    destruct (task_solution (task_new_holes G a b) X (task_arrow a b)) as [T|] eqn:E.
    2: { apply task_empty_decrease. cbn [task_size task_sum].
         pose proof (task_work_size_positive (work_check (exp_abs e) (typ_var_f X))); lia. }
    pose proof (task_new_holes_ranks R G X a b T UN E NX Z) as [PR SR].
    task_pivot (task_check_index (exp_abs e)); try lia.
    rewrite (proj2 (task_mem_false _ _) NX). cbn [Nat.pow]; lia.
  - task_pivot (task_check_index (exp_abs e)); try lia.
    match goal with |- context [3 ^ ?n] => pose proof (task_pow_pos n); lia end.
  - task_pivot (task_check_index e); try lia.
    pose proof (task_pow_pair (task_type_rank R A) (task_type_rank R B)
      (task_type_rank R A + task_type_rank R B) ltac:(lia) ltac:(lia)).
    lia.
  - task_pivot (task_check_index e); try lia.
    apply Nat.add_lt_mono_l, Nat.pow_lt_mono_r; lia.
  - task_pivot (task_check_index e); try lia.
    apply Nat.add_lt_mono_l, Nat.pow_lt_mono_r; lia.
  - task_pivot (task_infer_index (exp_var_f X)); lia.
  - task_pivot (task_infer_index (exp_anno e A)); lia.
  - task_pivot (task_infer_index (exp_tabs (exp_anno e A))); lia.
  - task_pivot (task_infer_index (exp_abs e)); lia.
  - task_pivot (task_infer_index exp_unit); lia.
  - task_pivot (task_infer_index (exp_app e f)); lia.
  - task_pivot (task_argument_index e); lia.
  - task_s_drop.
  - task_s_drop.
  - task_s_drop.
  - task_s_drop.
  - task_s_drop.
  - task_s_drop.
  - task_s_drop.
  - task_s_drop.
  - pose proof (task_etvar_color R G X C0 ltac:(assumption)) as NX.
    pose proof (task_arrow_zero R a b Fa Fb) as Z.
    pose proof (task_fresh_new_holes R0 G _ a b c U F) as UN.
    destruct (task_solution (task_new_holes G a b) X (task_arrow a b)) as [T|] eqn:E.
    2: { apply task_empty_decrease. cbn [task_size task_sum].
         pose proof (task_work_size_positive (work_infabs (typ_var_f X) cd)); lia. }
    pose proof (task_new_holes_ranks R G X a b T UN E NX Z) as [PR SR].
    right; split; [task_same_p|apply left_slex; task_calc_s].
    pose proof (task_secondary_subst R (task_arrow a b) X (work_applyd cd typ_unit typ_unit) NX Z) as Ecost.
    cbn [subst_typ_in_work task_secondary_work] in Ecost.
    rewrite Ecost. unfold task_secondary, task_zero_bind in SR. lia.
  - task_pivot (task_infer_index (exp_tapp e A)); lia.
  - task_s_drop.
  - task_s_drop.
  - task_s_drop.
  - task_s_drop.
  - task_s_drop.
  - task_s_drop.
  - task_s_drop.
  - destruct cs; cbn [task_apply_s].
    + task_pivot 0; lia.
    + task_pivot 0; lia.
    + task_s_drop.
    + task_s_drop.
    + task_pivot 0; lia.
  - destruct cd; cbn [task_apply_d]; task_s_drop.
Qed.

Lemma task_progress n R a b c G T :
  task_step a b c G T -> task_valid R G ->
  task_fresh3 (task_names_state R G) a b c ->
  task_bounded n (task_primary R G) ->
  task_search_order n (add c R,T) (R,G) /\
  task_bounded n (task_primary (add c R) T).
Proof.
  intros S [U [SC C]] F B.
  pose proof F as [F1 [F2 F3]]. unfold task_names_state in F1,F2,F3.
  pose proof (task_names_dom G).
  assert (FR : c `notin` task_names_aworklist G) by task_atomic.
  assert (FC : c `notin` dom (awl_to_aenv G)) by fsetdec.
  assert (V : task_valid (add c R) G) by (repeat split; auto using task_colors_extend).
  pose proof (task_step_rank_fixed (add c R) R a b c G T S V F
    ltac:(task_atomic) ltac:(task_atomic)) as [D|[E D]].
  - assert (P : task_poly_less (task_primary (add c R) T) (task_primary R G)).
    { destruct D as [k [L Same]]. exists k; split.
      - now rewrite <- (task_primary_fresh R c G FR k).
      - intros j J. now rewrite <- (task_primary_fresh R c G FR j), Same by assumption. }
    destruct (task_vector_drop _ _ _ B P) as [BT LT].
    split; [unfold task_search_order, task_measure; simpl; now apply left_slex|exact BT].
  - assert (PE : forall k, task_primary (add c R) T k = task_primary R G k)
      by (intro k; now rewrite E, task_primary_fresh by assumption).
    split.
    + unfold task_search_order, task_measure; simpl.
      assert (VE : task_vector n (task_primary (add c R) T) = task_vector n (task_primary R G))
        by (unfold task_vector; apply List.map_ext; exact PE).
      rewrite VE. apply right_slex.
      unfold task_low_rank in *. now rewrite <- (task_secondary_fresh R c G FR).
    + intros k K. rewrite PE; auto.
Qed.

Lemma task_list_exists (P : aworklist -> Prop) (l : list aworklist) :
  (forall t, List.In t l -> P t \/ ~ P t) ->
  (exists t, List.In t l /\ P t) \/ ~ (exists t, List.In t l /\ P t).
Proof.
  induction l as [|x l IH]; simpl; intros D.
  - right; intros [t [ [] _]].
  - destruct (D x ltac:(auto)) as [Y|N].
    + left; exists x; auto.
    + destruct (IH ltac:(eauto)) as [ [t [F Y]]|Z].
      * left; exists t; auto.
      * right; intros [t [ [ <-|F] Y]]; [exact (N Y)|apply Z; eauto].
Qed.

Lemma task_empty_dec (G : aworklist) : G = aworklist_empty \/ G <> aworklist_empty.
Proof. destruct G; auto; right; discriminate. Qed.

(* A finite traversal of the successor list under the well-founded
   order decides whether any branch reaches the empty worklist. *)
Lemma task_search n : forall st : task_world,
  task_valid (fst st) (snd st) ->
  task_bounded n (task_primary (fst st) (snd st)) ->
  a_wl_red (snd st) \/ ~ a_wl_red (snd st).
Proof.
  refine (well_founded_induction (task_search_wf n)
    (fun st => task_valid (fst st) (snd st) ->
      task_bounded n (task_primary (fst st) (snd st)) ->
      a_wl_red (snd st) \/ ~ a_wl_red (snd st)) _).
  intros [R G] IH V B. simpl in *.
  destruct (task_empty_dec G) as [ -> | NE]; [left; constructor|].
  destruct (task_pick3 (task_names_state R G)) as [ [ [a b] c] F].
  assert (D : forall T, List.In T (task_successors a b c G) ->
              a_wl_red T \/ ~ a_wl_red T).
  { intros T HT. apply task_successors_sound in HT.
    destruct (task_progress n R a b c G T HT V F B) as [L BT].
    exact (IH (add c R,T) L (task_step_preserves R a b c G T HT V F) BT). }
  destruct (task_list_exists a_wl_red _ D) as [ [T [MEM OK]]|No].
  - left. eapply task_step_red; [apply task_successors_sound; exact MEM|apply V|exact F|exact OK].
  - right; intro H; apply No.
    destruct (task_red_step R a b c G H (proj1 V) F) as [E | [T [ST OK]]]; [contradiction|].
    exists T; split; [now apply task_successors_complete|exact OK].
Qed.

Theorem a_wf_wl_red_decidable_thm : forall Γ,
  ⊢ᵃʷₛ Γ ->
  Γ ⟶ᵃʷ⁎⋅ \/ ~ Γ ⟶ᵃʷ⁎⋅.
Proof.
  intros Γ WF.
  destruct (task_wf_wl_init Γ WF) as [U S].
  set (R := task_rigids Γ).
  destruct (task_bounded_wl R Γ) as [n B].
  exact (task_search n (R,Γ) (conj U (conj S (task_colors_init Γ U))) B).
Qed.
