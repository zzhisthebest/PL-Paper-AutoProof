Require Import Metalib.Metatheory.

Require Import Lia.

Inductive typ : Set :=
 | t_int : typ
 | t_top : typ
 | t_bot : typ
 | t_arrow : typ -> typ -> typ
 | t_union : typ -> typ -> typ
 | t_and : typ -> typ -> typ
 | t_unit : typ
 | t_prim (n:var).

Definition envp : Set := list ( atom * typ ).

Inductive wft (PG:envp) : typ -> Prop :=
  | wft_top :
      wft PG t_top
  | wft_bot :
      wft PG t_bot
  | wft_int :
      wft PG t_int
  | wft_arrow : forall A B,
      wft PG A ->
      wft PG B ->
      wft PG (t_arrow A B)
  | wft_or : forall A B,
      wft PG A ->
      wft PG B ->
      wft PG (t_union A B)
  | wft_and : forall A B,
      wft PG A ->
      wft PG B ->
      wft PG (t_and A B)
  | wft_unit :
      wft PG t_unit
  | wft_prim : forall i A,
      binds i A PG ->
      wft PG (t_prim i).

Inductive okenvp : envp -> Prop :=
  | okenvp_empty :
      okenvp nil
  | okenvp_cons : forall (PG:envp) (i:var),
      okenvp PG ->
      i `notin` (dom PG) ->
      okenvp ((i, t_top) :: PG)
  | okenvp_sub : forall (PG:envp) (i j:var),
      okenvp PG ->
      wft PG (t_prim j) ->
      i `notin` (dom PG) ->
      okenvp ((i, (t_prim j)) :: PG).

Inductive declarative_subtyping (PG: envp) : typ -> typ -> Prop :=
 | DS_refl : forall (A:typ),
     okenvp PG ->
     wft PG A ->
     declarative_subtyping PG A A
 | DS_trans : forall (A C B:typ),
     declarative_subtyping PG A B ->
     declarative_subtyping PG B C ->
     declarative_subtyping PG A C
 | DS_top : forall (A:typ),
     okenvp PG ->
     wft PG A ->
     declarative_subtyping PG A t_top
 | DS_bot : forall (A:typ),
     okenvp PG ->
     wft PG A ->
     declarative_subtyping PG t_bot A
 | DS_arrow : forall (A C B D:typ),
     declarative_subtyping PG B A ->
     declarative_subtyping PG C D ->
     declarative_subtyping PG (t_arrow A C) (t_arrow B D)
 | DS_and : forall (A B C:typ),
     declarative_subtyping PG A B ->
     declarative_subtyping PG A C ->
     declarative_subtyping PG A (t_and B C)
 | DS_andl : forall (A B:typ),
     okenvp PG ->
     wft PG A -> wft PG B ->
     declarative_subtyping PG (t_and A B) A
 | DS_andr : forall (A B:typ),
     okenvp PG ->
     wft PG A -> wft PG B ->
     declarative_subtyping PG (t_and A B) B
 | DS_or : forall (A B C:typ),
     declarative_subtyping PG A C ->
     declarative_subtyping PG B C ->
     declarative_subtyping PG (t_union A B) C
 | DS_orl : forall (A B:typ),
     okenvp PG ->
     wft PG A -> wft PG B ->
     declarative_subtyping PG A (t_union A B)
 | DS_orr : forall (B A:typ),
     okenvp PG ->
     wft PG A -> wft PG B ->
     declarative_subtyping PG B (t_union A B)
 | DS_distArr : forall (A B1 B2:typ),
     okenvp PG ->
     wft PG A -> wft PG B1 -> wft PG B2 ->
     declarative_subtyping PG (t_and  (t_arrow A B1)   (t_arrow A B2) ) (t_arrow A (t_and B1 B2))
| DS_distArrU : forall (A1 B A2:typ),
     okenvp PG ->
     wft PG A1 -> wft PG A2 -> wft PG B ->
     declarative_subtyping PG (t_and  (t_arrow A1 B)   (t_arrow A2 B) ) (t_arrow (t_union A1 A2) B)
 | DS_distOr : forall (A1 B A2:typ),
     okenvp PG ->
     wft PG A1 -> wft PG A2 -> wft PG B ->
     declarative_subtyping PG (t_and  (t_union A1 B)   (t_union A2 B) ) (t_union  (t_and A1 A2)  B)
 | DS_prim : forall i A,
     okenvp PG ->
     binds i A PG ->
     declarative_subtyping PG (t_prim i) A.

Inductive ordu : typ -> Prop :=
 | OU_top :
     ordu t_top
 | OU_bot :
     ordu t_bot
 | OU_int :
     ordu t_int
 | OU_arrow : forall (A B:typ),
     ordu (t_arrow A B)
 | OU_and : forall (A B:typ),
     ordu A ->
     ordu B ->
     ordu (t_and A B)
 | OU_null :
     ordu t_unit
 | OU_prim : forall (i:var),
     ordu (t_prim i).

Inductive ordi : typ -> Prop :=
 | OI_top :
     ordi t_top
 | OI_bot :
     ordi t_bot
 | OI_int :
     ordi t_int
 | OI_arrow : forall (A B:typ),
     ordu A ->
     ordi B ->
     ordi (t_arrow A B)
 | OI_or : forall (A B:typ),
     ordi A ->
     ordi B ->
     ordi (t_union A B)
 | OI_null :
     ordi t_unit
 | OI_prim : forall (i:var),
     ordi (t_prim i).

Inductive splu : typ -> typ -> typ -> Prop :=
 | SpU_or : forall (A B:typ),
     splu (t_union A B) A B
 | SpU_andl : forall (A B A1 A2:typ),
     splu A A1 A2 ->
     splu (t_and A B) (t_and A1 B) (t_and A2 B)
 | SpU_andr : forall (A B B1 B2:typ),
     ordu A ->
     splu B B1 B2 ->
     splu (t_and A B) (t_and A B1) (t_and A B2).

Inductive spli : typ -> typ -> typ -> Prop :=
 | SpI_and : forall (A B:typ),
     spli (t_and A B) A B
 | SpI_arrow : forall (A B C D:typ),
     spli B C D ->
     spli (t_arrow A B) (t_arrow A C) (t_arrow A D)
 | SpI_arrowUnion : forall (A D B C:typ),
     ordi D ->
     splu A B C ->
     spli (t_arrow A D) (t_arrow B D) (t_arrow C D)
 | SpI_orl : forall (A B A1 A2:typ),
     spli A A1 A2 ->
     spli (t_union A B) (t_union A1 B) (t_union A2 B)
 | SpI_orr : forall (A B B1 B2:typ),
     ordi A ->
     spli B B1 B2 ->
     spli (t_union A B) (t_union A B1) (t_union A B2).

Inductive algo_sub : envp -> typ -> typ -> Prop :=
 | AS_refl : forall PG A,
     okenvp PG ->
     wft PG A ->
     algo_sub PG A A
 | AS_prim_neq : forall PG i A n1 n2,
     okenvp ((i, A) :: PG) ->

     i <> n1 ->
     algo_sub PG (t_prim n1) (t_prim n2) ->
     algo_sub (((i, A))::PG) (t_prim n1) (t_prim n2)
 | AS_prim_eq : forall PG j n1 n2,
     okenvp (((n1,t_prim j))::PG) ->

     algo_sub PG (t_prim j) (t_prim n2) ->
     algo_sub (((n1,t_prim j))::PG) (t_prim n1) (t_prim n2)
 | AS_top : forall PG (A:typ),
     okenvp PG ->
     wft PG A ->
     algo_sub PG A t_top
 | AS_bot : forall PG (A:typ),
     okenvp PG ->
     wft PG A ->
     algo_sub PG t_bot A
 | AS_arrow : forall PG (A1 A2 B1 B2:typ),
     algo_sub PG B1 A1 ->
     algo_sub PG A2 B2 ->
     algo_sub PG (t_arrow A1 A2) (t_arrow B1 B2)
 | AS_and : forall PG (A B B1 B2:typ),
     spli B B1 B2 ->
     algo_sub PG A B1 ->
     algo_sub PG A B2 ->
     algo_sub PG A B
 | AS_andl : forall PG (A B A1 A2:typ),
     wft PG A2 ->
     spli A A1 A2 ->
     algo_sub PG A1 B ->
     algo_sub PG A B
 | AS_andr : forall PG (A B A1 A2:typ),
     wft PG A1 ->
     spli A A1 A2 ->
     algo_sub PG A2 B ->
     algo_sub PG A B
 | AS_or : forall PG (A B A1 A2:typ),
     splu A A1 A2 ->
     algo_sub PG A1 B ->
     algo_sub PG A2 B ->
     algo_sub PG A B
 | AS_orl : forall PG (A B B1 B2:typ),
     wft PG B2 ->
     splu B B1 B2 ->
     algo_sub PG A B1 ->
     algo_sub PG A B
 | AS_orr : forall PG (A B B1 B2:typ),
     wft PG B1 ->
     splu B B1 B2 ->
     algo_sub PG A B2 ->
     algo_sub PG A B.

Fixpoint size_typ (A1 : typ) {struct A1} : nat :=
  match A1 with
    | t_int => 1
    | t_top => 1
    | t_bot => 1
    | t_unit => 1
    | t_prim _ => 1
    | t_arrow A2 B1 => 1 + (size_typ A2) + (size_typ B1)
    | t_and A2 B1 => 1 + (size_typ A2) + (size_typ B1)
    | t_union A2 B1 => 1 + (size_typ A2) + (size_typ B1)
  end.

Fixpoint size_envp (G : envp) := match G with
                                 | nil => 0
                                 | (i, A) :: G => size_envp G + size_typ A + 1
                                     end.

Lemma typ_eq_dec : forall (A B:typ), {A = B} + {A <> B}.
Proof. decide equality; apply eq_dec. Qed.

Fixpoint ordu_dec (A:typ) : {ordu A} + {~ ordu A}.
Proof.
  destruct A.
  - left; constructor.
  - left; constructor.
  - left; constructor.
  - left; constructor.
  - right; intro H; inversion H.
  - destruct (ordu_dec A1); destruct (ordu_dec A2).
    + left; constructor; auto.
    + right; intro H; inversion H; auto.
    + right; intro H; inversion H; auto.
    + right; intro H; inversion H; auto.
  - left; constructor.
  - left; constructor.
Defined.

Fixpoint ordi_dec (A:typ) : {ordi A} + {~ ordi A}.
Proof.
  destruct A.
  - left; constructor.
  - left; constructor.
  - left; constructor.
  - destruct (ordu_dec A1); destruct (ordi_dec A2).
    + left; constructor; auto.
    + right; intro H; inversion H; auto.
    + right; intro H; inversion H; auto.
    + right; intro H; inversion H; auto.
  - destruct (ordi_dec A1); destruct (ordi_dec A2).
    + left; constructor; auto.
    + right; intro H; inversion H; auto.
    + right; intro H; inversion H; auto.
    + right; intro H; inversion H; auto.
  - right; intro H; inversion H.
  - left; constructor.
  - left; constructor.
Defined.

Fixpoint splu_opt (A:typ) : option (typ*typ) :=
  match A with
  | t_union X Y => Some (X,Y)
  | t_and X Y =>
      match splu_opt X with
      | Some (B1,C1) => Some (t_and B1 Y, t_and C1 Y)
      | None => match ordu_dec X with
                | left _ => match splu_opt Y with
                            | Some (B2,C2) => Some (t_and X B2, t_and X C2)
                            | None => None end
                | right _ => None end
      end
  | _ => None
  end.

Fixpoint spli_opt (A:typ) : option (typ*typ) :=
  match A with
  | t_and X Y => Some (X,Y)
  | t_arrow X Y =>
      match spli_opt Y with
      | Some (C,D) => Some (t_arrow X C, t_arrow X D)
      | None => match ordi_dec Y with
                | left _ => match splu_opt X with
                            | Some (P,Q) => Some (t_arrow P Y, t_arrow Q Y)
                            | None => None end
                | right _ => None end
      end
  | t_union X Y =>
      match spli_opt X with
      | Some (P,Q) => Some (t_union P Y, t_union Q Y)
      | None => match ordi_dec X with
                | left _ => match spli_opt Y with
                            | Some (P,Q) => Some (t_union X P, t_union X Q)
                            | None => None end
                | right _ => None end
      end
  | _ => None
  end.

Lemma splu_opt_sound : forall A B C, splu_opt A = Some (B,C) -> splu A B C.
Proof.
  induction A; intros B C H; simpl in H; try discriminate.
  - inversion H; subst; constructor.
  - remember (splu_opt A1) as o eqn:E; destruct o as [[B1 C1]|].
    + inversion H; subst. constructor. apply IHA1; auto.
    + destruct (ordu_dec A1).
      * remember (splu_opt A2) as o2 eqn:E2; destruct o2 as [[B2 C2]|].
        -- inversion H; subst. apply SpU_andr; [assumption | apply IHA2; auto].
        -- discriminate.
      * discriminate.
Qed.

Lemma ordu_splu_opt_None : forall A, ordu A -> splu_opt A = None.
Proof.
  induction 1; simpl; auto.
  destruct (splu_opt A) as [[B0 C0]|] eqn:E.
  - exfalso; rewrite IHordu1 in E; discriminate.
  - simpl. destruct (ordu_dec A) as [Hd|Hd].
    + rewrite IHordu2; auto.
    + exfalso; apply Hd; assumption.
Qed.

Lemma splu_opt_complete : forall A B C, splu A B C -> splu_opt A = Some (B,C).
Proof.
  intros A B C H. induction H; simpl.
  - auto.
  - rewrite IHsplu. auto.
  - rewrite (ordu_splu_opt_None A H). simpl.
    destruct (ordu_dec A) as [HX|HX]; [rewrite IHsplu; auto | exfalso; apply HX; assumption].
Qed.

Lemma ordi_spli_opt_None : forall A, ordi A -> spli_opt A = None.
Proof.
  induction 1; simpl; auto.
  - match goal with IH : spli_opt ?Y = None |- _ =>
      rewrite IH; simpl; destruct (ordi_dec Y) as [Hd|Hd];
      [ rewrite (ordu_splu_opt_None A H); auto | exfalso; apply Hd; assumption ]
    end.
  - match goal with IH1 : spli_opt ?X = None, IH2 : spli_opt ?Y = None |- _ =>
      rewrite IH1; simpl; destruct (ordi_dec X) as [Hd|Hd];
      [ rewrite IH2; auto | exfalso; apply Hd; assumption ]
    end.
Qed.

Lemma spli_opt_sound : forall A B C, spli_opt A = Some (B,C) -> spli A B C.
Proof.
  induction A; intros B C H; simpl in H; try discriminate.
  - remember (spli_opt A2) as o eqn:E; destruct o as [[C1 D1]|].
    + inversion H; subst. constructor. apply IHA2; auto.
    + destruct (ordi_dec A2).
      * remember (splu_opt A1) as o2 eqn:E2; destruct o2 as [[P Q]|].
        -- inversion H; subst. apply SpI_arrowUnion; [assumption | apply splu_opt_sound; auto].
        -- discriminate.
      * discriminate.
  - remember (spli_opt A1) as o eqn:E; destruct o as [[P Q]|].
    + inversion H; subst. constructor. apply IHA1; auto.
    + destruct (ordi_dec A1).
      * remember (spli_opt A2) as o2 eqn:E2; destruct o2 as [[P Q]|].
        -- inversion H; subst. apply SpI_orr; [assumption | apply IHA2; auto].
        -- discriminate.
      * discriminate.
  - inversion H; subst; constructor.
Qed.

Lemma spli_opt_complete : forall A B C, spli A B C -> spli_opt A = Some (B,C).
Proof.
  intros A B C H. induction H; simpl.
  - auto.
  - rewrite IHspli. auto.
  - rewrite (ordi_spli_opt_None D H). simpl.
    destruct (ordi_dec D) as [HD|HD]; [rewrite (splu_opt_complete _ _ _ H0); auto | exfalso; apply HD; assumption].
  - rewrite IHspli. auto.
  - rewrite (ordi_spli_opt_None A H). simpl.
    destruct (ordi_dec A) as [HA|HA]; [rewrite IHspli; auto | exfalso; apply HA; assumption].
Qed.

Lemma splu_det : forall A B C B' C', splu A B C -> splu A B' C' -> B = B' /\ C = C'.
Proof.
  intros. apply splu_opt_complete in H. apply splu_opt_complete in H0.
  rewrite H in H0. inversion H0. auto.
Qed.
Lemma spli_det : forall A B C B' C', spli A B C -> spli A B' C' -> B = B' /\ C = C'.
Proof.
  intros. apply spli_opt_complete in H. apply spli_opt_complete in H0.
  rewrite H in H0. inversion H0. auto.
Qed.
Lemma splu_size : forall A B C, splu A B C -> size_typ B < size_typ A /\ size_typ C < size_typ A.
Proof. induction 1; simpl; lia. Qed.
Lemma spli_size : forall A B C, spli A B C -> size_typ B < size_typ A /\ size_typ C < size_typ A.
Proof. induction 1; simpl; try lia. apply splu_size in H0. simpl; lia. Qed.
Lemma size_pos : forall A, 1 <= size_typ A. Proof. induction A; simpl; lia. Qed.

Lemma ordu_or_splu : forall A, ordu A \/ (exists B C, splu A B C).
Proof.
  induction A as [| | | X IX Y IY | U IU V IV | P IP Q IQ | | i]; try solve [left; constructor].
  - right; exists U, V; constructor.
  - destruct IP as [H1|H1].
    + destruct IQ as [H2|H2].
      * left; constructor; auto.
      * destruct H2 as [B2 [C2 H2]]. right; exists (t_and P B2), (t_and P C2); econstructor; eauto.
    + destruct H1 as [B1 [C1 H1]]. right; exists (t_and B1 Q), (t_and C1 Q); econstructor; eauto.
Qed.

Lemma ordi_or_spli : forall A, ordi A \/ (exists B C, spli A B C).
Proof.
  induction A as [| | | X IX Y IY | U IU V IV | P IP Q IQ | | i]; try solve [left; constructor].
  - (* arrow *) destruct (ordu_or_splu X) as [H1|H1].
    + destruct IY as [H2|H2].
      * left; constructor; auto.
      * destruct H2 as [B2 [C2 H2]]. right; exists (t_arrow X B2), (t_arrow X C2); econstructor; eauto.
    + destruct H1 as [B1 [C1 H1]].
      destruct IY as [H2|H2].
      * right; exists (t_arrow B1 Y), (t_arrow C1 Y); econstructor; eauto.
      * destruct H2 as [B2 [C2 H2]]. right; exists (t_arrow X B2), (t_arrow X C2); econstructor; eauto.
  - (* union *) destruct IU as [H1|H1].
    + destruct IV as [H2|H2].
      * left; constructor; auto.
      * destruct H2 as [B2 [C2 H2]]. right; exists (t_union U B2), (t_union U C2); econstructor; eauto.
    + destruct H1 as [B1 [C1 H1]]. right; exists (t_union B1 V), (t_union C1 V); econstructor; eauto.
  - (* and *) right; exists P, Q; constructor.
Qed.

Fixpoint Uf (k:nat) (A:typ) : list typ :=
  match k with
  | 0 => [A]
  | S k' => match splu_opt A with
            | Some (B,C) => Uf k' B ++ Uf k' C
            | None => [A]
            end
  end.
Fixpoint If (k:nat) (A:typ) : list typ :=
  match k with
  | 0 => [A]
  | S k' => match spli_opt A with
            | Some (B,C) => If k' B ++ If k' C
            | None => [A]
            end
  end.
Definition U (A:typ) : list typ := Uf (size_typ A) A.
Definition I (A:typ) : list typ := If (size_typ A) A.

Lemma Uf_ordu : forall k A, size_typ A <= k -> Forall ordu (Uf k A).
Proof.
  induction k as [| k IH]; intros A Hs.
  - pose proof (size_pos A); lia.
  - simpl. destruct (splu_opt A) as [[B C]|] eqn:E.
    + rewrite Forall_app. split; apply IH; 
      assert (Hspl : splu A B C) by (apply splu_opt_sound; auto);
      apply splu_size in Hspl; destruct Hspl; lia.
    + apply Forall_forall; intros x Hx.
      simpl in Hx; destruct Hx as [Heq|Hf]; [subst x | destruct Hf].
      destruct (ordu_or_splu A) as [H|[B0 [C0 H]]]; auto.
      exfalso; apply splu_opt_complete in H; rewrite H in E; discriminate.
Qed.

Lemma If_ordi : forall k A, size_typ A <= k -> Forall ordi (If k A).
Proof.
  induction k as [| k IH]; intros A Hs.
  - pose proof (size_pos A); lia.
  - simpl. destruct (spli_opt A) as [[B C]|] eqn:E.
    + rewrite Forall_app. split; apply IH;
      assert (Hsp : spli A B C) by (apply spli_opt_sound; auto);
      apply spli_size in Hsp; destruct Hsp; lia.
    + apply Forall_forall; intros x Hx.
      simpl in Hx; destruct Hx as [Heq|Hf]; [subst x | destruct Hf].
      destruct (ordi_or_spli A) as [H|[B0 [C0 H]]]; auto.
      exfalso; apply spli_opt_complete in H; rewrite H in E; discriminate.
Qed.

Lemma Uf_stable : forall k A, size_typ A <= k -> Uf k A = U A.
Proof.
  intros k. induction k as [k IH] using lt_wf_ind. intros A Hs.
  destruct k as [| k'].
  - pose proof (size_pos A); lia.
  - unfold U. destruct (size_typ A) as [| s] eqn:Es.
    + pose proof (size_pos A); lia.
    + simpl. destruct (splu_opt A) as [[B C]|] eqn:E.
      * assert (Hspl : splu A B C) by (apply splu_opt_sound; auto).
        apply splu_size in Hspl as [HB HC].
        rewrite (IH k' ltac:(lia) B ltac:(lia)).
        rewrite (IH s ltac:(lia) B ltac:(lia)).
        rewrite (IH k' ltac:(lia) C ltac:(lia)).
        rewrite (IH s ltac:(lia) C ltac:(lia)).
        auto.
      * auto.
Qed.
Lemma If_stable : forall k A, size_typ A <= k -> If k A = I A.
Proof.
  intros k. induction k as [k IH] using lt_wf_ind. intros A Hs.
  destruct k as [| k'].
  - pose proof (size_pos A); lia.
  - unfold I. destruct (size_typ A) as [| s] eqn:Es.
    + pose proof (size_pos A); lia.
    + simpl. destruct (spli_opt A) as [[B C]|] eqn:E.
      * assert (Hsp : spli A B C) by (apply spli_opt_sound; auto).
        apply spli_size in Hsp as [HB HC].
        rewrite (IH k' ltac:(lia) B ltac:(lia)).
        rewrite (IH s ltac:(lia) B ltac:(lia)).
        rewrite (IH k' ltac:(lia) C ltac:(lia)).
        rewrite (IH s ltac:(lia) C ltac:(lia)).
        auto.
      * auto.
Qed.

Lemma U_ordu_singleton : forall A, ordu A -> U A = [A].
Proof.
  intros A Ho. unfold U. destruct (size_typ A) as [| k] eqn:E.
  - pose proof (size_pos A); lia.
  - simpl. rewrite (ordu_splu_opt_None A Ho). auto.
Qed.
Lemma I_ordi_singleton : forall A, ordi A -> I A = [A].
Proof.
  intros A Ho. unfold I. destruct (size_typ A) as [| k] eqn:E.
  - pose proof (size_pos A); lia.
  - simpl. rewrite (ordi_spli_opt_None A Ho). auto.
Qed.

Lemma U_step : forall A B C, splu_opt A = Some (B,C) -> U A = U B ++ U C.
Proof.
  intros A B C E. unfold U.
  destruct (size_typ A) as [| k] eqn:Es.
  - pose proof (size_pos A); lia.
  - simpl. rewrite E. rewrite (Uf_stable k B). rewrite (Uf_stable k C). auto.
    * assert (Hspl : splu A B C) by (apply splu_opt_sound; auto).
      apply splu_size in Hspl; destruct Hspl; lia.
    * assert (Hspl : splu A B C) by (apply splu_opt_sound; auto).
      apply splu_size in Hspl; destruct Hspl; lia.
Qed.
Lemma I_step : forall A B C, spli_opt A = Some (B,C) -> I A = I B ++ I C.
Proof.
  intros A B C E. unfold I.
  destruct (size_typ A) as [| k] eqn:Es.
  - pose proof (size_pos A); lia.
  - simpl. rewrite E. rewrite (If_stable k B). rewrite (If_stable k C). auto.
    * assert (Hsp : spli A B C) by (apply spli_opt_sound; auto).
      apply spli_size in Hsp; destruct Hsp; lia.
    * assert (Hsp : spli A B C) by (apply spli_opt_sound; auto).
      apply spli_size in Hsp; destruct Hsp; lia.
Qed.

(* ============ Semantic order on types ============ *)
Inductive cmp : envp -> typ -> typ -> Prop :=
| C_top : forall G u, okenvp G -> wft G u -> cmp G u t_top
| C_bot : forall G i, okenvp G -> wft G i -> cmp G t_bot i
| C_or_l : forall G u i1 i2, wft G i2 -> cmp G u i1 -> cmp G u (t_union i1 i2)
| C_or_r : forall G u i1 i2, wft G i1 -> cmp G u i2 -> cmp G u (t_union i1 i2)
| C_and_l : forall G u1 u2 i, wft G u2 -> cmp G u1 i -> cmp G (t_and u1 u2) i
| C_and_r : forall G u1 u2 i, wft G u1 -> cmp G u2 i -> cmp G (t_and u1 u2) i
| C_arrow : forall G a1 a2 b1 b2,
    (forall u, In u (U b1) -> forall i, In i (I a1) -> cmp G u i) ->
    (forall u, In u (U a2) -> forall i, In i (I b2) -> cmp G u i) ->
    cmp G (t_arrow a1 a2) (t_arrow b1 b2)
| C_int : forall G, okenvp G -> cmp G t_int t_int
| C_unit : forall G, okenvp G -> cmp G t_unit t_unit
| C_prim_refl : forall G n, okenvp G -> wft G (t_prim n) -> cmp G (t_prim n) (t_prim n)
| C_prim_neq : forall PG i A n1 n2,
    okenvp ((i,A)::PG) -> i <> n1 -> cmp PG (t_prim n1) (t_prim n2) ->
    cmp ((i,A)::PG) (t_prim n1) (t_prim n2)
| C_prim_eq : forall PG j n1 n2,
    okenvp ((n1,t_prim j)::PG) -> cmp PG (t_prim j) (t_prim n2) ->
    cmp ((n1,t_prim j)::PG) (t_prim n1) (t_prim n2).

Definition sle (G:envp) (A B:typ) : Prop :=
  forall u, In u (U A) -> forall i, In i (I B) -> cmp G u i.

Lemma ordu_inv_and : forall A B, ordu (t_and A B) -> ordu A /\ ordu B.
Proof. intros A B H; inversion H; subst; auto. Qed.
Lemma ordi_inv_or : forall A B, ordi (t_union A B) -> ordi A /\ ordi B.
Proof. intros A B H; inversion H; subst; auto. Qed.
Lemma ordi_inv_arrow : forall A B, ordi (t_arrow A B) -> ordu A /\ ordi B.
Proof. intros A B H; inversion H; subst; auto. Qed.

Definition meas (BIG:nat) (G:envp) (A B:typ) := size_envp G * BIG + size_typ A + size_typ B.

Lemma sle_asub_strong : forall BIG n,
  (forall G u i, size_typ u + size_typ i <= BIG ->
     meas BIG G u i <= n -> ordu u -> ordi i -> cmp G u i -> algo_sub G u i)
  /\ (forall G A B, size_typ A + size_typ B <= BIG ->
     meas BIG G A B <= n -> sle G A B -> algo_sub G A B).
Proof.
  intros BIG n. induction n as [n IH] using lt_wf_ind.
  assert (Hcmp : forall G u i, size_typ u + size_typ i <= BIG ->
     meas BIG G u i <= n -> ordu u -> ordi i -> cmp G u i -> algo_sub G u i).
  { intros G u i HB Hm Hu Hi Hc.
    inversion Hc; subst; clear Hc.
    - (* C_top *) apply AS_top; auto.
    - (* C_bot *) apply AS_bot; auto.
    - (* C_or_l *) destruct (ordi_inv_or i1 i2 Hi) as [Hi1 Hi2].
      eapply AS_orl with (B1 := i1) (B2 := i2).
      + assumption.
      + apply SpU_or.
      + apply (proj1 (IH (meas BIG G u i1) ltac:(unfold meas in *; simpl in *; lia))).
        * simpl in HB; lia.
        * unfold meas; simpl; lia.
        * exact Hu.
        * exact Hi1.
        * assumption.
    - (* C_or_r *) destruct (ordi_inv_or i1 i2 Hi) as [Hi1 Hi2].
      eapply AS_orr with (B1 := i1) (B2 := i2).
      + assumption.
      + apply SpU_or.
      + apply (proj1 (IH (meas BIG G u i2) ltac:(unfold meas in *; simpl in *; lia))).
        * simpl in HB; lia.
        * unfold meas; simpl; lia.
        * exact Hu.
        * exact Hi2.
        * assumption.
    - (* C_and_l *) destruct (ordu_inv_and u1 u2 Hu) as [Hu1 Hu2].
      eapply AS_andl with (A1 := u1) (A2 := u2).
      + assumption.
      + apply SpI_and.
      + apply (proj1 (IH (meas BIG G u1 i) ltac:(unfold meas in *; simpl in *; lia))).
        * simpl in HB; lia.
        * unfold meas; simpl; lia.
        * exact Hu1.
        * exact Hi.
        * assumption.
    - (* C_and_r *) destruct (ordu_inv_and u1 u2 Hu) as [Hu1 Hu2].
      eapply AS_andr with (A1 := u1) (A2 := u2).
      + assumption.
      + apply SpI_and.
      + apply (proj1 (IH (meas BIG G u2 i) ltac:(unfold meas in *; simpl in *; lia))).
        * simpl in HB; lia.
        * unfold meas; simpl; lia.
        * exact Hu2.
        * exact Hi.
        * assumption.
    - (* C_arrow *) apply AS_arrow.
      + apply (proj2 (IH (meas BIG G b1 a1) ltac:(unfold meas in *; simpl in *; lia))).
        * simpl in HB; lia.
        * unfold meas; simpl; lia.
        * exact H.
      + apply (proj2 (IH (meas BIG G a2 b2) ltac:(unfold meas in *; simpl in *; lia))).
        * simpl in HB; lia.
        * unfold meas; simpl; lia.
        * exact H0.
    - (* C_int *) apply AS_refl; [assumption | constructor].
    - (* C_unit *) apply AS_refl; [assumption | constructor].
    - (* C_prim_refl *) apply AS_refl; auto.
    - (* C_prim_neq *) eapply AS_prim_neq; eauto.
      apply (proj1 (IH (meas BIG PG (t_prim n1) (t_prim n2)) ltac:(unfold meas in *; simpl in *; lia))).
      * simpl in *; lia.
      * unfold meas; simpl; lia.
      * constructor.
      * constructor.
      * assumption.
    - (* C_prim_eq *) eapply AS_prim_eq; eauto.
      apply (proj1 (IH (meas BIG PG (t_prim j) (t_prim n2)) ltac:(unfold meas in *; simpl in *; lia))).
      * simpl in *; lia.
      * unfold meas; simpl; lia.
      * constructor.
      * constructor.
      * assumption.
  }
  split.
  - exact Hcmp.
  - intros G A B HB Hm Hs.
    destruct (splu_opt A) as [[A1 A2]|] eqn:EA.
    + assert (HA1 : size_typ A1 < size_typ A)
        by (assert (Hsp : splu A A1 A2) by (apply splu_opt_sound; auto);
            apply splu_size in Hsp; tauto).
      assert (HA2 : size_typ A2 < size_typ A)
        by (assert (Hsp : splu A A1 A2) by (apply splu_opt_sound; auto);
            apply splu_size in Hsp; tauto).
      assert (Hs1 : sle G A1 B).
      { unfold sle; intros u Hu i Hi.
        apply Hs. rewrite (U_step _ _ _ EA). apply in_or_app; left; exact Hu.
        exact Hi. }
      assert (Hs2 : sle G A2 B).
      { unfold sle; intros u Hu i Hi.
        apply Hs. rewrite (U_step _ _ _ EA). apply in_or_app; right; exact Hu.
        exact Hi. }
      eapply AS_or with (A1 := A1) (A2 := A2).
      * apply splu_opt_sound; auto.
      * apply (proj2 (IH (meas BIG G A1 B) ltac:(unfold meas in *; simpl in *; lia))).
        -- simpl in HB; lia.
        -- unfold meas; simpl; lia.
        -- exact Hs1.
      * apply (proj2 (IH (meas BIG G A2 B) ltac:(unfold meas in *; simpl in *; lia))).
        -- simpl in HB; lia.
        -- unfold meas; simpl; lia.
        -- exact Hs2.
    + destruct (spli_opt B) as [[B1 B2]|] eqn:EB.
      * assert (HB1 : size_typ B1 < size_typ B)
          by (assert (Hsp : spli B B1 B2) by (apply spli_opt_sound; auto);
              apply spli_size in Hsp; tauto).
        assert (HB2 : size_typ B2 < size_typ B)
          by (assert (Hsp : spli B B1 B2) by (apply spli_opt_sound; auto);
              apply spli_size in Hsp; tauto).
        assert (Hs1 : sle G A B1).
        { unfold sle; intros u Hu i Hi.
          apply Hs; [exact Hu |]. rewrite (I_step _ _ _ EB). apply in_or_app; left; exact Hi. }
        assert (Hs2 : sle G A B2).
        { unfold sle; intros u Hu i Hi.
          apply Hs; [exact Hu |]. rewrite (I_step _ _ _ EB). apply in_or_app; right; exact Hi. }
        eapply AS_and with (B1 := B1) (B2 := B2).
        -- apply spli_opt_sound; auto.
        -- apply (proj2 (IH (meas BIG G A B1) ltac:(unfold meas in *; simpl in *; lia))).
           ++ simpl in HB; lia.
           ++ unfold meas; simpl; lia.
           ++ exact Hs1.
        -- apply (proj2 (IH (meas BIG G A B2) ltac:(unfold meas in *; simpl in *; lia))).
           ++ simpl in HB; lia.
           ++ unfold meas; simpl; lia.
           ++ exact Hs2.
      * assert (HAord : ordu A).
        { destruct (ordu_or_splu A) as [H|[B0 [C0 H]]]; auto.
          exfalso; apply splu_opt_complete in H; rewrite H in EA; discriminate. }
        assert (HBord : ordi B).
        { destruct (ordi_or_spli B) as [H|[B0 [C0 H]]]; auto.
          exfalso; apply spli_opt_complete in H; rewrite H in EB; discriminate. }
        apply Hcmp.
        -- simpl in HB; lia.
        -- exact Hm.
        -- exact HAord.
        -- exact HBord.
        -- apply Hs.
           ++ rewrite (U_ordu_singleton A HAord). simpl; auto.
           ++ rewrite (I_ordi_singleton B HBord). simpl; auto.
Qed.


Corollary sle_asub : forall G A B, sle G A B -> algo_sub G A B.
Proof.
  intros G A B H.
  pose proof (proj2 (sle_asub_strong (size_typ A + size_typ B)
                     (meas (size_typ A + size_typ B) G A B)) G A B) as Hh.
  apply Hh.
  - lia.
  - unfold meas; lia.
  - exact H.
Qed.

(* ============ Well-formedness lemmas ============ *)
Lemma wft_inv_and : forall G A B, wft G (t_and A B) -> wft G A /\ wft G B.
Proof. intros G A B H; inversion H; subst; auto. Qed.
Lemma wft_inv_or : forall G A B, wft G (t_union A B) -> wft G A /\ wft G B.
Proof. intros G A B H; inversion H; subst; auto. Qed.
Lemma wft_inv_arrow : forall G A B, wft G (t_arrow A B) -> wft G A /\ wft G B.
Proof. intros G A B H; inversion H; subst; auto. Qed.
Lemma wft_prim_binds : forall G i, wft G (t_prim i) -> exists A, binds i A G.
Proof. intros G i H; inversion H; subst; eauto. Qed.

Lemma binds_cons_more : forall i A j B (G:envp), binds i A G -> binds i A ((j,B)::G).
Proof. intros; simpl; auto. Qed.

Lemma wft_weaken_cons : forall G A j B, wft G A -> wft ((j,B)::G) A.
Proof.
  intros G A j B H. induction H as
    [ | | | X Y HX IHY HY IHY2 | X Y HX IHY HY IHY2 | X Y HX IHY HY IHY2 | | i A0 Hb ].
  - constructor.
  - constructor.
  - constructor.
  - constructor; auto.
  - constructor; auto.
  - constructor; auto.
  - constructor.
  - apply wft_prim with (A:=A0); simpl; auto.
Qed.

Lemma splu_wft : forall G A B C, splu A B C -> wft G A -> wft G B /\ wft G C.
Proof.
  intros G A B C H. induction H; intros HA.
  - apply wft_inv_or in HA; auto.
  - apply wft_inv_and in HA; destruct HA as [HA0 HY].
    destruct (IHsplu HA0) as [HB HC]. split; apply wft_and; auto.
  - apply wft_inv_and in HA; destruct HA as [HX HB0].
    destruct (IHsplu HB0) as [HB HC]. split; apply wft_and; auto.
Qed.
Lemma splu_wft_inv : forall G A B C, splu A B C -> wft G B -> wft G C -> wft G A.
Proof.
  intros G A B C H. induction H; intros HB HC.
  - apply wft_or; auto.
  - apply wft_inv_and in HB; destruct HB as [HB1 HY].
    apply wft_inv_and in HC; destruct HC as [HC1 HY2].
    apply wft_and; auto.
  - apply wft_inv_and in HB; destruct HB as [HX HB1].
    apply wft_inv_and in HC; destruct HC as [HX2 HC1].
    apply wft_and; auto.
Qed.
Lemma spli_wft : forall G A B C, spli A B C -> wft G A -> wft G B /\ wft G C.
Proof.
  intros G A B C H. induction H; intros HA.
  - apply wft_inv_and in HA; auto.
  - apply wft_inv_arrow in HA; destruct HA as [HX HB].
    destruct (IHspli HB) as [HC HD]. split; apply wft_arrow; auto.
  - apply wft_inv_arrow in HA; destruct HA as [HA0 HD].
    destruct (splu_wft _ _ _ _ H0 HA0) as [HB HC]. split; apply wft_arrow; auto.
  - apply wft_inv_or in HA; destruct HA as [HA0 HY].
    destruct (IHspli HA0) as [HB HC]. split; apply wft_or; auto.
  - apply wft_inv_or in HA; destruct HA as [HX HB0].
    destruct (IHspli HB0) as [HB HC]. split; apply wft_or; auto.
Qed.
Lemma spli_wft_inv : forall G A B C, spli A B C -> wft G B -> wft G C -> wft G A.
Proof.
  intros G A B C H. induction H; intros HB HC.
  - apply wft_and; auto.
  - apply wft_inv_arrow in HB; destruct HB as [HX HB0].
    apply wft_inv_arrow in HC; destruct HC as [HX2 HC0].
    apply wft_arrow; auto.
  - apply wft_inv_arrow in HB; destruct HB as [HB0 HD].
    apply wft_inv_arrow in HC; destruct HC as [HC0 HD2].
    apply wft_arrow; auto. apply splu_wft_inv with (B:=B) (C:=C); auto.
  - apply wft_inv_or in HB; destruct HB as [HB0 HY].
    apply wft_inv_or in HC; destruct HC as [HC0 HY2].
    apply wft_or; auto.
  - apply wft_inv_or in HB; destruct HB as [HX HB0].
    apply wft_inv_or in HC; destruct HC as [HX2 HC0].
    apply wft_or; auto.
Qed.

(* ============ Declarative lattice helpers ============ *)
Lemma ds_refl : forall G A, okenvp G -> wft G A -> declarative_subtyping G A A.
Proof. intros; apply DS_refl; auto. Qed.
Lemma ds_trans : forall G A B C, declarative_subtyping G A B -> declarative_subtyping G B C -> declarative_subtyping G A C.
Proof. intros; eapply DS_trans; eauto. Qed.
Lemma ds_top : forall G A, okenvp G -> wft G A -> declarative_subtyping G A t_top.
Proof. intros; apply DS_top; auto. Qed.
Lemma ds_bot : forall G A, okenvp G -> wft G A -> declarative_subtyping G t_bot A.
Proof. intros; apply DS_bot; auto. Qed.
Lemma ds_and_intro : forall G A B C, declarative_subtyping G A B -> declarative_subtyping G A C -> declarative_subtyping G A (t_and B C).
Proof. intros; eapply DS_and; eauto. Qed.
Lemma ds_andl : forall G A B, okenvp G -> wft G A -> wft G B -> declarative_subtyping G (t_and A B) A.
Proof. intros; apply DS_andl; auto. Qed.
Lemma ds_andr : forall G A B, okenvp G -> wft G A -> wft G B -> declarative_subtyping G (t_and A B) B.
Proof. intros; apply DS_andr; auto. Qed.
Lemma ds_or_intro_l : forall G A B, okenvp G -> wft G A -> wft G B -> declarative_subtyping G A (t_union A B).
Proof. intros; apply DS_orl; auto. Qed.
Lemma ds_or_intro_r : forall G A B, okenvp G -> wft G A -> wft G B -> declarative_subtyping G B (t_union A B).
Proof. intros; apply DS_orr; auto. Qed.
Lemma ds_or_elim : forall G A B C, declarative_subtyping G A C -> declarative_subtyping G B C -> declarative_subtyping G (t_union A B) C.
Proof. intros; eapply DS_or; eauto. Qed.

Lemma ds_and_mono : forall G A A' B B',
  declarative_subtyping G A A' -> declarative_subtyping G B B' ->
  okenvp G -> wft G A -> wft G B ->
  declarative_subtyping G (t_and A B) (t_and A' B').
Proof.
  intros G A A' B B' HA HB Ho WA WB.
  apply ds_and_intro.
  - eapply ds_trans; [apply ds_andl; auto | exact HA].
  - eapply ds_trans; [apply ds_andr; auto | exact HB].
Qed.

Lemma ds_comm_and : forall G A B, okenvp G -> wft G A -> wft G B ->
  declarative_subtyping G (t_and A B) (t_and B A) /\ declarative_subtyping G (t_and B A) (t_and A B).
Proof.
  intros; split; apply ds_and_intro;
    [ apply ds_andr | apply ds_andl | apply ds_andr | apply ds_andl ]; auto.
Qed.

Lemma ds_comm_or : forall G A B, okenvp G -> wft G A -> wft G B ->
  declarative_subtyping G (t_union A B) (t_union B A) /\ declarative_subtyping G (t_union B A) (t_union A B).
Proof.
  intros; split; apply ds_or_elim;
    [ apply ds_or_intro_r | apply ds_or_intro_l | apply ds_or_intro_r | apply ds_or_intro_l ]; auto.
Qed.

Lemma ds_dist_std : forall G x y z, okenvp G -> wft G x -> wft G y -> wft G z ->
  declarative_subtyping G (t_and x (t_union y z)) (t_union (t_and x y) (t_and x z)).
Proof.
  intros G x y z Ho Wx Wy Wz.
  set (wxy := wft_and G x y Wx Wy).
  set (uyz := wft_or G y z Wy Wz).
  set (uxwxy := wft_or G x (t_and x y) Wx wxy).
  set (uzwxy := wft_or G z (t_and x y) Wz wxy).
  assert (HA : declarative_subtyping G (t_and x (t_union y z)) (t_union (t_and x y) z)).
  { eapply ds_trans with (B := t_and (t_union x z) (t_union y z)).
    - apply ds_and_intro.
      + eapply ds_trans; [ apply ds_andl; [exact Ho|exact Wx|exact uyz]
                         | apply ds_or_intro_l; [exact Ho|exact Wx|exact Wz] ].
      + apply ds_andr; [exact Ho | exact Wx | exact uyz].
    - apply DS_distOr; auto. }
  assert (HB : declarative_subtyping G (t_and x (t_union y z)) (t_and x (t_union (t_and x y) z))).
  { apply ds_and_intro.
    - apply ds_andl; [exact Ho | exact Wx | exact uyz].
    - exact HA. }
  set (uwz := wft_or G (t_and x y) z wxy Wz).
  assert (HC : declarative_subtyping G (t_and x (t_union (t_and x y) z)) (t_union (t_and x z) (t_and x y))).
  { eapply ds_trans with (B := t_and (t_union x (t_and x y)) (t_union z (t_and x y))).
    - apply ds_and_intro.
      + eapply ds_trans; [ apply ds_andl; [exact Ho|exact Wx|exact uwz]
                         | apply ds_or_intro_l; [exact Ho|exact Wx|exact wxy] ].
      + eapply ds_trans; [ apply ds_andr; [exact Ho|exact Wx|exact uwz]
                         | apply (proj1 (ds_comm_or G (t_and x y) z Ho wxy Wz)) ].
    - apply DS_distOr; auto. }
  eapply ds_trans; [exact HB|].
  eapply ds_trans; [exact HC|].
  apply (proj1 (ds_comm_or G (t_and x z) (t_and x y) Ho (wft_and G x z Wx Wz) wxy)).
Qed.

Lemma ds_dist_std' : forall G x y z, okenvp G -> wft G x -> wft G y -> wft G z ->
  declarative_subtyping G (t_and (t_union x y) z) (t_union (t_and x z) (t_and y z)).
Proof.
  intros G x y z Ho Wx Wy Wz.
  eapply ds_trans with (B := t_and z (t_union x y)).
  - apply (proj1 (ds_comm_and G (t_union x y) z Ho (wft_or G x y Wx Wy) Wz)).
  - assert (H := ds_dist_std G z x y Ho Wz Wx Wy).
    eapply ds_trans; [exact H|].
    apply ds_or_elim.
    + eapply ds_trans; [ apply (proj1 (ds_comm_and G z x Ho Wz Wx))
                       | apply ds_or_intro_l; [exact Ho | apply wft_and; auto | apply wft_and; auto] ].
    + eapply ds_trans; [ apply (proj1 (ds_comm_and G z y Ho Wz Wy))
                       | apply ds_or_intro_r; [exact Ho | apply wft_and; auto | apply wft_and; auto] ].
Qed.

(* ============ Algorithmic split lemmas ============ *)
Lemma asub_splu_l1 : forall G A B C, splu A B C -> okenvp G -> wft G B -> wft G C -> algo_sub G B A.
Proof.
  intros G A B C H. induction H as
    [ A0 B0 | A0 B0 A1 A2 Hp IHp | A0 B0 B1 B2 Ho Hp IHp ]; intros HoG WB WC.
  - eapply AS_orl with (B1 := A0) (B2 := B0).
    + exact WC. + apply SpU_or. + apply AS_refl; auto.
  - apply wft_inv_and in WB; destruct WB as [WA1 WB0].
    apply wft_inv_and in WC; destruct WC as [WA2 WB2].
    apply AS_and with (B1 := A0) (B2 := B0).
    + apply SpI_and.
    + eapply AS_andl with (A1 := A1) (A2 := B0).
      * exact WB0. * apply SpI_and. * apply IHp; auto.
    + eapply AS_andr with (A1 := A1) (A2 := B0).
      * exact WA1. * apply SpI_and. * apply AS_refl; auto.
  - apply wft_inv_and in WB; destruct WB as [WA WB1].
    apply wft_inv_and in WC; destruct WC as [WA2 WB2].
    apply AS_and with (B1 := A0) (B2 := B0).
    + apply SpI_and.
    + eapply AS_andl with (A1 := A0) (A2 := B1).
      * exact WB1. * apply SpI_and. * apply AS_refl; auto.
    + eapply AS_andr with (A1 := A0) (A2 := B1).
      * exact WA. * apply SpI_and. * apply IHp; auto.
Qed.
Lemma asub_splu_l2 : forall G A B C, splu A B C -> okenvp G -> wft G B -> wft G C -> algo_sub G C A.
Proof.
  intros G A B C H. induction H as
    [ A0 B0 | A0 B0 A1 A2 Hp IHp | A0 B0 B1 B2 Ho Hp IHp ]; intros HoG WB WC.
  - eapply AS_orr with (B1 := A0) (B2 := B0).
    + exact WB. + apply SpU_or. + apply AS_refl; auto.
  - apply wft_inv_and in WB; destruct WB as [WA1 WB0].
    apply wft_inv_and in WC; destruct WC as [WA2 WB2].
    apply AS_and with (B1 := A0) (B2 := B0).
    + apply SpI_and.
    + eapply AS_andl with (A1 := A2) (A2 := B0).
      * exact WB0. * apply SpI_and. * apply IHp; auto.
    + eapply AS_andr with (A1 := A2) (A2 := B0).
      * exact WA2. * apply SpI_and. * apply AS_refl; auto.
  - apply wft_inv_and in WB; destruct WB as [WA WB1].
    apply wft_inv_and in WC; destruct WC as [WA2 WB2].
    apply AS_and with (B1 := A0) (B2 := B0).
    + apply SpI_and.
    + eapply AS_andl with (A1 := A0) (A2 := B2).
      * exact WB2. * apply SpI_and. * apply AS_refl; auto.
    + eapply AS_andr with (A1 := A0) (A2 := B2).
      * exact WA. * apply SpI_and. * apply IHp; auto.
Qed.
Lemma asub_splu_join : forall G A B C, splu A B C -> okenvp G -> wft G B -> wft G C -> algo_sub G A (t_union B C).
Proof.
  intros G A B C H. induction H as
    [ A0 B0 | A0 B0 A1 A2 Hp IHp | A0 B0 B1 B2 Ho Hp IHp ]; intros HoG WB WC.
  - apply AS_refl; auto. apply wft_or; auto.
  - apply wft_inv_and in WB; destruct WB as [WA1 WB0].
    apply wft_inv_and in WC; destruct WC as [WA2 WB2].
    apply AS_or with (A1 := t_and A1 B0) (A2 := t_and A2 B0).
    + apply SpU_andl. exact Hp.
    + eapply AS_orl with (B1 := t_and A1 B0) (B2 := t_and A2 B0).
      * apply wft_and; auto. * apply SpU_or.
      * apply AS_refl; [exact HoG | apply wft_and; auto].
    + eapply AS_orr with (B1 := t_and A1 B0) (B2 := t_and A2 B0).
      * apply wft_and; auto. * apply SpU_or.
      * apply AS_refl; [exact HoG | apply wft_and; auto].
  - apply wft_inv_and in WB; destruct WB as [WA WB1].
    apply wft_inv_and in WC; destruct WC as [WA2 WB2].
    apply AS_or with (A1 := t_and A0 B1) (A2 := t_and A0 B2).
    + apply SpU_andr; auto.
    + eapply AS_orl with (B1 := t_and A0 B1) (B2 := t_and A0 B2).
      * apply wft_and; auto. * apply SpU_or.
      * apply AS_refl; [exact HoG | apply wft_and; auto].
    + eapply AS_orr with (B1 := t_and A0 B1) (B2 := t_and A0 B2).
      * apply wft_and; auto. * apply SpU_or.
      * apply AS_refl; [exact HoG | apply wft_and; auto].
Qed.

Lemma asub_spli_l1 : forall G A B C, spli A B C -> okenvp G -> wft G A -> algo_sub G A B.
Proof.
  intros G A B C H. induction H as
    [ A0 B0
    | A0 B0 C0 D Hp IHp
    | A0 D B0 C0 Ho Hp
    | A0 B0 A1 A2 Hp IHp
    | A0 B0 B1 B2 Ho Hp IHp ]; intros HoG WA.
  - apply wft_inv_and in WA; destruct WA as [HB HC].
    eapply AS_andl with (A1 := A0) (A2 := B0).
    + exact HC. + apply SpI_and. + apply AS_refl; auto.
  - apply wft_inv_arrow in WA; destruct WA as [WA0 WB0].
    eapply AS_arrow; [apply AS_refl; auto | eapply IHp; eauto].
  - apply wft_inv_arrow in WA; destruct WA as [WA0 WD].
    destruct (splu_wft G A0 B0 C0 Hp WA0) as [HB HC].
    eapply AS_arrow; [eapply asub_splu_l1 | apply AS_refl]; eauto.
  - apply wft_inv_or in WA; destruct WA as [WA0 WB0].
    destruct (spli_wft G A0 A1 A2 Hp WA0) as [WA1 WA2].
    apply AS_or with (A1 := A0) (A2 := B0).
    + apply SpU_or.
    + eapply AS_orl with (B1 := A1) (B2 := B0).
      * exact WB0. * apply SpU_or. * eapply IHp; eauto.
    + eapply AS_orr with (B1 := A1) (B2 := B0).
      * exact WA1. * apply SpU_or. * apply AS_refl; auto.
  - apply wft_inv_or in WA; destruct WA as [WA WB0].
    destruct (spli_wft G B0 B1 B2 Hp WB0) as [WB1 WB2].
    apply AS_or with (A1 := A0) (A2 := B0).
    + apply SpU_or.
    + eapply AS_orl with (B1 := A0) (B2 := B1).
      * exact WB1. * apply SpU_or. * apply AS_refl; auto.
    + eapply AS_orr with (B1 := A0) (B2 := B1).
      * exact WA. * apply SpU_or. * eapply IHp; eauto.
Qed.
Lemma asub_spli_l2 : forall G A B C, spli A B C -> okenvp G -> wft G A -> algo_sub G A C.
Proof.
  intros G A B C H. induction H as
    [ A0 B0
    | A0 B0 C0 D Hp IHp
    | A0 D B0 C0 Ho Hp
    | A0 B0 A1 A2 Hp IHp
    | A0 B0 B1 B2 Ho Hp IHp ]; intros HoG WA.
  - apply wft_inv_and in WA; destruct WA as [HB HC].
    eapply AS_andr with (A1 := A0) (A2 := B0).
    + exact HB. + apply SpI_and. + apply AS_refl; auto.
  - apply wft_inv_arrow in WA; destruct WA as [WA0 WB0].
    eapply AS_arrow; [apply AS_refl; auto | eapply IHp; eauto].
  - apply wft_inv_arrow in WA; destruct WA as [WA0 WD].
    destruct (splu_wft G A0 B0 C0 Hp WA0) as [HB HC].
    eapply AS_arrow; [eapply asub_splu_l2 | apply AS_refl]; eauto.
  - apply wft_inv_or in WA; destruct WA as [WA0 WB0].
    destruct (spli_wft G A0 A1 A2 Hp WA0) as [WA1 WA2].
    apply AS_or with (A1 := A0) (A2 := B0).
    + apply SpU_or.
    + eapply AS_orl with (B1 := A2) (B2 := B0).
      * exact WB0. * apply SpU_or. * eapply IHp; eauto.
    + eapply AS_orr with (B1 := A2) (B2 := B0).
      * exact WA2. * apply SpU_or. * apply AS_refl; auto.
  - apply wft_inv_or in WA; destruct WA as [WA WB0].
    destruct (spli_wft G B0 B1 B2 Hp WB0) as [WB1 WB2].
    apply AS_or with (A1 := A0) (A2 := B0).
    + apply SpU_or.
    + eapply AS_orl with (B1 := A0) (B2 := B2).
      * exact WB2. * apply SpU_or. * apply AS_refl; auto.
    + eapply AS_orr with (B1 := A0) (B2 := B2).
      * exact WA. * apply SpU_or. * eapply IHp; eauto.
Qed.

(* ============ Declarative split lemmas ============ *)
Lemma splu_ds_l1 : forall G A B C, splu A B C -> okenvp G -> wft G A -> declarative_subtyping G B A.
Proof.
  intros G A B C H. induction H as
    [ A0 B0 | A0 B0 A1 A2 Hp IHp | A0 B0 B1 B2 Ho Hp IHp ]; intros HoG WA.
  - apply wft_inv_or in WA; destruct WA as [WA0 WB0].
    apply DS_orl; auto.
  - apply wft_inv_and in WA; destruct WA as [WA0 WB0].
    destruct (splu_wft G A0 A1 A2 Hp WA0) as [WA1 WA2].
    apply ds_and_intro.
    + eapply ds_trans; [apply ds_andl; eauto | eapply IHp; eauto].
    + apply ds_andr; eauto.
  - apply wft_inv_and in WA; destruct WA as [WA0 WB0].
    destruct (splu_wft G B0 B1 B2 Hp WB0) as [WB1 WB2].
    apply ds_and_intro.
    + apply ds_andl; eauto.
    + eapply ds_trans; [apply ds_andr; eauto | eapply IHp; eauto].
Qed.
Lemma splu_ds_l2 : forall G A B C, splu A B C -> okenvp G -> wft G A -> declarative_subtyping G C A.
Proof.
  intros G A B C H. induction H as
    [ A0 B0 | A0 B0 A1 A2 Hp IHp | A0 B0 B1 B2 Ho Hp IHp ]; intros HoG WA.
  - apply wft_inv_or in WA; destruct WA as [WA0 WB0].
    apply DS_orr; auto.
  - apply wft_inv_and in WA; destruct WA as [WA0 WB0].
    destruct (splu_wft G A0 A1 A2 Hp WA0) as [WA1 WA2].
    apply ds_and_intro.
    + eapply ds_trans; [apply ds_andl; eauto | eapply IHp; eauto].
    + apply ds_andr; eauto.
  - apply wft_inv_and in WA; destruct WA as [WA0 WB0].
    destruct (splu_wft G B0 B1 B2 Hp WB0) as [WB1 WB2].
    apply ds_and_intro.
    + apply ds_andl; eauto.
    + eapply ds_trans; [apply ds_andr; eauto | eapply IHp; eauto].
Qed.
Lemma spli_ds_l1 : forall G A B C, spli A B C -> okenvp G -> wft G A -> declarative_subtyping G A B.
Proof.
  intros G A B C H. induction H as
    [ A0 B0
    | A0 B0 C0 D Hp IHp
    | A0 D B0 C0 Ho Hp
    | A0 B0 A1 A2 Hp IHp
    | A0 B0 B1 B2 Ho Hp IHp ]; intros HoG WA.
  - apply wft_inv_and in WA; destruct WA as [WA0 WB0].
    apply DS_andl; auto.
  - apply wft_inv_arrow in WA; destruct WA as [WA0 WB0].
    apply DS_arrow.
    + apply ds_refl; auto.
    + eapply IHp; eauto.
  - apply wft_inv_arrow in WA; destruct WA as [WA0 WD].
    apply DS_arrow.
    + eapply splu_ds_l1; eauto.
    + apply ds_refl; auto.
  - apply wft_inv_or in WA; destruct WA as [WA0 WB0].
    destruct (spli_wft G A0 A1 A2 Hp WA0) as [WA1 WA2].
    eapply ds_or_elim.
    + eapply ds_trans; [eapply IHp; eauto | apply ds_or_intro_l; eauto].
    + apply ds_or_intro_r; eauto.
  - apply wft_inv_or in WA; destruct WA as [WA WB0].
    destruct (spli_wft G B0 B1 B2 Hp WB0) as [WB1 WB2].
    eapply ds_or_elim.
    + apply ds_or_intro_l; eauto.
    + eapply ds_trans; [eapply IHp; eauto | apply ds_or_intro_r; eauto].
Qed.
Lemma spli_ds_l2 : forall G A B C, spli A B C -> okenvp G -> wft G A -> declarative_subtyping G A C.
Proof.
  intros G A B C H. induction H as
    [ A0 B0
    | A0 B0 C0 D Hp IHp
    | A0 D B0 C0 Ho Hp
    | A0 B0 A1 A2 Hp IHp
    | A0 B0 B1 B2 Ho Hp IHp ]; intros HoG WA.
  - apply wft_inv_and in WA; destruct WA as [WA0 WB0].
    apply DS_andr; auto.
  - apply wft_inv_arrow in WA; destruct WA as [WA0 WB0].
    apply DS_arrow.
    + apply ds_refl; auto.
    + eapply IHp; eauto.
  - apply wft_inv_arrow in WA; destruct WA as [WA0 WD].
    apply DS_arrow.
    + eapply splu_ds_l2; eauto.
    + apply ds_refl; auto.
  - apply wft_inv_or in WA; destruct WA as [WA0 WB0].
    destruct (spli_wft G A0 A1 A2 Hp WA0) as [WA1 WA2].
    eapply ds_or_elim.
    + eapply ds_trans; [eapply IHp; eauto | apply ds_or_intro_l; eauto].
    + apply ds_or_intro_r; eauto.
  - apply wft_inv_or in WA; destruct WA as [WA WB0].
    destruct (spli_wft G B0 B1 B2 Hp WB0) as [WB1 WB2].
    eapply ds_or_elim.
    + apply ds_or_intro_l; eauto.
    + eapply ds_trans; [eapply IHp; eauto | apply ds_or_intro_r; eauto].
Qed.

Lemma okenv_tail : forall i A G, okenvp ((i,A)::G) -> okenvp G.
Proof. intros i A G H; inversion H; subst; auto. Qed.

Lemma asub_regular : forall G A B, algo_sub G A B -> okenvp G /\ wft G A /\ wft G B.
Proof.
  intros G A B H. induction H.
  - repeat split; auto.
  - destruct IHalgo_sub as [Ho [HA HB]].
    repeat split; auto.
    + destruct (wft_prim_binds PG n1 HA) as [X Hx].
      apply wft_prim with (A := X). apply binds_cons_more. exact Hx.
    + destruct (wft_prim_binds PG n2 HB) as [X Hx].
      apply wft_prim with (A := X). apply binds_cons_more. exact Hx.
  - destruct IHalgo_sub as [Ho [HA HB]].
    repeat split; auto.
    + apply wft_prim with (A := t_prim j). simpl; auto.
    + destruct (wft_prim_binds PG n2 HB) as [X Hx].
      apply wft_prim with (A := X). apply binds_cons_more. exact Hx.
  - repeat split; auto; try constructor.
  - repeat split; auto; try constructor.
  - destruct IHalgo_sub1 as [Ho1 [HA1 HA2]].
    destruct IHalgo_sub2 as [Ho2 [HB1 HB2]].
    repeat split; auto.
    + apply wft_arrow; auto.
    + apply wft_arrow; auto.
  - destruct IHalgo_sub1 as [Ho1 [HA1 HA2]].
    destruct IHalgo_sub2 as [Ho2 [HB1 HB2]].
    repeat split; auto.
    eapply spli_wft_inv; eauto.
  - destruct IHalgo_sub as [Ho [HA HB]].
    repeat split; auto.
    eapply spli_wft_inv; eauto.
  - destruct IHalgo_sub as [Ho [HA HB]].
    repeat split; auto.
    eapply spli_wft_inv; eauto.
  - destruct IHalgo_sub1 as [Ho1 [HA1 HB1]].
    destruct IHalgo_sub2 as [Ho2 [HA2 HB2]].
    repeat split; auto.
    eapply splu_wft_inv; eauto.
  - destruct IHalgo_sub as [Ho [HA HB]].
    repeat split; auto.
    eapply splu_wft_inv; eauto.
  - destruct IHalgo_sub as [Ho [HA HB]].
    repeat split; auto.
    eapply splu_wft_inv; eauto.
Qed.

Lemma ds_weaken_cons : forall i A G B C,
  okenvp ((i,A)::G) -> declarative_subtyping G B C -> declarative_subtyping ((i,A)::G) B C.
Proof.
  intros i A G B C Hok H. induction H.
  - apply DS_refl; eauto using wft_weaken_cons.
  - eapply DS_trans; eauto.
  - apply DS_top; eauto using wft_weaken_cons.
  - apply DS_bot; eauto using wft_weaken_cons.
  - apply DS_arrow; eauto.
  - apply DS_and; eauto.
  - apply DS_andl; eauto using wft_weaken_cons.
  - apply DS_andr; eauto using wft_weaken_cons.
  - apply DS_or; eauto.
  - apply DS_orl; eauto using wft_weaken_cons.
  - apply DS_orr; eauto using wft_weaken_cons.
  - apply DS_distArr; eauto using wft_weaken_cons.
  - apply DS_distArrU; eauto using wft_weaken_cons.
  - apply DS_distOr; eauto using wft_weaken_cons.
  - apply DS_prim; eauto using binds_cons_more.
Qed.

Lemma splu_ds_join : forall G A B C, splu A B C -> okenvp G -> wft G A ->
  declarative_subtyping G A (t_union B C).
Proof.
  intros G A B C H. induction H as
    [ A0 B0 | A0 B0 A1 A2 Hp IHp | A0 B0 B1 B2 Ho Hp IHp ]; intros HoG WA.
  - apply wft_inv_or in WA; destruct WA as [WA0 WB0].
    apply DS_refl; auto. apply wft_or; auto.
  - apply wft_inv_and in WA; destruct WA as [WA0 WB0].
    destruct (splu_wft G A0 A1 A2 Hp WA0) as [WA1 WA2].
    eapply ds_trans with (B := t_and (t_union A1 A2) B0).
    + apply ds_and_intro.
      * eapply ds_trans; [apply ds_andl; eauto | eapply IHp; eauto].
      * apply ds_andr; eauto.
    + apply ds_dist_std'; auto.
  - apply wft_inv_and in WA; destruct WA as [WA0 WB0].
    destruct (splu_wft G B0 B1 B2 Hp WB0) as [WB1 WB2].
    eapply ds_trans with (B := t_and A0 (t_union B1 B2)).
    + apply ds_and_intro.
      * apply ds_andl; eauto.
      * eapply ds_trans; [apply ds_andr; eauto | eapply IHp; eauto].
    + apply ds_dist_std; auto.
Qed.

Lemma spli_ds_meet : forall G A B C, spli A B C -> okenvp G -> wft G B -> wft G C ->
  declarative_subtyping G (t_and B C) A.
Proof.
  intros G A B C H. induction H as
    [ A0 B0
    | A0 B0 C0 D Hp IHp
    | A0 D B0 C0 Ho Hp
    | A0 B0 A1 A2 Hp IHp
    | A0 B0 B1 B2 Ho Hp IHp ]; intros HoG WB WC.
  - apply DS_refl; auto. apply wft_and; auto.
  - apply wft_inv_arrow in WB; destruct WB as [WA0 WC0].
    apply wft_inv_arrow in WC; destruct WC as [WA0' WD].
    eapply ds_trans with (B := t_arrow A0 (t_and C0 D)).
    + apply DS_distArr; auto.
    + apply DS_arrow.
      * apply ds_refl; auto.
      * eapply IHp; eauto.
  - apply wft_inv_arrow in WB; destruct WB as [WB0 WD].
    apply wft_inv_arrow in WC; destruct WC as [WC0 WD'].
    assert (WA0 : wft G A0) by (eapply splu_wft_inv; eauto).
    eapply ds_trans with (B := t_arrow (t_union B0 C0) D).
    + apply DS_distArrU; auto.
    + apply DS_arrow.
      * eapply splu_ds_join; eauto.
      * apply ds_refl; auto.
  - apply wft_inv_or in WB; destruct WB as [WA1 WB0].
    apply wft_inv_or in WC; destruct WC as [WA2 WB2].
    assert (WA0 : wft G A0) by (eapply spli_wft_inv; eauto).
    eapply ds_trans with (B := t_union (t_and A1 A2) B0).
    + apply DS_distOr; auto.
    + apply DS_or.
      * eapply ds_trans; [eapply IHp; eauto | apply ds_or_intro_l; eauto].
      * apply ds_or_intro_r; eauto.
  - apply wft_inv_or in WB; destruct WB as [WA0 WB1].
    apply wft_inv_or in WC; destruct WC as [WA0' WB2].
    assert (WB0 : wft G B0) by (eapply spli_wft_inv; eauto).
    eapply ds_trans with (B := t_and (t_union B1 A0) (t_union B2 A0)).
    + apply ds_and_mono.
      * apply (proj1 (ds_comm_or G A0 B1 HoG WA0 WB1)).
      * apply (proj1 (ds_comm_or G A0 B2 HoG WA0 WB2)).
      * exact HoG.
      * apply wft_or; auto.
      * apply wft_or; auto.
    + eapply ds_trans with (B := t_union (t_and B1 B2) A0).
      * apply DS_distOr; auto.
      * eapply ds_trans with (B := t_union B0 A0).
        -- apply DS_or.
           ++ eapply ds_trans; [eapply IHp; eauto | apply ds_or_intro_l; eauto].
           ++ apply ds_or_intro_r; eauto.
        -- apply (proj1 (ds_comm_or G B0 A0 HoG WB0 WA0)).
Qed.

Theorem asub_sound : forall G A B, algo_sub G A B -> declarative_subtyping G A B.
Proof.
  intros G A B H. induction H.
  - apply DS_refl; auto.
  - eapply ds_weaken_cons; [exact H | exact IHalgo_sub].
  - eapply ds_trans.
    + apply DS_prim; [exact H | simpl; auto].
    + eapply ds_weaken_cons; [exact H | exact IHalgo_sub].
  - apply DS_top; auto.
  - apply DS_bot; auto.
  - apply DS_arrow; auto.
  - destruct (asub_regular _ _ _ H0) as [Ho [HA HB1]].
    destruct (asub_regular _ _ _ H1) as [_ [_ HB2]].
    eapply ds_trans.
    + apply ds_and_intro.
      * exact IHalgo_sub1.
      * exact IHalgo_sub2.
    + eapply spli_ds_meet; eauto.
  - destruct (asub_regular _ _ _ H1) as [Ho1 [HA1 HB1]].
    apply ds_trans with (B := A1).
    + eapply spli_ds_l1; [exact H0 | exact Ho1 | eapply spli_wft_inv; eauto].
    + exact IHalgo_sub.
  - destruct (asub_regular _ _ _ H1) as [Ho2 [HA2 HB2]].
    apply ds_trans with (B := A2).
    + eapply spli_ds_l2; [exact H0 | exact Ho2 | eapply spli_wft_inv; eauto].
    + exact IHalgo_sub.
  - destruct (asub_regular _ _ _ H0) as [Ho1 [HA1 HB1]].
    destruct (asub_regular _ _ _ H1) as [_ [HA2 HB2]].
    apply ds_trans with (B := t_union A1 A2).
    + eapply splu_ds_join; [exact H | exact Ho1 | eapply splu_wft_inv; eauto].
    + apply DS_or; auto.
  - destruct (asub_regular _ _ _ H1) as [Ho1 [HA1 HB1]].
    apply ds_trans with (B := B1).
    + exact IHalgo_sub.
    + eapply splu_ds_l1; [exact H0 | exact Ho1 | eapply splu_wft_inv; eauto].
  - destruct (asub_regular _ _ _ H1) as [Ho1 [HA1 HB1]].
    apply ds_trans with (B := B2).
    + exact IHalgo_sub.
    + eapply splu_ds_l2; [exact H0 | exact Ho1 | eapply splu_wft_inv; eauto].
Qed.


(* ============ Decidable tests ============ *)
Lemma pair_eq_dec : forall (p q: atom*typ), {p=q}+{p<>q}.
Proof.
  intros [i A] [j B].
  destruct (eq_dec i j) as [Heq|Hne].
  - subst j. destruct (typ_eq_dec A B) as [Heq2|Hne2].
    + left; subst; reflexivity.
    + right; intros H; apply Hne2; injection H; auto.
  - right; intros H; apply Hne; injection H; auto.
Qed.

Fixpoint binds_exists_opt (n:atom) (G:envp) : option typ :=
  match G with
  | nil => None
  | (j,B)::G' => if eq_dec n j then Some B else binds_exists_opt n G'
  end.

Lemma binds_exists_opt_some : forall n G A, binds_exists_opt n G = Some A -> binds n A G.
Proof.
  intros n G. induction G as [|[j B] G'].
  - simpl; intros A H; discriminate.
  - simpl. destruct (eq_dec n j) as [Heq|Hne]; intros A H.
    + injection H as HAB. subst A. subst j. simpl. left. reflexivity.
    + simpl. right. eapply IHG'. exact H.
Qed.
Lemma binds_exists_opt_none : forall n G, binds_exists_opt n G = None -> forall A, ~ binds n A G.
Proof.
  intros n G. induction G as [|[j B] G'].
  - simpl; intros _ A H; exact H.
  - simpl. destruct (eq_dec n j) as [Heq|Hne]; intros H A Hin.
    + discriminate.
    + simpl in Hin; destruct Hin as [Heq2|Hin].
      * apply Hne. injection Heq2 as Hnj _. symmetry. exact Hnj.
      * eapply IHG' with (A:=A); eauto.
Qed.

Fixpoint wft_dec (G:envp) (A:typ) : {wft G A} + {~ wft G A}.
Proof.
  destruct A.
  - left; apply wft_int.
  - left; apply wft_top.
  - left; apply wft_bot.
  - destruct (wft_dec G A1) as [H1|H1]; destruct (wft_dec G A2) as [H2|H2].
    + left; apply wft_arrow; auto.
    + right; intro H; apply H2; inversion H; auto.
    + right; intro H; apply H1; inversion H; auto.
    + right; intro H; apply H1; inversion H; auto.
  - destruct (wft_dec G A1) as [H1|H1]; destruct (wft_dec G A2) as [H2|H2].
    + left; apply wft_or; auto.
    + right; intro H; apply H2; inversion H; auto.
    + right; intro H; apply H1; inversion H; auto.
    + right; intro H; apply H1; inversion H; auto.
  - destruct (wft_dec G A1) as [H1|H1]; destruct (wft_dec G A2) as [H2|H2].
    + left; apply wft_and; auto.
    + right; intro H; apply H2; inversion H; auto.
    + right; intro H; apply H1; inversion H; auto.
    + right; intro H; apply H1; inversion H; auto.
  - left; apply wft_unit.
  - destruct (binds_exists_opt n G) as [T|] eqn:E.
    + left. apply wft_prim with (A := T). eapply binds_exists_opt_some; eauto.
    + right. intro H. destruct (wft_prim_binds G n H) as [T Hb].
      eapply binds_exists_opt_none; eauto.
Defined.

Lemma notin_dec : forall (x:atom) (s:atoms), {x \notin s} + {~ x \notin s}.
Proof.
  intros x s. destruct (AtomSetImpl.mem x s) eqn:E.
  - right; intro H; apply (proj1 (not_mem_iff s x)) in H; rewrite H in E; discriminate.
  - left; apply (proj2 (not_mem_iff s x)); exact E.
Qed.

Fixpoint okenvp_dec (G:envp) : {okenvp G} + {~ okenvp G}.
Proof.
  destruct G as [|[i A] PG].
  - left; apply okenvp_empty.
  - destruct (okenvp_dec PG) as [Ho|Ho].
    + destruct (notin_dec i (dom PG)) as [Hn|Hn].
      * destruct A as [| | | X Y | X Y | X Y | | n].
        -- right; intro H; inversion H.
        -- left; apply okenvp_cons; auto.
        -- right; intro H; inversion H.
        -- right; intro H; inversion H.
        -- right; intro H; inversion H.
        -- right; intro H; inversion H.
        -- right; intro H; inversion H.
        -- destruct (wft_dec PG (t_prim n)) as [Hw|Hw].
           ++ left; apply okenvp_sub; auto.
           ++ right; intro H; inversion H; subst; auto.
      * right; intro H; inversion H; subst; auto.
    + right; intro H; inversion H; subst; auto.
Defined.

Definition typ_eqb (A B:typ) : bool := if typ_eq_dec A B then true else false.
Lemma typ_eqb_eq : forall A B, typ_eqb A B = true -> A = B.
Proof. intros A B H; unfold typ_eqb in H; destruct (typ_eq_dec A B); auto; discriminate. Qed.
Lemma typ_eqb_complete : forall A B, A = B -> typ_eqb A B = true.
Proof. intros A B e; subst; unfold typ_eqb; destruct (typ_eq_dec B B); auto; exfalso; auto. Qed.

Definition eqb (x y:atom) : bool := if eq_dec x y then true else false.
Lemma eqb_eq : forall x y, eqb x y = true -> x = y.
Proof. intros x y H; unfold eqb in H; destruct (eq_dec x y); auto; discriminate. Qed.
Lemma eqb_complete : forall x y, x = y -> eqb x y = true.
Proof. intros x y e; subst; unfold eqb; destruct (eq_dec y y); auto; exfalso; auto. Qed.

Definition neqb (x y:atom) : bool := if eq_dec x y then false else true.
Lemma neqb_true : forall x y, neqb x y = true -> x <> y.
Proof. intros x y H; unfold neqb in H; destruct (eq_dec x y); auto; discriminate. Qed.
Lemma neqb_complete : forall x y, x <> y -> neqb x y = true.
Proof. intros x y H; unfold neqb; destruct (eq_dec x y); auto; contradiction. Qed.

Definition okenvp_b (G:envp) : bool := if okenvp_dec G then true else false.
Lemma okenvp_b_true : forall G, okenvp_b G = true -> okenvp G.
Proof. intros G H; unfold okenvp_b in H; destruct (okenvp_dec G); auto; discriminate. Qed.
Lemma okenvp_b_complete : forall G, okenvp G -> okenvp_b G = true.
Proof. intros G H; unfold okenvp_b; destruct (okenvp_dec G); auto; exfalso; auto. Qed.

Definition wft_b (G:envp) (A:typ) : bool := if wft_dec G A then true else false.
Lemma wft_b_true : forall G A, wft_b G A = true -> wft G A.
Proof. intros G A H; unfold wft_b in H; destruct (wft_dec G A); auto; discriminate. Qed.
Lemma wft_b_complete : forall G A, wft G A -> wft_b G A = true.
Proof. intros G A H; unfold wft_b; destruct (wft_dec G A); auto; exfalso; auto. Qed.

(* ============ Decision procedure ============ *)
Fixpoint orbs (l:list bool) : bool :=
  match l with
  | nil => false
  | b :: l' => orb b (orbs l')
  end.

Definition adec_rules (dec : envp -> typ -> typ -> bool) (G:envp) (A B:typ) : list bool :=
  (okenvp_b G && wft_b G A && typ_eqb A B) ::
  (okenvp_b G && wft_b G A && typ_eqb B t_top) ::
  (okenvp_b G && wft_b G B && typ_eqb A t_bot) ::
  (match G with
   | (i,C) :: PG =>
       (okenvp_b G &&
       match A, B with
       | t_prim n1, t_prim n2 =>
           (neqb i n1 && dec PG A B)
           || (eqb i n1 && match C with t_prim j => dec PG C B | _ => false end)
       | _ , _ => false
       end)
   | nil => false
   end) ::
  (match A, B with
   | t_arrow a1 a2, t_arrow b1 b2 => (dec G b1 a1 && dec G a2 b2)
   | _ , _ => false
   end) ::
  (match spli_opt B with
   | Some (B1,B2) => (dec G A B1 && dec G A B2)
   | None => false
   end) ::
  (match spli_opt A with
   | Some (A1,A2) => (wft_b G A2 && dec G A1 B)
   | None => false
   end) ::
  (match spli_opt A with
   | Some (A1,A2) => (wft_b G A1 && dec G A2 B)
   | None => false
   end) ::
  (match splu_opt A with
   | Some (A1,A2) => (dec G A1 B && dec G A2 B)
   | None => false
   end) ::
  (match splu_opt B with
   | Some (B1,B2) => (wft_b G B2 && dec G A B1)
   | None => false
   end) ::
  (match splu_opt B with
   | Some (B1,B2) => (wft_b G B1 && dec G A B2)
   | None => false
   end) ::
  nil.

Fixpoint adec (k:nat) (G:envp) (A B:typ) {struct k} : bool :=
  match k with
  | 0 => false
  | S k' => orbs (adec_rules (adec k') G A B)
  end.

Lemma orbs_true_iff : forall l, orbs l = true <-> exists b, In b l /\ b = true.
Proof.
  induction l as [|a l IH]; simpl.
  - split; [discriminate|intros [b [H _]]; inversion H].
  - rewrite orb_true_iff. split.
    + intros [H|H].
      * exists a; split; [left; reflexivity|exact H].
      * apply IH in H. destruct H as [b [Hin Hb]].
        exists b; split; [right; exact Hin|exact Hb].
    + intros [b [Hin Hb]]; destruct Hin as [Heq|Hin].
      * left; subst b; exact Hb.
      * right; apply IH; exists b; auto.
Qed.

Lemma rule_refl : forall (dec : envp -> typ -> typ -> bool) G A B,
  (okenvp_b G && wft_b G A && typ_eqb A B) = true -> algo_sub G A B.
Proof.
  intros dec G A B H. apply andb_true_iff in H; destruct H as [H1 H2].
  apply andb_true_iff in H1; destruct H1 as [Ho Hw].
  apply typ_eqb_eq in H2. subst B.
  apply AS_refl; auto using okenvp_b_true, wft_b_true.
Qed.
Lemma rule_top : forall (dec : envp -> typ -> typ -> bool) G A B,
  (okenvp_b G && wft_b G A && typ_eqb B t_top) = true -> algo_sub G A B.
Proof.
  intros dec G A B H. apply andb_true_iff in H; destruct H as [H1 H2].
  apply andb_true_iff in H1; destruct H1 as [Ho Hw].
  apply typ_eqb_eq in H2. subst B.
  apply AS_top; auto using okenvp_b_true, wft_b_true.
Qed.
Lemma rule_bot : forall (dec : envp -> typ -> typ -> bool) G A B,
  (okenvp_b G && wft_b G B && typ_eqb A t_bot) = true -> algo_sub G A B.
Proof.
  intros dec G A B H. apply andb_true_iff in H; destruct H as [H1 H2].
  apply andb_true_iff in H1; destruct H1 as [Ho Hw].
  apply typ_eqb_eq in H2. subst A.
  apply AS_bot; auto using okenvp_b_true, wft_b_true.
Qed.
Lemma rule_prim : forall (dec : envp -> typ -> typ -> bool) G A B,
  (match G with
   | (i,C) :: PG =>
       (okenvp_b G &&
       match A, B with
       | t_prim n1, t_prim n2 =>
           (neqb i n1 && dec PG A B)
           || (eqb i n1 && match C with t_prim j => dec PG C B | _ => false end)
       | _ , _ => false
       end)
   | nil => false
   end) = true ->
  (forall G A B, dec G A B = true -> algo_sub G A B) ->
  algo_sub G A B.
Proof.
  intros dec G A B H Hdec.
  destruct G as [|[i C] PG]; [simpl in H; discriminate|].
  simpl in H. apply andb_true_iff in H; destruct H as [Ho Hrest].
  destruct A; try (simpl in Hrest; discriminate);
    destruct B; try (simpl in Hrest; discriminate).
  apply orb_true_iff in Hrest; destruct Hrest as [Hne|Heq].
  - apply andb_true_iff in Hne; destruct Hne as [Hneq Hd].
    apply neqb_true in Hneq.
    eapply AS_prim_neq; [exact (okenvp_b_true _ Ho) | exact Hneq | apply Hdec; exact Hd].
  - apply andb_true_iff in Heq; destruct Heq as [Hieq Hd].
    apply eqb_eq in Hieq. subst i.
    destruct C; try (simpl in Hd; discriminate).
    eapply AS_prim_eq; [exact (okenvp_b_true _ Ho) | apply Hdec; exact Hd].
Qed.
Lemma rule_arrow : forall (dec : envp -> typ -> typ -> bool) G A B,
  (match A, B with
   | t_arrow a1 a2, t_arrow b1 b2 => (dec G b1 a1 && dec G a2 b2)
   | _ , _ => false
   end) = true ->
  (forall G A B, dec G A B = true -> algo_sub G A B) ->
  algo_sub G A B.
Proof.
  intros dec G A B H Hdec.
  destruct A; try (simpl in H; discriminate);
    destruct B; try (simpl in H; discriminate).
  simpl in H. apply andb_true_iff in H; destruct H as [H1 H2].
  eapply AS_arrow; [apply Hdec; exact H1 | apply Hdec; exact H2].
Qed.
Lemma rule_and : forall (dec : envp -> typ -> typ -> bool) G A B,
  (match spli_opt B with Some (B1,B2) => (dec G A B1 && dec G A B2) | None => false end) = true ->
  (forall G A B, dec G A B = true -> algo_sub G A B) -> algo_sub G A B.
Proof.
  intros dec G A B H Hdec.
  destruct (spli_opt B) as [[B1 B2]|] eqn:E; [|simpl in H; discriminate].
  simpl in H. apply andb_true_iff in H; destruct H as [H1 H2].
  eapply AS_and; [apply spli_opt_sound; exact E | apply Hdec; exact H1 | apply Hdec; exact H2].
Qed.
Lemma rule_andl : forall (dec : envp -> typ -> typ -> bool) G A B,
  (match spli_opt A with Some (A1,A2) => (wft_b G A2 && dec G A1 B) | None => false end) = true ->
  (forall G A B, dec G A B = true -> algo_sub G A B) -> algo_sub G A B.
Proof.
  intros dec G A B H Hdec.
  destruct (spli_opt A) as [[A1 A2]|] eqn:E; [|simpl in H; discriminate].
  simpl in H. apply andb_true_iff in H; destruct H as [Hw H1].
  eapply AS_andl; [apply wft_b_true; exact Hw | apply spli_opt_sound; exact E | apply Hdec; exact H1].
Qed.
Lemma rule_andr : forall (dec : envp -> typ -> typ -> bool) G A B,
  (match spli_opt A with Some (A1,A2) => (wft_b G A1 && dec G A2 B) | None => false end) = true ->
  (forall G A B, dec G A B = true -> algo_sub G A B) -> algo_sub G A B.
Proof.
  intros dec G A B H Hdec.
  destruct (spli_opt A) as [[A1 A2]|] eqn:E; [|simpl in H; discriminate].
  simpl in H. apply andb_true_iff in H; destruct H as [Hw H1].
  eapply AS_andr; [apply wft_b_true; exact Hw | apply spli_opt_sound; exact E | apply Hdec; exact H1].
Qed.
Lemma rule_or : forall (dec : envp -> typ -> typ -> bool) G A B,
  (match splu_opt A with Some (A1,A2) => (dec G A1 B && dec G A2 B) | None => false end) = true ->
  (forall G A B, dec G A B = true -> algo_sub G A B) -> algo_sub G A B.
Proof.
  intros dec G A B H Hdec.
  destruct (splu_opt A) as [[A1 A2]|] eqn:E; [|simpl in H; discriminate].
  simpl in H. apply andb_true_iff in H; destruct H as [H1 H2].
  eapply AS_or; [apply splu_opt_sound; exact E | apply Hdec; exact H1 | apply Hdec; exact H2].
Qed.
Lemma rule_orl : forall (dec : envp -> typ -> typ -> bool) G A B,
  (match splu_opt B with Some (B1,B2) => (wft_b G B2 && dec G A B1) | None => false end) = true ->
  (forall G A B, dec G A B = true -> algo_sub G A B) -> algo_sub G A B.
Proof.
  intros dec G A B H Hdec.
  destruct (splu_opt B) as [[B1 B2]|] eqn:E; [|simpl in H; discriminate].
  simpl in H. apply andb_true_iff in H; destruct H as [Hw H1].
  eapply AS_orl; [apply wft_b_true; exact Hw | apply splu_opt_sound; exact E | apply Hdec; exact H1].
Qed.
Lemma rule_orr : forall (dec : envp -> typ -> typ -> bool) G A B,
  (match splu_opt B with Some (B1,B2) => (wft_b G B1 && dec G A B2) | None => false end) = true ->
  (forall G A B, dec G A B = true -> algo_sub G A B) -> algo_sub G A B.
Proof.
  intros dec G A B H Hdec.
  destruct (splu_opt B) as [[B1 B2]|] eqn:E; [|simpl in H; discriminate].
  simpl in H. apply andb_true_iff in H; destruct H as [Hw H1].
  eapply AS_orr; [apply wft_b_true; exact Hw | apply splu_opt_sound; exact E | apply Hdec; exact H1].
Qed.

Lemma adec_rules_spec : forall dec G A B b,
  (forall G A B, dec G A B = true -> algo_sub G A B) ->
  In b (adec_rules dec G A B) -> b = true -> algo_sub G A B.
Proof.
  intros dec G A B b Hdec Hin Hb.
  unfold adec_rules in Hin. simpl in Hin.
  repeat match goal with H : _ \/ _ |- _ => destruct H as [Heq|H] end.
  all: try (exfalso; assumption).
  all: subst b.
  all: try (apply (rule_refl dec); exact Hb).
  all: try (apply (rule_top dec); exact Hb).
  all: try (apply (rule_bot dec); exact Hb).
  all: try (eapply (rule_prim dec); [exact Hb | exact Hdec]).
  all: try (eapply (rule_arrow dec); [exact Hb | exact Hdec]).
  all: try (eapply (rule_and dec); [exact Hb | exact Hdec]).
  all: try (eapply (rule_andl dec); [exact Hb | exact Hdec]).
  all: try (eapply (rule_andr dec); [exact Hb | exact Hdec]).
  all: try (eapply (rule_or dec); [exact Hb | exact Hdec]).
  all: try (eapply (rule_orl dec); [exact Hb | exact Hdec]).
  all: try (eapply (rule_orr dec); [exact Hb | exact Hdec]).
Qed.

Lemma adec_sound : forall k G A B, adec k G A B = true -> algo_sub G A B.
Proof.
  induction k as [|k IH]; intros G A B H.
  - simpl in H; discriminate.
  - change (orbs (adec_rules (adec k) G A B) = true) in H.
    apply orbs_true_iff in H. destruct H as [b [Hin Hb]].
    eapply adec_rules_spec.
    + intros G0 A0 B0 H0. apply IH; exact H0.
    + exact Hin.
    + exact Hb.
Qed.

(* ============ Completeness of the decision procedure ============ *)
Definition m (G:envp) (A B:typ) : nat := size_envp G + size_typ A + size_typ B.
Lemma m_ge_2 : forall G A B, 2 <= m G A B.
Proof. intros G A B; unfold m; pose (size_pos A); pose (size_pos B); lia. Qed.
Lemma m_splu_l : forall G A B C X, splu A B C -> m G B X < m G A X.
Proof. intros; unfold m; apply splu_size in H; lia. Qed.
Lemma m_splu_r : forall G A B C X, splu A B C -> m G C X < m G A X.
Proof. intros; unfold m; apply splu_size in H; lia. Qed.
Lemma m_spli_l : forall G A B C X, spli A B C -> m G B X < m G A X.
Proof. intros; unfold m; apply spli_size in H; lia. Qed.
Lemma m_spli_r : forall G A B C X, spli A B C -> m G C X < m G A X.
Proof. intros; unfold m; apply spli_size in H; lia. Qed.
Lemma m_arrow_l : forall G A1 A2 B1 B2, m G B1 A1 < m G (t_arrow A1 A2) (t_arrow B1 B2).
Proof. intros; unfold m; simpl; pose (size_pos A2); lia. Qed.
Lemma m_arrow_r : forall G A1 A2 B1 B2, m G A2 B2 < m G (t_arrow A1 A2) (t_arrow B1 B2).
Proof. intros; unfold m; simpl; pose (size_pos B1); lia. Qed.
Lemma m_prim : forall G i A n1 n2,
  m G (t_prim n1) (t_prim n2) < m ((i,A)::G) (t_prim n1) (t_prim n2).
Proof. intros; unfold m; simpl; pose (size_pos A); lia. Qed.

Lemma orbs_in : forall l b, In b l -> b = true -> orbs l = true.
Proof. intros l b Hin Hb. apply orbs_true_iff. exists b; auto. Qed.

Lemma rule_refl_complete : forall (dec:envp->typ->typ->bool) G A,
  okenvp G -> wft G A -> orbs (adec_rules dec G A A) = true.
Proof.
  intros dec G A Ho Hw.
  apply orbs_in with (b := (okenvp_b G && wft_b G A && typ_eqb A A)).
  - unfold adec_rules; simpl. left. reflexivity.
  - apply andb_true_iff; split.
    + apply andb_true_iff; split; [apply okenvp_b_complete; exact Ho | apply wft_b_complete; exact Hw].
    + apply typ_eqb_complete; reflexivity.
Qed.
Lemma rule_top_complete : forall (dec:envp->typ->typ->bool) G A,
  okenvp G -> wft G A -> orbs (adec_rules dec G A t_top) = true.
Proof.
  intros dec G A Ho Hw.
  apply orbs_in with (b := (okenvp_b G && wft_b G A && typ_eqb t_top t_top)).
  - unfold adec_rules; simpl. right. left. reflexivity.
  - apply andb_true_iff; split.
    + apply andb_true_iff; split; [apply okenvp_b_complete; exact Ho | apply wft_b_complete; exact Hw].
    + apply typ_eqb_complete; reflexivity.
Qed.
Lemma rule_bot_complete : forall (dec:envp->typ->typ->bool) G B,
  okenvp G -> wft G B -> orbs (adec_rules dec G t_bot B) = true.
Proof.
  intros dec G B Ho Hw.
  apply orbs_in with (b := (okenvp_b G && wft_b G B && typ_eqb t_bot t_bot)).
  - unfold adec_rules; simpl. right. right. left. reflexivity.
  - apply andb_true_iff; split.
    + apply andb_true_iff; split; [apply okenvp_b_complete; exact Ho | apply wft_b_complete; exact Hw].
    + apply typ_eqb_complete; reflexivity.
Qed.
Lemma rule_prim_neq_complete : forall (dec:envp->typ->typ->bool) PG i A n1 n2,
  okenvp ((i,A)::PG) -> i <> n1 -> dec PG (t_prim n1) (t_prim n2) = true ->
  orbs (adec_rules dec ((i,A)::PG) (t_prim n1) (t_prim n2)) = true.
Proof.
  intros dec PG i A n1 n2 Ho Hne Hd.
  apply orbs_in with (b := (okenvp_b ((i,A)::PG) &&
      ((neqb i n1 && dec PG (t_prim n1) (t_prim n2))
       || (eqb i n1 && match A with t_prim _ => dec PG A (t_prim n2) | _ => false end)))).
  - unfold adec_rules; simpl. right. right. right. left. reflexivity.
  - apply andb_true_iff; split.
    + apply okenvp_b_complete; exact Ho.
    + apply orb_true_iff; left. apply andb_true_iff; split;
        [apply neqb_complete; exact Hne | exact Hd].
Qed.
Lemma rule_prim_eq_complete : forall (dec:envp->typ->typ->bool) PG j n1 n2,
  okenvp ((n1,t_prim j)::PG) -> dec PG (t_prim j) (t_prim n2) = true ->
  orbs (adec_rules dec ((n1,t_prim j)::PG) (t_prim n1) (t_prim n2)) = true.
Proof.
  intros dec PG j n1 n2 Ho Hd.
  apply orbs_in with (b := (okenvp_b ((n1,t_prim j)::PG) &&
      ((neqb n1 n1 && dec PG (t_prim n1) (t_prim n2))
       || (eqb n1 n1 && match t_prim j with t_prim k => dec PG (t_prim k) (t_prim n2) | _ => false end)))).
  - unfold adec_rules; simpl. right. right. right. left. reflexivity.
  - apply andb_true_iff; split.
    + apply okenvp_b_complete; exact Ho.
    + apply orb_true_iff; right. apply andb_true_iff; split.
      * apply eqb_complete; reflexivity.
      * simpl. exact Hd.
Qed.
Lemma rule_arrow_complete : forall (dec:envp->typ->typ->bool) G a1 a2 b1 b2,
  dec G b1 a1 = true -> dec G a2 b2 = true ->
  orbs (adec_rules dec G (t_arrow a1 a2) (t_arrow b1 b2)) = true.
Proof.
  intros dec G a1 a2 b1 b2 H1 H2.
  apply orbs_in with (b := (dec G b1 a1 && dec G a2 b2)).
  - unfold adec_rules; simpl. right. right. right. right. left. reflexivity.
  - apply andb_true_iff; split; assumption.
Qed.
Lemma rule_and_complete : forall (dec:envp->typ->typ->bool) G A B B1 B2,
  spli B B1 B2 -> dec G A B1 = true -> dec G A B2 = true ->
  orbs (adec_rules dec G A B) = true.
Proof.
  intros dec G A B B1 B2 Hsp H1 H2.
  apply orbs_in with (b := (dec G A B1 && dec G A B2)).
  - unfold adec_rules; rewrite (spli_opt_complete _ _ _ Hsp).
    simpl. right. right. right. right. right. left. reflexivity.
  - apply andb_true_iff; split; assumption.
Qed.
Lemma rule_andl_complete : forall (dec:envp->typ->typ->bool) G A B A1 A2,
  spli A A1 A2 -> wft G A2 -> dec G A1 B = true ->
  orbs (adec_rules dec G A B) = true.
Proof.
  intros dec G A B A1 A2 Hsp Hw Hd.
  apply orbs_in with (b := (wft_b G A2 && dec G A1 B)).
  - unfold adec_rules; rewrite (spli_opt_complete _ _ _ Hsp).
    simpl. right. right. right. right. right. right. left. reflexivity.
  - apply andb_true_iff; split; [apply wft_b_complete; exact Hw | exact Hd].
Qed.
Lemma rule_andr_complete : forall (dec:envp->typ->typ->bool) G A B A1 A2,
  spli A A1 A2 -> wft G A1 -> dec G A2 B = true ->
  orbs (adec_rules dec G A B) = true.
Proof.
  intros dec G A B A1 A2 Hsp Hw Hd.
  apply orbs_in with (b := (wft_b G A1 && dec G A2 B)).
  - unfold adec_rules; rewrite (spli_opt_complete _ _ _ Hsp).
    simpl. right. right. right. right. right. right. right. left. reflexivity.
  - apply andb_true_iff; split; [apply wft_b_complete; exact Hw | exact Hd].
Qed.
Lemma rule_or_complete : forall (dec:envp->typ->typ->bool) G A B A1 A2,
  splu A A1 A2 -> dec G A1 B = true -> dec G A2 B = true ->
  orbs (adec_rules dec G A B) = true.
Proof.
  intros dec G A B A1 A2 Hsp H1 H2.
  apply orbs_in with (b := (dec G A1 B && dec G A2 B)).
  - unfold adec_rules; rewrite (splu_opt_complete _ _ _ Hsp).
    simpl. right. right. right. right. right. right. right. right. left. reflexivity.
  - apply andb_true_iff; split; assumption.
Qed.
Lemma rule_orl_complete : forall (dec:envp->typ->typ->bool) G A B B1 B2,
  splu B B1 B2 -> wft G B2 -> dec G A B1 = true ->
  orbs (adec_rules dec G A B) = true.
Proof.
  intros dec G A B B1 B2 Hsp Hw Hd.
  apply orbs_in with (b := (wft_b G B2 && dec G A B1)).
  - unfold adec_rules; rewrite (splu_opt_complete _ _ _ Hsp).
    simpl. right. right. right. right. right. right. right. right. right. left. reflexivity.
  - apply andb_true_iff; split; [apply wft_b_complete; exact Hw | exact Hd].
Qed.
Lemma rule_orr_complete : forall (dec:envp->typ->typ->bool) G A B B1 B2,
  splu B B1 B2 -> wft G B1 -> dec G A B2 = true ->
  orbs (adec_rules dec G A B) = true.
Proof.
  intros dec G A B B1 B2 Hsp Hw Hd.
  apply orbs_in with (b := (wft_b G B1 && dec G A B2)).
  - unfold adec_rules; rewrite (splu_opt_complete _ _ _ Hsp).
    simpl. right. right. right. right. right. right. right. right. right. right. left. reflexivity.
  - apply andb_true_iff; split; [apply wft_b_complete; exact Hw | exact Hd].
Qed.

Lemma adec_complete : forall n G A B, m G A B <= n -> algo_sub G A B -> adec n G A B = true.
Proof.
  intros n. induction n as [n IH] using lt_wf_ind.
  intros G A B Hm Ha.
  destruct n as [|k'].
  - exfalso; pose (m_ge_2 G A B); lia.
  - revert Hm. destruct Ha.
    all: intros Hm; cbn [adec].
    + apply rule_refl_complete; eassumption.
    + eapply rule_prim_neq_complete.
      * eassumption.
      * eassumption.
      * apply (IH k' ltac:(lia) PG (t_prim n1) (t_prim n2)).
        -- unfold m in *; simpl in *; lia.
        -- eassumption.
    + eapply rule_prim_eq_complete.
      * eassumption.
      * apply (IH k' ltac:(lia) PG (t_prim j) (t_prim n2)).
        -- unfold m in *; simpl in *; lia.
        -- eassumption.
    + apply rule_top_complete; eassumption.
    + apply rule_bot_complete; eassumption.
    + eapply rule_arrow_complete.
      * apply (IH k' ltac:(lia) PG B1 A1).
        -- unfold m in *; simpl in *; lia.
        -- eassumption.
      * apply (IH k' ltac:(lia) PG A2 B2).
        -- unfold m in *; simpl in *; lia.
        -- eassumption.
    + eapply rule_and_complete.
      * eassumption.
      * apply (IH k' ltac:(lia) PG A B1).
        -- match goal with Hs : spli B B1 B2 |- _ => pose proof (spli_size B B1 B2 Hs) end;
             unfold m in *; lia.
        -- eassumption.
      * apply (IH k' ltac:(lia) PG A B2).
        -- match goal with Hs : spli B B1 B2 |- _ => pose proof (spli_size B B1 B2 Hs) end;
             unfold m in *; lia.
        -- eassumption.
    + eapply rule_andl_complete.
      * eassumption.
      * eassumption.
      * apply (IH k' ltac:(lia) PG A1 B).
        -- match goal with Hs : spli A A1 A2 |- _ => pose proof (spli_size A A1 A2 Hs) end;
             unfold m in *; lia.
        -- eassumption.
    + eapply rule_andr_complete.
      * eassumption.
      * eassumption.
      * apply (IH k' ltac:(lia) PG A2 B).
        -- match goal with Hs : spli A A1 A2 |- _ => pose proof (spli_size A A1 A2 Hs) end;
             unfold m in *; lia.
        -- eassumption.
    + eapply rule_or_complete.
      * eassumption.
      * apply (IH k' ltac:(lia) PG A1 B).
        -- match goal with Hs : splu A A1 A2 |- _ => pose proof (splu_size A A1 A2 Hs) end;
             unfold m in *; lia.
        -- eassumption.
      * apply (IH k' ltac:(lia) PG A2 B).
        -- match goal with Hs : splu A A1 A2 |- _ => pose proof (splu_size A A1 A2 Hs) end;
             unfold m in *; lia.
        -- eassumption.
    + eapply rule_orl_complete.
      * eassumption.
      * eassumption.
      * apply (IH k' ltac:(lia) PG A B1).
        -- match goal with Hs : splu B B1 B2 |- _ => pose proof (splu_size B B1 B2 Hs) end;
             unfold m in *; lia.
        -- eassumption.
    + eapply rule_orr_complete.
      * eassumption.
      * eassumption.
      * apply (IH k' ltac:(lia) PG A B2).
        -- match goal with Hs : splu B B1 B2 |- _ => pose proof (splu_size B B1 B2 Hs) end;
             unfold m in *; lia.
        -- eassumption.
Qed.


Theorem decidability_proof : forall G A B, algo_sub G A B \/ not (algo_sub G A B).
Proof.
  intros G A B.
  destruct (adec (m G A B) G A B) eqn:E.
  - left. apply adec_sound with (k := m G A B); exact E.
  - right. intro H.
    apply adec_complete with (n := m G A B) in H.
    + rewrite E in H; discriminate.
    + lia.
Qed.

(* ============ Split inversion helpers ============ *)
Lemma splu_inv_union : forall X Y P Q, splu (t_union X Y) P Q -> P = X /\ Q = Y.
Proof.
  intros X Y P Q H. remember (t_union X Y) as T eqn:ET.
  destruct H as [A B | A B A1 A2 Hp | A B B1 B2 Ho Hp]; try discriminate.
  - injection ET as -> ->. auto.
Qed.

Lemma spli_inv_and : forall X Y P Q, spli (t_and X Y) P Q -> P = X /\ Q = Y.
Proof.
  intros X Y P Q H. remember (t_and X Y) as T eqn:ET.
  destruct H as [A B | A B C D Hp | A D B C Ho Hp | A B A1 A2 Hp | A B B1 B2 Ho Hp];
    try discriminate.
  - injection ET as -> ->. auto.
Qed.

Lemma splu_inv_and : forall X Y P Q, splu (t_and X Y) P Q ->
  (exists P1 Q1, P = t_and P1 Y /\ Q = t_and Q1 Y /\ splu X P1 Q1) \/
  (ordu X /\ exists P1 Q1, P = t_and X P1 /\ Q = t_and X Q1 /\ splu Y P1 Q1).
Proof.
  intros X Y P Q H. remember (t_and X Y) as T eqn:ET.
  destruct H as [A B | A B A1 A2 Hp | A B B1 B2 Ho Hp]; try discriminate.
  - injection ET as -> ->. left. exists A1, A2.
    split; [reflexivity|]. split; [reflexivity|assumption].
  - injection ET as -> ->. right. split; [assumption|]. exists B1, B2.
    split; [reflexivity|]. split; [reflexivity|assumption].
Qed.

Lemma spli_inv_union : forall X Y P Q, spli (t_union X Y) P Q ->
  (exists P1 Q1, P = t_union P1 Y /\ Q = t_union Q1 Y /\ spli X P1 Q1) \/
  (ordi X /\ exists P1 Q1, P = t_union X P1 /\ Q = t_union X Q1 /\ spli Y P1 Q1).
Proof.
  intros X Y P Q H. remember (t_union X Y) as T eqn:ET.
  destruct H as [A B | A B C D Hp | A D B C Ho Hp | A B A1 A2 Hp | A B B1 B2 Ho Hp];
    try discriminate.
  - injection ET as -> ->. left. exists A1, A2.
    split; [reflexivity|]. split; [reflexivity|assumption].
  - injection ET as -> ->. right. split; [assumption|]. exists B1, B2.
    split; [reflexivity|]. split; [reflexivity|assumption].
Qed.

Lemma spli_inv_arrow : forall X Y P Q, spli (t_arrow X Y) P Q ->
  (exists C D, P = t_arrow X C /\ Q = t_arrow X D /\ spli Y C D) \/
  (exists P1 Q1, ordi Y /\ P = t_arrow P1 Y /\ Q = t_arrow Q1 Y /\ splu X P1 Q1).
Proof.
  intros X Y P Q H. remember (t_arrow X Y) as T eqn:ET.
  destruct H as [A B | A B C D Hp | A D B C Ho Hp | A B A1 A2 Hp | A B B1 B2 Ho Hp];
    try discriminate.
  - injection ET as -> ->. left. exists C, D.
    split; [reflexivity|]. split; [reflexivity|assumption].
  - injection ET as -> ->. right. exists B, C.
    split; [assumption|]. split; [reflexivity|]. split; [reflexivity|assumption].
Qed.

(*** Source-splu projection ***)
Lemma asub_splu_proj : forall G A B, algo_sub G A B ->
  forall P Q, splu A P Q -> algo_sub G P B /\ algo_sub G Q B.
Proof.
  intros G A B H. induction H as
    [ G A0 Ho WA
    | G i A n1 n2 Hok Hne H1 IH1
    | G j n1 n2 Hok H1 IH1
    | G A0 Ho WA
    | G A0 Ho WA
    | G A1 A2 B1 B2 H1 IH1 H2 IH2
    | G A0 B0 B1 B2 Hsp H1 IH1 H2 IH2
    | G A0 B0 A1 A2 WA2 Hsp H1 IH1
    | G A0 B0 A1 A2 WA1 Hsp H1 IH1
    | G A0 B0 A1 A2 Hsp H1 IH1 H2 IH2
    | G A0 B0 B1 B2 WB2 Hsp H1 IH1
    | G A0 B0 B1 B2 WB1 Hsp H1 IH1 ];
    intros P Q Hs.
  - destruct (splu_wft G A0 P Q Hs WA) as [HP HQ].
    split; [eapply asub_splu_l1 | eapply asub_splu_l2]; eauto.
  - inversion Hs.
  - inversion Hs.
  - destruct (splu_wft G A0 P Q Hs WA) as [HP HQ].
    split; apply AS_top; auto.
  - inversion Hs.
  - inversion Hs.
  - destruct (IH1 P Q Hs) as [H1P H1Q]. destruct (IH2 P Q Hs) as [H2P H2Q].
    split; eapply AS_and; eauto.
  - (* andl *)
    destruct A0 as [| | | X Y | X Y | X Y | | n].
    + inversion Hs.
    + inversion Hs.
    + inversion Hs.
    + inversion Hs.
    + (* union *) destruct (splu_inv_union X Y P Q Hs) as [-> ->].
      destruct (spli_inv_union X Y A1 A2 Hsp) as
        [[A1' [A2' [-> [-> Hsub]]]] | [Hord [A1' [A2' [-> [-> Hsub]]]]]].
      * destruct (IH1 A1' Y ltac:(apply SpU_or)) as [H1' HY].
        split.
        -- eapply AS_andl; [exact (proj1 (wft_inv_or G A2' Y WA2)) | exact Hsub | exact H1'].
        -- exact HY.
      * destruct (IH1 X A1' ltac:(apply SpU_or)) as [HX H1'].
        split.
        -- exact HX.
        -- eapply AS_andl; [exact (proj2 (wft_inv_or G X A2' WA2)) | exact Hsub | exact H1'].
    + (* and *) destruct (splu_inv_and X Y P Q Hs) as
        [[P1 [Q1 [-> [-> HsubU]]]] | [Hord [P1 [Q1 [-> [-> HsubV]]]]]].
      * destruct (spli_inv_and X Y A1 A2 Hsp) as [-> ->].
        destruct (IH1 P1 Q1 HsubU) as [H1' H2'].
        split.
        -- eapply AS_andl; [exact WA2 | apply SpI_and | exact H1'].
        -- eapply AS_andl; [exact WA2 | apply SpI_and | exact H2'].
      * destruct (spli_inv_and X Y A1 A2 Hsp) as [-> ->].
        destruct (splu_wft G Y P1 Q1 HsubV WA2) as [WP1 WQ1].
        split.
        -- eapply AS_andl; [exact WP1 | apply SpI_and | exact H1].
        -- eapply AS_andl; [exact WQ1 | apply SpI_and | exact H1].
    + inversion Hs.
    + inversion Hs.
  - (* andr *)
    destruct A0 as [| | | X Y | X Y | X Y | | n].
    + inversion Hs.
    + inversion Hs.
    + inversion Hs.
    + inversion Hs.
    + (* union *) destruct (splu_inv_union X Y P Q Hs) as [-> ->].
      destruct (spli_inv_union X Y A1 A2 Hsp) as
        [[A1' [A2' [-> [-> Hsub]]]] | [Hord [A1' [A2' [-> [-> Hsub]]]]]].
      * destruct (IH1 A2' Y ltac:(apply SpU_or)) as [H2' HY].
        split.
        -- eapply AS_andr; [exact (proj1 (wft_inv_or G A1' Y WA1)) | exact Hsub | exact H2'].
        -- exact HY.
      * destruct (IH1 X A2' ltac:(apply SpU_or)) as [HX H2'].
        split.
        -- exact HX.
        -- eapply AS_andr; [exact (proj2 (wft_inv_or G X A1' WA1)) | exact Hsub | exact H2'].
    + (* and *) destruct (splu_inv_and X Y P Q Hs) as
        [[P1 [Q1 [-> [-> HsubU]]]] | [Hord [P1 [Q1 [-> [-> HsubV]]]]]].
      * destruct (spli_inv_and X Y A1 A2 Hsp) as [-> ->].
        destruct (splu_wft G X P1 Q1 HsubU WA1) as [WP1 WQ1].
        split.
        -- eapply AS_andr; [exact WP1 | apply SpI_and | exact H1].
        -- eapply AS_andr; [exact WQ1 | apply SpI_and | exact H1].
      * destruct (spli_inv_and X Y A1 A2 Hsp) as [-> ->].
        destruct (IH1 P1 Q1 HsubV) as [HP1 HQ1].
        split.
        -- eapply AS_andr; [exact WA1 | apply SpI_and | exact HP1].
        -- eapply AS_andr; [exact WA1 | apply SpI_and | exact HQ1].
    + inversion Hs.
    + inversion Hs.
  - destruct (splu_det A0 A1 A2 P Q Hsp Hs) as [-> ->]. split; assumption.
  - destruct (IH1 P Q Hs) as [H1P H1Q].
    split.
    + eapply AS_orl; [exact WB2 | exact Hsp | exact H1P].
    + eapply AS_orl; [exact WB2 | exact Hsp | exact H1Q].
  - destruct (IH1 P Q Hs) as [H1P H1Q].
    split.
    + eapply AS_orr; [exact WB1 | exact Hsp | exact H1P].
    + eapply AS_orr; [exact WB1 | exact Hsp | exact H1Q].
Qed.

(*** Target-spli projection ***)
Lemma asub_spli_proj : forall G A B, algo_sub G A B ->
  forall P Q, spli B P Q -> algo_sub G A P /\ algo_sub G A Q.
Proof.
  intros G A B H. induction H as
    [ G A0 Ho WA
    | G i A n1 n2 Hok Hne H1 IH1
    | G j n1 n2 Hok H1 IH1
    | G A0 Ho WA
    | G A0 Ho WA
    | G A1 A2 B1 B2 H1 IH1 H2 IH2
    | G A0 B0 B1 B2 Hsp H1 IH1 H2 IH2
    | G A0 B0 A1 A2 WA2 Hsp H1 IH1
    | G A0 B0 A1 A2 WA1 Hsp H1 IH1
    | G A0 B0 A1 A2 Hsp H1 IH1 H2 IH2
    | G A0 B0 B1 B2 WB2 Hsp H1 IH1
    | G A0 B0 B1 B2 WB1 Hsp H1 IH1 ];
    intros P Q Hs.
  - destruct (asub_regular _ _ _ (AS_refl G A0 Ho WA)) as [_ [WA0 _]].
    split; [eapply asub_spli_l1 | eapply asub_spli_l2]; eauto.
  - inversion Hs.
  - inversion Hs.
  - inversion Hs.
  - destruct (spli_wft G A0 P Q Hs WA) as [WP WQ].
    split; apply AS_bot; auto.
  - destruct (spli_inv_arrow B1 B2 P Q Hs) as
      [[C [D [-> [-> Hsub]]]] | [P1 [Q1 [Hord [-> [-> Hsub]]]]]].
    + destruct (IH2 C D Hsub) as [H2C H2D].
      split.
      * eapply AS_arrow; [exact H1 | exact H2C].
      * eapply AS_arrow; [exact H1 | exact H2D].
    + destruct (asub_splu_proj G B1 A1 H1 P1 Q1 Hsub) as [HP1 HQ1].
      split.
      * eapply AS_arrow; [exact HP1 | exact H2].
      * eapply AS_arrow; [exact HQ1 | exact H2].
  - destruct (spli_det B0 B1 B2 P Q Hsp Hs) as [-> ->]. split; assumption.
  - destruct (IH1 P Q Hs) as [HP HQ].
    split; [eapply AS_andl | eapply AS_andl]; [exact WA2|exact Hsp|exact HP|exact WA2|exact Hsp|exact HQ].
  - destruct (IH1 P Q Hs) as [HP HQ].
    split; [eapply AS_andr | eapply AS_andr]; [exact WA1|exact Hsp|exact HP|exact WA1|exact Hsp|exact HQ].
  - destruct (IH1 P Q Hs) as [H1P H1Q]. destruct (IH2 P Q Hs) as [H2P H2Q].
    split; eapply AS_or; eauto.
  - (* orl *)
    destruct B0 as [| | | X Y | X Y | X Y | | n].
    + inversion Hsp.
    + inversion Hsp.
    + inversion Hsp.
    + inversion Hsp.
    + (* union *) destruct (splu_inv_union X Y B1 B2 Hsp) as [-> ->].
      destruct (spli_inv_union X Y P Q Hs) as
        [[P1 [Q1 [-> [-> Hsub]]]] | [Hord [P1 [Q1 [-> [-> Hsub]]]]]].
      * destruct (IH1 P1 Q1 Hsub) as [H1P H1Q].
        split.
        -- eapply AS_orl; [exact WB2 | apply SpU_or | exact H1P].
        -- eapply AS_orl; [exact WB2 | apply SpU_or | exact H1Q].
      * destruct (spli_wft G Y P1 Q1 Hsub WB2) as [WP1 WQ1].
        split.
        -- eapply AS_orl; [exact WP1 | apply SpU_or | exact H1].
        -- eapply AS_orl; [exact WQ1 | apply SpU_or | exact H1].
    + (* and *) destruct (splu_inv_and X Y B1 B2 Hsp) as
        [[B1' [B2' [-> [-> HsubU]]]] | [Hord [B1' [B2' [-> [-> HsubV]]]]]].
      * destruct (spli_inv_and X Y P Q Hs) as [-> ->].
        destruct (IH1 B1' Y ltac:(apply SpI_and)) as [H1P H1Y].
        destruct (wft_inv_and _ _ _ WB2) as [WB2' _].
        split.
        -- eapply AS_orl; [exact WB2' | exact HsubU | exact H1P].
        -- exact H1Y.
      * destruct (spli_inv_and X Y P Q Hs) as [-> ->].
        destruct (IH1 X B1' ltac:(apply SpI_and)) as [H1X H1B1'].
        destruct (wft_inv_and _ _ _ WB2) as [_ WB2'].
        split.
        -- exact H1X.
        -- eapply AS_orl; [exact WB2' | exact HsubV | exact H1B1'].
    + inversion Hsp.
    + inversion Hsp.
  - (* orr *)
    destruct B0 as [| | | X Y | X Y | X Y | | n].
    + inversion Hsp.
    + inversion Hsp.
    + inversion Hsp.
    + inversion Hsp.
    + (* union *) destruct (splu_inv_union X Y B1 B2 Hsp) as [-> ->].
      destruct (spli_inv_union X Y P Q Hs) as
        [[P1 [Q1 [-> [-> Hsub]]]] | [Hord [P1 [Q1 [-> [-> Hsub]]]]]].
      * destruct (spli_wft G X P1 Q1 Hsub WB1) as [WP1 WQ1].
        split.
        -- eapply AS_orr; [exact WP1 | apply SpU_or | exact H1].
        -- eapply AS_orr; [exact WQ1 | apply SpU_or | exact H1].
      * destruct (IH1 P1 Q1 Hsub) as [H1P H1Q].
        split.
        -- eapply AS_orr; [exact WB1 | apply SpU_or | exact H1P].
        -- eapply AS_orr; [exact WB1 | apply SpU_or | exact H1Q].
    + (* and *) destruct (splu_inv_and X Y B1 B2 Hsp) as
        [[B1' [B2' [-> [-> HsubU]]]] | [Hord [B1' [B2' [-> [-> HsubV]]]]]].
      * destruct (spli_inv_and X Y P Q Hs) as [-> ->].
        destruct (IH1 B2' Y ltac:(apply SpI_and)) as [H1B2' H1Y].
        destruct (wft_inv_and _ _ _ WB1) as [WB1' _].
        split.
        -- eapply AS_orr; [exact WB1' | exact HsubU | exact H1B2'].
        -- exact H1Y.
      * destruct (spli_inv_and X Y P Q Hs) as [-> ->].
        destruct (IH1 X B2' ltac:(apply SpI_and)) as [H1X H1B2'].
        destruct (wft_inv_and _ _ _ WB1) as [_ WB1'].
        split.
        -- exact H1X.
        -- eapply AS_orr; [exact WB1' | exact HsubV | exact H1B2'].
    + inversion Hsp.
    + inversion Hsp.
Qed.

Lemma Uf_size : forall k A u, size_typ A <= k -> In u (Uf k A) -> size_typ u <= size_typ A.
Proof.
  induction k as [|k IH]; intros A u Hs Hu.
  - pose proof (size_pos A); lia.
  - destruct (splu_opt A) as [[B C]|] eqn:E.
    + cbn [Uf] in Hu; rewrite E in Hu; simpl in Hu. apply in_app_or in Hu. destruct Hu as [Hu|Hu].
      * assert (Hspl : splu A B C) by (apply splu_opt_sound; auto).
        apply splu_size in Hspl as [HB _].
        assert (HuB : size_typ u <= size_typ B) by (apply (IH B u); [lia|exact Hu]).
        lia.
      * assert (Hspl : splu A B C) by (apply splu_opt_sound; auto).
        apply splu_size in Hspl as [_ HC].
        assert (HuC : size_typ u <= size_typ C) by (apply (IH C u); [lia|exact Hu]).
        lia.
    + cbn [Uf] in Hu; rewrite E in Hu; simpl in Hu. destruct Hu as [->|[]]. lia.
Qed.

Lemma If_size : forall k A u, size_typ A <= k -> In u (If k A) -> size_typ u <= size_typ A.
Proof.
  induction k as [|k IH]; intros A u Hs Hu.
  - pose proof (size_pos A); lia.
  - destruct (spli_opt A) as [[B C]|] eqn:E.
    + cbn [If] in Hu; rewrite E in Hu; simpl in Hu. apply in_app_or in Hu. destruct Hu as [Hu|Hu].
      * assert (Hsp : spli A B C) by (apply spli_opt_sound; auto).
        apply spli_size in Hsp as [HB _].
        assert (HuB : size_typ u <= size_typ B) by (apply (IH B u); [lia|exact Hu]).
        lia.
      * assert (Hsp : spli A B C) by (apply spli_opt_sound; auto).
        apply spli_size in Hsp as [_ HC].
        assert (HuC : size_typ u <= size_typ C) by (apply (IH C u); [lia|exact Hu]).
        lia.
    + cbn [If] in Hu; rewrite E in Hu; simpl in Hu. destruct Hu as [->|[]]. lia.
Qed.

Lemma U_size : forall A u, In u (U A) -> size_typ u <= size_typ A.
Proof. intros A u Hu. unfold U in Hu. exact (Uf_size (size_typ A) A u ltac:(lia) Hu). Qed.

Lemma I_size : forall A u, In u (I A) -> size_typ u <= size_typ A.
Proof. intros A u Hu. unfold I in Hu. exact (If_size (size_typ A) A u ltac:(lia) Hu). Qed.

Lemma Uf_wft : forall G k A, size_typ A <= k -> wft G A -> forall u, In u (Uf k A) -> wft G u.
Proof.
  intros G k. induction k as [|k IH]; intros A Hs WA u Hu.
  - pose proof (size_pos A); lia.
  - destruct (splu_opt A) as [[B C]|] eqn:E.
    + cbn [Uf] in Hu; rewrite E in Hu; simpl in Hu. apply in_app_or in Hu. destruct Hu as [Hu|Hu].
      * assert (Hspl : splu A B C) by (apply splu_opt_sound; auto).
        destruct (splu_wft G A B C Hspl WA) as [WB _].
        apply (IH B); [|exact WB|exact Hu].
        apply splu_size in Hspl; lia.
      * assert (Hspl : splu A B C) by (apply splu_opt_sound; auto).
        destruct (splu_wft G A B C Hspl WA) as [_ WC].
        apply (IH C); [|exact WC|exact Hu].
        apply splu_size in Hspl; lia.
    + cbn [Uf] in Hu; rewrite E in Hu; simpl in Hu. destruct Hu as [->|[]]. exact WA.
Qed.

Lemma If_wft : forall G k A, size_typ A <= k -> wft G A -> forall u, In u (If k A) -> wft G u.
Proof.
  intros G k. induction k as [|k IH]; intros A Hs WA u Hu.
  - pose proof (size_pos A); lia.
  - destruct (spli_opt A) as [[B C]|] eqn:E.
    + cbn [If] in Hu; rewrite E in Hu; simpl in Hu. apply in_app_or in Hu. destruct Hu as [Hu|Hu].
      * assert (Hsp : spli A B C) by (apply spli_opt_sound; auto).
        destruct (spli_wft G A B C Hsp WA) as [WB _].
        apply (IH B); [|exact WB|exact Hu].
        apply spli_size in Hsp; lia.
      * assert (Hsp : spli A B C) by (apply spli_opt_sound; auto).
        destruct (spli_wft G A B C Hsp WA) as [_ WC].
        apply (IH C); [|exact WC|exact Hu].
        apply spli_size in Hsp; lia.
    + cbn [If] in Hu; rewrite E in Hu; simpl in Hu. destruct Hu as [->|[]]. exact WA.
Qed.

Lemma U_wft : forall G A u, wft G A -> In u (U A) -> wft G u.
Proof. intros G A u WA Hu. unfold U in Hu. exact (Uf_wft G (size_typ A) A ltac:(lia) WA u Hu). Qed.

Lemma I_wft : forall G A u, wft G A -> In u (I A) -> wft G u.
Proof. intros G A u WA Hu. unfold I in Hu. exact (If_wft G (size_typ A) A ltac:(lia) WA u Hu). Qed.

Lemma U_ordu : forall A u, In u (U A) -> ordu u.
Proof.
  intros A u Hu. unfold U in Hu.
  assert (Hfa : Forall ordu (Uf (size_typ A) A)) by (apply Uf_ordu; lia).
  exact (proj1 (Forall_forall ordu (Uf (size_typ A) A)) Hfa u Hu).
Qed.

Lemma I_ordi : forall A u, In u (I A) -> ordi u.
Proof.
  intros A u Hu. unfold I in Hu.
  assert (Hfa : Forall ordi (If (size_typ A) A)) by (apply If_ordi; lia).
  exact (proj1 (Forall_forall ordi (If (size_typ A) A)) Hfa u Hu).
Qed.

(* ============ Projection of an asub derivation along U / I ============ *)

Lemma asub_source_Uf : forall G A B, algo_sub G A B ->
  forall k u, In u (Uf k A) -> algo_sub G u B.
Proof.
  intros G A B H k. revert A B H.
  induction k as [|k IH]; intros A B H u Hu.
  - simpl in Hu. destruct Hu as [->|[]]. exact H.
  - destruct (splu_opt A) as [[P Q]|] eqn:E.
    + cbn [Uf] in Hu; rewrite E in Hu; simpl in Hu. apply in_app_or in Hu. destruct Hu as [Hu|Hu].
      * assert (Hspl : splu A P Q) by (apply splu_opt_sound; auto).
        destruct (asub_splu_proj G A B H P Q Hspl) as [HP _].
        apply (IH P B HP u Hu).
      * assert (Hspl : splu A P Q) by (apply splu_opt_sound; auto).
        destruct (asub_splu_proj G A B H P Q Hspl) as [_ HQ].
        apply (IH Q B HQ u Hu).
    + cbn [Uf] in Hu; rewrite E in Hu; simpl in Hu. destruct Hu as [->|[]]. exact H.
Qed.

Lemma asub_source_U : forall G A B, algo_sub G A B -> forall u, In u (U A) -> algo_sub G u B.
Proof.
  intros G A B H u Hu. unfold U in Hu.
  exact (asub_source_Uf G A B H (size_typ A) u Hu).
Qed.

Lemma asub_target_If : forall G A B, algo_sub G A B ->
  forall k i, In i (If k B) -> algo_sub G A i.
Proof.
  intros G A B H k. revert A B H.
  induction k as [|k IH]; intros A B H i Hi.
  - simpl in Hi. destruct Hi as [->|[]]. exact H.
  - destruct (spli_opt B) as [[P Q]|] eqn:E.
    + cbn [If] in Hi; rewrite E in Hi; simpl in Hi. apply in_app_or in Hi. destruct Hi as [Hi|Hi].
      * assert (Hsp : spli B P Q) by (apply spli_opt_sound; auto).
        destruct (asub_spli_proj G A B H P Q Hsp) as [HP _].
        apply (IH A P HP i Hi).
      * assert (Hsp : spli B P Q) by (apply spli_opt_sound; auto).
        destruct (asub_spli_proj G A B H P Q Hsp) as [_ HQ].
        apply (IH A Q HQ i Hi).
    + cbn [If] in Hi; rewrite E in Hi; simpl in Hi. destruct Hi as [->|[]]. exact H.
Qed.

Lemma asub_target_I : forall G A B, algo_sub G A B -> forall i, In i (I B) -> algo_sub G A i.
Proof.
  intros G A B H i Hi. unfold I in Hi.
  exact (asub_target_If G A B H (size_typ B) i Hi).
Qed.


(* Ranks for the two mutually recursive statements.

   rankA(u,i) = (max(size u, size i), size i, size u)
   rankB(C,u,i) = (max(max(size C, size u), size i), max(size i, size C), size C)

   The second component of rankB is [max(size i, size C)] rather than
   [size i]: this is needed so that B's internal call A(u,j) for
   j : I C (with size j < size C) has smaller rank. *)
Definition rankA (u i:typ) : nat*nat*nat :=
  (Nat.max (size_typ u) (size_typ i), size_typ i, size_typ u).

Definition rankB (C u i:typ) : nat*nat*nat :=
  (Nat.max (Nat.max (size_typ C) (size_typ u)) (size_typ i),
   Nat.max (size_typ i) (size_typ C),
   size_typ C).

Definition lex3 (p q : nat*nat*nat) : Prop :=
  let '(a,b,c) := p in
  let '(a',b',c') := q in
  a < a' \/ (a = a' /\ (b < b' \/ (b = b' /\ c < c'))).

Lemma rankA_bounds : forall u i, let '(a,b,c) := rankA u i in b <= a /\ c <= a.
Proof. intros u i. unfold rankA. simpl. lia. Qed.

Lemma rankB_bounds : forall C u i, let '(a,b,c) := rankB C u i in b <= a /\ c <= a.
Proof. intros C u i. unfold rankB. simpl. lia. Qed.

(* A(u',i) with u' a proper spli/splu component of u. *)
Lemma rankA_smaller_source : forall u u' i,
  size_typ u' < size_typ u -> lex3 (rankA u' i) (rankA u i).
Proof. intros. unfold lex3, rankA. simpl. lia. Qed.

(* A(u,j) with j a proper component of the target i. *)
Lemma rankA_smaller_target : forall u i j,
  size_typ j < size_typ i -> lex3 (rankA u j) (rankA u i).
Proof. intros. unfold lex3, rankA. simpl. lia. Qed.

(* B(C',u,i) with C' a proper component of C. *)
Lemma rankB_smaller_component : forall C C' u i,
  size_typ C' < size_typ C -> lex3 (rankB C' u i) (rankB C u i).
Proof. intros. unfold lex3, rankB. simpl. lia. Qed.

(* B(C,v,j) for components C of u, v of u and j of i is strictly below A(u,i):
   this is the L1/L2 decrease (the first component strictly drops). *)
Lemma rankB_lt_rankA_components : forall C u i v j,
  size_typ C < size_typ u -> size_typ v < size_typ u -> size_typ j < size_typ i ->
  lex3 (rankB C v j) (rankA u i).
Proof. intros. unfold lex3, rankB, rankA. simpl. lia. Qed.

(* Inside B(C,u,i), the call A(u,j) for a proper atom j of I C is smaller. *)
Lemma rankA_lt_rankB_same_source : forall C u i j,
  size_typ j < size_typ C -> lex3 (rankA u j) (rankB C u i).
Proof. intros. unfold lex3, rankA, rankB. simpl. lia. Qed.

(* Inside B(C,u,i), the call A(w,i) for a proper atom w of U C is smaller. *)
Lemma rankA_lt_rankB_source_component : forall C u i w,
  size_typ w < size_typ C -> lex3 (rankA w i) (rankB C u i).
Proof. intros. unfold lex3, rankA, rankB. simpl. lia. Qed.

(* cmp -> asub for ordu/ordi endpoints, extracted from sle_asub_strong. *)
Lemma cmp_asub : forall G u i, ordu u -> ordi i -> cmp G u i -> algo_sub G u i.
Proof.
  intros G u i Hu Hi Hc.
  destruct (sle_asub_strong (size_typ u + size_typ i) (meas (size_typ u + size_typ i) G u i))
    as [Hl _].
  apply (Hl G u i); auto; try (unfold meas; lia).
Qed.

(* The atomic-middle transitivity that B's base case needs.  Its arrow case
   reduces, via C_arrow, to B on the proper arrow components, so it belongs
   to the same strong induction on size C. *)
Definition cmp_trans_atomic_stmt : Prop :=
  forall G c a b, ordu c -> ordi c -> cmp G a c -> cmp G c b -> cmp G a b.

(* ============ Base case B(t_top,u,i) ============ *)
Lemma cmp_trans_top : forall G u i,
  ordu u -> wft G u -> cmp G u t_top -> cmp G t_top i -> cmp G u i.
Proof.
  intros G u i Hu Wu H1 H2.
  remember (size_typ i) as n eqn:En.
  revert G u i Hu Wu H1 H2 En.
  induction n as [n IH] using lt_wf_ind.
  intros G u i Hu Wu H1 H2 En.
  destruct i as [| | | X Y | X Y | X Y | | p].
  - inversion H2.
  - exact H1.
  - inversion H2.
  - inversion H2.
  - inversion H2; subst.
    + eapply C_or_l; [eassumption|].
      eapply (IH (size_typ X)); [simpl; lia | exact Hu | exact Wu | exact H1 | assumption | reflexivity].
    + eapply C_or_r; [eassumption|].
      eapply (IH (size_typ Y)); [simpl; lia | exact Hu | exact Wu | exact H1 | assumption | reflexivity].
  - inversion H2.
  - inversion H2.
  - inversion H2.
Qed.

(* B's base case C = t_top. *)
Lemma B_top : forall G u i,
  ordu u -> ordi i -> wft G t_top -> wft G u -> wft G i ->
  (forall j, In j (I t_top) -> cmp G u j) ->
  (forall w, In w (U t_top) -> cmp G w i) -> cmp G u i.
Proof.
  intros G u i Hu Hi Wc Wu Wi H1 H2.
  assert (Hc1 : cmp G u t_top)
    by (apply H1; unfold I; simpl; auto).
  assert (Hc2 : cmp G t_top i)
    by (apply H2; unfold U; simpl; auto).
  eapply cmp_trans_top; eauto.
Qed.

(* ============ Base case B(t_int,u,i) ============ *)
Lemma cmp_trans_int : forall G u i,
  ordu u -> wft G u -> cmp G u t_int -> cmp G t_int i -> cmp G u i.
Proof.
  intros G u i Hu Wu H1 H2.
  remember (size_typ i) as n eqn:En.
  revert G u i Hu Wu H1 H2 En.
  induction n as [n IH] using lt_wf_ind.
  intros G u i Hu Wu H1 H2 En.
  destruct i as [| | | X Y | X Y | X Y | | p].
  - exact H1.
  - inversion H2; subst. apply C_top; auto.
  - inversion H2.
  - inversion H2.
  - inversion H2; subst.
    + eapply C_or_l; [eassumption|].
      eapply (IH (size_typ X)); [simpl; lia | exact Hu | exact Wu | exact H1 | assumption | reflexivity].
    + eapply C_or_r; [eassumption|].
      eapply (IH (size_typ Y)); [simpl; lia | exact Hu | exact Wu | exact H1 | assumption | reflexivity].
  - inversion H2.
  - inversion H2.
  - inversion H2.
Qed.

Lemma B_int : forall G u i,
  ordu u -> ordi i -> wft G t_int -> wft G u -> wft G i ->
  (forall j, In j (I t_int) -> cmp G u j) ->
  (forall w, In w (U t_int) -> cmp G w i) -> cmp G u i.
Proof.
  intros G u i Hu Hi Wc Wu Wi H1 H2.
  assert (Hc1 : cmp G u t_int) by (apply H1; unfold I; simpl; auto).
  assert (Hc2 : cmp G t_int i) by (apply H2; unfold U; simpl; auto).
  eapply cmp_trans_int; eauto.
Qed.

(* ============ Base case B(t_unit,u,i) ============ *)
Lemma cmp_trans_unit : forall G u i,
  ordu u -> wft G u -> cmp G u t_unit -> cmp G t_unit i -> cmp G u i.
Proof.
  intros G u i Hu Wu H1 H2.
  remember (size_typ i) as n eqn:En.
  revert G u i Hu Wu H1 H2 En.
  induction n as [n IH] using lt_wf_ind.
  intros G u i Hu Wu H1 H2 En.
  destruct i as [| | | X Y | X Y | X Y | | p].
  - inversion H2.
  - inversion H2; subst. apply C_top; auto.
  - inversion H2.
  - inversion H2.
  - inversion H2; subst.
    + eapply C_or_l; [eassumption|].
      eapply (IH (size_typ X)); [simpl; lia | exact Hu | exact Wu | exact H1 | assumption | reflexivity].
    + eapply C_or_r; [eassumption|].
      eapply (IH (size_typ Y)); [simpl; lia | exact Hu | exact Wu | exact H1 | assumption | reflexivity].
  - inversion H2.
  - exact H1.
  - inversion H2.
Qed.

Lemma B_unit : forall G u i,
  ordu u -> ordi i -> wft G t_unit -> wft G u -> wft G i ->
  (forall j, In j (I t_unit) -> cmp G u j) ->
  (forall w, In w (U t_unit) -> cmp G w i) -> cmp G u i.
Proof.
  intros G u i Hu Hi Wc Wu Wi H1 H2.
  assert (Hc1 : cmp G u t_unit) by (apply H1; unfold I; simpl; auto).
  assert (Hc2 : cmp G t_unit i) by (apply H2; unfold U; simpl; auto).
  eapply cmp_trans_unit; eauto.
Qed.

(* ============ Base case B(t_bot,u,i) ============ *)

(* If u (ordu) is below bot then it is below anything wft. *)
Lemma cmp_bot_elim : forall G u,
  ordu u -> cmp G u t_bot -> forall i, okenvp G -> wft G i -> cmp G u i.
Proof.
  intros G u Hu H.
  remember (size_typ u) as n eqn:En.
  revert G u Hu H En.
  induction n as [n IH] using lt_wf_ind.
  intros G u Hu H En i Ho Wi.
  destruct u as [| | | X Y | X Y | X Y | | p].
  - inversion H.
  - inversion H.
  - apply C_bot; auto.
  - inversion H.
  - inversion Hu.
  - inversion H; subst.
    + apply C_and_l with (u1 := X); [assumption|].
      destruct (ordu_inv_and X Y Hu) as [HX _].
      eapply (IH (size_typ X)); [simpl; lia | exact HX | assumption | reflexivity | exact Ho | exact Wi].
    + apply C_and_r with (u2 := Y); [assumption|].
      destruct (ordu_inv_and X Y Hu) as [_ HY].
      eapply (IH (size_typ Y)); [simpl; lia | exact HY | assumption | reflexivity | exact Ho | exact Wi].
  - inversion H.
  - inversion H.
Qed.

Lemma cmp_trans_bot : forall G u i,
  ordu u -> wft G u -> cmp G u t_bot -> cmp G t_bot i -> cmp G u i.
Proof.
  intros G u i Hu Wu H1 H2.
  remember (size_typ i) as n eqn:En.
  revert G u i Hu Wu H1 H2 En.
  induction n as [n IH] using lt_wf_ind.
  intros G u i Hu Wu H1 H2 En.
  destruct i as [| | | X Y | X Y | X Y | | p].
  - inversion H2; subst; eapply (cmp_bot_elim G u Hu H1); eauto; try constructor.
  - inversion H2; subst; eapply (cmp_bot_elim G u Hu H1); eauto; try constructor.
  - inversion H2; subst; eapply (cmp_bot_elim G u Hu H1); eauto; try constructor.
  - inversion H2; subst; eapply (cmp_bot_elim G u Hu H1); eauto; try constructor.
  - inversion H2; subst.
    + eapply (cmp_bot_elim G u Hu H1); eauto; try constructor.
    + eapply C_or_l; [eassumption|].
      eapply (IH (size_typ X)); [simpl; lia | exact Hu | exact Wu | exact H1 | assumption | reflexivity].
    + eapply C_or_r; [eassumption|].
      eapply (IH (size_typ Y)); [simpl; lia | exact Hu | exact Wu | exact H1 | assumption | reflexivity].
  - inversion H2; subst; eapply (cmp_bot_elim G u Hu H1); eauto; try constructor.
  - inversion H2; subst; eapply (cmp_bot_elim G u Hu H1); eauto; try constructor.
  - inversion H2; subst; eapply (cmp_bot_elim G u Hu H1); eauto; try constructor.
Qed.

Lemma B_bot : forall G u i,
  ordu u -> ordi i -> wft G t_bot -> wft G u -> wft G i ->
  (forall j, In j (I t_bot) -> cmp G u j) ->
  (forall w, In w (U t_bot) -> cmp G w i) -> cmp G u i.
Proof.
  intros G u i Hu Hi Wc Wu Wi H1 H2.
  assert (Hc1 : cmp G u t_bot) by (apply H1; unfold I; simpl; auto).
  assert (Hc2 : cmp G t_bot i) by (apply H2; unfold U; simpl; auto).
  eapply cmp_trans_bot; eauto.
Qed.

(* ============ Prim-sourced cmp regularity ============ *)

Lemma cmp_wft_target_prim : forall G a n, cmp G a (t_prim n) -> wft G (t_prim n).
Proof.
  intros G a n H.
  remember (size_envp G + size_typ a) as m eqn:Em.
  revert G a n H Em.
  induction m as [m IH] using lt_wf_ind.
  intros G a n H Em.
  destruct a as [| | | X Y | X Y | X Y | | p].
  - inversion H.
  - inversion H.
  - inversion H; subst. assumption.
  - inversion H.
  - inversion H.
  - inversion H; subst.
    + apply (IH (size_envp G + size_typ X) ltac:(simpl; lia) G X n ltac:(assumption) ltac:(reflexivity)).
    + apply (IH (size_envp G + size_typ Y) ltac:(simpl; lia) G Y n ltac:(assumption) ltac:(reflexivity)).
  - inversion H.
  - inversion H; subst.
    + assumption.
    + try clear H.
      match goal with Hp : cmp ?PG (t_prim ?q) (t_prim n) |- _ =>
        eapply wft_weaken_cons;
        apply (IH (size_envp PG + size_typ (t_prim q)) ltac:(simpl; lia) PG (t_prim q) n Hp ltac:(reflexivity))
      end.
    + try clear H.
      match goal with Hp : cmp ?PG (t_prim ?q) (t_prim n) |- _ =>
        eapply wft_weaken_cons;
        apply (IH (size_envp PG + size_typ (t_prim q)) ltac:(simpl; lia) PG (t_prim q) n Hp ltac:(reflexivity))
      end.
Qed.

Lemma cmp_wft_src_prim : forall G u n, cmp G u (t_prim n) -> wft G u.
Proof.
  intros G u n H.
  remember (size_envp G + size_typ u) as m eqn:Em.
  revert G u n H Em.
  induction m as [m IH] using lt_wf_ind.
  intros G u n H Em.
  destruct u as [| | | X Y | X Y | X Y | | p].
  - inversion H.
  - inversion H.
  - inversion H; subst. constructor.
  - inversion H.
  - inversion H.
  - inversion H; subst.
    + apply wft_and.
      * apply (IH (size_envp G + size_typ X) ltac:(simpl; lia) G X n ltac:(assumption) ltac:(reflexivity)).
      * assumption.
    + apply wft_and.
      * assumption.
      * apply (IH (size_envp G + size_typ Y) ltac:(simpl; lia) G Y n ltac:(assumption) ltac:(reflexivity)).
  - inversion H.
  - inversion H; subst.
    + assumption.
    + try clear H.
      match goal with Hp : cmp ?PG (t_prim ?q) (t_prim n) |- _ =>
        eapply wft_weaken_cons;
        apply (IH (size_envp PG + size_typ (t_prim q)) ltac:(simpl; lia) PG (t_prim q) n Hp ltac:(reflexivity))
      end.
    + try clear H.
      match goal with Hp : cmp ?PG (t_prim ?q) (t_prim ?n') |- _ =>
        eapply wft_prim with (A := t_prim q); simpl; auto
      end.
Qed.

Lemma cmp_wft_tgt_of_prim : forall G n i, cmp G (t_prim n) i -> wft G i.
Proof.
  intros G n i H.
  remember (size_envp G + size_typ i) as m eqn:Em.
  revert G n i H Em.
  induction m as [m IH] using lt_wf_ind.
  intros G n i H Em.
  destruct i as [| | | X Y | X Y | X Y | | p].
  - inversion H.
  - inversion H; subst. constructor.
  - inversion H.
  - inversion H.
  - inversion H; subst.
    + eapply wft_or; [|assumption].
      apply (IH (size_envp G + size_typ X) ltac:(simpl; lia) G n X ltac:(assumption) ltac:(reflexivity)).
    + eapply wft_or; [assumption|].
      apply (IH (size_envp G + size_typ Y) ltac:(simpl; lia) G n Y ltac:(assumption) ltac:(reflexivity)).
  - inversion H.
  - inversion H.
  - inversion H; subst.
    + assumption.
    + try clear H.
      match goal with Hp : cmp ?PG (t_prim ?n1) (t_prim p) |- _ =>
        eapply wft_weaken_cons;
        apply (IH (size_envp PG + size_typ (t_prim p)) ltac:(simpl; lia) PG n1 (t_prim p) Hp ltac:(reflexivity))
      end.
    + try clear H.
      match goal with Hp : cmp ?PG (t_prim ?j) (t_prim p) |- _ =>
        eapply wft_weaken_cons;
        apply (IH (size_envp PG + size_typ (t_prim p)) ltac:(simpl; lia) PG j (t_prim p) Hp ltac:(reflexivity))
      end.
Qed.

(* Mixed prim-environment case: impossible. *)
Lemma prim_mixed_false : forall PG j p n1,
  okenvp ((n1, t_prim j) :: PG) ->
  cmp PG (t_prim p) (t_prim n1) -> False.
Proof.
  intros PG j p n1 Hok Hc.
  destruct (wft_prim_binds PG n1 (cmp_wft_target_prim PG (t_prim p) n1 Hc)) as [X Hb].
  inversion Hok; subst.
  eapply binds_dom_contradiction; eauto.
Qed.

(* The bot-source branch of cmp_trans_prim. *)
Lemma cmp_trans_prim_bot : forall G p i,
  cmp G t_bot (t_prim p) -> cmp G (t_prim p) i -> cmp G t_bot i.
Proof.
  intros G p i H1 H2.
  inversion H1; subst.
  apply C_bot; [assumption|].
  apply cmp_wft_tgt_of_prim with (n := p). exact H2.
Qed.


Lemma cmp_prim_cons_inv : forall h A PG q p,
  cmp ((h,A)::PG) (t_prim q) (t_prim p) ->
  (q = p) \/
  (h <> q /\ cmp PG (t_prim q) (t_prim p)) \/
  (exists j, h = q /\ A = t_prim j /\ cmp PG (t_prim j) (t_prim p)).
Proof.
  intros h A PG q p H. inversion H; subst; eauto.
  right; right; eexists; auto.
Qed.

Lemma cmp_prim_trans : forall G q p n2,
  okenvp G ->
  cmp G (t_prim q) (t_prim p) ->
  cmp G (t_prim p) (t_prim n2) ->
  cmp G (t_prim q) (t_prim n2).
Proof.
  intros G. remember (size_envp G) as n eqn:EG. revert G EG.
  induction n as [n IH] using lt_wf_ind.
  intros G EG q p n2 Ho H1 H2.
  destruct G as [|[h A] PG].
  - inversion H1; subst; exact H2.
  - assert (Hok : okenvp PG) by (eapply okenv_tail; exact Ho).
    destruct (cmp_prim_cons_inv h A PG q p H1) as [Hqp | [[Hhq H1t] | [j [Hhq [HA H1t]]]]].
    + subst q. exact H2.
    + destruct (cmp_prim_cons_inv h A PG p n2 H2) as [Hpn | [[Hhp H2t] | [j' [Hhp [HA' H2t]]]]].
      * subst n2. exact H1.
      * eapply C_prim_neq.
        -- exact Ho.
        -- exact Hhq.
        -- exact (IH (size_envp PG) ltac:(simpl in EG; lia) PG eq_refl q p n2 Hok H1t H2t).
      * exfalso. subst h. subst A. eapply (prim_mixed_false PG j' q p); [exact Ho | exact H1t].
    + destruct (cmp_prim_cons_inv h A PG p n2 H2) as [Hpn | [[Hhp H2t] | [j' [Hhp [HA' H2t]]]]].
      * subst n2. subst h. subst A. eapply C_prim_eq; [exact Ho | exact H1t].
      * subst h. subst A. eapply C_prim_eq.
        -- exact Ho.
        -- exact (IH (size_envp PG) ltac:(simpl in EG; lia) PG eq_refl j p n2 Hok H1t H2t).
      * subst h. subst A. subst p.
        injection HA' as Hjj. subst j'.
        eapply C_prim_eq; [exact Ho | exact H2t].
Qed.


Lemma cmp_trans_prim : forall G u p i,
  ordu u -> wft G u -> cmp G u (t_prim p) -> cmp G (t_prim p) i -> cmp G u i.
Proof.
  intros G u p i Hu Wu H1 H2.
  remember (size_envp G + size_typ u + size_typ i) as m eqn:Em.
  revert G u p i Hu Wu H1 H2 Em.
  induction m as [m IH] using lt_wf_ind.
  intros G u p i Hu Wu H1 H2 Em.
  destruct i as [| | | X Y | X Y | X Y | | n2].
  - inversion H2.
  - inversion H2; subst. apply C_top; auto.
  - inversion H2.
  - inversion H2.
  - inversion H2; subst.
    + eapply C_or_l; [eassumption|].
      eapply (IH (size_envp G + size_typ u + size_typ X));
        [simpl; lia | exact Hu | exact Wu | exact H1 | assumption | reflexivity].
    + eapply C_or_r; [eassumption|].
      eapply (IH (size_envp G + size_typ u + size_typ Y));
        [simpl; lia | exact Hu | exact Wu | exact H1 | assumption | reflexivity].
  - inversion H2.
  - inversion H2.
  - destruct u as [| | | X Y | X Y | X Y | | q].
    + inversion H1.
    + inversion H1.
    + apply (cmp_trans_prim_bot G p (t_prim n2)); assumption.
    + inversion H1.
    + inversion H1.
    + inversion H1; subst.
      * eapply C_and_l; [apply (proj2 (wft_inv_and G X Y Wu))|].
        match goal with Hp : cmp G X (t_prim p) |- _ =>
          eapply (IH (size_envp G + size_typ X + size_typ (t_prim n2)));
          [simpl; lia | exact (proj1 (ordu_inv_and X Y Hu)) | exact (proj1 (wft_inv_and G X Y Wu)) | exact Hp | exact H2 | reflexivity]
        end.
      * eapply C_and_r; [apply (proj1 (wft_inv_and G X Y Wu))|].
        match goal with Hp : cmp G Y (t_prim p) |- _ =>
          eapply (IH (size_envp G + size_typ Y + size_typ (t_prim n2)));
          [simpl; lia | exact (proj2 (ordu_inv_and X Y Hu)) | exact (proj2 (wft_inv_and G X Y Wu)) | exact Hp | exact H2 | reflexivity]
        end.
    + inversion H1.
    + (* u = prim q *)
      assert (Ho : okenvp G) by (inversion H1; subst; assumption).
      exact (cmp_prim_trans G q p n2 Ho H1 H2).
Qed.

Lemma B_prim : forall G p u i,
  ordu u -> ordi i -> wft G (t_prim p) -> wft G u -> wft G i ->
  (forall j, In j (I (t_prim p)) -> cmp G u j) ->
  (forall w, In w (U (t_prim p)) -> cmp G w i) -> cmp G u i.
Proof.
  intros G p u i Hu Hi Wc Wu Wi H1 H2.
  assert (Hc1 : cmp G u (t_prim p)) by (apply H1; unfold I; simpl; auto).
  assert (Hc2 : cmp G (t_prim p) i) by (apply H2; unfold U; simpl; auto).
  exact (cmp_trans_prim G u p i Hu Wu Hc1 Hc2).
Qed.

Lemma cmp_trans_arrow : forall G c1 c2,
  wft G c1 -> wft G c2 ->
  (forall u i, ordu u -> ordi i -> wft G c1 -> wft G u -> wft G i ->
     (forall j, In j (I c1) -> cmp G u j) ->
     (forall w, In w (U c1) -> cmp G w i) -> cmp G u i) ->
  (forall u i, ordu u -> ordi i -> wft G c2 -> wft G u -> wft G i ->
     (forall j, In j (I c2) -> cmp G u j) ->
     (forall w, In w (U c2) -> cmp G w i) -> cmp G u i) ->
  forall u i, ordu u -> wft G u -> wft G i ->
  cmp G u (t_arrow c1 c2) -> cmp G (t_arrow c1 c2) i -> cmp G u i.
Proof.
  intros G c1 c2 Wc1 Wc2 Bc1 Bc2 u i Hu Wu Wi H1 H2.
  remember (size_typ i + size_typ u) as m eqn:Em.
  revert G c1 c2 Wc1 Wc2 Bc1 Bc2 u i Hu Wu Wi H1 H2 Em.
  induction m as [m IH] using lt_wf_ind.
  intros G c1 c2 Wc1 Wc2 Bc1 Bc2 u i Hu Wu Wi H1 H2 Em.
  destruct i as [| | | b1 b2 | X Y | X Y | | p].
  - inversion H2.
  - inversion H2; subst. apply C_top; auto.
  - inversion H2.
  - (* target arrow b1 b2 *)
    assert (WiA := Wi). apply wft_inv_arrow in WiA as [Wb1 Wb2].
    inversion H2; subst; try discriminate.
    match goal with Hb : forall u0, In u0 (U b1) -> forall j, In j (I c1) -> cmp G u0 j |- _ => pose proof Hb as Hb1 end.
    match goal with Hb : forall u0, In u0 (U c2) -> forall j, In j (I b2) -> cmp G u0 j |- _ => pose proof Hb as Hb2 end.
    destruct u as [| | | a1 a2 | U1 U2 | U1 U2 | | q].
    + inversion H1.
    + inversion H1.
    + inversion H1; subst; apply C_bot; auto.
    + (* source arrow a1 a2 *)
      assert (WuA := Wu). apply wft_inv_arrow in WuA as [Wa1 Wa2].
      inversion H1; subst; try discriminate.
      match goal with Ha : forall u0, In u0 (U c1) -> forall j, In j (I a1) -> cmp G u0 j |- _ => pose proof Ha as Ha1 end.
      match goal with Ha : forall u0, In u0 (U a2) -> forall j, In j (I c2) -> cmp G u0 j |- _ => pose proof Ha as Ha2 end.
      apply C_arrow.
      * intros u0 Hu0 i0 Hi0.
        apply (Bc1 u0 i0 (U_ordu b1 u0 Hu0) (I_ordi a1 i0 Hi0) Wc1
                (U_wft G b1 u0 Wb1 Hu0) (I_wft G a1 i0 Wa1 Hi0)).
        -- intros j Hj. apply (Hb1 u0 Hu0 j Hj).
        -- intros w Hw. apply (Ha1 w Hw i0 Hi0).
      * intros u0 Hu0 i0 Hi0.
        apply (Bc2 u0 i0 (U_ordu a2 u0 Hu0) (I_ordi b2 i0 Hi0) Wc2
                (U_wft G a2 u0 Wa2 Hu0) (I_wft G b2 i0 Wb2 Hi0)).
        -- intros j Hj. apply (Ha2 u0 Hu0 j Hj).
        -- intros w Hw. apply (Hb2 w Hw i0 Hi0).
    + inversion H1.
    + (* source and U1 U2 *) inversion H1; subst.
      * eapply C_and_l; [apply (proj2 (wft_inv_and G U1 U2 Wu))|].
        eapply (IH (size_typ (t_arrow b1 b2) + size_typ U1));
          [simpl; lia | exact Wc1 | exact Wc2 | exact Bc1 | exact Bc2 |
           exact (proj1 (ordu_inv_and U1 U2 Hu)) | exact (proj1 (wft_inv_and G U1 U2 Wu)) | exact Wi | assumption | exact H2 | reflexivity].
      * eapply C_and_r; [apply (proj1 (wft_inv_and G U1 U2 Wu))|].
        eapply (IH (size_typ (t_arrow b1 b2) + size_typ U2));
          [simpl; lia | exact Wc1 | exact Wc2 | exact Bc1 | exact Bc2 |
           exact (proj2 (ordu_inv_and U1 U2 Hu)) | exact (proj2 (wft_inv_and G U1 U2 Wu)) | exact Wi | assumption | exact H2 | reflexivity].
    + inversion H1.
    + inversion H1.
  - (* target union X Y *) inversion H2; subst.
    + eapply C_or_l; [eassumption|].
      destruct (wft_inv_or G X Y Wi) as [WX _].
      eapply (IH (size_typ X + size_typ u));
        [simpl; lia | exact Wc1 | exact Wc2 | exact Bc1 | exact Bc2 | exact Hu | exact Wu | exact WX | exact H1 | assumption | reflexivity].
    + eapply C_or_r; [eassumption|].
      destruct (wft_inv_or G X Y Wi) as [_ WY].
      eapply (IH (size_typ Y + size_typ u));
        [simpl; lia | exact Wc1 | exact Wc2 | exact Bc1 | exact Bc2 | exact Hu | exact Wu | exact WY | exact H1 | assumption | reflexivity].
  - inversion H2.
  - inversion H2.
  - inversion H2.
Qed.

Lemma B_arrow : forall G c1 c2 u i,
  (forall u0 i0, ordu u0 -> ordi i0 -> wft G c1 -> wft G u0 -> wft G i0 ->
     (forall j, In j (I c1) -> cmp G u0 j) ->
     (forall w, In w (U c1) -> cmp G w i0) -> cmp G u0 i0) ->
  (forall u0 i0, ordu u0 -> ordi i0 -> wft G c2 -> wft G u0 -> wft G i0 ->
     (forall j, In j (I c2) -> cmp G u0 j) ->
     (forall w, In w (U c2) -> cmp G w i0) -> cmp G u0 i0) ->
  ordu u -> ordi i -> ordi (t_arrow c1 c2) ->
  wft G (t_arrow c1 c2) -> wft G u -> wft G i ->
  (forall j, In j (I (t_arrow c1 c2)) -> cmp G u j) ->
  (forall w, In w (U (t_arrow c1 c2)) -> cmp G w i) -> cmp G u i.
Proof.
  intros G c1 c2 u i Bc1 Bc2 Hu Hi Hordi Wc Wu Wi H1 H2.
  destruct (wft_inv_arrow G c1 c2 Wc) as [Wc1 Wc2].
  assert (Hc1 : cmp G u (t_arrow c1 c2))
    by (apply H1; rewrite (I_ordi_singleton (t_arrow c1 c2) Hordi); simpl; auto).
  assert (Hc2 : cmp G (t_arrow c1 c2) i)
    by (apply H2; rewrite (U_ordu_singleton (t_arrow c1 c2) (OU_arrow c1 c2)); simpl; auto).
  exact (cmp_trans_arrow G c1 c2 Wc1 Wc2 Bc1 Bc2 u i Hu Wu Wi Hc1 Hc2).
Qed.

Lemma In_U_ordu : forall A w, ordu A -> In w (U A) -> w = A.
Proof.
  intros A w Ho Hin. rewrite (U_ordu_singleton A Ho) in Hin.
  simpl in Hin. destruct Hin as [-> | Hnil]; [reflexivity | destruct Hnil].
Qed.

Lemma In_I_ordi : forall A w, ordi A -> In w (I A) -> w = A.
Proof.
  intros A w Ho Hin. rewrite (I_ordi_singleton A Ho) in Hin.
  simpl in Hin. destruct Hin as [-> | Hnil]; [reflexivity | destruct Hnil].
Qed.

Lemma B_and : forall G X Y u i,
  ordu X -> ordu Y ->
  (forall u0 i0, ordu u0 -> ordi i0 -> wft G X -> wft G u0 -> wft G i0 ->
     (forall j, In j (I X) -> cmp G u0 j) ->
     (forall w, In w (U X) -> cmp G w i0) -> cmp G u0 i0) ->
  (forall u0 i0, ordu u0 -> ordi i0 -> wft G Y -> wft G u0 -> wft G i0 ->
     (forall j, In j (I Y) -> cmp G u0 j) ->
     (forall w, In w (U Y) -> cmp G w i0) -> cmp G u0 i0) ->
  ordu u -> ordi i -> wft G (t_and X Y) -> wft G u -> wft G i ->
  (forall j, In j (I (t_and X Y)) -> cmp G u j) ->
  (forall w, In w (U (t_and X Y)) -> cmp G w i) -> cmp G u i.
Proof.
  intros G X Y u i HX HY BX BY Hu Hi Wc Wu Wi H1 H2.
  assert (Hstep : I (t_and X Y) = I X ++ I Y)
    by (apply I_step; apply spli_opt_complete; apply SpI_and).
  remember (size_typ i) as n eqn:En.
  revert G X Y u i HX HY BX BY Hu Hi Wc Wu Wi H1 H2 Hstep En.
  induction n as [n IH] using lt_wf_ind.
  intros G X Y u i HX HY BX BY Hu Hi Wc Wu Wi H1 H2 Hstep En.
  destruct (wft_inv_and G X Y Wc) as [WX WY].
  assert (OC : ordu (t_and X Y)) by (apply OU_and; assumption).
  assert (H2c : cmp G (t_and X Y) i)
    by (apply H2; rewrite (U_ordu_singleton (t_and X Y) OC); simpl; auto).
  inversion H2c; subst; try discriminate.
  - (* C_top *) apply C_top; auto.
  - (* C_or_l *)
    assert (H2' : forall w, In w (U (t_and X Y)) -> cmp G w i1).
    { intros w Hw. rewrite (In_U_ordu (t_and X Y) w OC Hw). assumption. }
    eapply C_or_l; [exact (proj2 (wft_inv_or G i1 i2 Wi))|].
    eapply (IH (size_typ i1));
      [simpl; lia | exact HX | exact HY | exact BX | exact BY | exact Hu | exact (proj1 (ordi_inv_or i1 i2 Hi)) | exact Wc | exact Wu |
       exact (proj1 (wft_inv_or G i1 i2 Wi)) | exact H1 | exact H2' | exact Hstep | reflexivity].
  - (* C_or_r *)
    assert (H2' : forall w, In w (U (t_and X Y)) -> cmp G w i2).
    { intros w Hw. rewrite (In_U_ordu (t_and X Y) w OC Hw). assumption. }
    eapply C_or_r; [exact (proj1 (wft_inv_or G i1 i2 Wi))|].
    eapply (IH (size_typ i2));
      [simpl; lia | exact HX | exact HY | exact BX | exact BY | exact Hu | exact (proj2 (ordi_inv_or i1 i2 Hi)) | exact Wc | exact Wu |
       exact (proj2 (wft_inv_or G i1 i2 Wi)) | exact H1 | exact H2' | exact Hstep | reflexivity].
  - (* C_and_l *)
    match goal with Hp : cmp G X i |- _ => apply (BX u i Hu Hi WX Wu Wi) end.
    + intros j Hj. apply H1. rewrite Hstep. apply in_or_app. left. exact Hj.
    + intros w Hw. rewrite (In_U_ordu X w HX Hw).
      match goal with Hp : cmp G X i |- _ => exact Hp end.
  - (* C_and_r *)
    match goal with Hp : cmp G Y i |- _ => apply (BY u i Hu Hi WY Wu Wi) end.
    + intros j Hj. apply H1. rewrite Hstep. apply in_or_app. right. exact Hj.
    + intros w Hw. rewrite (In_U_ordu Y w HY Hw).
      match goal with Hp : cmp G Y i |- _ => exact Hp end.
Qed.


Lemma I_none : forall A, spli_opt A = None -> I A = [A].
Proof.
  intros A H. unfold I. remember (size_typ A) as n eqn:E.
  destruct n as [|k].
  - pose (size_pos A); lia.
  - simpl. rewrite H. reflexivity.
Qed.

Lemma I_nonempty : forall A, exists x, In x (I A).
Proof.
  intros A. remember (size_typ A) as n eqn:E. revert A E.
  induction n as [n IH] using lt_wf_ind.
  intros A E. unfold I. destruct (size_typ A) as [|k] eqn:Es.
  - pose (size_pos A); lia.
  - simpl. destruct (spli_opt A) as [[B C]|] eqn:Esp.
    + assert (Hsp : spli A B C) by (apply spli_opt_sound; exact Esp).
      assert (HB : size_typ B < size_typ A) by (apply spli_size in Hsp; tauto).
      assert (HBle : size_typ B <= k).
      { rewrite Es in HB. simpl in HB. lia. }
      destruct (IH (size_typ B) ltac:(lia) B eq_refl) as [x Hx].
      exists x. apply in_or_app. left.
      rewrite (If_stable k B HBle). exact Hx.
    + exists A. simpl. left. reflexivity.
Qed.

Lemma I_arrow_surj : forall X Y C,
  In C (I Y) -> exists Z, In (t_arrow Z C) (I (t_arrow X Y)).
Proof.
  intros X Y. remember (size_typ (t_arrow X Y)) as n eqn:En.
  revert X Y En. induction n as [n IH] using lt_wf_ind.
  intros X Y En C HC.
  destruct (spli_opt Y) as [[C1 C2]|] eqn:EY.
  - assert (HspY : spli Y C1 C2) by (apply spli_opt_sound; exact EY).
    assert (HIY : I Y = I C1 ++ I C2) by (apply I_step; exact EY).
    assert (Esplit : spli_opt (t_arrow X Y) = Some (t_arrow X C1, t_arrow X C2)).
    { simpl. rewrite EY. reflexivity. }
    assert (HIA : I (t_arrow X Y) = I (t_arrow X C1) ++ I (t_arrow X C2))
      by (apply I_step; exact Esplit).
    rewrite HIY in HC. apply in_app_or in HC. destruct HC as [HC1|HC2].
    + assert (Hsize : size_typ (t_arrow X C1) < n).
      { subst n. apply spli_size in HspY. simpl. lia. }
      destruct (IH (size_typ (t_arrow X C1)) Hsize X C1 eq_refl C HC1) as [Z HZ].
      exists Z. rewrite HIA. apply in_or_app. left. exact HZ.
    + assert (Hsize : size_typ (t_arrow X C2) < n).
      { subst n. apply spli_size in HspY. simpl. lia. }
      destruct (IH (size_typ (t_arrow X C2)) Hsize X C2 eq_refl C HC2) as [Z HZ].
      exists Z. rewrite HIA. apply in_or_app. right. exact HZ.
  - assert (Hor : ordi Y).
    { destruct (ordi_or_spli Y) as [H| [P [Q Hs]]]; auto.
      exfalso. apply spli_opt_complete in Hs. rewrite EY in Hs. discriminate. }
    rewrite (I_ordi_singleton Y Hor) in HC. simpl in HC. destruct HC as [Heq|Hnil].
    + subst C.
      destruct (spli_opt (t_arrow X Y)) as [[P Q]|] eqn:Earr.
      * assert (HspArr : spli (t_arrow X Y) P Q) by (apply spli_opt_sound; exact Earr).
        destruct (spli_inv_arrow X Y P Q HspArr) as
          [[C [D [HP [HQ HspliY]]]] | [P1 [Q1 [HorY [HP [HQ Hsplu]]]]]].
        -- exfalso. apply spli_opt_complete in HspliY. rewrite EY in HspliY. discriminate.
        -- subst P Q.
           assert (HInY : In Y (I Y)).
           { rewrite (I_ordi_singleton Y Hor). simpl. left. reflexivity. }
           assert (HsizeP : size_typ (t_arrow P1 Y) < n).
           { subst n. apply splu_size in Hsplu. simpl. lia. }
           destruct (IH (size_typ (t_arrow P1 Y)) HsizeP P1 Y eq_refl Y HInY) as [Z HZ].
           exists Z. apply I_step in Earr. rewrite Earr. apply in_or_app. left. exact HZ.
      * assert (HIA : I (t_arrow X Y) = [t_arrow X Y]) by (apply I_none; exact Earr).
        exists X. rewrite HIA. simpl. left. reflexivity.
    + destruct Hnil.
Qed.

Lemma I_arrow_dom_cover : forall X Y w,
  In w (U X) ->
  exists Z C, In (t_arrow Z C) (I (t_arrow X Y)) /\ In w (U Z) /\ In C (I Y).
Proof.
  intros X Y. remember (size_typ (t_arrow X Y)) as n eqn:En.
  revert X Y En. induction n as [n IH] using lt_wf_ind.
  intros X Y En w Hw.
  destruct (spli_opt Y) as [[C1 C2]|] eqn:EY.
  - assert (HspY : spli Y C1 C2) by (apply spli_opt_sound; exact EY).
    assert (HIY : I Y = I C1 ++ I C2) by (apply I_step; exact EY).
    assert (Esplit : spli_opt (t_arrow X Y) = Some (t_arrow X C1, t_arrow X C2)).
    { simpl. rewrite EY. reflexivity. }
    assert (HIA : I (t_arrow X Y) = I (t_arrow X C1) ++ I (t_arrow X C2))
      by (apply I_step; exact Esplit).
    destruct (spli_opt C1) as [[D1 D2]|] eqn:EC1.
    + (* recurse into C1 regardless of its spli; just use IH at (X,C1) *)
      assert (Hsize : size_typ (t_arrow X C1) < n).
      { subst n. apply spli_size in HspY. simpl. lia. }
      destruct (IH (size_typ (t_arrow X C1)) Hsize X C1 eq_refl w Hw) as
        [Z [C [Hj [HwZ HC]]]].
      exists Z, C. split; [|split].
      * rewrite HIA. apply in_or_app. left. exact Hj.
      * exact HwZ.
      * rewrite HIY. apply in_or_app. left. exact HC.
    + assert (Hsize : size_typ (t_arrow X C1) < n).
      { subst n. apply spli_size in HspY. simpl. lia. }
      destruct (IH (size_typ (t_arrow X C1)) Hsize X C1 eq_refl w Hw) as
        [Z [C [Hj [HwZ HC]]]].
      exists Z, C. split; [|split].
      * rewrite HIA. apply in_or_app. left. exact Hj.
      * exact HwZ.
      * rewrite HIY. apply in_or_app. left. exact HC.
  - assert (Hor : ordi Y).
    { destruct (ordi_or_spli Y) as [H| [P [Q Hs]]]; auto.
      exfalso. apply spli_opt_complete in Hs. rewrite EY in Hs. discriminate. }
    destruct (spli_opt (t_arrow X Y)) as [[P Q]|] eqn:Earr.
    + assert (HspArr : spli (t_arrow X Y) P Q) by (apply spli_opt_sound; exact Earr).
      destruct (spli_inv_arrow X Y P Q HspArr) as
        [[C [D [HP [HQ HspliY]]]] | [P1 [Q1 [HorY [HP [HQ Hsplu]]]]]].
      * exfalso. apply spli_opt_complete in HspliY. rewrite EY in HspliY. discriminate.
      * subst P Q.
        assert (Hspopt : splu_opt X = Some (P1,Q1)) by (apply splu_opt_complete; exact Hsplu).
        assert (HUX : U X = U P1 ++ U Q1) by (apply U_step; exact Hspopt).
        rewrite HUX in Hw. apply in_app_or in Hw. destruct Hw as [Hw1|Hw2].
        -- assert (Hsize : size_typ (t_arrow P1 Y) < n).
           { subst n. apply splu_size in Hsplu. simpl. lia. }
           destruct (IH (size_typ (t_arrow P1 Y)) Hsize P1 Y eq_refl w Hw1) as
             [Z [C [Hj [HwZ HC]]]].
           exists Z, C. split; [|split].
           ++ apply I_step in Earr. rewrite Earr. apply in_or_app. left. exact Hj.
           ++ exact HwZ.
           ++ exact HC.
        -- assert (Hsize : size_typ (t_arrow Q1 Y) < n).
           { subst n. apply splu_size in Hsplu. simpl. lia. }
           destruct (IH (size_typ (t_arrow Q1 Y)) Hsize Q1 Y eq_refl w Hw2) as
             [Z [C [Hj [HwZ HC]]]].
           exists Z, C. split; [|split].
           ++ apply I_step in Earr. rewrite Earr. apply in_or_app. right. exact Hj.
           ++ exact HwZ.
           ++ exact HC.
    + assert (HIA : I (t_arrow X Y) = [t_arrow X Y]) by (apply I_none; exact Earr).
      assert (HInY : In Y (I Y)) by (rewrite (I_ordi_singleton Y Hor); simpl; left; reflexivity).
      exists X, Y. split; [|split].
      * rewrite HIA. simpl. left. reflexivity.
      * exact Hw.
      * exact HInY.
Qed.


Lemma In_singleton_typ : forall (x y:typ), In x [y] -> x = y.
Proof. intros x y H. simpl in H. destruct H as [H|H]; [subst y; reflexivity | destruct H]. Qed.

Lemma U_and_pair_aux : forall n A C u v,
  size_typ A + size_typ C <= n ->
  In u (U A) -> In v (U C) -> In (t_and u v) (U (t_and A C)).
Proof.
  induction n as [|n IH].
  - intros A C u v Hn. pose proof (size_pos A). pose proof (size_pos C). lia.
  - intros A C u v Hn Hu Hv.
    destruct (splu_opt A) as [[A1 A2]|] eqn:EA.
    + assert (Hspl : splu A A1 A2) by (apply splu_opt_sound; auto).
      assert (EUA : U A = U A1 ++ U A2) by (apply U_step; auto).
      rewrite EUA in Hu. apply in_app_or in Hu. destruct Hu as [Hu|Hu].
      * assert (EAC : splu_opt (t_and A C) = Some (t_and A1 C, t_and A2 C)).
        { simpl. rewrite EA. reflexivity. }
        assert (EUAC : U (t_and A C) = U (t_and A1 C) ++ U (t_and A2 C))
          by (apply U_step; auto).
        rewrite EUAC. apply in_or_app. left.
        apply (IH A1 C u v).
        { apply splu_size in Hspl. destruct Hspl. lia. }
        { exact Hu. }
        { exact Hv. }
      * assert (EAC : splu_opt (t_and A C) = Some (t_and A1 C, t_and A2 C)).
        { simpl. rewrite EA. reflexivity. }
        assert (EUAC : U (t_and A C) = U (t_and A1 C) ++ U (t_and A2 C))
          by (apply U_step; auto).
        rewrite EUAC. apply in_or_app. right.
        apply (IH A2 C u v).
        { apply splu_size in Hspl. destruct Hspl. lia. }
        { exact Hu. }
        { exact Hv. }
    + assert (OA : ordu A).
      { destruct (ordu_or_splu A) as [H|H]; auto.
        destruct H as [B [C0 HB]]. apply splu_opt_complete in HB. rewrite HB in EA. discriminate. }
      assert (EUA : U A = [A]) by (apply U_ordu_singleton; auto).
      rewrite EUA in Hu. assert (Heq : u = A) by (apply In_singleton_typ; exact Hu). subst u. rewrite <- EUA in Hu.
      destruct (splu_opt C) as [[C1 C2]|] eqn:EC.
      * assert (Hspl : splu C C1 C2) by (apply splu_opt_sound; auto).
        assert (EUC : U C = U C1 ++ U C2) by (apply U_step; auto).
        rewrite EUC in Hv. apply in_app_or in Hv. destruct Hv as [Hv|Hv].
        -- assert (EAC : splu_opt (t_and A C) = Some (t_and A C1, t_and A C2)).
           { simpl. rewrite EA. destruct (ordu_dec A) as [HdA|HdA]; [| exfalso; apply HdA; assumption].
             rewrite EC. reflexivity. }
           assert (EUAC : U (t_and A C) = U (t_and A C1) ++ U (t_and A C2))
             by (apply U_step; auto).
           rewrite EUAC. apply in_or_app. left.
           apply (IH A C1 A v).
           { apply splu_size in Hspl. destruct Hspl. lia. }
           { exact Hu. }
           { exact Hv. }
        -- assert (EAC : splu_opt (t_and A C) = Some (t_and A C1, t_and A C2)).
           { simpl. rewrite EA. destruct (ordu_dec A) as [HdA|HdA]; [| exfalso; apply HdA; assumption].
             rewrite EC. reflexivity. }
           assert (EUAC : U (t_and A C) = U (t_and A C1) ++ U (t_and A C2))
             by (apply U_step; auto).
           rewrite EUAC. apply in_or_app. right.
           apply (IH A C2 A v).
           { apply splu_size in Hspl. destruct Hspl. lia. }
           { exact Hu. }
           { exact Hv. }
      * assert (OC : ordu C).
        { destruct (ordu_or_splu C) as [H|H]; auto.
          destruct H as [B [C0 HB]]. apply splu_opt_complete in HB. rewrite HB in EC. discriminate. }
        assert (EUC : U C = [C]) by (apply U_ordu_singleton; auto).
        rewrite EUC in Hv. apply In_singleton_typ in Hv. subst v.
        assert (EUAC : U (t_and A C) = [t_and A C]).
        { apply U_ordu_singleton. apply OU_and; auto. }
        rewrite EUAC. simpl. auto.
Qed.

Lemma U_and_pair : forall A C u v,
  In u (U A) -> In v (U C) -> In (t_and u v) (U (t_and A C)).
Proof. intros. eapply U_and_pair_aux; eauto. Qed.

Lemma I_union_pair_aux : forall n A C d e,
  size_typ A + size_typ C <= n ->
  In d (I A) -> In e (I C) -> In (t_union d e) (I (t_union A C)).
Proof.
  induction n as [|n IH].
  - intros A C d e Hn. pose proof (size_pos A). pose proof (size_pos C). lia.
  - intros A C d e Hn Hd He.
    destruct (spli_opt A) as [[A1 A2]|] eqn:EA.
    + assert (Hsp : spli A A1 A2) by (apply spli_opt_sound; auto).
      assert (EIA : I A = I A1 ++ I A2) by (apply I_step; auto).
      rewrite EIA in Hd. apply in_app_or in Hd. destruct Hd as [Hd|Hd].
      * assert (EAC : spli_opt (t_union A C) = Some (t_union A1 C, t_union A2 C)).
        { simpl. rewrite EA. reflexivity. }
        assert (EIAC : I (t_union A C) = I (t_union A1 C) ++ I (t_union A2 C))
          by (apply I_step; auto).
        rewrite EIAC. apply in_or_app. left.
        apply (IH A1 C d e).
        { apply spli_size in Hsp. destruct Hsp. lia. }
        { exact Hd. }
        { exact He. }
      * assert (EAC : spli_opt (t_union A C) = Some (t_union A1 C, t_union A2 C)).
        { simpl. rewrite EA. reflexivity. }
        assert (EIAC : I (t_union A C) = I (t_union A1 C) ++ I (t_union A2 C))
          by (apply I_step; auto).
        rewrite EIAC. apply in_or_app. right.
        apply (IH A2 C d e).
        { apply spli_size in Hsp. destruct Hsp. lia. }
        { exact Hd. }
        { exact He. }
    + assert (OA : ordi A).
      { destruct (ordi_or_spli A) as [H|H]; auto.
        destruct H as [B [C0 HB]]. apply spli_opt_complete in HB. rewrite HB in EA. discriminate. }
      destruct (spli_opt C) as [[C1 C2]|] eqn:EC.
      * assert (Hsp : spli C C1 C2) by (apply spli_opt_sound; auto).
        assert (EIC : I C = I C1 ++ I C2) by (apply I_step; auto).
        rewrite EIC in He. apply in_app_or in He. destruct He as [He|He].
        -- assert (EAC : spli_opt (t_union A C) = Some (t_union A C1, t_union A C2)).
           { simpl. rewrite EA. destruct (ordi_dec A) as [HdA|HdA]; [| exfalso; apply HdA; assumption].
             rewrite EC. reflexivity. }
           assert (EIAC : I (t_union A C) = I (t_union A C1) ++ I (t_union A C2))
             by (apply I_step; auto).
           rewrite EIAC. apply in_or_app. left.
           apply (IH A C1 d e).
           { apply spli_size in Hsp. destruct Hsp. lia. }
           { exact Hd. }
           { exact He. }
        -- assert (EAC : spli_opt (t_union A C) = Some (t_union A C1, t_union A C2)).
           { simpl. rewrite EA. destruct (ordi_dec A) as [HdA|HdA]; [| exfalso; apply HdA; assumption].
             rewrite EC. reflexivity. }
           assert (EIAC : I (t_union A C) = I (t_union A C1) ++ I (t_union A C2))
             by (apply I_step; auto).
           rewrite EIAC. apply in_or_app. right.
           apply (IH A C2 d e).
           { apply spli_size in Hsp. destruct Hsp. lia. }
           { exact Hd. }
           { exact He. }
      * assert (OC : ordi C).
        { destruct (ordi_or_spli C) as [H|H]; auto.
          destruct H as [B [C0 HB]]. apply spli_opt_complete in HB. rewrite HB in EC. discriminate. }
        assert (EIA : I A = [A]) by (apply I_ordi_singleton; auto).
        assert (EIC : I C = [C]) by (apply I_ordi_singleton; auto).
        rewrite EIA in Hd. apply In_singleton_typ in Hd. subst d.
        rewrite EIC in He. apply In_singleton_typ in He. subst e.
        assert (EIAC : I (t_union A C) = [t_union A C]).
        { apply I_ordi_singleton. apply OI_or; auto. }
        rewrite EIAC. simpl. auto.
Qed.

Lemma I_union_pair : forall A C d e,
  In d (I A) -> In e (I C) -> In (t_union d e) (I (t_union A C)).
Proof. intros. eapply I_union_pair_aux; eauto. Qed.

Lemma U_and_mem_aux : forall n X Y u,
  size_typ X + size_typ Y <= n ->
  In u (U (t_and X Y)) ->
  exists u1 u2, u = t_and u1 u2 /\ In u1 (U X) /\ In u2 (U Y).
Proof.
  induction n as [|n IH].
  - intros X Y u Hn. pose proof (size_pos X). pose proof (size_pos Y). lia.
  - intros X Y u Hn Hu.
    destruct (splu_opt X) as [[X1 X2]|] eqn:EX.
    + assert (Hs : splu X X1 X2) by (apply splu_opt_sound; auto).
      destruct (splu_size X X1 X2 Hs) as [Hs1 Hs2].
      assert (EUX : U X = U X1 ++ U X2) by (apply U_step; auto).
      assert (EAC : splu_opt (t_and X Y) = Some (t_and X1 Y, t_and X2 Y)).
      { simpl. rewrite EX. reflexivity. }
      assert (EU : U (t_and X Y) = U (t_and X1 Y) ++ U (t_and X2 Y))
        by (apply U_step; auto).
      rewrite EU in Hu. apply in_app_or in Hu. destruct Hu as [Hu|Hu].
      * assert (E : exists u1 u2, u = t_and u1 u2 /\ In u1 (U X1) /\ In u2 (U Y)).
        { apply (IH X1 Y u); [lia | exact Hu]. }
        destruct E as [u1 [u2 [Heq [H1 H2]]]].
        exists u1, u2. split; [exact Heq|]. split; [|exact H2].
        rewrite EUX. apply in_or_app. left. exact H1.
      * assert (E : exists u1 u2, u = t_and u1 u2 /\ In u1 (U X2) /\ In u2 (U Y)).
        { apply (IH X2 Y u); [lia | exact Hu]. }
        destruct E as [u1 [u2 [Heq [H1 H2]]]].
        exists u1, u2. split; [exact Heq|]. split; [|exact H2].
        rewrite EUX. apply in_or_app. right. exact H1.
    + assert (OX : ordu X).
      { destruct (ordu_or_splu X) as [H|H]; auto.
        destruct H as [B [C0 HB]]. apply splu_opt_complete in HB. rewrite HB in EX. discriminate. }
      assert (EUX : U X = [X]) by (apply U_ordu_singleton; auto).
      destruct (splu_opt Y) as [[Y1 Y2]|] eqn:EY.
      * assert (Hs : splu Y Y1 Y2) by (apply splu_opt_sound; auto).
        destruct (splu_size Y Y1 Y2 Hs) as [Hs1 Hs2].
        assert (EUY : U Y = U Y1 ++ U Y2) by (apply U_step; auto).
        assert (EAC : splu_opt (t_and X Y) = Some (t_and X Y1, t_and X Y2)).
        { simpl. rewrite EX. destruct (ordu_dec X) as [Hd|Hd]; [| exfalso; apply Hd; assumption].
          rewrite EY. reflexivity. }
        assert (EU : U (t_and X Y) = U (t_and X Y1) ++ U (t_and X Y2))
          by (apply U_step; auto).
        rewrite EU in Hu. apply in_app_or in Hu. destruct Hu as [Hu|Hu].
        -- assert (E : exists u1 u2, u = t_and u1 u2 /\ In u1 (U X) /\ In u2 (U Y1)).
           { apply (IH X Y1 u); [lia | exact Hu]. }
           destruct E as [u1 [u2 [Heq [H1 H2]]]].
           exists u1, u2. split; [exact Heq|]. split; [exact H1|].
           rewrite EUY. apply in_or_app. left. exact H2.
        -- assert (E : exists u1 u2, u = t_and u1 u2 /\ In u1 (U X) /\ In u2 (U Y2)).
           { apply (IH X Y2 u); [lia | exact Hu]. }
           destruct E as [u1 [u2 [Heq [H1 H2]]]].
           exists u1, u2. split; [exact Heq|]. split; [exact H1|].
           rewrite EUY. apply in_or_app. right. exact H2.
      * assert (OY : ordu Y).
        { destruct (ordu_or_splu Y) as [H|H]; auto.
          destruct H as [B [C0 HB]]. apply splu_opt_complete in HB. rewrite HB in EY. discriminate. }
        assert (EUY : U Y = [Y]) by (apply U_ordu_singleton; auto).
        assert (EU : U (t_and X Y) = [t_and X Y]).
        { apply U_ordu_singleton. apply OU_and; auto. }
        rewrite EU in Hu. apply In_singleton_typ in Hu. subst u.
        exists X, Y. split; [reflexivity|]. split.
        -- rewrite EUX. simpl. auto.
        -- rewrite EUY. simpl. auto.
Qed.

Lemma U_and_mem : forall X Y u, In u (U (t_and X Y)) ->
  exists u1 u2, u = t_and u1 u2 /\ In u1 (U X) /\ In u2 (U Y).
Proof. intros. eapply U_and_mem_aux; eauto. Qed.

Lemma I_union_mem_aux : forall n X Y j,
  size_typ X + size_typ Y <= n ->
  In j (I (t_union X Y)) ->
  exists d e, j = t_union d e /\ In d (I X) /\ In e (I Y).
Proof.
  induction n as [|n IH].
  - intros X Y j Hn. pose proof (size_pos X). pose proof (size_pos Y). lia.
  - intros X Y j Hn Hj.
    destruct (spli_opt X) as [[X1 X2]|] eqn:EX.
    + assert (Hs : spli X X1 X2) by (apply spli_opt_sound; auto).
      destruct (spli_size X X1 X2 Hs) as [Hs1 Hs2].
      assert (EIX : I X = I X1 ++ I X2) by (apply I_step; auto).
      assert (EUnion : spli_opt (t_union X Y) = Some (t_union X1 Y, t_union X2 Y)).
      { simpl. rewrite EX. reflexivity. }
      assert (EI : I (t_union X Y) = I (t_union X1 Y) ++ I (t_union X2 Y))
        by (apply I_step; auto).
      rewrite EI in Hj. apply in_app_or in Hj. destruct Hj as [Hj|Hj].
      * assert (E : exists d e, j = t_union d e /\ In d (I X1) /\ In e (I Y)).
        { apply (IH X1 Y j); [lia | exact Hj]. }
        destruct E as [d [e [Heq [H1 H2]]]].
        exists d, e. split; [exact Heq|]. split; [|exact H2].
        rewrite EIX. apply in_or_app. left. exact H1.
      * assert (E : exists d e, j = t_union d e /\ In d (I X2) /\ In e (I Y)).
        { apply (IH X2 Y j); [lia | exact Hj]. }
        destruct E as [d [e [Heq [H1 H2]]]].
        exists d, e. split; [exact Heq|]. split; [|exact H2].
        rewrite EIX. apply in_or_app. right. exact H1.
    + assert (OX : ordi X).
      { destruct (ordi_or_spli X) as [H|H]; auto.
        destruct H as [B [C0 HB]]. apply spli_opt_complete in HB. rewrite HB in EX. discriminate. }
      assert (EIX : I X = [X]) by (apply I_ordi_singleton; auto).
      destruct (spli_opt Y) as [[Y1 Y2]|] eqn:EY.
      * assert (Hs : spli Y Y1 Y2) by (apply spli_opt_sound; auto).
        destruct (spli_size Y Y1 Y2 Hs) as [Hs1 Hs2].
        assert (EIY : I Y = I Y1 ++ I Y2) by (apply I_step; auto).
        assert (EUnion : spli_opt (t_union X Y) = Some (t_union X Y1, t_union X Y2)).
        { simpl. rewrite EX. destruct (ordi_dec X) as [Hd|Hd]; [| exfalso; apply Hd; assumption].
          rewrite EY. reflexivity. }
        assert (EI : I (t_union X Y) = I (t_union X Y1) ++ I (t_union X Y2))
          by (apply I_step; auto).
        rewrite EI in Hj. apply in_app_or in Hj. destruct Hj as [Hj|Hj].
        -- assert (E : exists d e, j = t_union d e /\ In d (I X) /\ In e (I Y1)).
           { apply (IH X Y1 j); [lia | exact Hj]. }
           destruct E as [d [e [Heq [H1 H2]]]].
           exists d, e. split; [exact Heq|]. split; [exact H1|].
           rewrite EIY. apply in_or_app. left. exact H2.
        -- assert (E : exists d e, j = t_union d e /\ In d (I X) /\ In e (I Y2)).
           { apply (IH X Y2 j); [lia | exact Hj]. }
           destruct E as [d [e [Heq [H1 H2]]]].
           exists d, e. split; [exact Heq|]. split; [exact H1|].
           rewrite EIY. apply in_or_app. right. exact H2.
      * assert (OY : ordi Y).
        { destruct (ordi_or_spli Y) as [H|H]; auto.
          destruct H as [B [C0 HB]]. apply spli_opt_complete in HB. rewrite HB in EY. discriminate. }
        assert (EIY : I Y = [Y]) by (apply I_ordi_singleton; auto).
        assert (EI : I (t_union X Y) = [t_union X Y]).
        { apply I_ordi_singleton. apply OI_or; auto. }
        rewrite EI in Hj. apply In_singleton_typ in Hj. subst j.
        exists X, Y. split; [reflexivity|]. split.
        -- rewrite EIX. simpl. auto.
        -- rewrite EIY. simpl. auto.
Qed.

Lemma I_union_mem : forall X Y j, In j (I (t_union X Y)) ->
  exists d e, j = t_union d e /\ In d (I X) /\ In e (I Y).
Proof. intros. eapply I_union_mem_aux; eauto. Qed.

Lemma I_arrow_mem_aux : forall n X Y k,
  size_typ X + size_typ Y <= n ->
  In k (I (t_arrow X Y)) ->
  exists P C, k = t_arrow P C /\ In P (U X) /\ In C (I Y).
Proof.
  induction n as [|n IH].
  - intros X Y k Hn. pose proof (size_pos X). pose proof (size_pos Y). lia.
  - intros X Y k Hn Hk.
    destruct (spli_opt Y) as [[C1 C2]|] eqn:EY.
    + assert (Hs : spli Y C1 C2) by (apply spli_opt_sound; auto).
      destruct (spli_size Y C1 C2 Hs) as [Hs1 Hs2].
      assert (EIY : I Y = I C1 ++ I C2) by (apply I_step; auto).
      assert (EArr : spli_opt (t_arrow X Y) = Some (t_arrow X C1, t_arrow X C2)).
      { simpl. rewrite EY. reflexivity. }
      assert (EI : I (t_arrow X Y) = I (t_arrow X C1) ++ I (t_arrow X C2))
        by (apply I_step; auto).
      rewrite EI in Hk. apply in_app_or in Hk. destruct Hk as [Hk|Hk].
      * assert (E : exists P C, k = t_arrow P C /\ In P (U X) /\ In C (I C1)).
        { apply (IH X C1 k); [lia | exact Hk]. }
        destruct E as [P [C [Heq [H1 H2]]]].
        exists P, C. split; [exact Heq|]. split; [exact H1|].
        rewrite EIY. apply in_or_app. left. exact H2.
      * assert (E : exists P C, k = t_arrow P C /\ In P (U X) /\ In C (I C2)).
        { apply (IH X C2 k); [lia | exact Hk]. }
        destruct E as [P [C [Heq [H1 H2]]]].
        exists P, C. split; [exact Heq|]. split; [exact H1|].
        rewrite EIY. apply in_or_app. right. exact H2.
    + assert (OY : ordi Y).
      { destruct (ordi_or_spli Y) as [H|H]; auto.
        destruct H as [B [C0 HB]]. apply spli_opt_complete in HB. rewrite HB in EY. discriminate. }
      assert (EIY : I Y = [Y]) by (apply I_ordi_singleton; auto).
      destruct (splu_opt X) as [[P Q]|] eqn:EX.
      * assert (Hs : splu X P Q) by (apply splu_opt_sound; auto).
        destruct (splu_size X P Q Hs) as [Hs1 Hs2].
        assert (EUX : U X = U P ++ U Q) by (apply U_step; auto).
        assert (EArr : spli_opt (t_arrow X Y) = Some (t_arrow P Y, t_arrow Q Y)).
        { simpl. rewrite EY. destruct (ordi_dec Y) as [Hd|Hd]; [| exfalso; apply Hd; assumption].
          rewrite EX. reflexivity. }
        assert (EI : I (t_arrow X Y) = I (t_arrow P Y) ++ I (t_arrow Q Y))
          by (apply I_step; auto).
        rewrite EI in Hk. apply in_app_or in Hk. destruct Hk as [Hk|Hk].
        -- assert (E : exists P0 C, k = t_arrow P0 C /\ In P0 (U P) /\ In C (I Y)).
           { apply (IH P Y k); [lia | exact Hk]. }
           destruct E as [P0 [C [Heq [H1 H2]]]].
           exists P0, C. split; [exact Heq|]. split; [|exact H2].
           rewrite EUX. apply in_or_app. left. exact H1.
        -- assert (E : exists P0 C, k = t_arrow P0 C /\ In P0 (U Q) /\ In C (I Y)).
           { apply (IH Q Y k); [lia | exact Hk]. }
           destruct E as [P0 [C [Heq [H1 H2]]]].
           exists P0, C. split; [exact Heq|]. split; [|exact H2].
           rewrite EUX. apply in_or_app. right. exact H1.
      * assert (OX : ordu X).
        { destruct (ordu_or_splu X) as [H|H]; auto.
          destruct H as [B [C0 HB]]. apply splu_opt_complete in HB. rewrite HB in EX. discriminate. }
        assert (EUX : U X = [X]) by (apply U_ordu_singleton; auto).
        assert (EI : I (t_arrow X Y) = [t_arrow X Y]).
        { apply I_ordi_singleton. apply OI_arrow; auto. }
        rewrite EI in Hk. apply In_singleton_typ in Hk. subst k.
        exists X, Y. split; [reflexivity|]. split.
        -- rewrite EUX. simpl. auto.
        -- rewrite EIY. simpl. auto.
Qed.

Lemma I_arrow_mem : forall X Y k, In k (I (t_arrow X Y)) ->
  exists P C, k = t_arrow P C /\ In P (U X) /\ In C (I Y).
Proof. intros. eapply I_arrow_mem_aux; eauto. Qed.

Lemma I_arrow_decomp_aux : forall n X Y P C,
  size_typ X + size_typ Y <= n ->
  In P (U X) -> In C (I Y) -> In (t_arrow P C) (I (t_arrow X Y)).
Proof.
  induction n as [|n IH].
  - intros X Y P C Hn. pose proof (size_pos X). pose proof (size_pos Y). lia.
  - intros X Y P C Hn HP HC.
    destruct (spli_opt Y) as [[C1 C2]|] eqn:EY.
    + assert (Hs : spli Y C1 C2) by (apply spli_opt_sound; auto).
      destruct (spli_size Y C1 C2 Hs) as [Hs1 Hs2].
      assert (EIY : I Y = I C1 ++ I C2) by (apply I_step; auto).
      assert (EArr : spli_opt (t_arrow X Y) = Some (t_arrow X C1, t_arrow X C2)).
      { simpl. rewrite EY. reflexivity. }
      assert (EI : I (t_arrow X Y) = I (t_arrow X C1) ++ I (t_arrow X C2))
        by (apply I_step; auto).
      rewrite EIY in HC. apply in_app_or in HC. destruct HC as [HC|HC].
      * rewrite EI. apply in_or_app. left.
        apply (IH X C1 P C); [lia | exact HP | exact HC].
      * rewrite EI. apply in_or_app. right.
        apply (IH X C2 P C); [lia | exact HP | exact HC].
    + assert (OY : ordi Y).
      { destruct (ordi_or_spli Y) as [H|H]; auto.
        destruct H as [B0 [C0 HB]]. apply spli_opt_complete in HB. rewrite HB in EY. discriminate. }
      assert (EIY : I Y = [Y]) by (apply I_ordi_singleton; auto).
      rewrite EIY in HC. apply (In_singleton_typ C Y) in HC. subst C.
      destruct (splu_opt X) as [[P1 P2]|] eqn:EX.
      * assert (Hs : splu X P1 P2) by (apply splu_opt_sound; auto).
        destruct (splu_size X P1 P2 Hs) as [Hs1 Hs2].
        assert (EUX : U X = U P1 ++ U P2) by (apply U_step; auto).
        assert (EArr : spli_opt (t_arrow X Y) = Some (t_arrow P1 Y, t_arrow P2 Y)).
        { simpl. rewrite EY. destruct (ordi_dec Y) as [Hd|Hd]; [| exfalso; apply Hd; assumption].
          rewrite EX. reflexivity. }
        assert (EI : I (t_arrow X Y) = I (t_arrow P1 Y) ++ I (t_arrow P2 Y))
          by (apply I_step; auto).
        rewrite EUX in HP. apply in_app_or in HP. destruct HP as [HP|HP].
        -- rewrite EI. apply in_or_app. left.
           apply (IH P1 Y P Y); [lia | exact HP | rewrite EIY; simpl; auto].
        -- rewrite EI. apply in_or_app. right.
           apply (IH P2 Y P Y); [lia | exact HP | rewrite EIY; simpl; auto].
      * assert (OX : ordu X).
        { destruct (ordu_or_splu X) as [H|H]; auto.
          destruct H as [B0 [C0 HB]]. apply splu_opt_complete in HB. rewrite HB in EX. discriminate. }
        assert (EUX : U X = [X]) by (apply U_ordu_singleton; auto).
        rewrite EUX in HP. apply (In_singleton_typ P X) in HP. subst P.
        assert (EI : I (t_arrow X Y) = [t_arrow X Y]).
        { apply I_ordi_singleton. apply OI_arrow; auto. }
        rewrite EI. simpl. auto.
Qed.

Lemma I_arrow_decomp : forall X Y P C,
  In P (U X) -> In C (I Y) -> In (t_arrow P C) (I (t_arrow X Y)).
Proof. intros. eapply I_arrow_decomp_aux; eauto. Qed.


Lemma In_U_ordu' : forall A w, ordu A -> In w (U A) -> w = A.
Proof.
  intros A w Ho Hin. rewrite (U_ordu_singleton A Ho) in Hin.
  simpl in Hin. destruct Hin as [H|H]; [symmetry; exact H|destruct H].
Qed.
Lemma In_I_ordi' : forall A w, ordi A -> In w (I A) -> w = A.
Proof.
  intros A w Ho Hin. rewrite (I_ordi_singleton A Ho) in Hin.
  simpl in Hin. destruct Hin as [H|H]; [symmetry; exact H|destruct H].
Qed.

Lemma sle_cmp_ordi : forall G u X,
  ordu u -> ordi X -> (sle G u X <-> cmp G u X).
Proof.
  intros G u X Hu HX. unfold sle. split.
  - intro H.
    specialize (H u).
    rewrite (U_ordu_singleton u Hu) in H. simpl in H.
    specialize (H (or_introl eq_refl) X).
    rewrite (I_ordi_singleton X HX) in H. simpl in H.
    exact (H (or_introl eq_refl)).
  - intros Hc w Hw j Hj.
    rewrite (In_U_ordu' u w Hu Hw).
    rewrite (In_I_ordi' X j HX Hj).
    exact Hc.
Qed.

Lemma sle_app_intro : forall G u A B C,
  I A = I B ++ I C -> sle G u B -> sle G u C -> sle G u A.
Proof.
  intros G u A B C EI HB HC. unfold sle in *. intros a Ha i Hi.
  rewrite EI in Hi. apply in_app_or in Hi. destruct Hi as [Hi|Hi].
  - exact (HB a Ha i Hi).
  - exact (HC a Ha i Hi).
Qed.
Lemma sle_app_l : forall G u A B C,
  I A = I B ++ I C -> sle G u A -> sle G u B.
Proof.
  intros G u A B C EI HA. unfold sle in *. intros a Ha i Hi.
  apply (HA a Ha i). rewrite EI. apply in_or_app. left. exact Hi.
Qed.
Lemma sle_app_r : forall G u A B C,
  I A = I B ++ I C -> sle G u A -> sle G u C.
Proof.
  intros G u A B C EI HA. unfold sle in *. intros a Ha i Hi.
  apply (HA a Ha i). rewrite EI. apply in_or_app. right. exact Hi.
Qed.

(* For ordi X,Y and ordu u, a comparison to the union splits. *)
Lemma cmp_union_split_ordi : forall G u X Y,
  okenvp G -> wft G u -> wft G X -> wft G Y ->
  ordi X -> ordi Y -> ordu u ->
  cmp G u (t_union X Y) -> sle G u X \/ sle G u Y.
Proof.
  intros G u X Y Ho Wu WX WY HX HY Hu Hc.
  remember (t_union X Y) as T eqn:ET.
  revert X Y WX WY HX HY ET.
  induction Hc; intros X Y WX WY HX HY ET; try discriminate.
  - (* C_bot *) left. apply sle_cmp_ordi; auto. apply C_bot; auto.
  - (* C_or_l *) left. injection ET as E1 E2. subst i1 i2.
    apply sle_cmp_ordi; auto.
  - (* C_or_r *) right. injection ET as E1 E2. subst i1 i2.
    apply sle_cmp_ordi; auto.
  - (* C_and_l *) subst i.
    destruct (ordu_inv_and u1 u2 Hu) as [Hu1 Hu2].
    destruct (wft_inv_and G u1 u2 Wu) as [Wu1 Wu2].
    destruct (IHHc Ho Wu1 Hu1 X Y WX WY HX HY eq_refl) as [Hs|Hs].
    + left. apply sle_cmp_ordi; auto. apply C_and_l; [exact Wu2|].
      apply (proj1 (sle_cmp_ordi G u1 X Hu1 HX)); exact Hs.
    + right. apply sle_cmp_ordi; auto. apply C_and_l; [exact Wu2|].
      apply (proj1 (sle_cmp_ordi G u1 Y Hu1 HY)); exact Hs.
  - (* C_and_r *) subst i.
    destruct (ordu_inv_and u1 u2 Hu) as [Hu1 Hu2].
    destruct (wft_inv_and G u1 u2 Wu) as [Wu1 Wu2].
    destruct (IHHc Ho Wu2 Hu2 X Y WX WY HX HY eq_refl) as [Hs|Hs].
    + left. apply sle_cmp_ordi; auto. apply C_and_r; [exact Wu1|].
      apply (proj1 (sle_cmp_ordi G u2 X Hu2 HX)); exact Hs.
    + right. apply sle_cmp_ordi; auto. apply C_and_r; [exact Wu1|].
      apply (proj1 (sle_cmp_ordi G u2 Y Hu2 HY)); exact Hs.
Qed.

Lemma splu_split_aux : forall n G u A B C,
  okenvp G -> ordu u -> wft G u -> wft G A -> size_typ A <= n ->
  splu A B C -> sle G u A -> sle G u B \/ sle G u C.
Proof.
  induction n as [|n IH].
  - intros. pose proof (size_pos A). lia.
  - intros G u A B C Ho Hu Wu WA Hn Hspl HA.
    destruct Hspl as [X Y | X Y X1 X2 Hspl | X Y Y1 Y2 HOrd Hspl].
    + (* SpU_or: A = union X Y *)
      destruct (splu_wft G (t_union X Y) X Y (SpU_or X Y) WA) as [WX WY].
      destruct (spli_opt X) as [[X1 X2]|] eqn:EX.
      * assert (HspX : spli X X1 X2) by (apply spli_opt_sound; auto).
        destruct (spli_size X X1 X2 HspX) as [HsX1 HsX2].
        destruct (spli_wft G X X1 X2 HspX WX) as [WX1 WX2].
        assert (EI : I (t_union X Y) = I (t_union X1 Y) ++ I (t_union X2 Y))
          by (apply I_step; apply spli_opt_complete; apply SpI_orl; auto).
        assert (H1 : sle G u (t_union X1 Y)) by (apply (sle_app_l _ _ _ _ _ EI); exact HA).
        assert (H2 : sle G u (t_union X2 Y)) by (apply (sle_app_r _ _ _ _ _ EI); exact HA).
        assert (WA1 : wft G (t_union X1 Y)) by (apply wft_or; auto).
        assert (WA2 : wft G (t_union X2 Y)) by (apply wft_or; auto).
        assert (R1 : sle G u X1 \/ sle G u Y).
        { apply (IH G u (t_union X1 Y) X1 Y Ho Hu Wu WA1); [simpl in *; lia | apply SpU_or | exact H1]. }
        assert (R2 : sle G u X2 \/ sle G u Y).
        { apply (IH G u (t_union X2 Y) X2 Y Ho Hu Wu WA2); [simpl in *; lia | apply SpU_or | exact H2]. }
        destruct R1 as [R1|R1].
        -- destruct R2 as [R2|R2].
           ++ left. assert (EIX : I X = I X1 ++ I X2) by (apply I_step; auto).
              apply (sle_app_intro _ _ _ _ _ EIX); auto.
           ++ right. exact R2.
        -- right. exact R1.
      * assert (OX : ordi X).
        { destruct (ordi_or_spli X) as [H|H]; auto.
          destruct H as [B0 [C0 HB]]. apply spli_opt_complete in HB. rewrite HB in EX. discriminate. }
        destruct (spli_opt Y) as [[Y1 Y2]|] eqn:EY.
        -- assert (HspY : spli Y Y1 Y2) by (apply spli_opt_sound; auto).
           destruct (spli_size Y Y1 Y2 HspY) as [HsY1 HsY2].
           destruct (spli_wft G Y Y1 Y2 HspY WY) as [WY1 WY2].
           assert (EI : I (t_union X Y) = I (t_union X Y1) ++ I (t_union X Y2))
             by (apply I_step; apply spli_opt_complete; apply SpI_orr; auto).
           assert (H1 : sle G u (t_union X Y1)) by (apply (sle_app_l _ _ _ _ _ EI); exact HA).
           assert (H2 : sle G u (t_union X Y2)) by (apply (sle_app_r _ _ _ _ _ EI); exact HA).
           assert (WA1 : wft G (t_union X Y1)) by (apply wft_or; auto).
           assert (WA2 : wft G (t_union X Y2)) by (apply wft_or; auto).
           assert (R1 : sle G u X \/ sle G u Y1).
           { apply (IH G u (t_union X Y1) X Y1 Ho Hu Wu WA1); [simpl in *; lia | apply SpU_or | exact H1]. }
           assert (R2 : sle G u X \/ sle G u Y2).
           { apply (IH G u (t_union X Y2) X Y2 Ho Hu Wu WA2); [simpl in *; lia | apply SpU_or | exact H2]. }
           destruct R1 as [R1|R1].
           ++ destruct R2 as [R2|R2].
              ** left. exact R1.
              ** left. exact R1.
           ++ destruct R2 as [R2|R2].
              ** left. exact R2.
              ** right. assert (EIY : I Y = I Y1 ++ I Y2) by (apply I_step; auto).
                 apply (sle_app_intro _ _ _ _ _ EIY); auto.
        -- assert (OY : ordi Y).
           { destruct (ordi_or_spli Y) as [H|H]; auto.
             destruct H as [B0 [C0 HB]]. apply spli_opt_complete in HB. rewrite HB in EY. discriminate. }
           assert (HC : cmp G u (t_union X Y)).
           { apply (proj1 (sle_cmp_ordi G u (t_union X Y) Hu (OI_or X Y OX OY))); exact HA. }
           apply cmp_union_split_ordi with (G:=G) (u:=u) (X:=X) (Y:=Y); auto.
    + (* SpU_andl: A = and X Y, splu X X1 X2 *)
      destruct (wft_inv_and G X Y WA) as [WX WY].
      destruct (splu_size X X1 X2 Hspl) as [HsX1 HsX2].
      assert (EIA : I (t_and X Y) = I X ++ I Y)
        by (apply I_step; apply spli_opt_complete; apply SpI_and).
      assert (HX : sle G u X) by (apply (sle_app_l _ _ _ _ _ EIA); exact HA).
      assert (HY : sle G u Y) by (apply (sle_app_r _ _ _ _ _ EIA); exact HA).
      assert (R1 : sle G u X1 \/ sle G u X2).
      { apply (IH G u X X1 X2 Ho Hu Wu WX); [simpl in *; lia | exact Hspl | exact HX]. }
      destruct R1 as [R1|R1].
      * left. assert (EI1 : I (t_and X1 Y) = I X1 ++ I Y)
          by (apply I_step; apply spli_opt_complete; apply SpI_and).
        apply (sle_app_intro _ _ _ _ _ EI1); auto.
      * right. assert (EI2 : I (t_and X2 Y) = I X2 ++ I Y)
          by (apply I_step; apply spli_opt_complete; apply SpI_and).
        apply (sle_app_intro _ _ _ _ _ EI2); auto.
    + (* SpU_andr: A = and X Y, splu Y Y1 Y2 *)
      destruct (wft_inv_and G X Y WA) as [WX WY].
      destruct (splu_size Y Y1 Y2 Hspl) as [HsY1 HsY2].
      assert (EIA : I (t_and X Y) = I X ++ I Y)
        by (apply I_step; apply spli_opt_complete; apply SpI_and).
      assert (HX : sle G u X) by (apply (sle_app_l _ _ _ _ _ EIA); exact HA).
      assert (HY : sle G u Y) by (apply (sle_app_r _ _ _ _ _ EIA); exact HA).
      assert (R1 : sle G u Y1 \/ sle G u Y2).
      { apply (IH G u Y Y1 Y2 Ho Hu Wu WY); [simpl in *; lia | exact Hspl | exact HY]. }
      destruct R1 as [R1|R1].
      * left. assert (EI1 : I (t_and X Y1) = I X ++ I Y1)
          by (apply I_step; apply spli_opt_complete; apply SpI_and).
        apply (sle_app_intro _ _ _ _ _ EI1); auto.
      * right. assert (EI2 : I (t_and X Y2) = I X ++ I Y2)
          by (apply I_step; apply spli_opt_complete; apply SpI_and).
        apply (sle_app_intro _ _ _ _ _ EI2); auto.
Qed.

Lemma splu_split : forall G u A B C,
  okenvp G -> ordu u -> wft G u -> wft G A ->
  splu A B C -> sle G u A -> sle G u B \/ sle G u C.
Proof. intros. eapply splu_split_aux; eauto. Qed.


Lemma U_split_aux : forall n G u Y,
  okenvp G -> ordu u -> wft G u -> wft G Y -> size_typ Y <= n ->
  sle G u Y -> exists w, In w (U Y) /\ sle G u w.
Proof.
  induction n as [|n IH].
  - intros. pose proof (size_pos Y). lia.
  - intros G u Y Ho Hu Wu WY Hn HY.
    destruct (ordu_or_splu Y) as [HoY | [Y1 [Y2 Hspl]]].
    + exists Y. split.
      * rewrite (U_ordu_singleton Y HoY). simpl. auto.
      * exact HY.
    + assert (Hsplopt : splu_opt Y = Some (Y1, Y2)) by (apply splu_opt_complete; auto).
      assert (EU : U Y = U Y1 ++ U Y2) by (apply U_step; auto).
      destruct (splu_wft G Y Y1 Y2 Hspl WY) as [WY1 WY2].
      destruct (splu_size Y Y1 Y2 Hspl) as [Hs1 Hs2].
      destruct (splu_split G u Y Y1 Y2 Ho Hu Wu WY Hspl HY) as [H1|H1].
      * assert (E1 : exists w, In w (U Y1) /\ sle G u w).
        { apply (IH G u Y1 Ho Hu Wu WY1); [lia | exact H1]. }
        destruct E1 as [w [Hw Hs]].
        exists w. split; [|exact Hs].
        rewrite EU. apply in_or_app. left. exact Hw.
      * assert (E2 : exists w, In w (U Y2) /\ sle G u w).
        { apply (IH G u Y2 Ho Hu Wu WY2); [lia | exact H1]. }
        destruct E2 as [w [Hw Hs]].
        exists w. split; [|exact Hs].
        rewrite EU. apply in_or_app. right. exact Hw.
Qed.

Lemma U_split : forall G u Y,
  okenvp G -> ordu u -> wft G u -> wft G Y ->
  sle G u Y -> exists w, In w (U Y) /\ sle G u w.
Proof. intros. eapply U_split_aux; eauto. Qed.


Lemma sle_refl_aux : forall n G A,
  okenvp G -> wft G A -> size_typ A <= n -> sle G A A.
Proof.
  induction n as [|n IH].
  - intros G A Ho WA Hn. pose proof (size_pos A). lia.
  - intros G A Ho WA Hn.
    destruct A as [| | | X Y | X Y | X Y | | p].
    + (* int *) unfold sle. intros u Hu j Hj.
      rewrite (In_U_ordu' t_int u OU_int Hu).
      rewrite (In_I_ordi' t_int j OI_int Hj).
      apply C_int; auto.
    + (* top *) unfold sle. intros u Hu j Hj.
      rewrite (In_U_ordu' t_top u OU_top Hu).
      rewrite (In_I_ordi' t_top j OI_top Hj).
      apply C_top; auto.
    + (* bot *) unfold sle. intros u Hu j Hj.
      rewrite (In_U_ordu' t_bot u OU_bot Hu).
      rewrite (In_I_ordi' t_bot j OI_bot Hj).
      apply C_bot; auto.
    + (* arrow X Y *) unfold sle. intros u Hu j Hj.
      rewrite (In_U_ordu' (t_arrow X Y) u (OU_arrow X Y) Hu).
      apply I_arrow_mem in Hj. destruct Hj as [P [C [Heq [HP HC]]]]. subst j.
      assert (WXY := WA). apply wft_inv_arrow in WXY as [WX WY].
      assert (ROX : sle G X X).
      { apply (IH G X Ho WX); simpl in *; lia. }
      assert (ROY : sle G Y Y).
      { apply (IH G Y Ho WY); simpl in *; lia. }
      apply C_arrow.
      * intros u0 Hu0 i0 Hi0.
        rewrite (In_U_ordu' P u0 (U_ordu X P HP) Hu0).
        unfold sle in ROX. apply (ROX P HP i0 Hi0).
      * intros u0 Hu0 i0 Hi0.
        rewrite (In_I_ordi' C i0 (I_ordi Y C HC) Hi0).
        unfold sle in ROY. apply (ROY u0 Hu0 C HC).
    + (* union X Y *) unfold sle. intros u Hu j Hj.
      assert (WXY := WA). apply wft_inv_or in WXY as [WX WY].
      assert (EU : U (t_union X Y) = U X ++ U Y).
      { apply U_step. apply splu_opt_complete. apply SpU_or. }
      rewrite EU in Hu. apply in_app_or in Hu. destruct Hu as [Hu|Hu].
      * apply I_union_mem in Hj. destruct Hj as [d [e [Heq [Hd He]]]]. subst j.
        assert (ROX : sle G X X) by (apply (IH G X Ho WX); simpl in *; lia).
        apply C_or_l; [apply (I_wft G Y e WY He)|].
        unfold sle in ROX. apply (ROX u Hu d Hd).
      * apply I_union_mem in Hj. destruct Hj as [d [e [Heq [Hd He]]]]. subst j.
        assert (ROY : sle G Y Y) by (apply (IH G Y Ho WY); simpl in *; lia).
        apply C_or_r; [apply (I_wft G X d WX Hd)|].
        unfold sle in ROY. apply (ROY u Hu e He).
    + (* and X Y *) unfold sle. intros u Hu j Hj.
      assert (WXY := WA). apply wft_inv_and in WXY as [WX WY].
      assert (EI : I (t_and X Y) = I X ++ I Y).
      { apply I_step. apply spli_opt_complete. apply SpI_and. }
      rewrite EI in Hj. apply in_app_or in Hj. destruct Hj as [Hj|Hj].
      * apply U_and_mem in Hu. destruct Hu as [u1 [u2 [Heq [H1 H2]]]]. subst u.
        assert (ROX : sle G X X) by (apply (IH G X Ho WX); simpl in *; lia).
        assert (Wu2 : wft G u2) by (apply (U_wft G Y u2 WY H2)).
        apply C_and_l; [exact Wu2|].
        unfold sle in ROX. apply (ROX u1 H1 j Hj).
      * apply U_and_mem in Hu. destruct Hu as [u1 [u2 [Heq [H1 H2]]]]. subst u.
        assert (ROY : sle G Y Y) by (apply (IH G Y Ho WY); simpl in *; lia).
        assert (Wu1 : wft G u1) by (apply (U_wft G X u1 WX H1)).
        apply C_and_r; [exact Wu1|].
        unfold sle in ROY. apply (ROY u2 H2 j Hj).
    + (* unit *) unfold sle. intros u Hu j Hj.
      rewrite (In_U_ordu' t_unit u OU_null Hu).
      rewrite (In_I_ordi' t_unit j OI_null Hj).
      apply C_unit; auto.
    + (* prim p *) unfold sle. intros u Hu j Hj.
      rewrite (In_U_ordu' (t_prim p) u (OU_prim p) Hu).
      rewrite (In_I_ordi' (t_prim p) j (OI_prim p) Hj).
      apply C_prim_refl; auto.
Qed.

Lemma sle_refl : forall G A, okenvp G -> wft G A -> sle G A A.
Proof. intros. eapply sle_refl_aux; eauto. Qed.


Fixpoint allb_typ (f:typ->bool) (l:list typ) : bool :=
  match l with
  | nil => true
  | x::xs => andb (f x) (allb_typ f xs)
  end.

Definition allpairs_dec (f:typ->typ->bool) (l1 l2:list typ) : bool :=
  allb_typ (fun x => allb_typ (f x) l2) l1.

Lemma allb_true : forall f l,
  allb_typ f l = true -> forall x, In x l -> f x = true.
Proof.
  intros f l. induction l as [|a l IH]; intros H x Hin; [destruct Hin|].
  simpl in H. apply andb_true_iff in H. destruct H as [Ha Hl].
  destruct Hin as [->|Hin].
  - exact Ha.
  - apply IH; auto.
Qed.
Lemma allb_false_exists : forall f l,
  allb_typ f l = false -> exists x, In x l /\ f x = false.
Proof.
  intros f l. induction l as [|a l IH]; intros H; [discriminate|].
  simpl in H. apply andb_false_iff in H. destruct H as [Ha|Hl].
  - exists a. split; [left; reflexivity|exact Ha].
  - destruct (IH Hl) as [x [Hx Hfx]]. exists x. split; [right; exact Hx|exact Hfx].
Qed.
Lemma allb_complete : forall f l,
  (forall x, In x l -> f x = true) -> allb_typ f l = true.
Proof.
  intros f l H. induction l as [|a l IH]; simpl; [reflexivity|].
  apply andb_true_iff. split.
  - apply H. left. reflexivity.
  - apply IH. intros x Hx. apply H. right. exact Hx.
Qed.

Lemma allpairs_true : forall f l1 l2,
  allpairs_dec f l1 l2 = true ->
  forall x, In x l1 -> forall y, In y l2 -> f x y = true.
Proof.
  intros f l1 l2 H x Hx y Hy.
  unfold allpairs_dec in H.
  pose proof (allb_true (fun x => allb_typ (f x) l2) l1 H x Hx) as Hx2.
  exact (allb_true (f x) l2 Hx2 y Hy).
Qed.
Lemma allpairs_complete : forall f l1 l2,
  (forall x, In x l1 -> forall y, In y l2 -> f x y = true) ->
  allpairs_dec f l1 l2 = true.
Proof.
  intros f l1 l2 H. unfold allpairs_dec.
  apply allb_complete. intros x Hx.
  apply allb_complete. intros y Hy.
  apply H; auto.
Qed.

Fixpoint cdec (k:nat) (G:envp) (u i:typ) {struct k} : bool :=
  match k with
  | 0 => false
  | S k' =>
    match i with
    | t_top => andb (okenvp_b G) (wft_b G u)
    | t_union i1 i2 =>
        orb (andb (wft_b G i2) (cdec k' G u i1))
            (orb (andb (wft_b G i1) (cdec k' G u i2))
                 (match u with
                  | t_and u1 u2 =>
                      orb (andb (wft_b G u2) (cdec k' G u1 i))
                          (andb (wft_b G u1) (cdec k' G u2 i))
                  | _ => false
                  end))
    | _ =>
      match u with
      | t_bot => andb (okenvp_b G) (wft_b G i)
      | t_and u1 u2 =>
          orb (andb (wft_b G u2) (cdec k' G u1 i))
              (andb (wft_b G u1) (cdec k' G u2 i))
      | t_arrow a1 a2 =>
          match i with
          | t_arrow b1 b2 =>
              andb (allpairs_dec (fun u0 i0 => cdec k' G u0 i0) (U b1) (I a1))
                   (allpairs_dec (fun u0 i0 => cdec k' G u0 i0) (U a2) (I b2))
          | _ => false
          end
      | t_int => match i with t_int => okenvp_b G | _ => false end
      | t_unit => match i with t_unit => okenvp_b G | _ => false end
      | t_prim n =>
          match i with
          | t_prim m =>
              if eq_dec n m then andb (okenvp_b G) (wft_b G (t_prim n))
              else match G with
                   | (h,A)::PG =>
                       if eq_dec h n then
                         match A with
                         | t_prim j => andb (okenvp_b G) (cdec k' PG (t_prim j) (t_prim m))
                         | _ => false
                         end
                       else andb (okenvp_b G) (cdec k' PG (t_prim n) (t_prim m))
                   | nil => false
                   end
          | _ => false
          end
      | _ => false
      end
    end
  end.

Lemma cdec_sound : forall k G u i, cdec k G u i = true -> cmp G u i.
Proof.
  induction k as [|k IH]; intros G u i H; [simpl in H; discriminate|].
  destruct i as [| | | b1 b2 | i1 i2 | i1 i2 | | m].
  - (* i = int *) destruct u as [| | | a1 a2 | U V | u1 u2 | | n]; simpl in H; try discriminate.
    + apply C_int. apply okenvp_b_true. exact H.
    + apply andb_true_iff in H as [Ho Hi].
      apply C_bot; [apply okenvp_b_true; exact Ho|apply wft_b_true; exact Hi].
    + apply orb_true_iff in H as [H|H].
      * apply andb_true_iff in H as [W Hc].
        apply C_and_l; [apply wft_b_true; exact W|apply IH; exact Hc].
      * apply andb_true_iff in H as [W Hc].
        apply C_and_r; [apply wft_b_true; exact W|apply IH; exact Hc].
  - (* i = top *) simpl in H. apply andb_true_iff in H as [Ho Wu].
    apply C_top; [apply okenvp_b_true; exact Ho|apply wft_b_true; exact Wu].
  - (* i = bot *) destruct u as [| | | a1 a2 | U V | u1 u2 | | n]; simpl in H; try discriminate.
    + apply andb_true_iff in H as [Ho Wi].
      apply C_bot; [apply okenvp_b_true; exact Ho|apply wft_b_true; exact Wi].
    + apply orb_true_iff in H as [H|H].
      * apply andb_true_iff in H as [W Hc].
        apply C_and_l; [apply wft_b_true; exact W|apply IH; exact Hc].
      * apply andb_true_iff in H as [W Hc].
        apply C_and_r; [apply wft_b_true; exact W|apply IH; exact Hc].
  - (* i = arrow b1 b2 *) destruct u as [| | | a1 a2 | U V | u1 u2 | | n]; simpl in H; try discriminate.
    + apply andb_true_iff in H as [Ho Wi].
      apply C_bot; [apply okenvp_b_true; exact Ho|apply wft_b_true; exact Wi].
    + apply andb_true_iff in H as [Ha Hb].
      apply C_arrow.
      * intros u0 Hu0 i0 Hi0.
        apply (IH G u0 i0). apply (allpairs_true (fun u0 i0 => cdec k G u0 i0) (U b1) (I a1) Ha u0 Hu0 i0 Hi0).
      * intros u0 Hu0 i0 Hi0.
        apply (IH G u0 i0). apply (allpairs_true (fun u0 i0 => cdec k G u0 i0) (U a2) (I b2) Hb u0 Hu0 i0 Hi0).
    + apply orb_true_iff in H as [H|H].
      * apply andb_true_iff in H as [W Hc].
        apply C_and_l; [apply wft_b_true; exact W|apply IH; exact Hc].
      * apply andb_true_iff in H as [W Hc].
        apply C_and_r; [apply wft_b_true; exact W|apply IH; exact Hc].
  - (* i = union i1 i2 *) simpl in H.
    apply orb_true_iff in H as [H|H].
    + apply andb_true_iff in H as [W Hc].
      apply C_or_l; [apply wft_b_true; exact W|apply IH; exact Hc].
    + apply orb_true_iff in H as [H|H].
      * apply andb_true_iff in H as [W Hc].
        apply C_or_r; [apply wft_b_true; exact W|apply IH; exact Hc].
      * destruct u as [| | | a1 a2 | U V | u1 u2 | | n]; simpl in H; try discriminate.
        -- apply orb_true_iff in H as [H|H].
           ++ apply andb_true_iff in H as [W Hc].
              apply C_and_l; [apply wft_b_true; exact W|apply IH; exact Hc].
           ++ apply andb_true_iff in H as [W Hc].
              apply C_and_r; [apply wft_b_true; exact W|apply IH; exact Hc].
  - (* i = and i1 i2 *) destruct u as [| | | a1 a2 | U V | u1 u2 | | n]; simpl in H; try discriminate.
    + apply andb_true_iff in H as [Ho Wi].
      apply C_bot; [apply okenvp_b_true; exact Ho|apply wft_b_true; exact Wi].
    + apply orb_true_iff in H as [H|H].
      * apply andb_true_iff in H as [W Hc].
        apply C_and_l; [apply wft_b_true; exact W|apply IH; exact Hc].
      * apply andb_true_iff in H as [W Hc].
        apply C_and_r; [apply wft_b_true; exact W|apply IH; exact Hc].
  - (* i = unit *) destruct u as [| | | a1 a2 | U V | u1 u2 | | n]; simpl in H; try discriminate.
    + apply andb_true_iff in H as [Ho Wi].
      apply C_bot; [apply okenvp_b_true; exact Ho|apply wft_b_true; exact Wi].
    + apply orb_true_iff in H as [H|H].
      * apply andb_true_iff in H as [W Hc].
        apply C_and_l; [apply wft_b_true; exact W|apply IH; exact Hc].
      * apply andb_true_iff in H as [W Hc].
        apply C_and_r; [apply wft_b_true; exact W|apply IH; exact Hc].
    + apply C_unit. apply okenvp_b_true. exact H.
  - (* i = prim m *) destruct u as [| | | a1 a2 | U V | u1 u2 | | n]; simpl in H; try discriminate.
    + apply andb_true_iff in H as [Ho Wi].
      apply C_bot; [apply okenvp_b_true; exact Ho|apply wft_b_true; exact Wi].
    + apply orb_true_iff in H as [H|H].
      * apply andb_true_iff in H as [W Hc].
        apply C_and_l; [apply wft_b_true; exact W|apply IH; exact Hc].
      * apply andb_true_iff in H as [W Hc].
        apply C_and_r; [apply wft_b_true; exact W|apply IH; exact Hc].
    + destruct (eq_dec n m) as [E|Hne].
      * subst m. apply andb_true_iff in H as [Ho Wn].
        apply C_prim_refl; [apply okenvp_b_true; exact Ho|apply wft_b_true; exact Wn].
      * destruct G as [|(h,A) PG]; simpl in H; try discriminate.
        destruct (eq_dec h n) as [Eh|Ehn]; simpl in H.
        -- subst h. destruct A as [| | | A1 A2 | A1 A2 | A1 A2 | | j]; simpl in H; try discriminate.
           apply andb_true_iff in H as [Ho Hc].
           apply C_prim_eq.
           ++ apply okenvp_b_true; exact Ho.
           ++ apply IH; exact Hc.
        -- apply andb_true_iff in H as [Ho Hc].
           apply C_prim_neq.
           ++ apply okenvp_b_true; exact Ho.
           ++ exact Ehn.
           ++ apply IH; exact Hc.
Qed.

Lemma cdec_complete : forall k G u i,
  size_envp G + size_typ u + size_typ i <= k ->
  okenvp G -> ordu u -> ordi i -> wft G u -> wft G i ->
  cmp G u i -> cdec k G u i = true.
Proof.
  induction k as [|k IH]; intros G u i Hk Ho Hu Hi Wu Wi Hc.
  - pose proof (size_pos u). pose proof (size_pos i). lia.
  - inversion Hc; subst; clear Hc.
    + (* C_top *) simpl. apply andb_true_iff. split.
      * apply okenvp_b_complete; exact H.
      * apply wft_b_complete; exact H0.
    + (* C_bot *) destruct i as [| | | b1 b2 | i1 i2 | i1 i2 | | m]; simpl.
      * apply andb_true_iff. split; [apply okenvp_b_complete; exact H|apply wft_b_complete; exact H0].
      * apply andb_true_iff. split; [apply okenvp_b_complete; exact H|apply wft_b_complete; exact Wu].
      * apply andb_true_iff. split; [apply okenvp_b_complete; exact H|apply wft_b_complete; exact H0].
      * apply andb_true_iff. split; [apply okenvp_b_complete; exact H|apply wft_b_complete; exact H0].
      * (* union *) apply orb_true_iff. left. apply andb_true_iff. split.
        -- apply wft_b_complete; apply (proj2 (wft_inv_or G i1 i2 H0)).
        -- apply (IH G t_bot i1); [simpl in *; lia | exact H | apply OU_bot | apply (proj1 (ordi_inv_or i1 i2 Hi)) | apply wft_bot | apply (proj1 (wft_inv_or G i1 i2 H0)) | apply C_bot; [exact H|apply (proj1 (wft_inv_or G i1 i2 H0))]].
      * (* and target: cmp bot (and) via C_bot? inversion C_bot target i arbitrary; i=and; cdec bot branch andb okenvp wft i *) apply andb_true_iff. split; [apply okenvp_b_complete; exact H|apply wft_b_complete; exact H0].
      * apply andb_true_iff. split; [apply okenvp_b_complete; exact H|apply wft_b_complete; exact H0].
      * apply andb_true_iff. split; [apply okenvp_b_complete; exact H|apply wft_b_complete; exact H0].
    + (* C_or_l *) simpl. apply orb_true_iff. left. apply andb_true_iff. split.
      * apply wft_b_complete; exact H.
      * apply (IH G u i1); [simpl in *; lia | exact Ho | exact Hu | exact (proj1 (ordi_inv_or i1 i2 Hi)) | exact Wu | exact (proj1 (wft_inv_or G i1 i2 Wi)) | exact H0].
    + (* C_or_r *) simpl. apply orb_true_iff. right. apply orb_true_iff. left. apply andb_true_iff. split.
      * apply wft_b_complete; exact H.
      * apply (IH G u i2); [simpl in *; lia | exact Ho | exact Hu | exact (proj2 (ordi_inv_or i1 i2 Hi)) | exact Wu | exact (proj2 (wft_inv_or G i1 i2 Wi)) | exact H0].
    + (* C_and_l *) destruct i as [| | | b1 b2 | i1 i2 | i1 i2 | | m]; simpl.
      * (* int *) apply orb_true_iff. left. apply andb_true_iff. split.
        -- apply wft_b_complete; exact H.
        -- apply (IH G u1 t_int); [simpl in *; lia | exact Ho | exact (proj1 (ordu_inv_and u1 u2 Hu)) | apply OI_int | exact (proj1 (wft_inv_and G u1 u2 Wu)) | apply wft_int | exact H0].
      * (* top *) apply andb_true_iff. split.
        -- apply okenvp_b_complete; exact Ho.
        -- apply wft_b_complete. apply wft_and; [apply (proj1 (wft_inv_and G u1 u2 Wu))|apply (proj2 (wft_inv_and G u1 u2 Wu))].
      * (* bot *) apply orb_true_iff. left. apply andb_true_iff. split.
        -- apply wft_b_complete; exact H.
        -- apply (IH G u1 t_bot); [simpl in *; lia | exact Ho | exact (proj1 (ordu_inv_and u1 u2 Hu)) | apply OI_bot | exact (proj1 (wft_inv_and G u1 u2 Wu)) | apply wft_bot | exact H0].
      * (* arrow *) apply orb_true_iff. left. apply andb_true_iff. split.
        -- apply wft_b_complete; exact H.
        -- apply (IH G u1 (t_arrow b1 b2)); [simpl in *; lia | exact Ho | exact (proj1 (ordu_inv_and u1 u2 Hu)) | exact Hi | exact (proj1 (wft_inv_and G u1 u2 Wu)) | exact Wi | exact H0].
      * (* union *) apply orb_true_iff. right. apply orb_true_iff. right. apply orb_true_iff. left. apply andb_true_iff. split.
        -- apply wft_b_complete; exact H.
        -- apply (IH G u1 (t_union i1 i2)); [simpl in *; lia | exact Ho | exact (proj1 (ordu_inv_and u1 u2 Hu)) | exact Hi | exact (proj1 (wft_inv_and G u1 u2 Wu)) | exact Wi | exact H0].
      * (* target and impossible because i is ordi *) exfalso. inversion Hi.
      * (* unit *) apply orb_true_iff. left. apply andb_true_iff. split.
        -- apply wft_b_complete; exact H.
        -- apply (IH G u1 t_unit); [simpl in *; lia | exact Ho | exact (proj1 (ordu_inv_and u1 u2 Hu)) | apply OI_null | exact (proj1 (wft_inv_and G u1 u2 Wu)) | apply wft_unit | exact H0].
      * (* prim *) apply orb_true_iff. left. apply andb_true_iff. split.
        -- apply wft_b_complete; exact H.
        -- apply (IH G u1 (t_prim m)); [simpl in *; lia | exact Ho | exact (proj1 (ordu_inv_and u1 u2 Hu)) | apply OI_prim | exact (proj1 (wft_inv_and G u1 u2 Wu)) | exact Wi | exact H0].
    + (* C_and_r *) destruct i as [| | | b1 b2 | i1 i2 | i1 i2 | | m]; simpl.
      * apply orb_true_iff. right. apply andb_true_iff. split.
        -- apply wft_b_complete; exact H.
        -- apply (IH G u2 t_int); [simpl in *; lia | exact Ho | exact (proj2 (ordu_inv_and u1 u2 Hu)) | apply OI_int | exact (proj2 (wft_inv_and G u1 u2 Wu)) | apply wft_int | exact H0].
      * apply andb_true_iff. split.
        -- apply okenvp_b_complete; exact Ho.
        -- apply wft_b_complete. apply wft_and; [apply (proj1 (wft_inv_and G u1 u2 Wu))|apply (proj2 (wft_inv_and G u1 u2 Wu))].
      * apply orb_true_iff. right. apply andb_true_iff. split.
        -- apply wft_b_complete; exact H.
        -- apply (IH G u2 t_bot); [simpl in *; lia | exact Ho | exact (proj2 (ordu_inv_and u1 u2 Hu)) | apply OI_bot | exact (proj2 (wft_inv_and G u1 u2 Wu)) | apply wft_bot | exact H0].
      * apply orb_true_iff. right. apply andb_true_iff. split.
        -- apply wft_b_complete; exact H.
        -- apply (IH G u2 (t_arrow b1 b2)); [simpl in *; lia | exact Ho | exact (proj2 (ordu_inv_and u1 u2 Hu)) | exact Hi | exact (proj2 (wft_inv_and G u1 u2 Wu)) | exact Wi | exact H0].
      * apply orb_true_iff. right. apply orb_true_iff. right. apply orb_true_iff. right. apply andb_true_iff. split.
        -- apply wft_b_complete; exact H.
        -- apply (IH G u2 (t_union i1 i2)); [simpl in *; lia | exact Ho | exact (proj2 (ordu_inv_and u1 u2 Hu)) | exact Hi | exact (proj2 (wft_inv_and G u1 u2 Wu)) | exact Wi | exact H0].
      * exfalso. inversion Hi.
      * apply orb_true_iff. right. apply andb_true_iff. split.
        -- apply wft_b_complete; exact H.
        -- apply (IH G u2 t_unit); [simpl in *; lia | exact Ho | exact (proj2 (ordu_inv_and u1 u2 Hu)) | apply OI_null | exact (proj2 (wft_inv_and G u1 u2 Wu)) | apply wft_unit | exact H0].
      * apply orb_true_iff. right. apply andb_true_iff. split.
        -- apply wft_b_complete; exact H.
        -- apply (IH G u2 (t_prim m)); [simpl in *; lia | exact Ho | exact (proj2 (ordu_inv_and u1 u2 Hu)) | apply OI_prim | exact (proj2 (wft_inv_and G u1 u2 Wu)) | exact Wi | exact H0].
    + (* C_arrow *) simpl. apply andb_true_iff. split.
      * apply allpairs_complete. intros u0 Hu0 i0 Hi0.
        destruct (wft_inv_arrow G a1 a2 Wu) as [Wa1 Wa2].
        destruct (wft_inv_arrow G b1 b2 Wi) as [Wb1 Wb2].
        apply (IH G u0 i0).
        -- apply U_size in Hu0. apply I_size in Hi0. simpl in *. lia.
        -- exact Ho.
        -- apply (U_ordu b1 u0 Hu0).
        -- apply (I_ordi a1 i0 Hi0).
        -- apply (U_wft G b1 u0 Wb1 Hu0).
        -- apply (I_wft G a1 i0 Wa1 Hi0).
        -- apply (H u0 Hu0 i0 Hi0).
      * apply allpairs_complete. intros u0 Hu0 i0 Hi0.
        destruct (wft_inv_arrow G a1 a2 Wu) as [Wa1 Wa2].
        destruct (wft_inv_arrow G b1 b2 Wi) as [Wb1 Wb2].
        apply (IH G u0 i0).
        -- apply U_size in Hu0. apply I_size in Hi0. simpl in *. lia.
        -- exact Ho.
        -- apply (U_ordu a2 u0 Hu0).
        -- apply (I_ordi b2 i0 Hi0).
        -- apply (U_wft G a2 u0 Wa2 Hu0).
        -- apply (I_wft G b2 i0 Wb2 Hi0).
        -- apply (H0 u0 Hu0 i0 Hi0).
    + (* C_int *) simpl. apply okenvp_b_complete; exact H.
    + (* C_unit *) simpl. apply okenvp_b_complete; exact H.
    + (* C_prim_refl *) simpl. destruct (eq_dec n n) as [E|Hne]; [| exfalso; apply Hne; reflexivity].
      apply andb_true_iff. split.
      * apply okenvp_b_complete; exact H.
      * apply wft_b_complete; exact H0.
    + (* C_prim_neq *) simpl.
      destruct (eq_dec n1 n2) as [E|Hnm].
      * subst n2. apply andb_true_iff. split.
        -- apply okenvp_b_complete; exact H.
        -- apply wft_b_complete. eapply wft_weaken_cons.
           apply (cmp_wft_src_prim PG (t_prim n1) n1 H1).
      * destruct (eq_dec i0 n1) as [Eh|Ehn].
        -- exfalso. apply H0. exact Eh.
        -- apply andb_true_iff. split.
           ++ apply okenvp_b_complete; exact H.
           ++ apply (IH PG (t_prim n1) (t_prim n2)).
              ** simpl in *. lia.
              ** apply (okenv_tail i0 A PG). exact H.
              ** apply OU_prim.
              ** apply OI_prim.
              ** apply (cmp_wft_src_prim PG (t_prim n1) n2). exact H1.
              ** apply (cmp_wft_target_prim PG (t_prim n1) n2). exact H1.
              ** exact H1.
    + (* C_prim_eq *) simpl.
      destruct (eq_dec n1 n2) as [E|Hnm].
      * subst n2. apply andb_true_iff. split.
        -- apply okenvp_b_complete; exact H.
        -- apply wft_b_complete. apply wft_prim with (A := t_prim j).
           unfold binds. simpl. auto.
      * destruct (eq_dec n1 n1) as [E|Hne]; [| exfalso; apply Hne; reflexivity].
        apply andb_true_iff. split.
        -- apply okenvp_b_complete; exact H.
        -- apply (IH PG (t_prim j) (t_prim n2)).
           ++ simpl in *. lia.
           ++ apply (okenv_tail n1 (t_prim j) PG). exact H.
           ++ apply OU_prim.
           ++ apply OI_prim.
           ++ apply (cmp_wft_src_prim PG (t_prim j) n2). exact H0.
           ++ apply (cmp_wft_target_prim PG (t_prim j) n2). exact H0.
           ++ exact H0.
Qed.


Lemma sle_U_app_l : forall G A B C b,
  U A = U B ++ U C -> sle G A b -> sle G B b.
Proof.
  intros G A B C b EU HA. unfold sle in *. intros u Hu j Hj.
  apply (HA u); [|exact Hj]. rewrite EU. apply in_or_app. left. exact Hu.
Qed.
Lemma sle_U_app_r : forall G A B C b,
  U A = U B ++ U C -> sle G A b -> sle G C b.
Proof.
  intros G A B C b EU HA. unfold sle in *. intros u Hu j Hj.
  apply (HA u); [|exact Hj]. rewrite EU. apply in_or_app. right. exact Hu.
Qed.

Lemma sle_lift_or_l : forall G C b1 b2,
  ordi b1 -> ordi b2 -> wft G b1 -> wft G b2 ->
  sle G C b1 -> sle G C (t_union b1 b2).
Proof.
  intros G C b1 b2 O1 O2 W1 W2 HC. unfold sle in *.
  intros u Hu j Hj.
  rewrite (I_ordi_singleton (t_union b1 b2) (OI_or b1 b2 O1 O2)) in Hj.
  apply (In_singleton_typ j (t_union b1 b2)) in Hj. subst j.
  apply C_or_l; [exact W2|].
  apply (HC u Hu b1).
  rewrite (I_ordi_singleton b1 O1). simpl. auto.
Qed.
Lemma sle_lift_or_r : forall G C b1 b2,
  ordi b1 -> ordi b2 -> wft G b1 -> wft G b2 ->
  sle G C b2 -> sle G C (t_union b1 b2).
Proof.
  intros G C b1 b2 O1 O2 W1 W2 HC. unfold sle in *.
  intros u Hu j Hj.
  rewrite (I_ordi_singleton (t_union b1 b2) (OI_or b1 b2 O1 O2)) in Hj.
  apply (In_singleton_typ j (t_union b1 b2)) in Hj. subst j.
  apply C_or_r; [exact W1|].
  apply (HC u Hu b2).
  rewrite (I_ordi_singleton b2 O2). simpl. auto.
Qed.

Lemma sle_top_any : forall G C,
  okenvp G -> wft G C -> sle G C t_top.
Proof.
  intros G C Ho WC. unfold sle. intros u Hu j Hj.
  rewrite (I_ordi_singleton t_top OI_top) in Hj.
  apply (In_singleton_typ j t_top) in Hj. subst j.
  apply C_top; [exact Ho|apply (U_wft G C u WC Hu)].
Qed.

Lemma cmp_and_split_ordi : forall n G u v b,
  ordi b -> size_typ b <= n -> cmp G (t_and u v) b -> cmp G u b \/ cmp G v b.
Proof.
  induction n as [|n IH].
  - intros. pose proof (size_pos b). lia.
  - intros G u v b Ob Hn Hc.
    destruct b as [| | | X Y | X Y | X Y | | p].
    + (* int *) inversion Hc; subst; try discriminate.
      all: try (left; eassumption).
      all: try (right; eassumption).
      all: try (match goal with |- ?G => idtac "INT:" G end).
    + (* top *) inversion Hc; subst; try discriminate.
      all: try (left; eassumption).
      all: try (right; eassumption).
      all: try (left; apply C_top; [eassumption|]).
      all: try (left; apply C_top; [eassumption|]);
           try (match goal with Hw : wft ?GG (t_and ?UU ?VV) |- wft ?GG ?UU =>
                  exact (proj1 (wft_inv_and GG UU VV Hw)) end).
    + (* bot *) inversion Hc; subst; try discriminate.
      all: try (left; eassumption).
      all: try (right; eassumption).
    + (* arrow *) inversion Hc; subst; try discriminate.
      all: try (left; eassumption).
      all: try (right; eassumption).
    + (* union X Y *) inversion Hc; subst; try discriminate.
      all: try (left; eassumption).
      all: try (right; eassumption).
      * (* C_or_l *) destruct (ordi_inv_or X Y Ob) as [OX OY].
        assert (R : cmp G u X \/ cmp G v X).
        { apply (IH G u v X OX); [simpl in *; lia | assumption]. }
        destruct R as [Hu|Hv].
        -- left. apply C_or_l; [assumption|exact Hu].
        -- right. apply C_or_l; [assumption|exact Hv].
      * (* C_or_r *) destruct (ordi_inv_or X Y Ob) as [OX OY].
        assert (R : cmp G u Y \/ cmp G v Y).
        { apply (IH G u v Y OY); [simpl in *; lia | assumption]. }
        destruct R as [Hu|Hv].
        -- left. apply C_or_r; [assumption|exact Hu].
        -- right. apply C_or_r; [assumption|exact Hv].
    + (* and: not ordi *) exfalso. inversion Ob.
    + (* unit *) inversion Hc; subst; try discriminate.
      all: try (left; eassumption).
      all: try (right; eassumption).
    + (* prim *) inversion Hc; subst; try discriminate.
      all: try (left; eassumption).
      all: try (right; eassumption).
Qed.

Lemma matrix_lem : forall G (LA LC:list typ) b,
  okenvp G -> wft G b -> ordi b ->
  (forall u, In u LA -> ordu u) ->
  (forall u, In u LA -> wft G u) ->
  (forall v, In v LC -> ordu v) ->
  (forall v, In v LC -> wft G v) ->
  (forall u, In u LA -> forall v, In v LC -> cmp G (t_and u v) b) ->
  (forall u, In u LA -> cmp G u b) \/ (forall v, In v LC -> cmp G v b).
Proof.
  intros G LA LC b Ho Wb Ob OLA WLA OLC WLC H.
  destruct (allb_typ (fun u => cdec (size_envp G + size_typ u + size_typ b) G u b) LA) eqn:E.
  - left. intros u Hu.
    apply (cdec_sound (size_envp G + size_typ u + size_typ b) G u b).
    apply (allb_true (fun u => cdec (size_envp G + size_typ u + size_typ b) G u b) LA E u Hu).
  - right. intros v Hv.
    destruct (allb_false_exists (fun u => cdec (size_envp G + size_typ u + size_typ b) G u b) LA E) as [u [Hu Hfu]].
    assert (Hbad : ~ cmp G u b).
    { intro Hc.
      assert (Htrue : cdec (size_envp G + size_typ u + size_typ b) G u b = true).
      { exact (cdec_complete (size_envp G + size_typ u + size_typ b) G u b
                 (Nat.le_refl _) Ho (OLA u Hu) Ob (WLA u Hu) Wb Hc). }
      rewrite Hfu in Htrue. discriminate. }
    destruct (cmp_and_split_ordi (size_typ b) G u v b Ob (Nat.le_refl _) (H u Hu v Hv)) as [Hc|Hc].
    + contradiction.
    + exact Hc.
Qed.

Lemma cmp_all_to_sle : forall G X b,
  ordi b -> (forall u, In u (U X) -> cmp G u b) -> sle G X b.
Proof.
  intros G X b Ob H. unfold sle. intros u Hu j Hj.
  rewrite (In_I_ordi' b j Ob Hj). apply H. exact Hu.
Qed.

Lemma mp_aux : forall n G B b,
  size_typ B + size_typ b <= n ->
  okenvp G -> wft G B -> wft G b -> ordi b ->
  sle G B b -> exists C, In C (I B) /\ sle G C b.
Proof.
  induction n as [|n IH].
  - intros. pose proof (size_pos B). pose proof (size_pos b). lia.
  - intros G B b Hn Ho WB Wb Ob HB.
    destruct (ordu_or_splu B) as [OB | [B1 [B2 Hspl]]].
    + (* B ordu *)
      assert (EUB : U B = [B]) by (apply U_ordu_singleton; auto).
      assert (HBc : cmp G B b).
      { unfold sle in HB. specialize (HB B).
        apply HB; [rewrite EUB; simpl; auto|].
        rewrite (I_ordi_singleton b Ob); simpl; auto. }
      destruct (ordi_or_spli B) as [OiB | [Z1 [Z2 HsplB]]].
      * (* B ordi *) exists B. split.
        -- rewrite (I_ordi_singleton B OiB). simpl. auto.
        -- unfold sle. intros u Hu j Hj.
           rewrite (I_ordi_singleton b Ob) in Hj.
           apply (In_singleton_typ j b) in Hj. subst j.
           rewrite (U_ordu_singleton B OB) in Hu.
           apply (In_singleton_typ u B) in Hu. subst u.
           exact HBc.
      * (* B ordu, not ordi *)
        assert (HnO : ~ ordi B).
        { intro Hord. apply ordi_spli_opt_None in Hord. apply spli_opt_complete in HsplB.
          rewrite HsplB in Hord. discriminate. }
        destruct B as [| | | X Y | X Y | X Y | | p].
        -- exfalso. apply HnO. apply OI_int.
        -- exfalso. apply HnO. apply OI_top.
        -- exfalso. apply HnO. apply OI_bot.
        -- (* arrow X Y *) inversion HBc; subst; clear HBc; try discriminate.
           ++ (* C_top *) destruct (I_nonempty (t_arrow X Y)) as [C HC].
              exists C. split; [exact HC|].
              apply sle_top_any; [exact Ho|].
              apply (I_wft G (t_arrow X Y) C WB HC).
           ++ (* C_or_l *)
              destruct (ordi_inv_or i1 i2 Ob) as [O1 O2].
              destruct (wft_inv_or G i1 i2 Wb) as [W1 W2].
              assert (E1 : exists C, In C (I (t_arrow X Y)) /\ sle G C i1).
              { apply (IH G (t_arrow X Y) i1); [simpl in *; lia | exact Ho | exact WB | exact W1 | exact O1 | apply (proj2 (sle_cmp_ordi G (t_arrow X Y) i1 OB O1)); exact H0]. }
              destruct E1 as [C [HC Hs]].
              exists C. split; [exact HC|].
              apply (sle_lift_or_l G C i1 i2 O1 O2 W1 W2 Hs).
           ++ (* C_or_r *)
              destruct (ordi_inv_or i1 i2 Ob) as [O1 O2].
              destruct (wft_inv_or G i1 i2 Wb) as [W1 W2].
              assert (E2 : exists C, In C (I (t_arrow X Y)) /\ sle G C i2).
              { apply (IH G (t_arrow X Y) i2); [simpl in *; lia | exact Ho | exact WB | exact W2 | exact O2 | apply (proj2 (sle_cmp_ordi G (t_arrow X Y) i2 OB O2)); exact H0]. }
              destruct E2 as [C [HC Hs]].
              exists C. split; [exact HC|].
              apply (sle_lift_or_r G C i1 i2 O1 O2 W1 W2 Hs).
           ++ (* C_arrow *)
              assert (Hdom : sle G b1 X) by assumption.
              assert (Hcod : sle G Y b2) by assumption.
              destruct (ordi_inv_arrow b1 b2 Ob) as [Od1 Od2].
              destruct (wft_inv_arrow G b1 b2 Wb) as [Wd1 Wd2].
              destruct (wft_inv_arrow G X Y WB) as [WX WY].
              assert (JPX : exists P, In P (U X) /\ sle G b1 P).
              { apply (U_split G b1 X Ho Od1 Wd1 WX Hdom). }
              destruct JPX as [P [HP HsP]].
              assert (MPY : exists C, In C (I Y) /\ sle G C b2).
              { apply (IH G Y b2); [simpl in *; lia | exact Ho | exact WY | exact Wd2 | exact Od2 | exact Hcod]. }
              destruct MPY as [C [HC HsC]].
              assert (HK : In (t_arrow P C) (I (t_arrow X Y)))
                by (apply (I_arrow_decomp X Y P C HP HC)).
              exists (t_arrow P C). split; [exact HK|].
              apply (proj2 (sle_cmp_ordi G (t_arrow P C) (t_arrow b1 b2)
                             (OU_arrow P C) (OI_arrow b1 b2 Od1 Od2))).
              apply C_arrow; assumption.
        -- (* union X Y *) exfalso. inversion OB.
        -- (* and X Y *)
           destruct (wft_inv_and G X Y WB) as [WX WY].
           assert (Hmat : forall u, In u (U X) -> forall v, In v (U Y) -> cmp G (t_and u v) b).
           { intros u Hu v Hv. apply HB.
             apply (U_and_pair X Y u v Hu Hv).
             rewrite (I_ordi_singleton b Ob). simpl. auto. }
           destruct (matrix_lem G (U X) (U Y) b Ho Wb Ob (fun u Hu => U_ordu X u Hu) (fun u Hu => U_wft G X u WX Hu) (fun v Hv => U_ordu Y v Hv) (fun v Hv => U_wft G Y v WY Hv) Hmat) as [HX|HY].
           ++ assert (E1 : exists C, In C (I X) /\ sle G C b).
              { apply (IH G X b); [simpl in *; lia | exact Ho | exact WX | exact Wb | exact Ob | apply (cmp_all_to_sle G X b Ob); exact HX]. }
              destruct E1 as [C [HC Hs]].
              exists C. split; [|exact Hs].
              assert (EI : I (t_and X Y) = I X ++ I Y)
                by (apply I_step; apply spli_opt_complete; apply SpI_and).
              rewrite EI. apply in_or_app. left. exact HC.
           ++ assert (E2 : exists C, In C (I Y) /\ sle G C b).
              { apply (IH G Y b); [simpl in *; lia | exact Ho | exact WY | exact Wb | exact Ob | apply (cmp_all_to_sle G Y b Ob); exact HY]. }
              destruct E2 as [C [HC Hs]].
              exists C. split; [|exact Hs].
              assert (EI : I (t_and X Y) = I X ++ I Y)
                by (apply I_step; apply spli_opt_complete; apply SpI_and).
              rewrite EI. apply in_or_app. right. exact HC.
        -- exfalso. apply HnO. apply OI_null.
        -- exfalso. apply HnO. apply OI_prim.
    + (* B not ordu *)
      assert (Hsplopt : splu_opt B = Some (B1,B2)) by (apply splu_opt_complete; auto).
      assert (EUB : U B = U B1 ++ U B2) by (apply U_step; auto).
      assert (HB1 : sle G B1 b) by (apply (sle_U_app_l _ _ _ _ _ EUB); exact HB).
      assert (HB2 : sle G B2 b) by (apply (sle_U_app_r _ _ _ _ _ EUB); exact HB).
      destruct (splu_wft G B B1 B2 Hspl WB) as [W1 W2].
      destruct B as [| | | X Y | X Y | X Y | | p].
      * exfalso. inversion Hspl.
      * exfalso. inversion Hspl.
      * exfalso. inversion Hspl.
      * exfalso. inversion Hspl.
      * (* union X Y *)
        apply splu_inv_union in Hspl as [E1 E2]. subst B1 B2.
        destruct (wft_inv_or G X Y WB) as [WX WY].
        assert (EX : exists C, In C (I X) /\ sle G C b).
        { apply (IH G X b); [simpl in *; lia | exact Ho | exact WX | exact Wb | exact Ob | exact HB1]. }
        destruct EX as [d [Hd Hsd]].
        assert (EY : exists C, In C (I Y) /\ sle G C b).
        { apply (IH G Y b); [simpl in *; lia | exact Ho | exact WY | exact Wb | exact Ob | exact HB2]. }
        destruct EY as [e [He Hse]].
        exists (t_union d e). split.
        -- apply (I_union_pair X Y d e Hd He).
        -- assert (EU : U (t_union d e) = U d ++ U e)
             by (apply U_step; apply splu_opt_complete; apply SpU_or).
           unfold sle in *. intros u Hu j Hj.
           rewrite EU in Hu. apply in_app_or in Hu. destruct Hu as [Hu|Hu].
           ++ apply (Hsd u Hu j Hj).
           ++ apply (Hse u Hu j Hj).
      * (* and X Y *)
        destruct (wft_inv_and G X Y WB) as [WX WY].
        assert (Hmat : forall u, In u (U X) -> forall v, In v (U Y) -> cmp G (t_and u v) b).
        { intros u Hu v Hv. apply HB.
          apply (U_and_pair X Y u v Hu Hv).
          rewrite (I_ordi_singleton b Ob). simpl. auto. }
        destruct (matrix_lem G (U X) (U Y) b Ho Wb Ob (fun u Hu => U_ordu X u Hu) (fun u Hu => U_wft G X u WX Hu) (fun v Hv => U_ordu Y v Hv) (fun v Hv => U_wft G Y v WY Hv) Hmat) as [HX|HY].
        -- assert (EX : exists C, In C (I X) /\ sle G C b).
           { apply (IH G X b); [simpl in *; lia | exact Ho | exact WX | exact Wb | exact Ob | apply (cmp_all_to_sle G X b Ob); exact HX]. }
           destruct EX as [C [HC Hs]].
           exists C. split; [|exact Hs].
           assert (EI : I (t_and X Y) = I X ++ I Y)
             by (apply I_step; apply spli_opt_complete; apply SpI_and).
           rewrite EI. apply in_or_app. left. exact HC.
        -- assert (EY : exists C, In C (I Y) /\ sle G C b).
           { apply (IH G Y b); [simpl in *; lia | exact Ho | exact WY | exact Wb | exact Ob | apply (cmp_all_to_sle G Y b Ob); exact HY]. }
           destruct EY as [C [HC Hs]].
           exists C. split; [|exact Hs].
           assert (EI : I (t_and X Y) = I X ++ I Y)
             by (apply I_step; apply spli_opt_complete; apply SpI_and).
           rewrite EI. apply in_or_app. right. exact HC.
      * exfalso. inversion Hspl.
      * exfalso. inversion Hspl.
Qed.

Lemma mp : forall G B b,
  okenvp G -> wft G B -> wft G b -> ordi b ->
  sle G B b -> exists C, In C (I B) /\ sle G C b.
Proof. intros. eapply mp_aux; eauto. Qed.


Lemma sle_from_I : forall G u B,
  ordu u -> (forall j, In j (I B) -> cmp G u j) -> sle G u B.
Proof.
  intros G u B Hu H. unfold sle. intros a Ha j Hj.
  rewrite (In_U_ordu' u a Hu Ha). apply H. exact Hj.
Qed.
Lemma sle_from_U : forall G B i,
  ordi i -> (forall w, In w (U B) -> cmp G w i) -> sle G B i.
Proof.
  intros G B i Hi H. unfold sle. intros w Hw j Hj.
  rewrite (In_I_ordi' i j Hi Hj). apply H. exact Hw.
Qed.
Lemma sle_to_I : forall G u B,
  ordu u -> sle G u B -> forall j, In j (I B) -> cmp G u j.
Proof.
  intros G u B Hu H j Hj.
  assert (Ha : In u (U u)) by (rewrite U_ordu_singleton; auto; simpl; auto).
  exact (H u Ha j Hj).
Qed.
Lemma sle_to_U : forall G B i,
  ordi i -> sle G B i -> forall w, In w (U B) -> cmp G w i.
Proof.
  intros G B i Hi H w Hw.
  assert (Hj : In i (I i)) by (rewrite I_ordi_singleton; auto; simpl; auto).
  exact (H w Hw i Hj).
Qed.

Lemma I_lt_of_not_ordi : forall B C,
  ~ ordi B -> In C (I B) -> size_typ C < size_typ B.
Proof.
  intros B C HnO HC.
  destruct (ordi_or_spli B) as [H| [B1 [B2 Hs]]]; [contradiction|].
  assert (Hsopt : spli_opt B = Some (B1,B2)) by (apply spli_opt_complete; auto).
  assert (EI : I B = I B1 ++ I B2) by (apply I_step; auto).
  rewrite EI in HC. apply in_app_or in HC. destruct HC as [HC|HC].
  - apply I_size in HC. apply spli_size in Hs. destruct Hs. lia.
  - apply I_size in HC. apply spli_size in Hs. destruct Hs. lia.
Qed.

Lemma bridge_aux : forall n G B u i,
  size_typ B <= n ->
  okenvp G -> wft G B -> ordu u -> ordi i -> wft G u -> wft G i ->
  (forall j, In j (I B) -> cmp G u j) ->
  (forall w, In w (U B) -> cmp G w i) -> cmp G u i.
Proof.
  induction n as [|n IH].
  - intros. pose proof (size_pos B). lia.
  - intros G B u i Hn Ho WB Hu Hi Wu Wi H1 H2.
    destruct (ordu_or_splu B) as [OB | [B1 [B2 Hspl]]].
    + (* B ordu *)
      assert (EUB : U B = [B]) by (apply U_ordu_singleton; auto).
      assert (HBsle : sle G B i) by (apply (sle_from_U G B i Hi); exact H2).
      assert (HBc : cmp G B i).
      { apply (sle_to_U G B i Hi HBsle B). rewrite EUB. simpl. auto. }
      destruct (ordi_or_spli B) as [OiB | [Z1 [Z2 HsplB]]].
      * (* B ordi *)
        destruct B as [| | | X Y | X Y | X Y | | p].
        -- (* int *) apply (B_int G u i Hu Hi WB Wu Wi H1 H2).
        -- (* top *) apply (B_top G u i Hu Hi WB Wu Wi H1 H2).
        -- (* bot *) apply (B_bot G u i Hu Hi WB Wu Wi H1 H2).
        -- (* arrow X Y *)
           assert (BcX : forall u0 i0,
             ordu u0 -> ordi i0 -> wft G X -> wft G u0 -> wft G i0 ->
             (forall j, In j (I X) -> cmp G u0 j) ->
             (forall w, In w (U X) -> cmp G w i0) -> cmp G u0 i0).
           { intros u0 i0 Hu0 Hi0 WX Wu0 Wi0 H1x H2x.
             apply (IH G X u0 i0); [simpl in *; lia | exact Ho | exact WX | exact Hu0 | exact Hi0 | exact Wu0 | exact Wi0 | exact H1x | exact H2x]. }
           assert (BcY : forall u0 i0,
             ordu u0 -> ordi i0 -> wft G Y -> wft G u0 -> wft G i0 ->
             (forall j, In j (I Y) -> cmp G u0 j) ->
             (forall w, In w (U Y) -> cmp G w i0) -> cmp G u0 i0).
           { intros u0 i0 Hu0 Hi0 WY Wu0 Wi0 H1y H2y.
             apply (IH G Y u0 i0); [simpl in *; lia | exact Ho | exact WY | exact Hu0 | exact Hi0 | exact Wu0 | exact Wi0 | exact H1y | exact H2y]. }
           exact (B_arrow G X Y u i BcX BcY Hu Hi OiB WB Wu Wi H1 H2).
        -- (* union *) inversion OB.
        -- (* and *) inversion OiB.
        -- (* unit *) apply (B_unit G u i Hu Hi WB Wu Wi H1 H2).
        -- (* prim p *) apply (B_prim G p u i Hu Hi WB Wu Wi H1 H2).
      * (* B ordu, not ordi *)
        assert (HnO : ~ ordi B).
        { intro Hord. apply ordi_spli_opt_None in Hord. apply spli_opt_complete in HsplB.
          rewrite HsplB in Hord. discriminate. }
        assert (E : exists C, In C (I B) /\ sle G C i)
          by (apply (mp G B i Ho WB Wi Hi HBsle)).
        destruct E as [C [HC HsCi]].
        assert (HClt : size_typ C < size_typ B).
        { apply (I_lt_of_not_ordi B C); [exact HnO | exact HC]. }
        assert (HuC : cmp G u C) by (apply H1; exact HC).
        assert (H1' : forall j, In j (I C) -> cmp G u j).
        { intros j Hj. rewrite (In_I_ordi' C j (I_ordi B C HC) Hj). exact HuC. }
        assert (H2' : forall w, In w (U C) -> cmp G w i).
        { intros w Hw. apply (HsCi w Hw i). rewrite (I_ordi_singleton i Hi). simpl. auto. }
        apply (IH G C u i); [lia | exact Ho | apply (I_wft G B C WB HC) | exact Hu | exact Hi | exact Wu | exact Wi | exact H1' | exact H2'].
    + (* B not ordu *)
      assert (Hsplopt : splu_opt B = Some (B1,B2)) by (apply splu_opt_complete; auto).
      assert (EUB : U B = U B1 ++ U B2) by (apply U_step; auto).
      assert (W1W2 := splu_wft G B B1 B2 Hspl WB).
      destruct W1W2 as [W1 W2].
      assert (Hsizes := splu_size B B1 B2 Hspl). destruct Hsizes as [Hs1 Hs2].
      assert (HBsle : sle G u B) by (apply (sle_from_I G u B Hu); exact H1).
      destruct (splu_split G u B B1 B2 Ho Hu Wu WB Hspl HBsle) as [HsB1|HsB2].
      * assert (H2B1 : forall w, In w (U B1) -> cmp G w i).
        { intros w Hw. apply H2. rewrite EUB. apply in_or_app. left. exact Hw. }
        assert (H2sle : sle G B1 i) by (apply (sle_from_U G B1 i Hi); exact H2B1).
        apply (IH G B1 u i); [lia | exact Ho | exact W1 | exact Hu | exact Hi | exact Wu | exact Wi | apply (sle_to_I G u B1 Hu); exact HsB1 | apply (sle_to_U G B1 i Hi); exact H2sle].
      * assert (H2B2 : forall w, In w (U B2) -> cmp G w i).
        { intros w Hw. apply H2. rewrite EUB. apply in_or_app. right. exact Hw. }
        assert (H2sle : sle G B2 i) by (apply (sle_from_U G B2 i Hi); exact H2B2).
        apply (IH G B2 u i); [lia | exact Ho | exact W2 | exact Hu | exact Hi | exact Wu | exact Wi | apply (sle_to_I G u B2 Hu); exact HsB2 | apply (sle_to_U G B2 i Hi); exact H2sle].
Qed.

Lemma bridge : forall G B u i,
  okenvp G -> wft G B -> ordu u -> ordi i -> wft G u -> wft G i ->
  (forall j, In j (I B) -> cmp G u j) ->
  (forall w, In w (U B) -> cmp G w i) -> cmp G u i.
Proof.
  intros. apply (bridge_aux (size_typ B) G B u i); try lia; auto.
Qed.


Lemma wft_prim_tail : forall i A G n,
  wft ((i,A)::G) (t_prim n) -> i <> n -> wft G (t_prim n).
Proof.
  intros i A G n H Hne.
  apply wft_prim_binds in H. destruct H as [B HB].
  unfold binds in HB. simpl in HB. destruct HB as [Heq|HB].
  - inversion Heq. subst. exfalso. apply Hne. reflexivity.
  - apply wft_prim with (A:=B). exact HB.
Qed.

Lemma spli_ordu_components : forall u A1 A2,
  ordu u -> spli u A1 A2 -> ordu A1 /\ ordu A2.
Proof.
  intros u A1 A2 Hu Hsp. destruct Hsp.
  - apply ordu_inv_and; auto.
  - split; apply OU_arrow.
  - split; apply OU_arrow.
  - inversion Hu.
  - inversion Hu.
Qed.

Lemma asub_to_cmp_oi_aux : forall n G u i,
  size_envp G + size_typ u + size_typ i <= n ->
  ordu u -> ordi i -> wft G u -> wft G i -> algo_sub G u i -> cmp G u i.
Proof.
  induction n as [|n IH].
  - intros G u i Hn. pose proof (size_pos u). pose proof (size_pos i). lia.
  - intros G u i Hn Hu Hi Wu Wi Hsub.
    assert (Ho : okenvp G) by (apply (proj1 (asub_regular G u i Hsub))).
    inversion Hsub; subst; clear Hsub.
    + (* AS_refl *)
      match goal with
      | Hok : okenvp ?G, W : wft ?G ?A |- cmp ?G ?A ?A =>
          let R := fresh "R" in
          pose proof (sle_refl G A Hok W) as R;
          assert (HuU : In A (U A)) by (rewrite U_ordu_singleton; auto; simpl; auto);
          assert (HiI : In A (I A)) by (rewrite I_ordi_singleton; auto; simpl; auto);
          unfold sle in R; exact (R A HuU A HiI)
      end.
    + (* AS_prim_neq *) apply C_prim_neq; [exact H|exact H0|].
      assert (Hreg := asub_regular PG (t_prim n1) (t_prim n2) H1).
      destruct Hreg as [Ho' [Wu' Wi']].
      apply (IH PG (t_prim n1) (t_prim n2)).
      * simpl in *; lia.
      * apply OU_prim.
      * apply OI_prim.
      * exact Wu'.
      * exact Wi'.
      * exact H1.
    + (* AS_prim_eq *) apply C_prim_eq; [exact H|].
      assert (Hreg := asub_regular PG (t_prim j) (t_prim n2) H0).
      destruct Hreg as [Ho' [Wu' Wi']].
      apply (IH PG (t_prim j) (t_prim n2)).
      * simpl in *; lia.
      * apply OU_prim.
      * apply OI_prim.
      * exact Wu'.
      * exact Wi'.
      * exact H0.
    + (* AS_top *) apply C_top; auto.
    + (* AS_bot *) apply C_bot; auto.
    + (* AS_arrow *)
      assert (Hord := ordi_inv_arrow B1 B2 Hi). destruct Hord as [OB1 OiB2].
      assert (WA := Wu). apply wft_inv_arrow in WA as [WA1 WA2].
      assert (WB := Wi). apply wft_inv_arrow in WB as [WB1 WB2].
      apply C_arrow.
      * intros u0 Hu0 j Hj.
        assert (Hsu : algo_sub G u0 A1) by (eapply asub_source_U; eauto).
        assert (Hsj : algo_sub G u0 j) by (eapply asub_target_I; eauto).
        apply (IH G u0 j).
        -- apply U_size in Hu0. apply I_size in Hj. simpl in *. lia.
        -- apply (U_ordu B1 u0 Hu0).
        -- apply (I_ordi A1 j Hj).
        -- apply (U_wft G B1 u0 WB1 Hu0).
        -- apply (I_wft G A1 j WA1 Hj).
        -- exact Hsj.
      * intros u0 Hu0 j Hj.
        assert (Hsu : algo_sub G u0 B2) by (eapply asub_source_U; eauto).
        assert (Hsj : algo_sub G u0 j) by (eapply asub_target_I; eauto).
        apply (IH G u0 j).
        -- apply U_size in Hu0. apply I_size in Hj. simpl in *. lia.
        -- apply (U_ordu A2 u0 Hu0).
        -- apply (I_ordi B2 j Hj).
        -- apply (U_wft G A2 u0 WA2 Hu0).
        -- apply (I_wft G B2 j WB2 Hj).
        -- exact Hsj.
    + (* AS_and: target spli, impossible because target ordi *)
      exfalso. apply ordi_spli_opt_None in Hi. apply spli_opt_complete in H. rewrite H in Hi. discriminate.
    + (* AS_andl *)
      destruct (spli_ordu_components u A1 A2 Hu H0) as [OA1 OA2].
      destruct (spli_wft G u A1 A2 H0 Wu) as [WA1 WA2].
      destruct (spli_size u A1 A2 H0) as [HsA1 HsA2].
      assert (Hc1 : cmp G A1 i).
      { apply (IH G A1 i); [simpl in *; lia | exact OA1 | exact Hi | exact WA1 | exact Wi | exact H1]. }
      assert (H1sle : sle G u A1).
      { unfold sle. intros a Ha j Hj.
        assert (Ea : a = u) by (apply (In_U_ordu' u a Hu Ha)). subst a.
        assert (R := sle_refl G u Ho Wu). unfold sle in R.
        assert (HuU : In u (U u)) by (rewrite U_ordu_singleton; auto; simpl; auto).
        assert (EI : I u = I A1 ++ I A2) by (apply I_step; apply spli_opt_complete; auto).
        assert (HjU : In j (I u)) by (rewrite EI; apply in_or_app; left; exact Hj).
        exact (R u HuU j HjU). }
      assert (H2sle : sle G A1 i)
        by (apply (proj2 (sle_cmp_ordi G A1 i OA1 Hi)); exact Hc1).
      assert (H1B : forall j, In j (I A1) -> cmp G u j)
        by (apply (sle_to_I G u A1 Hu); exact H1sle).
      assert (H2B : forall w, In w (U A1) -> cmp G w i)
        by (apply (sle_to_U G A1 i Hi); exact H2sle).
      apply (bridge G A1 u i Ho WA1 Hu Hi Wu Wi H1B H2B).
    + (* AS_andr *)
      destruct (spli_ordu_components u A1 A2 Hu H0) as [OA1 OA2].
      destruct (spli_wft G u A1 A2 H0 Wu) as [WA1 WA2].
      destruct (spli_size u A1 A2 H0) as [HsA1 HsA2].
      assert (Hc2 : cmp G A2 i).
      { apply (IH G A2 i); [simpl in *; lia | exact OA2 | exact Hi | exact WA2 | exact Wi | exact H1]. }
      assert (H2sle0 : sle G u A2).
      { unfold sle. intros a Ha j Hj.
        assert (Ea : a = u) by (apply (In_U_ordu' u a Hu Ha)). subst a.
        assert (R := sle_refl G u Ho Wu). unfold sle in R.
        assert (HuU : In u (U u)) by (rewrite U_ordu_singleton; auto; simpl; auto).
        assert (EI : I u = I A1 ++ I A2) by (apply I_step; apply spli_opt_complete; auto).
        assert (HjU : In j (I u)) by (rewrite EI; apply in_or_app; right; exact Hj).
        exact (R u HuU j HjU). }
      assert (H2sle : sle G A2 i)
        by (apply (proj2 (sle_cmp_ordi G A2 i OA2 Hi)); exact Hc2).
      assert (H1B : forall j, In j (I A2) -> cmp G u j)
        by (apply (sle_to_I G u A2 Hu); exact H2sle0).
      assert (H2B : forall w, In w (U A2) -> cmp G w i)
        by (apply (sle_to_U G A2 i Hi); exact H2sle).
      apply (bridge G A2 u i Ho WA2 Hu Hi Wu Wi H1B H2B).
    + (* AS_or: source splu, impossible because source ordu *)
      exfalso. apply ordu_splu_opt_None in Hu. apply splu_opt_complete in H. rewrite H in Hu. discriminate.
    + (* AS_orl *)
      destruct H0 as [X Y | X Y X1 X2 Hspl | X Y Y1 Y2 HOrd Hspl].
      * (* SpU_or X Y *)         destruct (ordi_inv_or X Y Hi) as [Oi1 Oi2].
        destruct (splu_wft G (t_union X Y) X Y (SpU_or X Y) Wi) as [WX WY].
        assert (Hc1 : cmp G u X).
        { apply (IH G u X); [simpl in *; lia | exact Hu | exact Oi1 | exact Wu | exact WX | exact H1]. }
        apply C_or_l; [exact WY | exact Hc1].
      * (* SpU_andl *) inversion Hi.
      * (* SpU_andr *) inversion Hi.
    + (* AS_orr *)
      destruct H0 as [X Y | X Y X1 X2 Hspl | X Y Y1 Y2 HOrd Hspl].
      * (* SpU_or X Y *)         destruct (ordi_inv_or X Y Hi) as [Oi1 Oi2].
        destruct (splu_wft G (t_union X Y) X Y (SpU_or X Y) Wi) as [WX WY].
        assert (Hc2 : cmp G u Y).
        { apply (IH G u Y); [simpl in *; lia | exact Hu | exact Oi2 | exact Wu | exact WY | exact H1]. }
        apply C_or_r; [exact WX | exact Hc2].
      * (* SpU_andl *) inversion Hi.
      * (* SpU_andr *) inversion Hi.
Qed.

Lemma asub_to_cmp_oi : forall G u i,
  ordu u -> ordi i -> wft G u -> wft G i -> algo_sub G u i -> cmp G u i.
Proof. intros. eapply asub_to_cmp_oi_aux; eauto. Qed.


(* ============ Declarative regularity ============ *)

Lemma binds_wft : forall G i A, okenvp G -> binds i A G -> wft G A.
Proof.
  intros G. induction G as [|[h B] PG IHG]; intros i A Ho Hb.
  - simpl in Hb. destruct Hb.
  - simpl in Hb. destruct Hb as [Heq|Hin].
    + injection Heq as Hih HAB. subst i A.
      inversion Ho; subst.
      * (* head binding is t_top *)
        apply wft_weaken_cons; apply wft_top.
      * (* head binding is t_prim j; use okenvp_sub's wft premise *)
        apply wft_weaken_cons. assumption.
    + inversion Ho; subst; apply wft_weaken_cons; eapply IHG; eauto.
Qed.

Lemma dsub_regular : forall G A B,
  declarative_subtyping G A B -> okenvp G /\ wft G A /\ wft G B.
Proof.
  intros G A B H. induction H.
  - repeat split; auto.
  - destruct IHdeclarative_subtyping1 as [Ho [HA HM]].
    destruct IHdeclarative_subtyping2 as [_ [HM' HB]].
    repeat split; auto.
  - repeat split; auto; try constructor.
  - repeat split; auto; try constructor.
  - destruct IHdeclarative_subtyping1 as [Ho [HB HA]].
    destruct IHdeclarative_subtyping2 as [_ [HC HD]].
    repeat split; auto; apply wft_arrow; auto.
  - destruct IHdeclarative_subtyping1 as [Ho [HA HB]].
    destruct IHdeclarative_subtyping2 as [_ [HA' HC]].
    repeat split; auto; apply wft_and; auto.
  - repeat split; auto; apply wft_and; auto.
  - repeat split; auto; apply wft_and; auto.
  - destruct IHdeclarative_subtyping1 as [Ho [HA HC]].
    destruct IHdeclarative_subtyping2 as [_ [HB HC']].
    repeat split; auto; apply wft_or; auto.
  - repeat split; auto; apply wft_or; auto.
  - repeat split; auto; apply wft_or; auto.
  - repeat split; auto.
    + apply wft_and; apply wft_arrow; auto.
    + apply wft_arrow; [auto | apply wft_and; auto].
  - repeat split; auto.
    + apply wft_and; apply wft_arrow; auto.
    + apply wft_arrow; [apply wft_or; auto | auto].
  - repeat split; auto.
    + apply wft_and; apply wft_or; auto.
    + apply wft_or; [apply wft_and; auto | auto].
  - repeat split; auto.
    + apply wft_prim with (A := A); assumption.
    + eapply binds_wft; eauto.
Qed.

(* ============ DS_distArrU, generalized ============ *)

Lemma distArrU_gen : forall G A1 A2 B C,
  okenvp G -> wft G A1 -> wft G A2 -> wft G B -> wft G C ->
  algo_sub G B C ->
  algo_sub G (t_and (t_arrow A1 B) (t_arrow A2 B)) (t_arrow (t_union A1 A2) C).
Proof.
  intros G A1 A2 B C. remember (size_typ C) as n eqn:EC.
  revert C EC. induction n as [n IH] using lt_wf_ind.
  intros C EC Ho WA1 WA2 WB WC HBC.
  destruct (ordi_dec C) as [HCordi|HCnot].
  - assert (Hsp : spli (t_arrow (t_union A1 A2) C)
                       (t_arrow A1 C) (t_arrow A2 C)).
    { apply SpI_arrowUnion; auto. apply SpU_or. }
    apply AS_and with (B1 := t_arrow A1 C) (B2 := t_arrow A2 C).
    + exact Hsp.
    + eapply AS_andl with (A1 := t_arrow A1 B) (A2 := t_arrow A2 B).
      * apply wft_arrow; auto.
      * apply SpI_and.
      * apply AS_arrow with (A1 := A1) (A2 := B) (B1 := A1) (B2 := C).
        -- apply AS_refl; auto.
        -- exact HBC.
    + eapply AS_andr with (A1 := t_arrow A1 B) (A2 := t_arrow A2 B).
      * apply wft_arrow; auto.
      * apply SpI_and.
      * apply AS_arrow with (A1 := A2) (A2 := B) (B1 := A2) (B2 := C).
        -- apply AS_refl; auto.
        -- exact HBC.
  - destruct (ordi_or_spli C) as [HCordi'| [C1 [C2 Hsp]]]; [contradiction|].
    assert (Hsize1 : size_typ C1 < size_typ C).
    { apply spli_size in Hsp; tauto. }
    assert (Hsize2 : size_typ C2 < size_typ C).
    { apply spli_size in Hsp; tauto. }
    assert (Hwf := spli_wft G C C1 C2 Hsp WC). destruct Hwf as [WC1 WC2].
    assert (HBC1 : algo_sub G B C1).
    { apply asub_spli_proj with (P := C1) (Q := C2) in HBC; tauto. }
    assert (HBC2 : algo_sub G B C2).
    { apply asub_spli_proj with (P := C1) (Q := C2) in HBC; tauto. }
    assert (Htsp : spli (t_arrow (t_union A1 A2) C)
                         (t_arrow (t_union A1 A2) C1)
                         (t_arrow (t_union A1 A2) C2)).
    { apply SpI_arrow; exact Hsp. }
    apply AS_and with (B1 := t_arrow (t_union A1 A2) C1)
                      (B2 := t_arrow (t_union A1 A2) C2).
    + exact Htsp.
    + apply (IH (size_typ C1)); auto; lia.
    + apply (IH (size_typ C2)); auto; lia.
Qed.

Lemma distArrU_asub : forall G A1 A2 B,
  okenvp G -> wft G A1 -> wft G A2 -> wft G B ->
  algo_sub G (t_and (t_arrow A1 B) (t_arrow A2 B)) (t_arrow (t_union A1 A2) B).
Proof.
  intros. apply distArrU_gen with (C := B); auto.
  apply AS_refl; auto.
Qed.

(* ============ Direct algorithmic closure facts ============ *)

Lemma asub_and_intro : forall G A B C,
  algo_sub G A B -> algo_sub G A C -> algo_sub G A (t_and B C).
Proof.
  intros. apply AS_and with (B1 := B) (B2 := C).
  - apply SpI_and.
  - exact H.
  - exact H0.
Qed.

Lemma asub_andl : forall G A B,
  okenvp G -> wft G A -> wft G B -> algo_sub G (t_and A B) A.
Proof.
  intros. eapply AS_andl with (A1 := A) (A2 := B).
  - exact H1.
  - apply SpI_and.
  - apply AS_refl; auto.
Qed.

Lemma asub_andr : forall G A B,
  okenvp G -> wft G A -> wft G B -> algo_sub G (t_and A B) B.
Proof.
  intros. eapply AS_andr with (A1 := A) (A2 := B).
  - exact H0.
  - apply SpI_and.
  - apply AS_refl; auto.
Qed.

Lemma asub_or_intro : forall G A B C,
  algo_sub G A C -> algo_sub G B C -> algo_sub G (t_union A B) C.
Proof.
  intros. apply AS_or with (A1 := A) (A2 := B).
  - apply SpU_or.
  - exact H.
  - exact H0.
Qed.

Lemma asub_orl : forall G A B,
  okenvp G -> wft G A -> wft G B -> algo_sub G A (t_union A B).
Proof.
  intros. eapply AS_orl with (B1 := A) (B2 := B).
  - exact H1.
  - apply SpU_or.
  - apply AS_refl; auto.
Qed.

Lemma asub_orr : forall G A B,
  okenvp G -> wft G A -> wft G B -> algo_sub G B (t_union A B).
Proof.
  intros. eapply AS_orr with (B1 := A) (B2 := B).
  - exact H0.
  - apply SpU_or.
  - apply AS_refl; auto.
Qed.

Lemma asub_top : forall G A, okenvp G -> wft G A -> algo_sub G A t_top.
Proof. intros; apply AS_top; auto. Qed.
Lemma asub_bot : forall G A, okenvp G -> wft G A -> algo_sub G t_bot A.
Proof. intros; apply AS_bot; auto. Qed.
Lemma asub_arrow : forall G A B C D,
  algo_sub G B A -> algo_sub G C D -> algo_sub G (t_arrow A C) (t_arrow B D).
Proof. intros; eapply AS_arrow; eauto. Qed.

Lemma asub_refl : forall G A, okenvp G -> wft G A -> algo_sub G A A.
Proof. intros; apply AS_refl; auto. Qed.

(* DS_distArr *)
Lemma distArr_asub : forall G A B1 B2,
  okenvp G -> wft G A -> wft G B1 -> wft G B2 ->
  algo_sub G (t_and (t_arrow A B1) (t_arrow A B2)) (t_arrow A (t_and B1 B2)).
Proof.
  intros G A B1 B2 Ho WA WB1 WB2.
  assert (Htsp : spli (t_arrow A (t_and B1 B2)) (t_arrow A B1) (t_arrow A B2)).
  { apply SpI_arrow. apply SpI_and. }
  apply AS_and with (B1 := t_arrow A B1) (B2 := t_arrow A B2).
  - exact Htsp.
  - eapply AS_andl with (A1 := t_arrow A B1) (A2 := t_arrow A B2).
    + apply wft_arrow; auto.
    + apply SpI_and.
    + apply AS_refl; auto. apply wft_arrow; auto.
  - eapply AS_andr with (A1 := t_arrow A B1) (A2 := t_arrow A B2).
    + apply wft_arrow; auto.
    + apply SpI_and.
    + apply AS_refl; auto. apply wft_arrow; auto.
Qed.

(* ============ DS_distOr, under algorithmic transitivity ============ *)
Section ClosureTrans.
Variable asub_trans : forall G A B C,
  algo_sub G A B -> algo_sub G B C -> algo_sub G A C.

Lemma distOr_l : forall G A1 A2 B,
  okenvp G -> wft G A1 -> wft G A2 -> wft G B ->
  algo_sub G (t_and (t_union A1 B) (t_union A2 B)) (t_union (t_and A1 A2) B).
Proof.
  intros G A1 A2 B. remember (size_typ A1) as n eqn:EA.
  revert A1 EA. induction n as [n IH] using lt_wf_ind.
  intros A1 EA Ho WA1 WA2 WB.
  set (T := t_union (t_and A1 A2) B).
  assert (HC2 : algo_sub G (t_and B (t_union A2 B)) T).
  { eapply AS_andl with (A1 := B) (A2 := t_union A2 B).
    - apply wft_or; auto.
    - apply SpI_and.
    - eapply AS_orr with (B1 := t_and A1 A2) (B2 := B).
      + apply wft_and; auto.
      + apply SpU_or.
      + apply AS_refl; auto. }
  assert (HC1 : algo_sub G (t_and A1 (t_union A2 B)) T).
  { destruct (ordu_dec A1) as [Hord|Hnot].
    - assert (Hsp : splu (t_and A1 (t_union A2 B)) (t_and A1 A2) (t_and A1 B)).
      { eapply SpU_andr; [exact Hord | apply SpU_or]. }
      eapply AS_or with (A1 := t_and A1 A2) (A2 := t_and A1 B).
      + exact Hsp.
      + eapply AS_orl with (B1 := t_and A1 A2) (B2 := B).
        * exact WB.
        * apply SpU_or.
        * apply AS_refl; auto. apply wft_and; auto.
      + eapply AS_andr with (A1 := A1) (A2 := B).
        * exact WA1.
        * apply SpI_and.
        * eapply AS_orr with (B1 := t_and A1 A2) (B2 := B).
          -- apply wft_and; auto.
          -- apply SpU_or.
          -- apply AS_refl; auto.
    - destruct (ordu_or_splu A1) as [Hc|[P [Q HspA]]]; [contradiction|].
      assert (HPsize : size_typ P < size_typ A1) by (apply splu_size in HspA; tauto).
      assert (HQsize : size_typ Q < size_typ A1) by (apply splu_size in HspA; tauto).
      assert (HPwf := splu_wft G A1 P Q HspA WA1). destruct HPwf as [WP WQ].
      assert (HspC1 : splu (t_and A1 (t_union A2 B))
                           (t_and P (t_union A2 B)) (t_and Q (t_union A2 B))).
      { eapply SpU_andl. exact HspA. }
      eapply AS_or with (A1 := t_and P (t_union A2 B)) (A2 := t_and Q (t_union A2 B)).
      + exact HspC1.
      + (* P component *)
        assert (HEmb : algo_sub G (t_and P (t_union A2 B))
                                  (t_and (t_union P B) (t_union A2 B))).
        { apply AS_and with (B1 := t_union P B) (B2 := t_union A2 B).
          - apply SpI_and.
          - eapply AS_andl with (A1 := P) (A2 := t_union A2 B).
            + apply wft_or; auto.
            + apply SpI_and.
            + eapply AS_orl with (B1 := P) (B2 := B).
              * exact WB.
              * apply SpU_or.
              * apply AS_refl; auto.
          - eapply AS_andr with (A1 := P) (A2 := t_union A2 B).
            + exact WP.
            + apply SpI_and.
            + apply AS_refl; auto. apply wft_or; auto. }
        assert (HIH : algo_sub G (t_and (t_union P B) (t_union A2 B))
                                   (t_union (t_and P A2) B)).
        { apply (IH (size_typ P)); auto; lia. }
        assert (HToT : algo_sub G (t_union (t_and P A2) B) T).
        { assert (HPA1 : algo_sub G (t_and P A2) A1).
          { eapply AS_andl with (A1 := P) (A2 := A2).
            - exact WA2.
            - apply SpI_and.
            - eapply asub_splu_l1; eauto. }
          assert (HPA2 : algo_sub G (t_and P A2) A2).
          { eapply AS_andr with (A1 := P) (A2 := A2).
            - exact WP.
            - apply SpI_and.
            - apply AS_refl; auto. }
          assert (HPAA : algo_sub G (t_and P A2) (t_and A1 A2)).
          { apply AS_and with (B1 := A1) (B2 := A2).
            - apply SpI_and.
            - exact HPA1.
            - exact HPA2. }
          eapply AS_or with (A1 := t_and P A2) (A2 := B).
          - apply SpU_or.
          - eapply AS_orl with (B1 := t_and A1 A2) (B2 := B).
            + exact WB.
            + apply SpU_or.
            + exact HPAA.
          - eapply AS_orr with (B1 := t_and A1 A2) (B2 := B).
            + apply wft_and; auto.
            + apply SpU_or.
            + apply AS_refl; auto. }
        eapply asub_trans; [exact HEmb | eapply asub_trans; [exact HIH | exact HToT]].
      + (* Q component *)
        assert (HEmb : algo_sub G (t_and Q (t_union A2 B))
                                  (t_and (t_union Q B) (t_union A2 B))).
        { apply AS_and with (B1 := t_union Q B) (B2 := t_union A2 B).
          - apply SpI_and.
          - eapply AS_andl with (A1 := Q) (A2 := t_union A2 B).
            + apply wft_or; auto.
            + apply SpI_and.
            + eapply AS_orl with (B1 := Q) (B2 := B).
              * exact WB.
              * apply SpU_or.
              * apply AS_refl; auto.
          - eapply AS_andr with (A1 := Q) (A2 := t_union A2 B).
            + exact WQ.
            + apply SpI_and.
            + apply AS_refl; auto. apply wft_or; auto. }
        assert (HIH : algo_sub G (t_and (t_union Q B) (t_union A2 B))
                                   (t_union (t_and Q A2) B)).
        { apply (IH (size_typ Q)); auto; lia. }
        assert (HToT : algo_sub G (t_union (t_and Q A2) B) T).
        { assert (HPA1 : algo_sub G (t_and Q A2) A1).
          { eapply AS_andl with (A1 := Q) (A2 := A2).
            - exact WA2.
            - apply SpI_and.
            - eapply asub_splu_l2; eauto. }
          assert (HPA2 : algo_sub G (t_and Q A2) A2).
          { eapply AS_andr with (A1 := Q) (A2 := A2).
            - exact WQ.
            - apply SpI_and.
            - apply AS_refl; auto. }
          assert (HPAA : algo_sub G (t_and Q A2) (t_and A1 A2)).
          { apply AS_and with (B1 := A1) (B2 := A2).
            - apply SpI_and.
            - exact HPA1.
            - exact HPA2. }
          eapply AS_or with (A1 := t_and Q A2) (A2 := B).
          - apply SpU_or.
          - eapply AS_orl with (B1 := t_and A1 A2) (B2 := B).
            + exact WB.
            + apply SpU_or.
            + exact HPAA.
          - eapply AS_orr with (B1 := t_and A1 A2) (B2 := B).
            + apply wft_and; auto.
            + apply SpU_or.
            + apply AS_refl; auto. }
        eapply asub_trans; [exact HEmb | eapply asub_trans; [exact HIH | exact HToT]].
  }
  assert (HspS : splu (t_and (t_union A1 B) (t_union A2 B))
                       (t_and A1 (t_union A2 B)) (t_and B (t_union A2 B))).
  { eapply SpU_andl. apply SpU_or. }
  eapply AS_or with (A1 := t_and A1 (t_union A2 B)) (A2 := t_and B (t_union A2 B)).
  - exact HspS.
  - exact HC1.
  - exact HC2.
Qed.

End ClosureTrans.


(* ============ Primitive-binding closure ============ *)

Lemma bind_shape : forall G i A,
  okenvp G -> binds i A G -> (A = t_top \/ exists j, A = t_prim j).
Proof.
  intros G. induction G as [|[h B] PG IHG]; intros i A Ho Hb.
  - simpl in Hb. destruct Hb.
  - simpl in Hb. destruct Hb as [Heq|Hin].
    + injection Heq as Hih HAB. subst i A.
      inversion Ho; subst.
      * left; reflexivity.
      * right; exists j; reflexivity.
    + inversion Ho; subst.
      * eapply IHG; eauto.
      * eapply IHG; eauto.
Qed.

Lemma okenv_lookup_notin : forall h B PG,
  okenvp ((h,B)::PG) -> h \notin dom PG.
Proof. intros; inversion H; subst; auto. Qed.

Lemma okenv_sub_wft : forall h PG j,
  okenvp ((h,t_prim j)::PG) -> wft PG (t_prim j).
Proof. intros; inversion H; subst; auto. Qed.

Lemma asub_prim_bind : forall G i j,
  okenvp G -> binds i (t_prim j) G -> algo_sub G (t_prim i) (t_prim j).
Proof.
  intros G. induction G as [|[h B] PG IHG]; intros i j Ho Hb.
  - simpl in Hb. destruct Hb.
  - simpl in Hb. destruct Hb as [Heq|Hin].
    + injection Heq as Hih HAB. subst i B.
      eapply AS_prim_eq.
      * exact Ho.
      * apply AS_refl.
        -- eapply okenv_tail; exact Ho.
        -- eapply okenv_sub_wft; exact Ho.
    + assert (Hh : h <> i).
      { intro Heq2.
        apply (binds_dom_contradiction _ _ _ _ Hin).
        rewrite <- Heq2. apply okenv_lookup_notin in Ho. exact Ho. }
      eapply AS_prim_neq.
      * exact Ho.
      * exact Hh.
      * eapply IHG.
        -- eapply okenv_tail; exact Ho.
        -- exact Hin.
Qed.

Lemma asub_prim_dsub : forall G i A,
  okenvp G -> binds i A G -> algo_sub G (t_prim i) A.
Proof.
  intros G i A Ho Hb.
  destruct (bind_shape G i A Ho Hb) as [HA | [j HA]].
  - subst A. apply AS_top; auto. apply wft_prim with (A := t_top); exact Hb.
  - subst A. eapply asub_prim_bind; eauto.
Qed.

(* ============ Declarative -> algorithmic, given algorithmic transitivity ============ *)
Section MainClosure.
Variable asub_trans : forall G A B C,
  algo_sub G A B -> algo_sub G B C -> algo_sub G A C.

Lemma asub_of_dsub : forall G A B,
  declarative_subtyping G A B -> algo_sub G A B.
Proof.
  intros G A B H. induction H.
  - apply AS_refl; auto.
  - eapply asub_trans; eauto.
  - apply AS_top; auto.
  - apply AS_bot; auto.
  - eapply AS_arrow; eauto.
  - eapply asub_and_intro; eauto.
  - eapply asub_andl; eauto.
  - eapply asub_andr; eauto.
  - eapply asub_or_intro; eauto.
  - eapply asub_orl; eauto.
  - eapply asub_orr; eauto.
  - eapply distArr_asub; eauto.
  - eapply distArrU_asub; eauto.
  - eapply (distOr_l asub_trans); eauto.
  - eapply asub_prim_dsub; eauto.
Qed.

End MainClosure.


Section Endgame.
Variable asub_to_cmp_oi : forall G u i,
  ordu u -> ordi i -> wft G u -> wft G i -> algo_sub G u i -> cmp G u i.

Variable bridge : forall G B u i,
  okenvp G -> wft G B -> ordu u -> ordi i -> wft G u -> wft G i ->
  (forall j, In j (I B) -> cmp G u j) ->
  (forall w, In w (U B) -> cmp G w i) ->
  cmp G u i.

Lemma asub_to_sle : forall G A B,
  algo_sub G A B -> sle G A B.
Proof.
  intros G A B H u Hu i Hi.
  destruct (asub_regular G A B H) as [Ho [HA HB]].
  assert (HuB : algo_sub G u B) by (exact (asub_source_U G A B H u Hu)).
  assert (Hui : algo_sub G u i) by (exact (asub_target_I G u B HuB i Hi)).
  eapply asub_to_cmp_oi.
  - exact (U_ordu A u Hu).
  - exact (I_ordi B i Hi).
  - exact (U_wft G A u HA Hu).
  - exact (I_wft G B i HB Hi).
  - exact Hui.
Qed.

Lemma sle_trans : forall G A B C,
  okenvp G -> wft G A -> wft G B -> wft G C ->
  sle G A B -> sle G B C -> sle G A C.
Proof.
  intros G A B C Ho HA HB HC H1 H2 u Hu i Hi.
  eapply bridge.
  - exact Ho.
  - exact HB.
  - exact (U_ordu A u Hu).
  - exact (I_ordi C i Hi).
  - exact (U_wft G A u HA Hu).
  - exact (I_wft G C i HC Hi).
  - intros j Hj. exact (H1 u Hu j Hj).
  - intros w Hw. exact (H2 w Hw i Hi).
Qed.

Lemma asub_trans : forall G A B C,
  algo_sub G A B -> algo_sub G B C -> algo_sub G A C.
Proof.
  intros G A B C H1 H2.
  destruct (asub_regular G A B H1) as [Ho [HA HB]].
  destruct (asub_regular G B C H2) as [_ [HB' HC]].
  eapply sle_asub.
  eapply sle_trans.
  - exact Ho.
  - exact HA.
  - exact HB.
  - exact HC.
  - eapply asub_to_sle; eauto.
  - eapply asub_to_sle; eauto.
Qed.

End Endgame.


Lemma asub_trans_final : forall G A B C,
  algo_sub G A B -> algo_sub G B C -> algo_sub G A C.
Proof.
  intros. eapply (asub_trans asub_to_cmp_oi bridge); eauto.
Qed.

Lemma forward_final : forall G A B,
  declarative_subtyping G A B -> algo_sub G A B.
Proof.
  intros. eapply asub_of_dsub. exact asub_trans_final. exact H.
Qed.

Lemma dsub2asub_final : forall G A B,
  declarative_subtyping G A B <-> algo_sub G A B.
Proof.
  intros. split.
  - apply forward_final.
  - apply asub_sound.
Qed.


Theorem dsub2asub: forall G A B,
    declarative_subtyping G A B <-> algo_sub G A B.
Proof.
  exact dsub2asub_final.
Qed.

Theorem decidability : forall G A B,
    algo_sub G A B \/ not (algo_sub G A B).
Proof.
  exact decidability_proof.
Qed.
