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

Lemma wft_mono : forall G A,
    wft G A -> forall H, (forall i B, binds i B G -> binds i B H) -> wft H A.
Proof.
  induction 1; eauto using wft.
Qed.

Lemma wft_cons : forall G i B A, wft G A -> wft ((i, B) :: G) A.
Proof.
  eauto using wft_mono, binds_cons.
Qed.

Lemma splu_wft : forall A B C,
    splu A B C -> forall G, wft G A <-> wft G B /\ wft G C.
Proof.
  induction 1; intro G; split; intro WF.
  all: repeat match goal with
       | H : _ /\ _ |- _ => destruct H
       | H : wft _ (t_union _ _) |- _ => inversion H; subst; clear H
       | H : wft _ (t_and _ _) |- _ => inversion H; subst; clear H
       end.
  all: firstorder eauto using wft.
Qed.

Lemma spli_wft : forall A B C,
    spli A B C -> forall G, wft G A <-> wft G B /\ wft G C.
Proof.
  induction 1; intro G; split; intro WF.
  all: repeat match goal with
       | H : _ /\ _ |- _ => destruct H
       | H : wft _ (t_union _ _) |- _ => inversion H; subst; clear H
       | H : wft _ (t_and _ _) |- _ => inversion H; subst; clear H
       | H : wft _ (t_arrow _ _) |- _ => inversion H; subst; clear H
       | H : splu _ _ _ |- _ => pose proof (splu_wft _ _ _ H G); clear H
       end.
  all: firstorder eauto using wft.
Qed.

Lemma splu_size : forall A B C, splu A B C ->
    size_typ B < size_typ A /\ size_typ C < size_typ A.
Proof.
  induction 1; simpl; lia.
Qed.

Lemma spli_size : forall A B C, spli A B C ->
    size_typ B < size_typ A /\ size_typ C < size_typ A.
Proof.
  induction 1; simpl; try lia.
  apply splu_size in H0. lia.
Qed.

Lemma ordu_no_splu : forall A B C, ordu A -> splu A B C -> False.
Proof.
  intros A B C H. revert B C.
  induction H; intros B' C' S; inversion S; subst; eauto.
Qed.

Lemma ordi_no_spli : forall A B C, ordi A -> spli A B C -> False.
Proof.
  intros A B C H. revert B C.
  induction H; intros B' C' S; inversion S; subst; eauto using ordu_no_splu.
Qed.

Lemma splu_unique : forall A B C, splu A B C ->
    forall D E, splu A D E -> B = D /\ C = E.
Proof.
  induction 1; intros D E S; inversion S; subst;
    try solve [exfalso; eauto using ordu_no_splu].
  all: repeat match goal with
       | IH : forall D E, splu ?A D E -> _, H : splu ?A _ _ |- _ =>
           specialize (IH _ _ H); destruct IH; subst
       end; auto.
Qed.

Lemma spli_unique : forall A B C, spli A B C ->
    forall D E, spli A D E -> B = D /\ C = E.
Proof.
  induction 1; intros E F S; inversion S; subst;
    try solve [exfalso; eauto using ordi_no_spli].
  all: repeat match goal with
       | IH : forall D E, spli ?A D E -> _, H : spli ?A _ _ |- _ =>
           specialize (IH _ _ H); destruct IH; subst
       | H : splu ?A ?B ?C, H' : splu ?A ?D ?E |- _ =>
           first [constr_eq H H'; fail 1 |
                  destruct (splu_unique _ _ _ H _ _ H'); subst; clear H']
       end; auto.
Qed.

Lemma splu_cases : forall A, ordu A \/ exists B C, splu A B C.
Proof.
  induction A; try solve [left; constructor].
  - right. eauto using splu.
  - destruct IHA1 as [O | (B & C & S)].
    + destruct IHA2 as [O' | (B & C & S)].
      * left. now constructor.
      * right. eauto using splu.
    + right. eauto using splu.
Qed.

Lemma spli_cases : forall A, ordi A \/ exists B C, spli A B C.
Proof.
  induction A; try solve [left; constructor].
  - destruct IHA2 as [O | (B & C & S)].
    + destruct (splu_cases A1) as [O' | (B & C & S)].
      * left. now constructor.
      * right. eauto using spli.
    + right. eauto using spli.
  - destruct IHA1 as [O | (B & C & S)].
    + destruct IHA2 as [O' | (B & C & S)].
      * left. now constructor.
      * right. eauto using spli.
    + right. eauto using spli.
  - right. eauto using spli.
Qed.

Lemma spli_ordu : forall A B C, spli A B C ->
    ordu A -> ordu B /\ ordu C.
Proof.
  induction 1; intro O; inversion O; subst; eauto using ordu.
Qed.

Lemma splu_ordi : forall A B C, splu A B C ->
    ordi A -> ordi B /\ ordi C.
Proof.
  induction 1; intro O; inversion O; subst; auto.
Qed.

Lemma algo_wf : forall G A B, algo_sub G A B ->
    okenvp G /\ wft G A /\ wft G B.
Proof.
  induction 1; repeat match goal with H : _ /\ _ |- _ => destruct H end.
  all: try solve [eauto 8 using wft, wft_cons, binds_cons_2].
  all: first
    [ match goal with H : spli _ _ _ |- _ =>
        pose proof (spli_wft _ _ _ H PG) end
    | match goal with H : splu _ _ _ |- _ =>
        pose proof (splu_wft _ _ _ H PG) end ].
  all: firstorder.
Qed.

Lemma algo_ok : forall G A B, algo_sub G A B -> okenvp G.
Proof. intros G A B H. exact (proj1 (algo_wf _ _ _ H)). Qed.

Lemma algo_wft_l : forall G A B, algo_sub G A B -> wft G A.
Proof. intros G A B H. exact (proj1 (proj2 (algo_wf _ _ _ H))). Qed.

Lemma algo_wft_r : forall G A B, algo_sub G A B -> wft G B.
Proof. intros G A B H. exact (proj2 (proj2 (algo_wf _ _ _ H))). Qed.

Lemma splu_wft_parts : forall G A B C, splu A B C -> wft G A ->
    wft G B /\ wft G C.
Proof. intros. now apply (splu_wft _ _ _ H). Qed.

Lemma spli_wft_parts : forall G A B C, spli A B C -> wft G A ->
    wft G B /\ wft G C.
Proof. intros. now apply (spli_wft _ _ _ H). Qed.

Ltac split_parts_wft :=
  repeat match goal with
  | S : splu ?A ?B ?C, H : wft ?G ?A |- _ =>
      first [assert (wft G B) by assumption; fail 1 |
             destruct (splu_wft_parts _ _ _ _ S H)]
  | S : spli ?A ?B ?C, H : wft ?G ?A |- _ =>
      first [assert (wft G B) by assumption; fail 1 |
             destruct (spli_wft_parts _ _ _ _ S H)]
  end.

Ltac equalize_splits :=
  repeat match goal with
  | H : spli ?A ?B ?C, S : spli ?A ?D ?E |- _ =>
      first [constr_eq H S; fail 1 |
             destruct (spli_unique _ _ _ H _ _ S); subst; clear S]
  | H : splu ?A ?B ?C, S : splu ?A ?D ?E |- _ =>
      first [constr_eq H S; fail 1 |
             destruct (splu_unique _ _ _ H _ _ S); subst; clear S]
  end.

Ltac apply_split_ih :=
  repeat match goal with
  | IH : forall X Y, spli ?B X Y -> _,
    S : spli ?B ?X ?Y |- _ => destruct (IH _ _ S); clear IH
  | IH : forall X Y, splu ?A X Y -> _,
    S : splu ?A ?X ?Y |- _ => destruct (IH _ _ S); clear IH
  end.

Ltac invert_wft :=
  repeat match goal with
  | H : wft _ (t_arrow _ _) |- _ => inversion H; subst; clear H
  | H : wft _ (t_and _ _) |- _ => inversion H; subst; clear H
  | H : wft _ (t_union _ _) |- _ => inversion H; subst; clear H
  end.

Ltac apply_root_split_ih :=
  repeat match goal with
  | IH : forall X Y, spli (t_and ?A ?B) X Y -> _ |- _ =>
      destruct (IH _ _ (SpI_and A B)); clear IH
  | IH : forall X Y, splu (t_union ?A ?B) X Y -> _ |- _ =>
      destruct (IH _ _ (SpU_or A B)); clear IH
  end.

(* A target intersection and a source union require both split judgments. *)
Lemma algo_split_all : forall G A B, algo_sub G A B ->
    (forall B1 B2, spli B B1 B2 -> algo_sub G A B1 /\ algo_sub G A B2) /\
    (forall A1 A2, splu A A1 A2 -> algo_sub G A1 B /\ algo_sub G A2 B).
Proof.
  induction 1;
    repeat match goal with H : _ /\ _ |- _ => destruct H end;
    split; intros X Y S.
  all: try solve [inversion S].
  all: try solve [equalize_splits; auto].
  all: try solve [apply_split_ih; split; eauto using AS_and, AS_andl,
                               AS_andr, AS_or, AS_orl, AS_orr].
  { split_parts_wft.
    split; [eapply AS_andl with (A2 := Y) | eapply AS_andr with (A1 := X)];
      eauto using AS_refl. }
  { split_parts_wft.
    split; [eapply AS_orl with (B2 := Y) | eapply AS_orr with (B1 := X)];
      eauto using AS_refl. }
  { split_parts_wft. split; auto using AS_top. }
  { split_parts_wft. split; auto using AS_bot. }
  { inversion S; subst; apply_split_ih; split; auto using AS_arrow. }
  all: inversion H0; subst; clear H0; inversion S; subst;
    split_parts_wft; invert_wft; apply_split_ih; apply_root_split_ih; split;
    eauto using AS_andl, AS_andr, AS_orl, AS_orr, SpI_and, SpU_or.
Qed.

Lemma algo_spli_all : forall G A B B1 B2,
    algo_sub G A B -> spli B B1 B2 -> algo_sub G A B1 /\ algo_sub G A B2.
Proof. intros G A B B1 B2 H. exact (proj1 (algo_split_all _ _ _ H) _ _). Qed.

Lemma algo_splu_all : forall G A B A1 A2,
    algo_sub G A B -> splu A A1 A2 -> algo_sub G A1 B /\ algo_sub G A2 B.
Proof. intros G A B A1 A2 H. exact (proj2 (algo_split_all _ _ _ H) _ _). Qed.

Ltac apply_choice_ih :=
  repeat match goal with
  | IH : forall X Y, spli ?A X Y -> ordi ?B -> _,
    S : spli ?A _ _, O : ordi ?B |- _ => destruct (IH _ _ S O); clear IH
  | IH : forall X Y, splu ?B X Y -> ordu ?A -> _,
    S : splu ?B _ _, O : ordu ?A |- _ => destruct (IH _ _ S O); clear IH
  | IH : forall X Y, spli (t_and ?A ?B) X Y -> ordi ?C -> _,
    O : ordi ?C |- _ => destruct (IH _ _ (SpI_and A B) O); clear IH
  | IH : forall X Y, splu (t_union ?B ?C) X Y -> ordu ?A -> _,
    O : ordu ?A |- _ => destruct (IH _ _ (SpU_or B C) O); clear IH
  end.

(* On the opposite sides, an ordinary type makes a single branch sufficient. *)
Lemma algo_split_choice : forall G A B, algo_sub G A B ->
    (forall A1 A2, spli A A1 A2 -> ordi B ->
      algo_sub G A1 B \/ algo_sub G A2 B) /\
    (forall B1 B2, splu B B1 B2 -> ordu A ->
      algo_sub G A B1 \/ algo_sub G A B2).
Proof.
  induction 1;
    repeat match goal with H : _ /\ _ |- _ => destruct H end;
    split; intros X Y S O.
  all: try solve [inversion S].
  all: try solve [exfalso; eauto using ordi_no_spli, ordu_no_splu].
  all: try solve [equalize_splits; auto].
  all: try solve [split_parts_wft; auto using AS_top, AS_bot].
  all: repeat match goal with
       | T : spli ?A _ _, O : ordu ?A |- _ =>
           destruct (spli_ordu _ _ _ T O); clear O
       | T : splu ?B _ _, O : ordi ?B |- _ =>
           destruct (splu_ordi _ _ _ T O); clear O
       end.
  all: try solve [apply_choice_ih; eauto using AS_andl, AS_andr, AS_orl, AS_orr].
  { inversion O; subst; inversion S; subst; apply_choice_ih; auto using AS_arrow. }
  all: inversion H; subst; clear H; inversion S; subst;
    apply_choice_ih; eauto using AS_and, AS_or, SpI_and, SpU_or.
Qed.

Lemma algo_spli_choice : forall G A B A1 A2,
    algo_sub G A B -> spli A A1 A2 -> ordi B ->
    algo_sub G A1 B \/ algo_sub G A2 B.
Proof. intros G A B A1 A2 H. exact (proj1 (algo_split_choice _ _ _ H) _ _). Qed.

Lemma algo_splu_choice : forall G A B B1 B2,
    algo_sub G A B -> splu B B1 B2 -> ordu A ->
    algo_sub G A B1 \/ algo_sub G A B2.
Proof. intros G A B B1 B2 H. exact (proj2 (algo_split_choice _ _ _ H) _ _). Qed.

Lemma wft_prim_binds : forall G i, wft G (t_prim i) <-> exists A, binds i A G.
Proof.
  split; [intro H; inversion H; eauto | intros [A H]; eauto using wft].
Qed.

Lemma okenvp_tail : forall G i A, okenvp ((i,A) :: G) -> okenvp G.
Proof. intros G i A H; inversion H; assumption. Qed.

Lemma okenvp_fresh : forall G i A, okenvp ((i,A) :: G) -> i `notin` dom G.
Proof. intros G i A H; inversion H; assumption. Qed.

Lemma tail_prim_neq : forall G i A j,
    okenvp ((i,A) :: G) -> wft G (t_prim j) -> i <> j.
Proof.
  intros G i A j O W ->.
  apply wft_prim_binds in W as [B W].
  exact (okenvp_fresh _ _ _ O (binds_In _ _ _ _ W)).
Qed.

Ltac invert_atomic_splits :=
  repeat match goal with
  | H : spli t_int _ _ |- _ => inversion H
  | H : spli t_unit _ _ |- _ => inversion H
  | H : spli t_top _ _ |- _ => inversion H
  | H : spli t_bot _ _ |- _ => inversion H
  | H : spli (t_prim _) _ _ |- _ => inversion H
  | H : splu t_int _ _ |- _ => inversion H
  | H : splu t_unit _ _ |- _ => inversion H
  | H : splu t_top _ _ |- _ => inversion H
  | H : splu t_bot _ _ |- _ => inversion H
  | H : splu (t_prim _) _ _ |- _ => inversion H
  | H : splu (t_arrow _ _) _ _ |- _ => inversion H
  end.

Lemma algo_prim_tail : forall G i A a b,
    i <> a -> algo_sub ((i,A) :: G) (t_prim a) (t_prim b) ->
    algo_sub G (t_prim a) (t_prim b).
Proof.
  intros G i A a b N H. inversion H; subst; invert_atomic_splits;
    try contradiction; try assumption.
  apply AS_refl; [eauto using okenvp_tail | ].
  match goal with W : wft _ (t_prim _) |- _ =>
    apply wft_prim_binds in W as [B W];
    apply binds_cons_1 in W as [[? ?] | W]
  end.
  - congruence.
  - eauto using wft.
Qed.

(* A non-reflexive primitive step has its target in the tail of the environment. *)
Lemma algo_prim_trans : forall G a b c,
    algo_sub G (t_prim a) (t_prim b) ->
    algo_sub G (t_prim b) (t_prim c) ->
    algo_sub G (t_prim a) (t_prim c).
Proof.
  induction G as [| [i A] G IH]; intros a b c AB BC.
  - inversion AB; subst; invert_atomic_splits; assumption.
  - inversion AB; subst; invert_atomic_splits; try assumption.
    + eapply AS_prim_neq; try eassumption.
      eapply IH; [eassumption | apply (algo_prim_tail G i A); [| assumption]].
      eauto using tail_prim_neq, algo_wft_r.
    + eapply AS_prim_eq; try eassumption.
      eapply IH; [eassumption | eapply algo_prim_tail; [| eassumption]].
      eauto using tail_prim_neq, algo_wft_r.
Qed.

Ltac impossible_ordinary_split :=
  solve [exfalso; eauto using ordu_no_splu, ordi_no_spli].

Ltac cut_smaller smaller :=
  match goal with
  | H : algo_sub ?G ?X ?Y, K : algo_sub ?G ?Y ?Z
    |- algo_sub ?G ?X ?Z =>
      eapply (smaller X Y Z); [simpl in *; lia | exact H | exact K]
  end.

Lemma algo_trans : forall G A B C,
    algo_sub G A B -> algo_sub G B C -> algo_sub G A C.
Proof.
  assert (Cut : forall n G A B C, size_typ A + size_typ B + size_typ C = n ->
    algo_sub G A B -> algo_sub G B C -> algo_sub G A C).
  2: { intros; eapply Cut; eauto. }
  induction n using lt_wf_ind.
  intros G A B C Size AB BC.
  rename H into IH.
  assert (Smaller : forall X Y Z,
    size_typ X + size_typ Y + size_typ Z < n ->
    algo_sub G X Y -> algo_sub G Y Z -> algo_sub G X Z).
  { intros X Y Z LT. eapply IH; [exact LT | reflexivity]. }
  clear IH.
  destruct (splu_cases A) as [OA | (A1 & A2 & SA)].
  2: { destruct (algo_splu_all _ _ _ _ _ AB SA).
       destruct (splu_size _ _ _ SA).
       eapply AS_or; [exact SA | eapply (Smaller _ B _) | eapply (Smaller _ B _)];
         try lia; assumption. }
  destruct (spli_cases C) as [OC | (C1 & C2 & SC)].
  2: { destruct (algo_spli_all _ _ _ _ _ BC SC).
       destruct (spli_size _ _ _ SC).
       eapply AS_and; [exact SC | eapply (Smaller _ B _) | eapply (Smaller _ B _)];
         try lia; assumption. }
  (* The outer types are now ordinary on their respective sides.
     A split of the middle type gives both premises on one side and a choice on the other. *)
  destruct (spli_cases B) as [OBi | (B1 & B2 & SB)].
  2: { destruct (algo_spli_all _ _ _ _ _ AB SB).
       destruct (spli_size _ _ _ SB).
       destruct (algo_spli_choice _ _ _ _ _ BC SB OC).
       - eapply (Smaller _ B1 _); [lia | assumption | assumption].
       - eapply (Smaller _ B2 _); [lia | assumption | assumption]. }
  destruct (splu_cases B) as [OBu | (B1 & B2 & SB)].
  2: { destruct (algo_splu_all _ _ _ _ _ BC SB).
       destruct (splu_size _ _ _ SB).
       destruct (algo_splu_choice _ _ _ _ _ AB SB OA).
       - eapply (Smaller _ B1 _); [lia | assumption | assumption].
       - eapply (Smaller _ B2 _); [lia | assumption | assumption]. }
  inversion AB; subst; try impossible_ordinary_split;
    try solve [assumption | eauto using AS_bot, algo_wft_r].
  all: try match goal with
       | S : spli ?X ?X1 ?X2, D : algo_sub _ ?X1 _ |- algo_sub _ ?X _ =>
           pose proof (spli_size _ _ _ S);
           eapply AS_andl with (A1 := X1) (A2 := X2); [eassumption | exact S | cut_smaller Smaller]
       | S : spli ?X ?X1 ?X2, D : algo_sub _ ?X2 _ |- algo_sub _ ?X _ =>
           pose proof (spli_size _ _ _ S);
           eapply AS_andr with (A1 := X1) (A2 := X2); [eassumption | exact S | cut_smaller Smaller]
       end.
  all: inversion BC; subst; invert_atomic_splits; try impossible_ordinary_split;
    try solve [assumption | eauto using AS_top, algo_wft_l |
               eauto using algo_prim_trans].
  all: try solve [apply AS_arrow; cut_smaller Smaller].
  all: match goal with
       | S : splu ?Z ?Z1 ?Z2, D : algo_sub _ _ ?Z1 |- algo_sub _ _ ?Z =>
           pose proof (splu_size _ _ _ S);
           eapply AS_orl with (B1 := Z1) (B2 := Z2); [eassumption | exact S | cut_smaller Smaller]
       | S : splu ?Z ?Z1 ?Z2, D : algo_sub _ _ ?Z2 |- algo_sub _ _ ?Z =>
           pose proof (splu_size _ _ _ S);
           eapply AS_orr with (B1 := Z1) (B2 := Z2); [eassumption | exact S | cut_smaller Smaller]
       end.
Qed.

Lemma okenvp_bind_shape : forall G i A, okenvp G -> binds i A G ->
    A = t_top \/ exists j, A = t_prim j.
Proof.
  induction 1; intro B; [inversion B | |];
    apply binds_cons_1 in B as [[? ?] | B]; subst; eauto.
Qed.

Lemma algo_bind : forall G i A, okenvp G -> binds i A G ->
    algo_sub G (t_prim i) A.
Proof.
  intros G i A O. revert i A.
  induction O; intros a A S; [inversion S | |];
    apply binds_cons_1 in S as [[? ?] | S]; subst.
  - eapply AS_top; eauto using okenvp_cons, wft_prim, binds_cons_2.
  - destruct (okenvp_bind_shape _ _ _ O S) as [-> | (j & ->)].
    + eapply AS_top; eauto using okenvp_cons, wft_prim, binds_cons.
    + eapply AS_prim_neq; eauto using okenvp_cons, tail_prim_neq, wft_prim.
  - eapply AS_prim_eq; eauto using okenvp_sub, AS_refl.
  - destruct (okenvp_bind_shape _ _ _ O S) as [-> | (k & ->)].
    + eapply AS_top; eauto using okenvp_sub, wft_prim, binds_cons.
    + eapply AS_prim_neq; eauto using okenvp_sub, tail_prim_neq, wft_prim.
Qed.

Lemma algo_join_domains : forall G B X A1 A2,
    algo_sub G X (t_arrow A1 B) -> algo_sub G X (t_arrow A2 B) ->
    algo_sub G X (t_arrow (t_union A1 A2) B).
Proof.
  assert (Join : forall n G B X A1 A2, size_typ B = n ->
    algo_sub G X (t_arrow A1 B) -> algo_sub G X (t_arrow A2 B) ->
    algo_sub G X (t_arrow (t_union A1 A2) B)).
  2: { intros; eapply Join; eauto. }
  induction n using lt_wf_ind; intros G B X A1 A2 Size S1 S2.
  destruct (spli_cases B) as [O | (B1 & B2 & S)].
  - eapply AS_and; [apply SpI_arrowUnion; [exact O | apply SpU_or] | exact S1 | exact S2].
  - destruct (algo_spli_all _ _ _ _ _ S1 (SpI_arrow A1 _ _ _ S)).
    destruct (algo_spli_all _ _ _ _ _ S2 (SpI_arrow A2 _ _ _ S)).
    destruct (spli_size _ _ _ S).
    eapply AS_and; [apply SpI_arrow; exact S | | ].
    + eapply (H (size_typ B1)); [lia | reflexivity | eassumption | eassumption].
    + eapply (H (size_typ B2)); [lia | reflexivity | eassumption | eassumption].
Qed.

Lemma algo_distribute_union : forall G X A B C,
    algo_sub G X (t_union A B) -> algo_sub G X (t_union C B) ->
    algo_sub G X (t_union (t_and A C) B).
Proof.
  assert (Dist : forall n G X A B C, size_typ X = n ->
    algo_sub G X (t_union A B) -> algo_sub G X (t_union C B) ->
    algo_sub G X (t_union (t_and A C) B)).
  2: { intros; eapply Dist; eauto. }
  induction n using lt_wf_ind; intros G X A B C Size S1 S2.
  destruct (splu_cases X) as [O | (X1 & X2 & S)].
  - pose proof (algo_wft_r _ _ _ S1) as W1.
    pose proof (algo_wft_r _ _ _ S2) as W2.
    invert_wft.
    destruct (algo_splu_choice _ _ _ _ _ S1 (SpU_or A B) O);
    destruct (algo_splu_choice _ _ _ _ _ S2 (SpU_or C B) O).
    + eapply AS_orl; [| apply SpU_or |]; [assumption |].
      eapply AS_and; [apply SpI_and | assumption | assumption].
    + eapply AS_orr; [| apply SpU_or |]; eauto using wft_and.
    + eapply AS_orr; [| apply SpU_or |]; eauto using wft_and.
    + eapply AS_orr; [| apply SpU_or |]; eauto using wft_and.
  - destruct (algo_splu_all _ _ _ _ _ S1 S).
    destruct (algo_splu_all _ _ _ _ _ S2 S).
    destruct (splu_size _ _ _ S).
    eapply AS_or; [exact S | | ].
    + eapply (H (size_typ X1)); [lia | reflexivity | eassumption | eassumption].
    + eapply (H (size_typ X2)); [lia | reflexivity | eassumption | eassumption].
Qed.

Lemma declarative_to_algo : forall G A B,
    declarative_subtyping G A B -> algo_sub G A B.
Proof.
  induction 1; try solve [eauto using AS_refl, algo_trans, AS_top, AS_bot,
                                      AS_arrow, algo_bind].
  - eapply AS_and; [apply SpI_and | assumption | assumption].
  - eapply AS_andl; [| apply SpI_and |]; eauto using AS_refl.
  - eapply AS_andr; [| apply SpI_and |]; eauto using AS_refl.
  - eapply AS_or; [apply SpU_or | assumption | assumption].
  - eapply AS_orl; [| apply SpU_or |]; eauto using AS_refl.
  - eapply AS_orr; [| apply SpU_or |]; eauto using AS_refl.
  - eapply AS_and; [apply SpI_arrow; apply SpI_and | |].
    + eapply AS_andl; [| apply SpI_and |]; eauto using AS_refl, wft_arrow.
    + eapply AS_andr; [| apply SpI_and |]; eauto using AS_refl, wft_arrow.
  - apply algo_join_domains.
    + eapply AS_andl; [| apply SpI_and |]; eauto using AS_refl, wft_arrow.
    + eapply AS_andr; [| apply SpI_and |]; eauto using AS_refl, wft_arrow.
  - apply algo_distribute_union.
    + eapply AS_andl; [| apply SpI_and |]; eauto using AS_refl, wft_or.
    + eapply AS_andr; [| apply SpI_and |]; eauto using AS_refl, wft_or.
Qed.

Section DeclarativeSplitting.
  Context (G : envp) (OK : okenvp G).
  Local Notation "A ⊑ B" := (declarative_subtyping G A B) (at level 70).

  #[local] Hint Resolve DS_refl DS_arrow DS_and DS_andl DS_andr
    DS_or DS_orl DS_orr DS_distArr DS_distArrU DS_distOr : lattice.
  #[local] Hint Constructors wft : lattice.

  Lemma decl_and_mono : forall A B C D,
      wft G A -> wft G B -> A ⊑ C -> B ⊑ D ->
      t_and A B ⊑ t_and C D.
  Proof.
    intros A B C D WA WB AC BD. apply DS_and.
    - eapply DS_trans; [apply DS_andl | exact AC]; assumption.
    - eapply DS_trans; [apply DS_andr | exact BD]; assumption.
  Qed.

  Lemma decl_or_mono : forall A B C D,
      wft G C -> wft G D -> A ⊑ C -> B ⊑ D ->
      t_union A B ⊑ t_union C D.
  Proof.
    intros A B C D WC WD AC BD. apply DS_or.
    - eapply DS_trans; [exact AC | apply DS_orl]; assumption.
    - eapply DS_trans; [exact BD | apply DS_orr]; assumption.
  Qed.

  Lemma decl_and_comm : forall A B,
      wft G A -> wft G B -> t_and A B ⊑ t_and B A.
  Proof. eauto 9 with lattice. Qed.

  Lemma decl_or_comm : forall A B,
      wft G A -> wft G B -> t_union A B ⊑ t_union B A.
  Proof. eauto 9 with lattice. Qed.

  #[local] Hint Resolve decl_and_mono decl_or_mono decl_and_comm decl_or_comm : lattice.

  Lemma decl_dist_shared_left : forall A B C,
      wft G A -> wft G B -> wft G C ->
      t_and (t_union B A) (t_union B C) ⊑ t_union B (t_and A C).
  Proof.
    intros.
    eapply DS_trans with (B := t_and (t_union A B) (t_union C B)).
    { eauto 9 with lattice. }
    eapply DS_trans with (B := t_union (t_and A C) B); eauto 9 with lattice.
  Qed.

  Lemma decl_meet_over_join : forall A B C,
      wft G A -> wft G B -> wft G C ->
      t_and (t_union A B) C ⊑ t_union (t_and A C) (t_and B C).
  Proof.
    intros A B C WA WB WC.
    eapply DS_trans with (B := t_union (t_and B C) (t_and A C)).
    2: eauto 9 with lattice.
    eapply DS_trans with (B := t_and (t_union B (t_and A C)) (t_union C (t_and A C))).
    2: eauto 9 with lattice.
    apply DS_and.
    - eapply DS_trans with (B := t_and (t_union A B) (t_union C B)).
      { apply DS_and.
        - eauto 9 with lattice.
        - eapply DS_trans with (B := C); eauto 9 with lattice. }
      eapply DS_trans with (B := t_union (t_and A C) B); eauto 9 with lattice.
    - eapply DS_trans with (B := C); eauto 9 with lattice.
  Qed.

  Lemma decl_meet_over_join_right : forall A B C,
      wft G A -> wft G B -> wft G C ->
      t_and A (t_union B C) ⊑ t_union (t_and A B) (t_and A C).
  Proof.
    intros A B C WA WB WC.
    eapply DS_trans with (B := t_and (t_union B C) A).
    { eauto 9 with lattice. }
    eapply DS_trans with (B := t_union (t_and B A) (t_and C A)).
    - now apply decl_meet_over_join.
    - eauto 9 with lattice.
  Qed.

  Lemma decl_splu : forall A B C, splu A B C -> wft G A ->
      B ⊑ A /\ C ⊑ A /\ A ⊑ t_union B C.
  Proof.
    intros A B C S.
    induction S as [A B | A B A1 A2 S IH | A B B1 B2 O S IH]; intro W.
    - invert_wft. eauto 9 with lattice.
    - assert (V : wft G A) by (inversion W; assumption).
      destruct (IH V) as (D1 & D2 & D).
      split_parts_wft. invert_wft.
      split; [eauto 9 with lattice | split; [eauto 9 with lattice | ]].
      eapply DS_trans with (B := t_and (t_union A1 A2) B).
      + eauto 9 with lattice.
      + eauto using decl_meet_over_join.
    - assert (V : wft G B) by (inversion W; assumption).
      destruct (IH V) as (D1 & D2 & D).
      split_parts_wft. invert_wft.
      split; [eauto 9 with lattice | split; [eauto 9 with lattice | ]].
      eapply DS_trans with (B := t_and A (t_union B1 B2)).
      + eauto 9 with lattice.
      + eauto using decl_meet_over_join_right.
  Qed.

  Lemma decl_spli : forall A B C, spli A B C -> wft G A ->
      A ⊑ B /\ A ⊑ C /\ t_and B C ⊑ A.
  Proof.
    intros A B C S.
    induction S as [A B | A B C D S IH | A D B C O S |
                    A B A1 A2 S IH | A B B1 B2 O S IH]; intro W.
    - invert_wft. eauto 9 with lattice.
    - assert (V : wft G B) by (inversion W; assumption).
      destruct (IH V) as (D1 & D2 & E).
      split_parts_wft. invert_wft.
      split; [eauto 9 with lattice | split; [eauto 9 with lattice | ]].
      eapply DS_trans with (B := t_arrow A (t_and C D)); eauto 9 with lattice.
    - assert (V : wft G A) by (inversion W; assumption).
      destruct (decl_splu _ _ _ S V) as (D1 & D2 & E).
      split_parts_wft. invert_wft.
      split; [eauto 9 with lattice | split; [eauto 9 with lattice | ]].
      eapply DS_trans with (B := t_arrow (t_union B C) D); eauto 9 with lattice.
    - assert (V : wft G A) by (inversion W; assumption).
      destruct (IH V) as (D1 & D2 & E).
      split_parts_wft. invert_wft.
      split; [eauto 9 with lattice | split; [eauto 9 with lattice | ]].
      eapply DS_trans with (B := t_union (t_and A1 A2) B); eauto 9 with lattice.
    - assert (V : wft G B) by (inversion W; assumption).
      destruct (IH V) as (D1 & D2 & E).
      split_parts_wft. invert_wft.
      split; [eauto 9 with lattice | split; [eauto 9 with lattice | ]].
      eapply DS_trans with (B := t_union A (t_and B1 B2)).
      + eauto using decl_dist_shared_left.
      + eauto 9 with lattice.
  Qed.
End DeclarativeSplitting.

Lemma decl_mono : forall G A B, declarative_subtyping G A B ->
    forall E, okenvp E ->
    (forall i T, binds i T G -> binds i T E) ->
    declarative_subtyping E A B.
Proof.
  induction 1; intros E O Keep; eauto using declarative_subtyping, wft_mono.
Qed.

Lemma decl_cons : forall G A B i T,
    declarative_subtyping G A B -> okenvp ((i,T) :: G) ->
    declarative_subtyping ((i,T) :: G) A B.
Proof. eauto using decl_mono, binds_cons. Qed.

Lemma algo_to_declarative : forall G A B,
    algo_sub G A B -> declarative_subtyping G A B.
Proof.
  induction 1; try solve [eauto using DS_refl, DS_top, DS_bot, DS_arrow, decl_cons].
  { eapply DS_trans with (B := t_prim j).
    - eauto using DS_prim, binds_cons_2.
    - eauto using decl_cons. }
  all: repeat match goal with
       | A : algo_sub _ _ _ |- _ =>
           destruct (algo_wf _ _ _ A) as (? & ? & ?); clear A
       end.
  all: match goal with
       | O : okenvp ?G, S : spli ?A ?B ?C, WB : wft ?G ?B, WC : wft ?G ?C |- _ =>
           let W := fresh "W" in assert (wft G A) as W by (apply (spli_wft _ _ _ S); auto);
           destruct (decl_spli _ O _ _ _ S W) as (? & ? & ?)
       | O : okenvp ?G, S : splu ?A ?B ?C, WB : wft ?G ?B, WC : wft ?G ?C |- _ =>
           let W := fresh "W" in assert (wft G A) as W by (apply (splu_wft _ _ _ S); auto);
           destruct (decl_splu _ O _ _ _ S W) as (? & ? & ?)
       end.
  all: eauto using DS_trans, DS_and, DS_or.
Qed.

Theorem dsub2asub: forall G A B,
    declarative_subtyping G A B <-> algo_sub G A B.
Proof.
  split; auto using declarative_to_algo, algo_to_declarative.
Qed.

Lemma wft_prim_dec : forall G i, wft G (t_prim i) \/ ~ wft G (t_prim i).
Proof.
  induction G as [| [j T] G IH]; intro i.
  - right. intro W. apply wft_prim_binds in W as [A W]. inversion W.
  - destruct (Atom.eq_dec i j) as [-> | N].
    + left. eauto using wft_prim, binds_cons_2.
    + destruct (IH i) as [W | N'].
      * left. now apply wft_cons.
      * right. intro W. apply wft_prim_binds in W as [A W].
        apply binds_cons_1 in W as [[? ?] | W]; [congruence |].
        apply N'. eauto using wft_prim.
Qed.

Lemma wft_dec : forall G A, wft G A \/ ~ wft G A.
Proof.
  intros G A. induction A; try solve [left; constructor | apply wft_prim_dec].
  all: destruct IHA1, IHA2; try solve [left; constructor; assumption];
       right; inversion 1; contradiction.
Qed.

Lemma okenvp_dec : forall G, okenvp G \/ ~ okenvp G.
Proof.
  induction G as [| [i A] G IH].
  - left. constructor.
  - destruct IH as [O | N].
    2: { right. intro H. apply N. eapply okenvp_tail; exact H. }
    destruct (AtomSetImpl.mem i (dom G)) eqn:M.
    { right. intro H. apply (okenvp_fresh _ _ _ H).
      now apply AtomSetImpl.mem_2. }
    assert (Fresh : i `notin` dom G).
    { intro I. apply AtomSetImpl.mem_1 in I. congruence. }
    destruct A; try solve [right; inversion 1 | left; now apply okenvp_cons].
    destruct (wft_prim_dec G n) as [W | NW].
    + left. now apply okenvp_sub.
    + right. inversion 1. contradiction.
Qed.

Lemma typ_eq_dec : forall A B : typ, {A = B} + {A <> B}.
Proof. decide equality; apply Atom.eq_dec. Qed.

Lemma algo_prim_dec : forall G a b,
    algo_sub G (t_prim a) (t_prim b) \/ ~ algo_sub G (t_prim a) (t_prim b).
Proof.
  induction G as [| [i T] G IH]; intros a b.
  - right. intro S. apply algo_wft_l in S.
    apply wft_prim_binds in S as [A S]. inversion S.
  - destruct (okenvp_dec ((i,T) :: G)) as [O | N].
    2: { right. eauto using algo_ok. }
    destruct (Atom.eq_dec a b) as [-> | N].
    { destruct (wft_prim_dec ((i,T) :: G) b) as [W | NW].
      - left. now apply AS_refl.
      - right. eauto using algo_wft_l. }
    destruct (Atom.eq_dec i a) as [-> | Fresh].
    + destruct T; try solve [right; intro S; inversion S; subst;
                              invert_atomic_splits; contradiction].
      destruct (IH n b) as [S | NS].
      * left. now apply AS_prim_eq.
      * right. intro S. inversion S; subst; invert_atomic_splits; contradiction.
    + destruct (IH a b) as [S | NS].
      * left. now apply AS_prim_neq.
      * right. intro S. apply NS. eapply algo_prim_tail; eassumption.
Qed.

Lemma decide_from : forall P Q : Prop, (P -> Q) -> (Q -> P) ->
    (Q \/ ~ Q) -> P \/ ~ P.
Proof. tauto. Qed.

Lemma decide_both : forall P Q : Prop, (P \/ ~ P) -> (Q \/ ~ Q) ->
    (P /\ Q) \/ ~ (P /\ Q).
Proof. tauto. Qed.

Lemma decide_either : forall P Q : Prop, (P \/ ~ P) -> (Q \/ ~ Q) ->
    (P \/ Q) \/ ~ (P \/ Q).
Proof. tauto. Qed.

Theorem decidability : forall G A B,
    algo_sub G A B \/ not (algo_sub G A B).
Proof.
  assert (Dec : forall n G A B, size_typ A + size_typ B = n ->
    algo_sub G A B \/ ~ algo_sub G A B).
  2: { intros; eapply Dec; reflexivity. }
  induction n using lt_wf_ind; intros G A B Size.
  assert (Smaller : forall X Y, size_typ X + size_typ Y < n ->
    algo_sub G X Y \/ ~ algo_sub G X Y).
  { intros X Y LT. eapply H; [exact LT | reflexivity]. }
  clear H.
  destruct (okenvp_dec G) as [O | NO]; [| right; eauto using algo_ok].
  destruct (wft_dec G A) as [WA | NA]; [| right; eauto using algo_wft_l].
  destruct (wft_dec G B) as [WB | NB]; [| right; eauto using algo_wft_r].
  destruct (typ_eq_dec A B) as [-> | NE]; [left; now apply AS_refl |].
  (* Process the splits that require both branches before testing the choice splits. *)
  destruct (splu_cases A) as [OUA | (A1 & A2 & S)].
  2: { destruct (splu_size _ _ _ S).
       eapply (decide_from _ (algo_sub G A1 B /\ algo_sub G A2 B)).
       - eauto using algo_splu_all.
       - intros [S1 S2]. eauto using AS_or.
       - apply decide_both; apply Smaller; lia. }
  destruct (spli_cases B) as [OIB | (B1 & B2 & S)].
  2: { destruct (spli_size _ _ _ S).
       eapply (decide_from _ (algo_sub G A B1 /\ algo_sub G A B2)).
       - eauto using algo_spli_all.
       - intros [S1 S2]. eauto using AS_and.
       - apply decide_both; apply Smaller; lia. }
  destruct (spli_cases A) as [OIA | (A1 & A2 & S)].
  2: { destruct (spli_size _ _ _ S).
       destruct (spli_wft_parts _ _ _ _ S WA).
       eapply (decide_from _ (algo_sub G A1 B \/ algo_sub G A2 B)).
       - eauto using algo_spli_choice.
       - intros [S1 | S2]; eauto using AS_andl, AS_andr.
       - apply decide_either; apply Smaller; lia. }
  destruct (splu_cases B) as [OUB | (B1 & B2 & S)].
  2: { destruct (splu_size _ _ _ S).
       destruct (splu_wft_parts _ _ _ _ S WB).
       eapply (decide_from _ (algo_sub G A B1 \/ algo_sub G A B2)).
       - eauto using algo_splu_choice.
       - intros [S1 | S2]; eauto using AS_orl, AS_orr.
       - apply decide_either; apply Smaller; lia. }
  destruct A; try solve [inversion OUA | inversion OIA];
    destruct B; try solve [inversion OUB | inversion OIB].
  all: try solve [left; apply AS_bot; assumption | left; apply AS_top; assumption].
  all: try solve [right; intro S; inversion S; subst;
                  try impossible_ordinary_split; contradiction].
  - eapply (decide_from _ (algo_sub G B1 A1 /\ algo_sub G A2 B2)).
    + intro S. inversion S; subst; try impossible_ordinary_split; try contradiction.
      auto.
    + intros [D C]. now apply AS_arrow.
    + apply decide_both; apply Smaller; simpl in Size; lia.
  - apply algo_prim_dec.
Qed.
