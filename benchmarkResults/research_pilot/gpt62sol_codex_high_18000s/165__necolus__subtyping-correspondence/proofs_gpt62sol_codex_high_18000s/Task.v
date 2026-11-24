Require Import Metalib.Metatheory.

Require Import syntax_ott.

From Stdlib Require Import List Lia Arith.Wf_nat.

Import ListNotations.

Definition applyfs (fs : ls) (A : styp) :=
  fold_right (fun el acc =>
                match el with
                | st_ty A => styp_arrow A acc
                | st_la l => styp_rcd l acc
                end) A fs.

Lemma applyfs_app : forall fs gs A,
    applyfs (fs ++ gs) A = applyfs fs (applyfs gs A).
Proof.
  induction fs as [|[T|l] fs IH]; intros gs A; simpl.
  - reflexivity.
  - now rewrite IH.
  - now rewrite IH.
Qed.

Lemma calAnd_sub : forall fs A B,
    sub (styp_and (applyfs fs A) (applyfs fs B))
        (applyfs fs (styp_and A B)) (calAnd fs).
Proof.
  induction fs as [|[T|l] fs IH]; intros A B; simpl.
  - apply S_refl.
  - eapply S_trans.
    + apply S_arr; [apply S_refl | apply IH].
    + apply S_distArr.
  - eapply S_trans.
    + apply S_rcd, IH.
    + apply S_distRcd.
Qed.

Lemma calTop_sub : forall fs,
    sub styp_top (applyfs fs styp_top) (calTop fs).
Proof.
  induction fs as [|[T|l] fs IH]; simpl.
  - apply S_top.
  - eapply S_trans.
    + apply S_arr; [apply S_refl | apply IH].
    + eapply S_trans.
      * apply S_arr; apply S_top.
      * eapply S_trans; [apply S_topArr | apply S_top].
  - eapply S_trans.
    + apply S_rcd, IH.
    + apply S_topRcd.
Qed.

Theorem ASub2sub : forall fs A B c,
    ASub fs A B c -> sub A (applyfs fs B) c.
Proof.
  intros fs A B c H.
  induction H; simpl.
  - apply S_refl.
  - now apply S_rcd.
  - now rewrite applyfs_app in IHASub.
  - eapply S_trans; [apply calTop_sub | apply S_top].
  - eapply S_trans; [apply calAnd_sub | now apply S_and].
  - now rewrite applyfs_app in IHASub.
  - eapply S_trans; [exact IHASub | apply S_andl].
  - eapply S_trans; [exact IHASub | apply S_andr].
  - now apply S_arr.
Qed.

(* A path lists the arrow domains and record labels leading to a nat leaf.
   Intersections contribute the paths from both branches. *)
Fixpoint type_paths (A : styp) : list ls :=
  match A with
  | styp_top => []
  | styp_nat => [[]]
  | styp_and A B => type_paths A ++ type_paths B
  | styp_arrow A B => map (cons (st_ty A)) (type_paths B)
  | styp_rcd l A => map (cons (st_la l)) (type_paths A)
  end.

Inductive path_sub : ls -> ls -> Prop :=
| PS_nil : path_sub [] []
| PS_arrow : forall A B p q,
    (forall r, In r (type_paths A) ->
       exists s, In s (type_paths B) /\ path_sub s r) ->
    path_sub p q ->
    path_sub (st_ty A :: p) (st_ty B :: q)
| PS_record : forall l p q,
    path_sub p q ->
    path_sub (st_la l :: p) (st_la l :: q).

Fixpoint type_size (A : styp) : nat :=
  match A with
  | styp_top | styp_nat => 1
  | styp_and A B | styp_arrow A B => S (type_size A + type_size B)
  | styp_rcd _ A => S (type_size A)
  end.

Fixpoint path_size (p : ls) : nat :=
  match p with
  | [] => 0
  | st_ty A :: p => S (type_size A + path_size p)
  | st_la _ :: p => S (path_size p)
  end.

Lemma type_paths_smaller : forall A p,
    In p (type_paths A) -> path_size p < type_size A.
Proof.
  induction A as [| |A IHA B IHB|A IHA B IHB|l A IH];
    intros p Hp; simpl in Hp |- *.
  - contradiction.
  - destruct Hp as [<- | []]. simpl. lia.
  - apply in_app_or in Hp as [Hp | Hp].
    + specialize (IHA p Hp). lia.
    + specialize (IHB p Hp). lia.
  - apply in_map_iff in Hp as [q [<- Hq]].
    specialize (IHB q Hq). simpl. lia.
  - apply in_map_iff in Hp as [q [<- Hq]].
    specialize (IH q Hq). simpl. lia.
Qed.

Lemma path_sub_refl : forall p, path_sub p p.
Proof.
  induction p as [p IH] using
    (well_founded_induction (well_founded_ltof ls path_size)).
  destruct p as [|[A|l] p].
  - apply PS_nil.
  - apply PS_arrow.
    + intros r Hr. exists r. split; [exact Hr |].
      apply IH. unfold ltof. simpl.
      pose proof (type_paths_smaller A r Hr). lia.
    + apply IH. unfold ltof. simpl. lia.
  - apply PS_record. apply IH. unfold ltof. simpl. lia.
Qed.

Lemma path_sub_trans : forall q p r,
    path_sub p q -> path_sub q r -> path_sub p r.
Proof.
  induction q as [q IH] using
    (well_founded_induction (well_founded_ltof ls path_size)).
  intros p r Hpq Hqr.
  destruct Hpq as [|A B p q HBA Hpq|l p q Hpq].
  - exact Hqr.
  - inversion Hqr as [|A' C q' r' HCB Hqr'|]; subst.
    apply PS_arrow.
    + intros a Ha.
      destruct (HBA a Ha) as [b [Hb Hba]].
      destruct (HCB b Hb) as [d [Hd Hdb]].
      exists d. split; [exact Hd |].
      eapply (IH b).
      * unfold ltof. simpl. pose proof (type_paths_smaller B b Hb). lia.
      * exact Hdb.
      * exact Hba.
    + eapply (IH q); [unfold ltof; simpl; lia | exact Hpq | exact Hqr'].
  - inversion Hqr as [| |l' q' r' Hqr']; subst.
    apply PS_record.
    eapply (IH q); [unfold ltof; simpl; lia | exact Hpq | exact Hqr'].
Qed.

Definition paths_sub (fs : ls) (A B : styp) : Prop :=
  forall p, In p (type_paths B) ->
    exists q, In q (type_paths A) /\ path_sub q (fs ++ p).

Lemma paths_sub_incl : forall A B,
    incl (type_paths B) (type_paths A) -> paths_sub [] A B.
Proof.
  intros A B H p Hp.
  exists p. split; [now apply H | apply path_sub_refl].
Qed.

Lemma sub_paths : forall A B c, sub A B c -> paths_sub [] A B.
Proof.
  intros A B c H. induction H.
  - apply paths_sub_incl. intros p Hp. exact Hp.
  - intros r Hr.
    destruct (IHsub1 r Hr) as [q [Hq Hqr]].
    destruct (IHsub2 q Hq) as [p [Hp Hpq]].
    exists p. split; [exact Hp | eauto using path_sub_trans].
  - apply paths_sub_incl. intros p Hp. contradiction.
  - apply paths_sub_incl. intros p Hp. contradiction.
  - apply paths_sub_incl. intros p Hp. contradiction.
  - intros p Hp. simpl in Hp |- *.
    apply in_map_iff in Hp as [q [<- Hq]].
    destruct (IHsub2 q Hq) as [r [Hr Hrq]].
    exists (st_ty A1 :: r). split.
    + now apply in_map.
    + now apply PS_arrow.
  - intros p Hp. simpl in Hp.
    apply in_app_or in Hp as [Hp | Hp]; [now apply IHsub1 | now apply IHsub2].
  - apply paths_sub_incl. intros p Hp. apply in_or_app. now left.
  - apply paths_sub_incl. intros p Hp. apply in_or_app. now right.
  - apply paths_sub_incl. simpl. now rewrite map_app.
  - intros p Hp. simpl in Hp |- *.
    apply in_map_iff in Hp as [q [<- Hq]].
    destruct (IHsub q Hq) as [r [Hr Hrq]].
    exists (st_la l :: r). split.
    + now apply in_map.
    + now apply PS_record.
  - apply paths_sub_incl. simpl. now rewrite map_app.
Qed.

Lemma paths_sub_nat : forall fs A,
    paths_sub fs A styp_nat <->
    exists p, In p (type_paths A) /\ path_sub p fs.
Proof.
  intros fs A. split.
  - intros H. specialize (H [] (or_introl eq_refl)).
    now rewrite app_nil_r in H.
  - intros H p Hp. destruct Hp as [<- | []].
    now rewrite app_nil_r.
Qed.

Lemma path_size_app : forall fs gs,
    path_size (fs ++ gs) = path_size fs + path_size gs.
Proof.
  induction fs as [|[A|l] fs IH]; intros gs; simpl.
  - reflexivity.
  - rewrite IH. lia.
  - now rewrite IH.
Qed.

Lemma paths_ASub : forall fs A B,
    paths_sub fs A B -> exists c, ASub fs A B c.
Proof.
  intros fs A B.
  (* Moving a constructor from B to fs preserves the combined size
     and decreases the size of B. *)
  remember (type_size A + path_size fs + type_size B) as n eqn:Hn.
  remember (type_size B) as k eqn:Hk in |- *.
  revert fs A B Hn Hk.
  revert k.
  induction n as [n IH] using lt_wf_ind.
  intro k.
  induction k as [k IHk] using lt_wf_ind.
  intros fs A B Hn Hk H.
  assert (recur : forall gs S T,
      type_size S + path_size gs + type_size T < n \/
      (type_size S + path_size gs + type_size T = n /\ type_size T < k) ->
      paths_sub gs S T -> exists c, ASub gs S T c).
  {
    intros gs S T [Hlt | [Heq Hlt]].
    - exact (IH _ Hlt _ gs S T eq_refl eq_refl).
    - exact (IHk _ Hlt gs S T (eq_sym Heq) eq_refl).
  }
  destruct B as [| |B1 B2|B1 B2|l B].
  - eexists. apply A_top.
  - apply paths_sub_nat in H as [p [Hp Hpf]].
    destruct A as [| |A1 A2|A1 A2|l A]; simpl in Hp.
    + contradiction.
    + destruct Hp as [<- | []]. inversion Hpf; subst.
      exists co_id. apply A_nat.
    + apply in_app_or in Hp as [Hp | Hp].
      * assert (H1 : paths_sub fs A1 styp_nat).
        { apply paths_sub_nat. exists p. now split. }
        destruct (recur fs A1 styp_nat
                    ltac:(left; simpl in Hn |- *; lia) H1) as [c Hc].
        exists (co_trans c co_proj1). now apply A_andN1.
      * assert (H2 : paths_sub fs A2 styp_nat).
        { apply paths_sub_nat. exists p. now split. }
        destruct (recur fs A2 styp_nat
                    ltac:(left; simpl in Hn |- *; lia) H2) as [c Hc].
        exists (co_trans c co_proj2). now apply A_andN2.
    + apply in_map_iff in Hp as [q [<- Hq]].
      inversion Hpf as [|A' B' q' gs Hdom Htail|]; subst.
      assert (H1 : paths_sub [] B' A1) by exact Hdom.
      assert (H2 : paths_sub gs A2 styp_nat).
      { apply paths_sub_nat. exists q. now split. }
      destruct (recur [] B' A1 ltac:(left; simpl; lia) H1) as [c1 Hc1].
      destruct (recur gs A2 styp_nat ltac:(left; simpl; lia) H2) as [c2 Hc2].
      exists (co_arr c1 c2). now apply A_arrNat.
    + apply in_map_iff in Hp as [q [<- Hq]].
      inversion Hpf as [| |l' q' gs Htail]; subst.
      assert (H1 : paths_sub gs A styp_nat).
      { apply paths_sub_nat. exists q. now split. }
      destruct (recur gs A styp_nat ltac:(left; simpl; lia) H1) as [c Hc].
      eexists. exact (A_rcdNat _ gs A c Hc).
  - assert (H1 : paths_sub fs A B1).
    { intros p Hp. apply H. apply in_or_app. now left. }
    assert (H2 : paths_sub fs A B2).
    { intros p Hp. apply H. apply in_or_app. now right. }
    destruct (recur fs A B1 ltac:(left; simpl in Hn; lia) H1) as [c1 Hc1].
    destruct (recur fs A B2 ltac:(left; simpl in Hn; lia) H2) as [c2 Hc2].
    exists (co_trans (calAnd fs) (co_pair c1 c2)). now apply A_and.
  - assert (H1 : paths_sub (fs ++ [st_ty B1]) A B2).
    { intros p Hp. rewrite <- app_assoc. apply H. now apply in_map. }
    destruct (recur (fs ++ [st_ty B1]) A B2
                ltac:(right; rewrite path_size_app; simpl in Hn, Hk |- *; lia)
                H1) as [c Hc].
    exists c. now apply A_arr.
  - assert (H1 : paths_sub (fs ++ [st_la l]) A B).
    { intros p Hp. rewrite <- app_assoc. apply H. now apply in_map. }
    destruct (recur (fs ++ [st_la l]) A B
                ltac:(right; rewrite path_size_app; simpl in Hn, Hk |- *; lia)
                H1) as [c Hc].
    exists c. now apply A_rcd.
Qed.

Theorem sub2ASub : forall A B c,
    sub A B c -> exists c', ASub nil A B c'.
Proof.
  intros A B c H. apply paths_ASub. now apply sub_paths in H.
Qed.
