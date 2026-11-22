Set Implicit Arguments.

From TLC Require Import LibLN.

Require Import Full_ott Full_Infra.

Require Import Lia List.
From Stdlib Require Import Program.Equality.

Implicit Types x : var.

(* Mutual structural induction over [sub] and [wf].  This is needed for
   scope invariants (free variables of everything mentioned in a typing
   or in a well-formed environment's bindings live in the domain).       *)
Scheme sub_wf_mut := Induction for sub Sort Prop
  with wf_mut := Induction for wf Sort Prop.

(* Membership in the domain of a binding. *)
Lemma binds_in_dom : forall (G : env) (x : var) (v : binding),
  binds x v G -> x \in dom G.
Proof. intros G x v H. unfold binds in H. exact (get_some_inv H). Qed.

(* Free-variable behaviour of opening: opening does not remove free
   variables, and every free variable of the opened term is either a free
   variable of the original term or belongs to the opening argument.     *)

Lemma fv_open_rec_lower : forall e,
  forall k v z, z \in fv_trm e ->
    z \in fv_trm (open_trm_wrt_trm_rec k v e).
Proof.
  induction e as [n | y | | | e1 IHe1 e2 IHe2 | e1 IHe1 A IHA e2 IHe2
               | e IHe A IHA B IHB | A IHA e IHe | e IHe | e IHe A IHA ];
  intros k v z Hz; simpl in *.
  - rewrite in_empty in Hz. destruct Hz.
  - rewrite in_singleton in Hz. rewrite in_singleton. exact Hz.
  - rewrite in_empty in Hz. destruct Hz.
  - rewrite in_empty in Hz. destruct Hz.
  - assert (L1 : z \in fv_trm e1 -> z \in fv_trm (open_trm_wrt_trm_rec k v e1))
      by (intros H; exact (IHe1 k v z H)).
    assert (L2 : z \in fv_trm e2 -> z \in fv_trm (open_trm_wrt_trm_rec k v e2))
      by (intros H; exact (IHe2 k v z H)).
    repeat rewrite in_union in *. tauto.
  - assert (L1 : z \in fv_trm e1 -> z \in fv_trm (open_trm_wrt_trm_rec k v e1))
      by (intros H; exact (IHe1 k v z H)).
    assert (LA : z \in fv_trm A -> z \in fv_trm (open_trm_wrt_trm_rec k v A))
      by (intros H; exact (IHA k v z H)).
    assert (L2 : z \in fv_trm e2 -> z \in fv_trm (open_trm_wrt_trm_rec (S k) v e2))
      by (intros H; exact (IHe2 (S k) v z H)).
    repeat rewrite in_union in *. tauto.
  - assert (L1 : z \in fv_trm e -> z \in fv_trm (open_trm_wrt_trm_rec k v e))
      by (intros H; exact (IHe k v z H)).
    assert (LA : z \in fv_trm A -> z \in fv_trm (open_trm_wrt_trm_rec k v A))
      by (intros H; exact (IHA k v z H)).
    assert (LB : z \in fv_trm B -> z \in fv_trm (open_trm_wrt_trm_rec (S k) v B))
      by (intros H; exact (IHB (S k) v z H)).
    repeat rewrite in_union in *. tauto.
  - assert (LA : z \in fv_trm A -> z \in fv_trm (open_trm_wrt_trm_rec k v A))
      by (intros H; exact (IHA k v z H)).
    assert (L1 : z \in fv_trm e -> z \in fv_trm (open_trm_wrt_trm_rec k v e))
      by (intros H; exact (IHe k v z H)).
    repeat rewrite in_union in *. tauto.
  - exact (IHe k v z Hz).
  - assert (L1 : z \in fv_trm e -> z \in fv_trm (open_trm_wrt_trm_rec k v e))
      by (intros H; exact (IHe k v z H)).
    assert (LA : z \in fv_trm A -> z \in fv_trm (open_trm_wrt_trm_rec k v A))
      by (intros H; exact (IHA k v z H)).
    repeat rewrite in_union in *. tauto.
Qed.

Lemma fv_open_rec_upper : forall e,
  forall k v z, z \in fv_trm (open_trm_wrt_trm_rec k v e) ->
    z \in fv_trm e \u fv_trm v.
Proof.
  induction e as [n | y | | | e1 IHe1 e2 IHe2 | e1 IHe1 A IHA e2 IHe2
               | e IHe A IHA B IHB | A IHA e IHe | e IHe | e IHe A IHA ];
  intros k v z Hz; simpl in *.
  - destruct (classic (k = n)) as [Hk|Hk].
    + rewrite If_l in Hz by exact Hk. simpl in Hz.
      rewrite in_union. right. exact Hz.
    + rewrite If_r in Hz by exact Hk. simpl in Hz.
      rewrite in_empty in Hz. destruct Hz.
  - rewrite in_singleton in Hz. rewrite in_union. left.
    rewrite in_singleton. exact Hz.
  - rewrite in_empty in Hz. destruct Hz.
  - rewrite in_empty in Hz. destruct Hz.
  - assert (L1 : z \in fv_trm (open_trm_wrt_trm_rec k v e1) -> z \in fv_trm e1 \u fv_trm v)
      by (intros H; exact (IHe1 k v z H)).
    assert (L2 : z \in fv_trm (open_trm_wrt_trm_rec k v e2) -> z \in fv_trm e2 \u fv_trm v)
      by (intros H; exact (IHe2 k v z H)).
    repeat rewrite in_union in *. tauto.
  - assert (L1 : z \in fv_trm (open_trm_wrt_trm_rec k v e1) -> z \in fv_trm e1 \u fv_trm v)
      by (intros H; exact (IHe1 k v z H)).
    assert (LA : z \in fv_trm (open_trm_wrt_trm_rec k v A) -> z \in fv_trm A \u fv_trm v)
      by (intros H; exact (IHA k v z H)).
    assert (L2 : z \in fv_trm (open_trm_wrt_trm_rec (S k) v e2) -> z \in fv_trm e2 \u fv_trm v)
      by (intros H; exact (IHe2 (S k) v z H)).
    repeat rewrite in_union in *. tauto.
  - assert (L1 : z \in fv_trm (open_trm_wrt_trm_rec k v e) -> z \in fv_trm e \u fv_trm v)
      by (intros H; exact (IHe k v z H)).
    assert (LA : z \in fv_trm (open_trm_wrt_trm_rec k v A) -> z \in fv_trm A \u fv_trm v)
      by (intros H; exact (IHA k v z H)).
    assert (LB : z \in fv_trm (open_trm_wrt_trm_rec (S k) v B) -> z \in fv_trm B \u fv_trm v)
      by (intros H; exact (IHB (S k) v z H)).
    repeat rewrite in_union in *. tauto.
  - assert (LA : z \in fv_trm (open_trm_wrt_trm_rec k v A) -> z \in fv_trm A \u fv_trm v)
      by (intros H; exact (IHA k v z H)).
    assert (L1 : z \in fv_trm (open_trm_wrt_trm_rec k v e) -> z \in fv_trm e \u fv_trm v)
      by (intros H; exact (IHe k v z H)).
    repeat rewrite in_union in *. tauto.
  - exact (IHe k v z Hz).
  - assert (L1 : z \in fv_trm (open_trm_wrt_trm_rec k v e) -> z \in fv_trm e \u fv_trm v)
      by (intros H; exact (IHe k v z H)).
    assert (LA : z \in fv_trm (open_trm_wrt_trm_rec k v A) -> z \in fv_trm A \u fv_trm v)
      by (intros H; exact (IHA k v z H)).
    repeat rewrite in_union in *. tauto.
Qed.

Lemma fv_open_lower : forall e v z, z \in fv_trm e ->
  z \in fv_trm (open_trm_wrt_trm e v).
Proof. intros e v z H. exact (@fv_open_rec_lower e 0 v z H). Qed.

Lemma fv_open_upper : forall e v z,
  z \in fv_trm (open_trm_wrt_trm e v) ->
  z \in fv_trm e \u fv_trm v.
Proof. intros e v z H. exact (@fv_open_rec_upper e 0 v z H). Qed.

(* ********************************************************************** *)
(* Syntactic preliminaries                                                *)
(* ********************************************************************** *)

Definition open_var_rec (k:nat) (x:var) (e:trm) : trm :=
  open_trm_wrt_trm_rec k (trm_var_f x) e.

(* [nb m e] : every de Bruijn index in [e] is bound, where the outermost
   [m] levels are considered bound by an enclosing context.  In other
   words, index [n] occurring under [d] binders satisfies [n < m + d]. *)

Inductive nb (m:nat) : trm -> Prop :=
 | nb_var_b : forall n, n < m -> nb m (trm_var_b n)
 | nb_var_f : forall x, nb m (trm_var_f x)
 | nb_star : nb m trm_star
 | nb_top : nb m trm_top
 | nb_app : forall e1 e2, nb m e1 -> nb m e2 -> nb m (trm_app e1 e2)
 | nb_abs : forall e1 A e2, nb m e1 -> nb m A -> nb (S m) e2 ->
      nb m (trm_abs e1 A e2)
 | nb_prod : forall e A B, nb m e -> nb m A -> nb (S m) B ->
      nb m (trm_prod e A B)
 | nb_castup : forall A e, nb m A -> nb m e -> nb m (trm_castup A e)
 | nb_castdn : forall e, nb m e -> nb m (trm_castdn e)
 | nb_anno : forall e A, nb m e -> nb m A -> nb m (trm_anno e A).

Lemma lc_var_b_inv : forall n, ~ lc_trm (trm_var_b n).
Proof. intros n H. inversion H. Qed.

Lemma nb_open_rec_ge : forall m e, nb m e ->
  forall k, m <= k -> forall a, open_trm_wrt_trm_rec k a e = e.
Proof.
  intros m e H. induction H; intros k Hk a; simpl.
  - (* var_b *) apply If_r. lia.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - (* app *) rewrite IHnb1; auto. rewrite IHnb2; auto.
  - (* abs *) rewrite IHnb1; auto. rewrite IHnb2; auto.
    erewrite IHnb3; [reflexivity|lia].
  - (* prod *) rewrite IHnb1; auto. rewrite IHnb2; auto.
    erewrite IHnb3; [reflexivity|lia].
  - (* castup *) rewrite IHnb1; auto. rewrite IHnb2; auto.
  - (* castdn *) rewrite IHnb; auto.
  - (* anno *) rewrite IHnb1; auto. rewrite IHnb2; auto.
Qed.

Fixpoint open_many_from (k:nat) (xs:list var) (e:trm) : trm :=
  match xs with
  | nil => e
  | x :: xs' => open_trm_wrt_trm_rec k (trm_var_f x)
                    (open_many_from (S k) xs' e)
  end.

Lemma om_var_f : forall xs k x,
  open_many_from k xs (trm_var_f x) = trm_var_f x.
Proof.
  intros xs. induction xs as [|y ys IH]; intros k x; simpl.
  - reflexivity.
  - rewrite IH. reflexivity.
Qed.

Lemma om_star : forall xs k, open_many_from k xs trm_star = trm_star.
Proof.
  intros xs. induction xs as [|y ys IH]; intros k; simpl.
  - reflexivity.
  - rewrite IH. reflexivity.
Qed.

Lemma om_top : forall xs k, open_many_from k xs trm_top = trm_top.
Proof.
  intros xs. induction xs as [|y ys IH]; intros k; simpl.
  - reflexivity.
  - rewrite IH. reflexivity.
Qed.

Lemma om_app : forall xs k e1 e2,
  open_many_from k xs (trm_app e1 e2) =
  trm_app (open_many_from k xs e1) (open_many_from k xs e2).
Proof.
  intros xs. induction xs as [|y ys IH]; intros k e1 e2; simpl.
  - reflexivity.
  - rewrite IH. reflexivity.
Qed.

Lemma om_abs : forall xs k e1 A e2,
  open_many_from k xs (trm_abs e1 A e2) =
  trm_abs (open_many_from k xs e1) (open_many_from k xs A)
          (open_many_from (S k) xs e2).
Proof.
  intros xs. induction xs as [|y ys IH]; intros k e1 A e2; simpl.
  - reflexivity.
  - rewrite IH. reflexivity.
Qed.

Lemma om_prod : forall xs k e A B,
  open_many_from k xs (trm_prod e A B) =
  trm_prod (open_many_from k xs e) (open_many_from k xs A)
           (open_many_from (S k) xs B).
Proof.
  intros xs. induction xs as [|y ys IH]; intros k e A B; simpl.
  - reflexivity.
  - rewrite IH. reflexivity.
Qed.

Lemma om_castup : forall xs k A e,
  open_many_from k xs (trm_castup A e) =
  trm_castup (open_many_from k xs A) (open_many_from k xs e).
Proof.
  intros xs. induction xs as [|y ys IH]; intros k A e; simpl.
  - reflexivity.
  - rewrite IH. reflexivity.
Qed.

Lemma om_castdn : forall xs k e,
  open_many_from k xs (trm_castdn e) = trm_castdn (open_many_from k xs e).
Proof.
  intros xs. induction xs as [|y ys IH]; intros k e; simpl.
  - reflexivity.
  - rewrite IH. reflexivity.
Qed.

Lemma om_anno : forall xs k e A,
  open_many_from k xs (trm_anno e A) =
  trm_anno (open_many_from k xs e) (open_many_from k xs A).
Proof.
  intros xs. induction xs as [|y ys IH]; intros k e A; simpl.
  - reflexivity.
  - rewrite IH. reflexivity.
Qed.

Lemma om_var_b_ge : forall xs k n, k + length xs <= n ->
  open_many_from k xs (trm_var_b n) = trm_var_b n.
Proof.
  intros xs. induction xs as [|y ys IH]; intros k n Hle; simpl in *.
  - reflexivity.
  - assert (Hle' : S k + length ys <= n) by lia.
    rewrite (IH (S k) n Hle').
    apply If_r. lia.
Qed.

(* [open_many_from] with a list of length [m] does not touch indices that
   are at least [m] levels above the root. *)

Lemma nb_of_lc_open : forall m xs e, length xs = m ->
  lc_trm (open_many_from 0 xs e) -> nb m e.
Proof.
  intros m xs e. revert m xs.
  induction e as [n | x | | | e1 IHe1 e2 IHe2 | e1 IHe1 A IHA e2 IHe2 | e IHe A IHA B IHB | A IHA e IHe | e IHe | e IHe A IHA ];
  intros m xs Hlen Hlc.
  - (* var_b *)
    destruct (classic (n < m)) as [Hlt|Hge].
    + apply nb_var_b; auto.
    + exfalso.
      rewrite (@om_var_b_ge xs 0 n) in Hlc by lia.
      apply lc_var_b_inv in Hlc. auto.
  - (* var_f *) rewrite om_var_f in Hlc. apply nb_var_f.
  - (* star *) rewrite om_star in Hlc. apply nb_star.
  - (* top *) rewrite om_top in Hlc. apply nb_top.
  - (* app *)
    rewrite om_app in Hlc. inversion Hlc; subst.
    apply nb_app.
    + apply (IHe1 (length xs) xs); auto.
    + apply (IHe2 (length xs) xs); auto.
  - (* abs *)
    rewrite om_abs in Hlc.
    inversion Hlc as [| | | | LL e1' A' e2' Hc1 Hc2 Hbody| | | |]; subst.
    apply nb_abs.
    + apply (IHe1 (length xs) xs); auto.
    + apply (IHA (length xs) xs); auto.
    + destruct (var_fresh LL) as [y Hy].
      apply (IHe2 (S (length xs)) (y :: xs)).
      * simpl. lia.
      * change (lc_trm (open_many_from 0 (y :: xs) e2)). apply Hbody; auto.
  - (* prod *)
    rewrite om_prod in Hlc.
    inversion Hlc as [| | | | | LL e' A' B' Hc1 Hc2 Hbody| | |]; subst.
    apply nb_prod.
    + apply (IHe (length xs) xs); auto.
    + apply (IHA (length xs) xs); auto.
    + destruct (var_fresh LL) as [y Hy].
      apply (IHB (S (length xs)) (y :: xs)).
      * simpl. lia.
      * change (lc_trm (open_many_from 0 (y :: xs) B)). apply Hbody; auto.
  - (* castup *)
    rewrite om_castup in Hlc. inversion Hlc; subst.
    apply nb_castup.
    + apply (IHA (length xs) xs); auto.
    + apply (IHe (length xs) xs); auto.
  - (* castdn *)
    rewrite om_castdn in Hlc. inversion Hlc; subst.
    apply nb_castdn. apply (IHe (length xs) xs); auto.
  - (* anno *)
    rewrite om_anno in Hlc. inversion Hlc; subst.
    apply nb_anno.
    + apply (IHe (length xs) xs); auto.
    + apply (IHA (length xs) xs); auto.
Qed.

Lemma lc_nb : forall e, lc_trm e -> nb 0 e.
Proof.
  intros e H. apply (@nb_of_lc_open 0 nil e); auto.
Qed.

Lemma lc_closed_all : forall e, lc_trm e ->
  forall k x, open_trm_wrt_trm_rec k (trm_var_f x) e = e.
Proof.
  intros e Hlc k x. apply (@nb_open_rec_ge 0 e). apply lc_nb; auto. lia.
Qed.

(* Substituting a variable for a free variable commutes with opening at a
   different (variable) level, provided the substituted term is locally
   closed. *)

Lemma subst_trm_var_f_eq : forall a x,
  subst_trm a x (trm_var_f x) = a.
Proof. intros. simpl. rewrite If_l; auto. Qed.

Lemma subst_trm_var_f_neq : forall a x y, y <> x ->
  subst_trm a x (trm_var_f y) = trm_var_f y.
Proof. intros. simpl. rewrite If_r; auto. Qed.

Lemma subst_trm_var_b : forall a x n,
  subst_trm a x (trm_var_b n) = trm_var_b n.
Proof. reflexivity. Qed.

Lemma subst_open_var_comm : forall argv x z,
  (forall k, open_trm_wrt_trm_rec k (trm_var_f z) argv = argv) ->
  x <> z ->
  forall e k,
  subst_trm argv x (open_trm_wrt_trm_rec k (trm_var_f z) e) =
  open_trm_wrt_trm_rec k (trm_var_f z) (subst_trm argv x e).
Proof.
  intros argv x z Hcl Hxz e.
  induction e as [n | y | | | e1 IHe1 e2 IHe2 | e1 IHe1 A IHA e2 IHe2
                | e IHe A IHA B IHB | A IHA e IHe | e IHe | e IHe A IHA ];
  intros k; simpl.
  - (* var_b *)
    destruct (classic (k = n)) as [Heq|Hneq].
    + subst k. rewrite If_l; auto. simpl.
      apply subst_trm_var_f_neq. auto.
    + rewrite If_r; auto.
  - (* var_f *)
    destruct (classic (y = x)) as [->|Hyx].
    + rewrite If_l; auto.
    + rewrite If_r; auto.
  - reflexivity.
  - reflexivity.
  - (* app *) rewrite IHe1; auto. rewrite IHe2; auto.
  - (* abs *) rewrite IHe1; auto. rewrite IHA; auto. rewrite IHe2; auto.
  - (* prod *) rewrite IHe; auto. rewrite IHA; auto. rewrite IHB; auto.
  - (* castup *) rewrite IHA; auto. rewrite IHe; auto.
  - (* castdn *) rewrite IHe; auto.
  - (* anno *) rewrite IHe; auto. rewrite IHA; auto.
Qed.

Lemma lc_subst_open_var_comm : forall e argv x z,
  lc_trm argv -> x <> z ->
  forall k,
  subst_trm argv x (open_trm_wrt_trm_rec k (trm_var_f z) e) =
  open_trm_wrt_trm_rec k (trm_var_f z) (subst_trm argv x e).
Proof.
  intros. apply subst_open_var_comm; auto.
  intros k'. apply lc_closed_all; auto.
Qed.

(* Opening with a variable and then substituting that variable *)

Lemma subst_open_compose_gen : forall e argv x,
  x \notin fv_trm e ->
  forall k,
  subst_trm argv x (open_trm_wrt_trm_rec k (trm_var_f x) e) =
  open_trm_wrt_trm_rec k argv e.
Proof.
  induction e as [n | y | | | e1 IHe1 e2 IHe2 | e1 IHe1 A IHA e2 IHe2
                | e IHe A IHA B IHB | A IHA e IHe | e IHe | e IHe A IHA ];
  intros argv x Hfv k; simpl in *.
  - (* var_b *)
    destruct (classic (k = n)) as [Heq|Hneq].
    + subst k. rewrite If_l; auto. rewrite subst_trm_var_f_eq.
      rewrite If_l; auto.
    + rewrite If_r; auto. rewrite If_r; auto.
  - (* var_f *)
    apply notin_singleton_r in Hfv.
    rewrite If_r; [reflexivity|]. intro H; apply Hfv; symmetry; auto.
  - reflexivity.
  - reflexivity.
  - (* app *)
    apply notin_union_r in Hfv. destruct Hfv as [H1 H2].
    rewrite (IHe1 argv x H1 k), (IHe2 argv x H2 k). reflexivity.
  - (* abs *)
    apply notin_union_r in Hfv. destruct Hfv as [H1 Hrest].
    apply notin_union_r in Hrest. destruct Hrest as [HA H2].
    rewrite (IHe1 argv x H1 k), (IHA argv x HA k), (IHe2 argv x H2 (S k)).
    reflexivity.
  - (* prod *)
    apply notin_union_r in Hfv. destruct Hfv as [H1 Hrest].
    apply notin_union_r in Hrest. destruct Hrest as [HA HB].
    rewrite (IHe argv x H1 k), (IHA argv x HA k), (IHB argv x HB (S k)).
    reflexivity.
  - (* castup *)
    apply notin_union_r in Hfv. destruct Hfv as [HA H1].
    rewrite (IHA argv x HA k), (IHe argv x H1 k). reflexivity.
  - (* castdn *)
    rewrite (IHe argv x Hfv k). reflexivity.
  - (* anno *)
    apply notin_union_r in Hfv. destruct Hfv as [H1 HA].
    rewrite (IHe argv x H1 k), (IHA argv x HA k). reflexivity.
Qed.

Lemma subst_open_compose : forall e argv x,
  x \notin fv_trm e ->
  subst_trm argv x (open_trm_wrt_trm_rec 0 (trm_var_f x) e) =
  open_trm_wrt_trm_rec 0 argv e.
Proof. intros. exact (@subst_open_compose_gen e argv x H 0). Qed.

(* Basic facts about [nb]. *)

Lemma nb_mono : forall m e, nb m e -> nb (S m) e.
Proof.
  intros m e H. induction H.
  - apply nb_var_b; lia.
  - apply nb_var_f.
  - apply nb_star.
  - apply nb_top.
  - apply nb_app; auto.
  - apply nb_abs; auto.
  - apply nb_prod; auto.
  - apply nb_castup; auto.
  - apply nb_castdn; auto.
  - apply nb_anno; auto.
Qed.

Lemma nb_subst : forall m e argv x, nb m e -> nb m argv ->
  nb m (subst_trm argv x e).
Proof.
  intros m e argv x H. induction H; intros Harg; simpl.
  - apply nb_var_b; auto.
  - destruct (classic (x0 = x)) as [Heq|Hneq].
    + subst x0. rewrite If_l; auto.
    + rewrite If_r; auto. apply nb_var_f.
  - apply nb_star.
  - apply nb_top.
  - apply nb_app; auto.
  - apply nb_abs; auto. apply IHnb3. apply nb_mono; auto.
  - apply nb_prod; auto. apply IHnb3. apply nb_mono; auto.
  - apply nb_castup; auto.
  - apply nb_castdn; auto.
  - apply nb_anno; auto.
Qed.

Lemma nb_open_rec_lc : forall m e, nb m e -> forall k a, nb m a -> nb m (open_trm_wrt_trm_rec k a e).
Proof.
  intros m e H. induction H; intros k b Hb; simpl.
  - destruct (classic (k = n)) as [Heq|Hneq].
    + subst k. rewrite If_l; auto.
    + rewrite If_r; auto. apply nb_var_b; auto.
  - apply nb_var_f.
  - apply nb_star.
  - apply nb_top.
  - apply nb_app; auto.
  - apply nb_abs; auto. apply IHnb3. apply nb_mono; auto.
  - apply nb_prod; auto. apply IHnb3. apply nb_mono; auto.
  - apply nb_castup; auto.
  - apply nb_castdn; auto.
  - apply nb_anno; auto.
Qed.

(* ********************************************************************** *)
(* More opening lemmas and the converse of [lc_nb]                        *)
(* ********************************************************************** *)

Lemma om_var_b_lt : forall xs k n, n < k ->
  open_many_from k xs (trm_var_b n) = trm_var_b n.
Proof.
  intros xs. induction xs as [|y ys IH]; intros k n Hlt; simpl.
  - reflexivity.
  - rewrite IH by lia.
    apply If_r. lia.
Qed.

Lemma om_var_b_var : forall xs k n, k <= n < k + length xs ->
  exists x, In x xs /\ open_many_from k xs (trm_var_b n) = trm_var_f x.
Proof.
  intros xs. induction xs as [|y ys IH]; intros k n Hlt; simpl in *.
  - lia.
  - destruct (classic (k = n)) as [Heq|Hneq].
    + subst n. exists y. split; [left; reflexivity|].
      rewrite om_var_b_lt by lia.
      simpl. rewrite If_l; auto.
    + assert (Hkn : k < n) by lia.
      assert (Hlt' : S k <= n < S k + length ys) by lia.
      destruct (IH (S k) n Hlt') as [x [Hin Hx]].
      exists x. split; [right; auto|].
      rewrite Hx. reflexivity.
Qed.

Lemma lc_om_var_b : forall xs n, n < length xs ->
  lc_trm (open_many_from 0 xs (trm_var_b n)).
Proof.
  intros xs n Hlt.
  assert (Hin : 0 <= n < 0 + length xs) by lia.
  destruct (om_var_b_var xs Hin) as [x [_ Hx]].
  rewrite Hx. apply lc_trm_var_f.
Qed.

Lemma nb_lc_multi : forall m e, nb m e ->
  forall xs, length xs = m -> lc_trm (open_many_from 0 xs e).
Proof.
  intros m e H. induction H; intros xs Hlen; simpl.
  - apply lc_om_var_b. lia.
  - rewrite om_var_f. apply lc_trm_var_f.
  - rewrite om_star. apply lc_trm_star.
  - rewrite om_top. apply lc_trm_top.
  - rewrite om_app. apply lc_trm_app; auto.
  - rewrite om_abs.
    apply (@lc_trm_abs \{});
      [ auto | auto | ].
    intros y Hy.
    apply (IHnb3 (y :: xs)). simpl. lia.
  - rewrite om_prod.
    apply (@lc_trm_prod \{});
      [ auto | auto | ].
    intros y Hy.
    apply (IHnb3 (y :: xs)). simpl. lia.
  - rewrite om_castup. apply lc_trm_castup; auto.
  - rewrite om_castdn. apply lc_trm_castdn; auto.
  - rewrite om_anno. apply lc_trm_anno; auto.
Qed.

Lemma lc_of_nb : forall e, nb 0 e -> lc_trm e.
Proof.
  intros e H. apply (@nb_lc_multi 0 e H nil). reflexivity.
Qed.

Lemma lc_subst : forall e a x, lc_trm e -> lc_trm a ->
  lc_trm (subst_trm a x e).
Proof.
  intros e a x He Ha.
  apply lc_of_nb. apply nb_subst.
  - apply lc_nb; auto.
  - apply lc_nb; auto.
Qed.

(* ********************************************************************** *)
(* Substitution commutes with opening (arbitrary replacement)             *)
(* ********************************************************************** *)

Lemma subst_open_rec_comm_gen : forall argv x,
  lc_trm argv ->
  forall e k b,
  subst_trm argv x (open_trm_wrt_trm_rec k b e) =
  open_trm_wrt_trm_rec k (subst_trm argv x b) (subst_trm argv x e).
Proof.
  intros argv x Hlc e.
  induction e as [n | y | | | e1 IHe1 e2 IHe2 | e1 IHe1 A IHA e2 IHe2
                | e IHe A IHA B IHB | A IHA e IHe | e IHe | e IHe A IHA ];
  intros k b; simpl.
  - (* var_b *)
    destruct (classic (k = n)) as [Heq|Hneq].
    + subst k. rewrite If_l; auto. rewrite If_l; auto.
    + rewrite If_r; auto. rewrite If_r; auto.
  - (* var_f *)
    destruct (classic (y = x)) as [Heq|Hneq].
    + subst y. rewrite If_l; auto. symmetry.
      exact (@nb_open_rec_ge 0 argv (lc_nb Hlc) k ltac:(lia) (subst_trm argv x b)).
    + rewrite If_r; auto.
  - reflexivity.
  - reflexivity.
  - (* app *) rewrite IHe1; auto. rewrite IHe2; auto.
  - (* abs *) rewrite IHe1; auto. rewrite IHA; auto. rewrite IHe2; auto.
  - (* prod *) rewrite IHe; auto. rewrite IHA; auto. rewrite IHB; auto.
  - (* castup *) rewrite IHA; auto. rewrite IHe; auto.
  - (* castdn *) rewrite IHe; auto.
  - (* anno *) rewrite IHe; auto. rewrite IHA; auto.
Qed.

Lemma lc_abs_inv : forall e A b, lc_trm (trm_abs e A b) ->
  lc_trm e /\ lc_trm A.
Proof. intros e A b H. inversion H; auto. Qed.

Lemma lc_app_inv : forall e1 e2, lc_trm (trm_app e1 e2) ->
  lc_trm e1 /\ lc_trm e2.
Proof. intros e1 e2 H. inversion H; auto. Qed.

Lemma lc_castup_inv : forall A e, lc_trm (trm_castup A e) ->
  lc_trm A /\ lc_trm e.
Proof. intros A e H. inversion H; auto. Qed.

(* ********************************************************************** *)
(* Reduction: inversions, determinism, substitution                       *)
(* ********************************************************************** *)

Lemma reduct_var_b_inv : forall n t, ~ reduct (trm_var_b n) t.
Proof. intros n t H. inversion H. Qed.

Lemma reduct_var_f_inv : forall x t, ~ reduct (trm_var_f x) t.
Proof. intros x t H. inversion H. Qed.

Lemma reduct_star_inv : forall t, ~ reduct trm_star t.
Proof. intros t H. inversion H. Qed.

Lemma reduct_top_inv : forall t, ~ reduct trm_top t.
Proof. intros t H. inversion H. Qed.

Lemma reduct_abs_inv : forall e A b t, ~ reduct (trm_abs e A b) t.
Proof. intros e A b t H. inversion H. Qed.

Lemma reduct_prod_inv : forall e A B t, ~ reduct (trm_prod e A B) t.
Proof. intros e A B t H. inversion H. Qed.

Lemma reduct_castup_inv : forall A e t, ~ reduct (trm_castup A e) t.
Proof. intros A e t H. inversion H. Qed.

Lemma reduct_anno_inv : forall e A t, ~ reduct (trm_anno e A) t.
Proof. intros e A t H. inversion H. Qed.

Lemma reduct_subst : forall argv x, lc_trm argv ->
  forall t u, reduct t u ->
  reduct (subst_trm argv x t) (subst_trm argv x u).
Proof.
  intros argv x Hlc t u Hred. induction Hred; simpl.
  - (* beta *)
    change (reduct
      (trm_app (trm_abs (subst_trm argv x e3) (subst_trm argv x A) (subst_trm argv x e1))
               (subst_trm argv x e2))
      (subst_trm argv x (open_trm_wrt_trm_rec 0 e2 e1))).
    rewrite subst_open_rec_comm_gen; auto.
    apply reduct_beta.
    + apply lc_subst; auto.
    + apply lc_subst; auto.
    + inversion H1 as [| | | | L0 d1 Ad b Hd1 HdA Hbody| | | |]; subst.
      apply (@lc_trm_abs (L0 \u \{x})).
      * apply lc_subst; auto.
      * apply lc_subst; auto.
      * intros z Hz.
        apply notin_union_r1 in Hz as Hz0.
        apply notin_union_r2 in Hz as Hzx.
        apply notin_singleton_r in Hzx.
        pose proof (Hbody z Hz0) as Hzb.
        pose proof (@lc_subst (e1 ^ z) argv x Hzb Hlc) as Hzs.
        change (lc_trm (subst_trm argv x
                  (open_trm_wrt_trm_rec 0 (trm_var_f z) e1))) in Hzs.
        rewrite (@lc_subst_open_var_comm e1 argv x z
                   Hlc (not_eq_sym Hzx) 0) in Hzs.
        exact Hzs.
    + apply lc_subst; auto.
  - (* app congruence *)
    apply reduct_app.
    + apply lc_subst; auto.
    + auto.
  - (* castdn congruence *) apply reduct_castdn; auto.
  - (* castelim *)
    apply reduct_castelim.
    + apply lc_subst; auto.
    + apply lc_subst; auto.
Qed.

Lemma reduct_det : forall t u, reduct t u -> forall v, reduct t v -> u = v.
Proof.
  intros t u H.
  induction H as [ e3 A e1 e2 Hlc3 HlcA Hlcabs Hlc2
                 | e1 e2 e1' Hlc2 Hred IHred
                 | e1 e1' Hred IHred
                 | A e HlcA Hlce ];
  intros v Hv.
  - (* beta *)
    inversion Hv; subst.
    + reflexivity.
    + exfalso. eapply reduct_abs_inv; eauto.
  - (* app congruence *)
    inversion Hv; subst.
    + exfalso. eapply reduct_abs_inv; eauto.
    + rewrite (IHred e1'0); auto.
  - (* castdn congruence *)
    inversion Hv; subst.
    + rewrite (IHred e1'0); auto.
    + exfalso. eapply reduct_castup_inv; eauto.
  - (* castelim *)
    inversion Hv; subst.
    + exfalso. eapply reduct_castup_inv; eauto.
    + reflexivity.
Qed.

(* ********************************************************************** *)
(* Typing metatheory basics                                               *)
(* ********************************************************************** *)

Lemma sub_wf : forall G e1 e2 A, sub G e1 e2 A -> wf G.
Proof.
  intros G e1 e2 A H. induction H; auto.
Qed.

Lemma wf_cons_inv : forall G x e A,
  wf (G & x ~ bind_sub e A) -> wf G /\ sub G e e A /\ sub G A A trm_star /\ x # G.
Proof.
  intros G x e A H. inversion H; subst.
  - apply empty_push_inv in H1. destruct H1.
  - apply eq_push_inv in H0. destruct H0 as [Hx [Hb HE]].
    injection Hb. intros He HA. subst.
    split; [apply sub_wf in H1; exact H1|].
    split; [exact H1|].
    split; [exact H2|exact H3].
Qed.

Lemma wf_ok : forall G, wf G -> ok G.
Proof.
  intros G H. induction G as [| E x v IH] using env_ind.
  - apply ok_empty.
  - destruct v as [e A].
    destruct (@wf_cons_inv E x e A H) as [Hwf [Hsub [Hstar Hfresh]]].
    apply ok_push; auto.
Qed.

Definition subenv (G G':env) : Prop :=
  forall x b, binds x b G -> binds x b G'.

Lemma subenv_push : forall G G' x b,
  subenv G G' -> subenv (G & x ~ b) (G' & x ~ b).
Proof.
  intros G G' x b Hsub y c Hy.
  destruct (classic (y = x)) as [Heq|Hneq].
  - subst y. apply binds_push_eq_inv in Hy. subst c.
    apply binds_tail.
  - eapply binds_push_neq; eauto using binds_push_neq_inv.
Qed.

Lemma sub_lc_terms : forall G e1 e2 A,
  sub G e1 e2 A -> lc_trm e1 /\ lc_trm e2.
Proof.
  intros G e1 e2 A H. induction H as
    [ G0 Hwf
    | G0 x5 A0 e Hwf Hb
    | G0 x5 e2 A0 e1 Hb Hprem IHprem
    | G0 e A0 Hprem IHprem
    | G0 A0 Hprem IHprem
    | L G0 e1 A0 e2 e2' B h1 IH1 h2 IH2 hbody IHbody hbs IHbstar
    | G0 e1 A0 e2 C e3 B h1 IH1 h2 IH2
    | L G0 e A0 B e' A' B' h1 IH1 h2 IH2 h3 IH3 h4 IH4 h5 IH5 h6 IH6 h7 IH7
    | G0 B e1 e2 A0 h1 IH1 h2 IH2 hr
    | G0 e1 e2 B A0 h1 IH1 h2 IH2 hr
    | G0 e1 e2 B A0 h1 IH1 h2 IH2 ].
  - split; apply lc_trm_star.
  - split; apply lc_trm_var_f.
  - destruct IHprem as [_ H2]. split; [apply lc_trm_var_f|exact H2].
  - destruct IHprem as [H1 _]. split; [exact H1|apply lc_trm_top].
  - split; apply lc_trm_top.
  - (* abs *)
    destruct IH1 as [He1 _]. destruct IH2 as [HA _].
    split; apply (@lc_trm_abs L); auto.
    + intros x Hx. apply (proj1 (IHbody x Hx)).
    + intros x Hx. apply (proj2 (IHbody x Hx)).
  - (* app *)
    destruct IH1 as [He1 He2]. destruct IH2 as [HA _].
    split; apply lc_trm_app; auto.
  - (* prod *)
    destruct IH1 as [HA' HA].
    destruct IH2 as [He' He].
    destruct IH7 as [He'2 _].
    split.
    + apply (@lc_trm_prod L); auto.
      intros x Hx. apply (proj1 (IH4 x Hx)).
    + apply (@lc_trm_prod L); auto.
      intros x Hx. apply (proj2 (IH5 x Hx)).
  - (* castup *)
    destruct IH1 as [HB _]. destruct IH2 as [He1 He2].
    split; apply lc_trm_castup; auto.
  - (* castdn *)
    destruct IH2 as [He1 He2].
    split; [apply lc_trm_castdn; exact He1 | apply lc_trm_castdn; exact He2].
  - (* sub *) exact IH1.
Qed.

Lemma sub_left : forall G e1 e2 A, sub G e1 e2 A -> sub G e1 e1 A.
Proof.
  intros G e1 e2 A H. induction H as
    [ G0 Hwf
    | G0 x5 A0 e Hwf Hb
    | G0 x5 e2 A0 e1 Hb Hprem IHprem
    | G0 e A0 Hprem IHprem
    | G0 A0 Hprem IHprem
    | L G0 e1 A0 e2 e2' B h1 IH1 h2 IH2 hbody IHbody hbs IHbstar
    | G0 e1 A0 e2 C e3 B h1 IH1 h2 IH2
    | L G0 e A0 B e' A' B' h1 IH1 h2 IH2 h3 IH3 h4 IH4 h5 IH5 h6 IH6 h7 IH7
    | G0 B e1 e2 A0 h1 IH1 h2 IH2 hr
    | G0 e1 e2 B A0 h1 IH1 h2 IH2 hr
    | G0 e1 e2 B A0 h1 IH1 h2 IH2 ].
  - apply sub_ax; auto.
  - apply sub_var_refl with (e := e); auto.
  - apply sub_var_refl with (e := e1); auto. apply sub_wf in Hprem; auto.
  - assumption.
  - apply sub_top_refl; assumption.
  - refine (sub_abs L G0 e1 A0 e2 e2 B h1 h2 _ hbs).
    intros x Hx. apply (IHbody x Hx).
  - refine (sub_app G0 e1 A0 e1 C e3 B IH1 h2).
  - refine (sub_prod L G0 e A0 B e A0 B h3 h6 h3 h4 h4 h6 h6).
  - refine (sub_castup G0 B e1 e1 A0 h1 IH2 hr).
  - refine (sub_castdn G0 e1 e1 B A0 h1 IH2 hr).
  - refine (sub_sub G0 e1 e1 B A0 IH1 h2).
Qed.

Lemma sub_top_inv : forall G e A, sub G trm_top e A -> e = trm_top.
Proof.
  intros G e A H.
  remember trm_top as d eqn:Ed.
  revert Ed. induction H; intros Ed; try discriminate Ed.
  - symmetry. exact Ed.
  - reflexivity.
  - subst e1. apply IHsub1. reflexivity.
Qed.

Lemma sub_star_inv : forall G e A,
  sub G trm_star e A -> e = trm_star \/ e = trm_top.
Proof.
  intros G e A H.
  remember trm_star as d eqn:Ed.
  revert Ed. induction H; intros Ed; try discriminate Ed.
  - left. reflexivity.
  - right. reflexivity.
  - subst e1. apply IHsub1. reflexivity.
Qed.

Lemma sub_abs_shape : forall G e A,
  sub G (trm_abs (trm_var_b 0) (trm_var_b 0) (trm_var_b 0)) e A ->
  True.
Proof. auto. Qed.

Lemma sub_second_var : forall G e1 x A,
  sub G e1 (trm_var_f x) A -> exists y, e1 = trm_var_f y.
Proof.
  intros G e1 x A H.
  remember (trm_var_f x) as d eqn:Ed.
  revert Ed. induction H; intros Ed; try discriminate Ed.
  - injection Ed as Hx. subst x5. exists x. reflexivity.
  - exists x5. reflexivity.
  - subst e2. apply IHsub1. reflexivity.
Qed.

Lemma sub_second_prod : forall G e1 e2 A,
  sub G e1 e2 A ->
  forall d, e2 = d ->
  forall e A' B', d = trm_prod e A' B' ->
  (exists e' A'' B'', e1 = trm_prod e' A'' B'') \/
  (exists x, e1 = trm_var_f x).
Proof.
  intros G e1 e2 A H.
  induction H; intros d Ed eX AX BX Hp.
  - subst d. discriminate Hp.
  - subst d. discriminate Hp.
  - right. exists x5. reflexivity.
  - subst d. discriminate Hp.
  - subst d. discriminate Hp.
  - subst d. discriminate Hp.
  - subst d. discriminate Hp.
  - subst d. injection Hp as He HA HB. subst.
    left. exists e. exists A. exists B. reflexivity.
  - subst d. discriminate Hp.
  - subst d. discriminate Hp.
  - exact (IHsub1 d Ed eX AX BX Hp).
Qed.

(* Type-shape lemmas: kinds of types a judgement can have, by the head of
   its first component. *)

Lemma sub_star_type_shape_gen : forall G d e T,
  sub G d e T -> d = trm_star -> T = trm_star \/ T = trm_top.
Proof.
  intros G d e T H. induction H; intros Ed.
  - left. reflexivity.
  - discriminate Ed.
  - discriminate Ed.
  - apply IHsub. exact Ed.
  - discriminate Ed.
  - discriminate Ed.
  - discriminate Ed.
  - discriminate Ed.
  - discriminate Ed.
  - discriminate Ed.
  - apply IHsub1 in Ed. destruct Ed as [HA|HA]; subst.
    + apply sub_star_inv in H0. destruct H0 as [HB|HB]; subst; auto.
    + apply sub_top_inv in H0. subst. right. reflexivity.
Qed.

Lemma sub_star_type_shape : forall G e T,
  sub G trm_star e T -> T = trm_star \/ T = trm_top.
Proof. intros G e T H. exact (sub_star_type_shape_gen H eq_refl). Qed.

Lemma sub_prod_type_shape_gen : forall G d e T,
  sub G d e T -> forall p q r, d = trm_prod p q r ->
  T = trm_star \/ T = trm_top.
Proof.
  intros G d e T H. induction H; intros p q r Ed.
  - discriminate Ed.
  - discriminate Ed.
  - discriminate Ed.
  - exact (IHsub p q r Ed).
  - discriminate Ed.
  - discriminate Ed.
  - discriminate Ed.
  - left. reflexivity.
  - discriminate Ed.
  - discriminate Ed.
  - pose proof (IHsub1 p q r Ed) as HA. destruct HA as [HA|HA]; subst.
    + apply sub_star_inv in H0. destruct H0 as [HB|HB]; subst; auto.
    + apply sub_top_inv in H0. subst. right. reflexivity.
Qed.

Lemma sub_prod_target_shape_gen : forall G d e,
  sub G d e trm_star -> forall p q r, d = trm_prod p q r ->
  e = trm_top \/ (exists p' q' r', e = trm_prod p' q' r').
Proof.
  intros G d e H. induction H; intros p q r Ed.
  - discriminate Ed.
  - discriminate Ed.
  - discriminate Ed.
  - left. reflexivity.
  - discriminate Ed.
  - discriminate Ed.
  - discriminate Ed.
  - right. exists e'. exists A'. exists B'. reflexivity.
  - discriminate Ed.
  - discriminate Ed.
  - exact (IHsub1 p q r Ed).
Qed.

Lemma sub_prod_target_shape : forall G e,
  sub G (trm_prod trm_star trm_star trm_star) e trm_star ->
  e = trm_top \/ (exists p q r, e = trm_prod p q r).
Proof. intros G e H. exact (sub_prod_target_shape_gen H eq_refl). Qed.

Lemma sub_abs_target_shape_gen : forall G d e,
  sub G d e trm_star -> forall a b c, d = trm_abs a b c ->
  e = trm_top \/ (exists a' b' c', e = trm_abs a' b' c').
Proof.
  intros G d e H. induction H; intros a b c Ed.
  - discriminate Ed.
  - discriminate Ed.
  - discriminate Ed.
  - left. reflexivity.
  - discriminate Ed.
  - right. exists e1. exists A. exists e2'. reflexivity.
  - discriminate Ed.
  - discriminate Ed.
  - discriminate Ed.
  - discriminate Ed.
  - exact (IHsub1 a b c Ed).
Qed.

Lemma sub_abs_target_shape : forall G e,
  sub G (trm_abs trm_star trm_star trm_star) e trm_star ->
  e = trm_top \/ (exists a b c, e = trm_abs a b c).
Proof. intros G e H. exact (sub_abs_target_shape_gen H eq_refl). Qed.

Lemma sub_abs_type_shape_gen : forall G d e T,
  sub G d e T -> forall a b c, d = trm_abs a b c ->
  T = trm_top \/ (exists p q r, T = trm_prod p q r).
Proof.
  intros G d e T H. induction H; intros a b c Ed.
  - discriminate Ed.
  - discriminate Ed.
  - discriminate Ed.
  - exact (IHsub a b c Ed).
  - discriminate Ed.
  - right. exists e1. exists A. exists B. reflexivity.
  - discriminate Ed.
  - discriminate Ed.
  - discriminate Ed.
  - discriminate Ed.
  - pose proof (IHsub1 a b c Ed) as HA. destruct HA as [HA|HA]; subst.
    + apply sub_top_inv in H0. subst. left. reflexivity.
    + destruct HA as [p [q [r Hp]]]; subst.
      exact (sub_prod_target_shape_gen H0 eq_refl).
Qed.

Lemma sub_abs_type_shape : forall G T,
  sub G (trm_abs trm_star trm_star trm_star)
        (trm_abs trm_star trm_star trm_star) T ->
  T = trm_top \/ (exists p q r, T = trm_prod p q r).
Proof. intros G T H. exact (sub_abs_type_shape_gen H eq_refl). Qed.

Lemma sub_star_target_irred : forall G A,
  sub G trm_star A trm_star -> ~ (exists B, reduct A B).
Proof.
  intros G A H [B HB].
  apply sub_star_inv in H. destruct H as [Heq|Heq].
  - subst A. apply reduct_star_inv in HB; auto.
  - subst A. apply reduct_top_inv in HB; auto.
Qed.

Lemma sub_prod_target_irred : forall G p q r A,
  sub G (trm_prod p q r) A trm_star -> ~ (exists B, reduct A B).
Proof.
  intros G p q r A H [B HB].
  pose proof (sub_prod_target_shape_gen H eq_refl) as Hs.
  destruct Hs as [-> | [p' [q' [r' Hp]]]]; subst.
  - apply reduct_top_inv in HB; auto.
  - apply reduct_prod_inv in HB; auto.
Qed.

Lemma sub_abs_target_irred : forall G a b c A,
  sub G (trm_abs a b c) A trm_star -> ~ (exists B, reduct A B).
Proof.
  intros G a b c A H [B HB].
  pose proof (sub_abs_target_shape_gen H eq_refl) as Hs.
  destruct Hs as [-> | [a' [b' [c' Ha]]]]; subst.
  - apply reduct_top_inv in HB; auto.
  - apply reduct_abs_inv in HB; auto.
Qed.

Lemma sub_star_diag_irred : forall G A,
  sub G trm_star trm_star A -> ~ (exists B, reduct A B).
Proof.
  intros G A H [B HB].
  pose proof (sub_star_type_shape H) as Hs.
  destruct Hs as [Heq|Heq].
  - subst A. apply reduct_star_inv in HB; auto.
  - subst A. apply reduct_top_inv in HB; auto.
Qed.

Lemma sub_prod_diag_irred : forall G p q r A,
  sub G (trm_prod p q r) (trm_prod p q r) A -> ~ (exists B, reduct A B).
Proof.
  intros G p q r A H [B HB].
  pose proof (sub_prod_type_shape_gen H eq_refl) as Hs.
  destruct Hs as [Heq|Heq].
  - subst A. apply reduct_star_inv in HB; auto.
  - subst A. apply reduct_top_inv in HB; auto.
Qed.

Lemma sub_abs_diag_irred : forall G a b c A,
  sub G (trm_abs a b c) (trm_abs a b c) A -> ~ (exists B, reduct A B).
Proof.
  intros G a b c A H [B HB].
  pose proof (sub_abs_type_shape_gen H eq_refl) as Hs.
  destruct Hs as [-> | [p [q [r Hp]]]]; subst.
  - apply reduct_top_inv in HB; auto.
  - apply reduct_prod_inv in HB; auto.
Qed.

(* Progress helpers. *)

Lemma sub_castup_reduct : forall G d e T, sub G d e T ->
  forall B e0, d = trm_castup B e0 -> exists A, reduct B A.
Proof.
  intros G d e T H. induction H; intros Bt et Ed.
  - discriminate Ed.
  - discriminate Ed.
  - discriminate Ed.
  - exact (IHsub Bt et Ed).
  - discriminate Ed.
  - discriminate Ed.
  - discriminate Ed.
  - discriminate Ed.
  - injection Ed as HB _. subst Bt. eexists. eassumption.
  - discriminate Ed.
  - exact (IHsub1 Bt et Ed).
Qed.

Lemma castup_type_shape_gen : forall G d e T, sub G d e T ->
  forall B e0, d = trm_castup B e0 -> (exists A, reduct B A) ->
  (~ (exists p q r, T = trm_prod p q r)) /\ (~ (exists y, T = trm_var_f y)).
Proof.
  intros G d e T H. induction H; intros Bt et Ed Hred.
  - discriminate Ed.
  - discriminate Ed.
  - discriminate Ed.
  - exact (IHsub Bt et Ed Hred).
  - discriminate Ed.
  - discriminate Ed.
  - discriminate Ed.
  - discriminate Ed.
  - (* castup *) injection Ed as HB _. subst Bt. split.
    + intros [p [q [r Hp]]]. rewrite Hp in Hred.
      destruct Hred as [Ax HAx]. apply reduct_prod_inv in HAx; auto.
    + intros [y Hy]. rewrite Hy in Hred.
      destruct Hred as [Ax HAx]. apply reduct_var_f_inv in HAx; auto.
  - discriminate Ed.
  - (* sub_sub *)
    pose proof (IHsub1 Bt et Ed Hred) as [Hnp Hnv].
    split.
    + intros [p [q [r Hp]]].
      destruct (sub_second_prod H0 Hp eq_refl) as
          [[a [b' [c' Ha]]] | [y Hy]].
      * apply Hnp. exists a, b', c'. exact Ha.
      * apply Hnv. exists y. exact Hy.
    + intros [y Hy].
      rewrite Hy in H0.
      apply sub_second_var in H0. destruct H0 as [z Hz].
      apply Hnv. exists z. exact Hz.
Qed.

Lemma sub_castup_prod_false : forall G B e p q r,
  sub G (trm_castup B e) (trm_castup B e) (trm_prod p q r) -> False.
Proof.
  intros G B e p q r H.
  pose proof (@sub_castup_reduct G (trm_castup B e) (trm_castup B e) (trm_prod p q r) H B e eq_refl) as [A HA].
  pose proof (@castup_type_shape_gen G (trm_castup B e) (trm_castup B e) (trm_prod p q r) H B e eq_refl (ex_intro _ A HA)) as [Hnp _].
  apply Hnp. exists p, q, r. reflexivity.
Qed.

Lemma sub_star_prod_false : forall G p q r,
  sub G trm_star trm_star (trm_prod p q r) -> False.
Proof.
  intros G p q r H.
  pose proof (sub_star_type_shape_gen H eq_refl) as Hs.
  destruct Hs as [Heq|Heq]; subst; discriminate.
Qed.

Lemma sub_prod_prod_false : forall G a b c p q r,
  sub G (trm_prod a b c) (trm_prod a b c) (trm_prod p q r) -> False.
Proof.
  intros G a b c p q r H.
  pose proof (sub_prod_type_shape_gen H eq_refl) as Hs.
  destruct Hs as [Heq|Heq]; subst; discriminate.
Qed.

Lemma progress_any : forall G e1 e2 A,
  sub G e1 e2 A -> e1 = e2 -> value e1 \/ exists t, e1 --> t.
Proof.
  intros G e1 e2 A H.
  induction H as
    [ G0 Hwf
    | G0 x5 A0 e Hwf Hb
    | G0 x5 e2 A0 e1 Hb Hprem IHprem
    | G0 e A0 Hprem IHprem
    | G0 A0 Hprem IHprem
    | L G0 e1 A0 e2 e2' B h1 IH1 h2 IH2 hbody IHbody hbs IHbstar
    | G0 e1 A0 e2 C e3 B h1 IH1 h2 IH2
    | L G0 e A0 B e' A' B' h1 IH1 h2 IH2 h3 IH3 h4 IH4 h5 IH5 h6 IH6 h7 IH7
    | G0 B e1 e2 A0 h1 IH1 h2 IH2 hr
    | G0 e1 e2 B A0 h1 IH1 h2 IH2 hr
    | G0 e1 e2 B A0 h1 IH1 h2 IH2 ];
  intros Ed.
  - left. apply value_star.
  - left. apply value_ivalue, ivalue_var.
  - left. apply value_ivalue, ivalue_var.
  - exact (IHprem eq_refl).
  - left. apply value_ivalue, ivalue_top.
  - (* abs *)
    left. apply value_abs.
    + exact (proj1 (sub_lc_terms h1)).
    + exact (proj1 (sub_lc_terms h2)).
    + apply (@lc_trm_abs L e1 A0 e2).
      * exact (proj1 (sub_lc_terms h1)).
      * exact (proj1 (sub_lc_terms h2)).
      * intros x Hx. exact (proj1 (sub_lc_terms (hbody x Hx))).
  - (* app *)
    injection Ed as He. subst e2.
    destruct (IH1 eq_refl) as [Hv | [e1' Hs]].
    + destruct Hv as [ | e Hiv | a b c Hlca Hlcb Hlcabs | p q r Hlcp Hlcq Hlcprod | A' e HlcA Hlce ].
      * exfalso. exact (@sub_star_prod_false G0 e3 B C h1).
      * left. apply value_ivalue, ivalue_app.
        -- exact (proj1 (sub_lc_terms h2)).
        -- exact Hiv.
      * right. exists (open_trm_wrt_trm c A0). eapply reduct_beta.
        -- exact Hlca.
        -- exact Hlcb.
        -- exact Hlcabs.
        -- exact (proj1 (sub_lc_terms h2)).
      * exfalso. exact (@sub_prod_prod_false G0 p q r e3 B C h1).
      * exfalso. exact (@sub_castup_prod_false G0 A' e e3 B C h1).
    + right. exists (trm_app e1' A0). apply reduct_app.
      * exact (proj1 (sub_lc_terms h2)).
      * exact Hs.
  - (* prod *)
    left. apply value_prod.
    + exact (proj1 (sub_lc_terms h6)).
    + exact (proj1 (sub_lc_terms h3)).
    + apply (@lc_trm_prod L e A0 B).
      * exact (proj1 (sub_lc_terms h6)).
      * exact (proj1 (sub_lc_terms h3)).
      * intros x Hx. exact (proj1 (sub_lc_terms (h4 x Hx))).
  - (* castup *)
    left. apply value_castup.
    + exact (proj1 (sub_lc_terms h1)).
    + exact (proj1 (sub_lc_terms h2)).
  - (* castdn *)
    injection Ed as He. subst e2.
    destruct (IH2 eq_refl) as [Hv | [e1' Hs]].
    + destruct Hv as [ | e Hiv | a b c Hlca Hlcb Hlcabs | p q r Hlcp Hlcq Hlcprod | A' e HlcA Hlce ].
      * exfalso. exact (@sub_star_diag_irred G0 A0 h2 (ex_intro (fun X => reduct A0 X) B hr)).
      * left. apply value_ivalue, ivalue_castdn. exact Hiv.
      * exfalso. exact (@sub_abs_diag_irred G0 a b c A0 h2 (ex_intro (fun X => reduct A0 X) B hr)).
      * exfalso. exact (@sub_prod_diag_irred G0 p q r A0 h2 (ex_intro (fun X => reduct A0 X) B hr)).
      * right. exists e. apply reduct_castelim.
        -- exact HlcA.
        -- exact Hlce.
    + right. exists (trm_castdn e1'). apply reduct_castdn. exact Hs.
  - (* sub *)
    exact (IH1 Ed).
Qed.

(* Small facts used by type-well-formedness / right-projection attempts. *)

Lemma sub_star_top_star : forall G, wf G -> sub G trm_star trm_top trm_star.
Proof.
  intros G Hwf. apply sub_top. apply sub_ax. exact Hwf.
Qed.

Lemma sub_top_top_star : forall G, wf G -> sub G trm_top trm_top trm_star.
Proof.
  intros G Hwf. apply sub_top_refl. apply sub_ax. exact Hwf.
Qed.

Lemma sub_star_self_top : forall G e, sub G e e trm_star -> sub G e e trm_top.
Proof.
  intros G e H. eapply sub_sub; [ exact H | ].
  apply sub_star_top_star. apply (sub_wf H).
Qed.

(* A judgement whose second component is [star] can only have a first
   component that is [star] itself or a variable.  This is the dual of
   [sub_star_inv] and is used in the product/codomain case analysis.       *)

Lemma sub_second_star : forall G e A, sub G e trm_star A ->
  e = trm_star \/ exists x, e = trm_var_f x.
Proof.
  intros G e A H.
  remember trm_star as d eqn:Ed.
  revert Ed. induction H; intros Ed; try discriminate Ed.
  - left. reflexivity.
  - right. exists x5. reflexivity.
  - subst e2. apply IHsub1. reflexivity.
Qed.

(* A judgement whose second component is [star] is diagonalizable: the
   only rules producing second component [star] are [sub_ax] and
   [sub_var_trans] (under [sub_sub]), and in both cases the diagonal
   judgement at the same type is derivable.                             *)

Lemma sub_second_star_diag : forall G e A,
  sub G e trm_star A -> sub G e e A.
Proof.
  intros G e A H.
  remember trm_star as d eqn:Ed.
  revert Ed. induction H as
    [ G0 Hwf
    | G0 x5 A0 e0 Hwf Hb
    | G0 x5 e2 A0 e1 Hb Hprem IHprem
    | G0 e0 A0 Hprem IHprem
    | G0 A0 Hprem IHprem
    | L G0 e1 A0 e2 e2' B h1 IH1 h2 IH2 hbody IHbody hbs IHbstar
    | G0 e1 A0 e2 C e3 B h1 IH1 h2 IH2
    | L G0 e A0 B e' A' B' h1 IH1 h2 IH2 h3 IH3 h4 IH4 h5 IH5 h6 IH6 h7 IH7
    | G0 B e1 e2 A0 h1 IH1 h2 IH2 hr
    | G0 e1 e2 B A0 h1 IH1 h2 IH2 hr
    | G0 e1 e2 B A0 h1 IH1 h2 IH2 ];
  intros Ed; try discriminate Ed.
  - apply sub_ax. exact Hwf.
  - apply sub_var_refl with (e := e1); [ apply (sub_wf Hprem) | exact Hb ].
  - subst e2. eapply sub_sub; [ apply IH1; reflexivity | exact h2 ].
Qed.

(* Components of any product that occurs as the first component of a
   judgement are themselves well formed: the domain type is typed at
   [star], the domain term is typed at the domain type, and the codomain
   family is self-typed (cofinitely) in the domain's context.            *)

Lemma sub_prod_components_gen : forall G d e T, sub G d e T ->
  forall p q r, d = trm_prod p q r ->
  (sub G q q trm_star) /\
  (sub G p p q) /\
  (exists L, forall x, x \notin L ->
     sub (G & x ~ bind_sub p q)
         (open_trm_wrt_trm r (trm_var_f x))
         (open_trm_wrt_trm r (trm_var_f x)) trm_star).
Proof.
  intros G d e T H.
  induction H as
    [ G0 Hwf
    | G0 x5 A0 e0 Hwf Hb
    | G0 x5 e2 A0 e1 Hb Hprem IHprem
    | G0 e0 A0 Hprem IHprem
    | G0 A0 Hprem IHprem
    | L G0 e1 A0 e2 e2' B h1 IH1 h2 IH2 hbody IHbody hbs IHbstar
    | G0 e1 A0 e2 C e3 B h1 IH1 h2 IH2
    | L G0 e A0 B e' A' B' h1 IH1 h2 IH2 h3 IH3 h4 IH4 h5 IH5 h6 IH6 h7 IH7
    | G0 B e1 e2 A0 h1 IH1 h2 IH2 hr
    | G0 e1 e2 B A0 h1 IH1 h2 IH2 hr
    | G0 e1 e2 B A0 h1 IH1 h2 IH2 ];
  intros p q r Ed; try discriminate Ed.
  - (* sub_top *) exact (IHprem p q r Ed).
  - (* sub_prod *)
    injection Ed as He HA HB. subst.
    split; [ exact h3 | split ].
    + exact h6.
    + exists L. exact h4.
  - (* sub_sub *) exact (IH1 p q r Ed).
Qed.

(* Context weakening for the unified judgment, proved by induction on the
   derivation.  The [sub_prod] case builds the well-formedness of the
   extended contexts from the induction hypotheses; the needed self-typing
   of the target domain type follows by first projection ([sub_left]) of
   the source-domain premise.                                             *)

Lemma sub_weaken : forall G t1 t2 T,
  sub G t1 t2 T ->
  forall G', wf G' -> subenv G G' -> sub G' t1 t2 T.
Proof.
  intros G t1 t2 T H.
  induction H as
    [ G0 Hwf
    | G0 x5 A0 e0 Hwf Hb
    | G0 x5 e2 A0 e1 Hb Hprem IHprem
    | G0 e0 A0 Hprem IHprem
    | G0 A0 Hprem IHprem
    | L G0 e1 A0 e2 e2' B h1 IH1 h2 IH2 hbody IHbody hbs IHbstar
    | G0 e1 A0 e2 C e3 B h1 IH1 h2 IH2
    | L G0 e A0 B e' A' B' h1 IH1 h2 IH2 h3 IH3 h4 IH4 h5 IH5 h6 IH6 h7 IH7
    | G0 B e1 e2 A0 h1 IH1 h2 IH2 hr
    | G0 e1 e2 B A0 h1 IH1 h2 IH2 hr
    | G0 e1 e2 B A0 h1 IH1 h2 IH2 ];
  intros G' Hwf' Hsub.
  - (* ax *) apply sub_ax. exact Hwf'.
  - (* var_refl *)
    apply sub_var_refl with (e := e0); [ exact Hwf' | apply Hsub; exact Hb ].
  - (* var_trans *)
    eapply sub_var_trans; [ apply Hsub; exact Hb | ].
    apply IHprem; [ exact Hwf' | exact Hsub ].
  - (* top *) apply sub_top. apply IHprem; [ exact Hwf' | exact Hsub ].
  - (* top_refl *) apply sub_top_refl. apply IHprem; [ exact Hwf' | exact Hsub ].
  - (* abs *)
    apply (@sub_abs (L \u dom G') G' e1 A0 e2 e2' B).
    + apply IH1; [ exact Hwf' | exact Hsub ].
    + apply IH2; [ exact Hwf' | exact Hsub ].
    + intros x Hx. apply notin_union_r1 in Hx as HxL.
      apply notin_union_r2 in Hx as HxG.
      apply (IHbody x HxL (G' & x ~ bind_sub e1 A0)).
      * apply wf_cons.
        -- apply IH1; [ exact Hwf' | exact Hsub ].
        -- apply IH2; [ exact Hwf' | exact Hsub ].
        -- exact HxG.
      * apply subenv_push. exact Hsub.
    + intros x Hx. apply notin_union_r1 in Hx as HxL.
      apply notin_union_r2 in Hx as HxG.
      apply (IHbstar x HxL (G' & x ~ bind_sub e1 A0)).
      * apply wf_cons.
        -- apply IH1; [ exact Hwf' | exact Hsub ].
        -- apply IH2; [ exact Hwf' | exact Hsub ].
        -- exact HxG.
      * apply subenv_push. exact Hsub.
  - (* app *) eapply sub_app; [ apply IH1; [exact Hwf'|exact Hsub] | apply IH2; [exact Hwf'|exact Hsub] ].
  - (* prod *)
    pose proof (sub_left (IH1 G' Hwf' Hsub)) as HA'.
    apply (@sub_prod (L \u dom G') G' e A0 B e' A' B').
    + apply IH1; [ exact Hwf' | exact Hsub ].
    + apply IH2; [ exact Hwf' | exact Hsub ].
    + apply IH3; [ exact Hwf' | exact Hsub ].
    + intros x Hx. apply notin_union_r1 in Hx as HxL.
      apply notin_union_r2 in Hx as HxG.
      apply (IH4 x HxL (G' & x ~ bind_sub e A0)).
      * apply wf_cons.
        -- apply IH6; [ exact Hwf' | exact Hsub ].
        -- apply IH3; [ exact Hwf' | exact Hsub ].
        -- exact HxG.
      * apply subenv_push. exact Hsub.
    + intros x Hx. apply notin_union_r1 in Hx as HxL.
      apply notin_union_r2 in Hx as HxG.
      apply (IH5 x HxL (G' & x ~ bind_sub e' A')).
      * apply wf_cons.
        -- apply IH7; [ exact Hwf' | exact Hsub ].
        -- exact HA'.
        -- exact HxG.
      * apply subenv_push. exact Hsub.
    + apply IH6; [ exact Hwf' | exact Hsub ].
    + apply IH7; [ exact Hwf' | exact Hsub ].
  - (* castup *) eapply sub_castup; [ apply IH1; [exact Hwf'|exact Hsub] | apply IH2; [exact Hwf'|exact Hsub] | exact hr ].
  - (* castdn *) eapply sub_castdn; [ apply IH1; [exact Hwf'|exact Hsub] | apply IH2; [exact Hwf'|exact Hsub] | exact hr ].
  - (* sub *) eapply sub_sub; [ apply IH1; [exact Hwf'|exact Hsub] | apply IH2; [exact Hwf'|exact Hsub] ].
Qed.

(* Extending a context on the right preserves [subenv], and the packaged
   form of weakening by one fresh binder.                              *)

Lemma subenv_push_right : forall G G' x b,
  subenv G G' -> x # G' -> subenv G (G' & x ~ b).
Proof.
  intros G G' x b H X y c Hy.
  apply binds_push_neq.
  - apply H. exact Hy.
  - intro Hyx. subst y.
    exfalso. apply X.
    apply (get_some_inv (v := c)).
    apply (binds_get (v := c)). apply H. exact Hy.
Qed.

Lemma sub_weaken_push : forall G G' x b t1 t2 T,
  wf (G' & x ~ b) -> subenv G G' -> x # G' ->
  sub G t1 t2 T -> sub (G' & x ~ b) t1 t2 T.
Proof.
  intros G G' x b t1 t2 T Hwf Hsub Hx Hs.
  eapply sub_weaken; [ exact Hs | exact Hwf | apply subenv_push_right; assumption ].
Qed.

(* Right-projection instances for `top' and variable second components. *)

Lemma sub_second_top_diag : forall G e A,
  sub G e trm_top A -> sub G e e A.
Proof.
  intros G e A H.
  remember trm_top as d eqn:Ed.
  revert Ed. induction H as
    [ G0 Hwf
    | G0 x5 A0 e0 Hwf Hb
    | G0 x5 e2 A0 e1 Hb Hprem IHprem
    | G0 e0 A0 Hprem IHprem
    | G0 A0 Hprem IHprem
    | L G0 e1 A0 e2 e2' B h1 IH1 h2 IH2 hbody IHbody hbs IHbstar
    | G0 e1 A0 e2 C e3 B h1 IH1 h2 IH2
    | L G0 e A0 B e' A' B' h1 IH1 h2 IH2 h3 IH3 h4 IH4 h5 IH5 h6 IH6 h7 IH7
    | G0 B e1 e2 A0 h1 IH1 h2 IH2 hr
    | G0 e1 e2 B A0 h1 IH1 h2 IH2 hr
    | G0 e1 e2 B A0 h1 IH1 h2 IH2 ];
  intros Ed; try discriminate Ed.
  - (* var_trans *)
    apply sub_var_refl with (e := e1); [ apply (sub_wf Hprem) | exact Hb ].
  - (* top *) exact Hprem.
  - (* top_refl *) apply sub_top_refl. exact Hprem.
  - (* sub_sub *)
    subst e2. eapply sub_sub; [ apply IH1; reflexivity | exact h2 ].
Qed.

Lemma sub_second_var_diag : forall G e x A,
  sub G e (trm_var_f x) A -> sub G e e A.
Proof.
  intros G e x A H.
  remember (trm_var_f x) as d eqn:Ed.
  revert Ed. induction H as
    [ G0 Hwf
    | G0 x5 A0 e0 Hwf Hb
    | G0 x5 e2 A0 e1 Hb Hprem IHprem
    | G0 e0 A0 Hprem IHprem
    | G0 A0 Hprem IHprem
    | L G0 e1 A0 e2 e2' B h1 IH1 h2 IH2 hbody IHbody hbs IHbstar
    | G0 e1 A0 e2 C e3 B h1 IH1 h2 IH2
    | L G0 e A0 B e' A' B' h1 IH1 h2 IH2 h3 IH3 h4 IH4 h5 IH5 h6 IH6 h7 IH7
    | G0 B e1 e2 A0 h1 IH1 h2 IH2 hr
    | G0 e1 e2 B A0 h1 IH1 h2 IH2 hr
    | G0 e1 e2 B A0 h1 IH1 h2 IH2 ];
  intros Ed; try discriminate Ed.
  - (* var_refl *)
    injection Ed as Hx. subst x5.
    apply sub_var_refl with (e := e0); [ exact Hwf | exact Hb ].
  - (* var_trans *)
    apply sub_var_refl with (e := e1); [ apply (sub_wf Hprem) | exact Hb ].
  - (* sub_sub *)
    subst e2. eapply sub_sub; [ apply IH1; reflexivity | exact h2 ].
Qed.

(* The type in any well-formed binding is itself well formed at [star]. *)

Lemma subenv_refl : forall G, subenv G G.
Proof. intros G y b H. exact H. Qed.

Lemma wf_binds_type : forall G x e A,
  wf G -> binds x (bind_sub e A) G -> sub G A A trm_star.
Proof.
  intros G. induction G as [| G' y b IH] using env_ind.
  - intros x e A Hwf Hb. apply binds_empty_inv in Hb. destruct Hb.
  - intros x e A Hwf Hb.
    destruct b as [eb Ab].
    destruct (@wf_cons_inv G' y eb Ab Hwf) as [Hwf' [He' [HA' HyG]]].
    apply binds_push_inv in Hb.
    destruct Hb as [[Hxy He] | [Hxy Hb']].
    + subst y. injection He as Hbe HAb. subst eb Ab.
      eapply sub_weaken_push; [ exact Hwf | apply subenv_refl | exact HyG | exact HA' ].
    + eapply sub_weaken_push; [ exact Hwf | apply subenv_refl | exact HyG | ].
      eapply IH; [ exact Hwf' | exact Hb' ].
Qed.

(* The *term* in any well-formed binding is self-typed at the binding's
   type.  This complements [wf_binds_type] and is what makes a context's
   stored definitions usable under weakening.                            *)

Lemma wf_binds_sub : forall G x e A,
  wf G -> binds x (bind_sub e A) G -> sub G e e A.
Proof.
  intros G. induction G as [| G' y b IH] using env_ind.
  - intros x e A Hwf Hb. apply binds_empty_inv in Hb. destruct Hb.
  - intros x e A Hwf Hb.
    destruct b as [eb Ab].
    destruct (@wf_cons_inv G' y eb Ab Hwf) as [Hwf' [He' [HA' HyG]]].
    apply binds_push_inv in Hb.
    destruct Hb as [[Hxy He] | [Hxy Hb']].
    + subst y. injection He as Hbe HAb. subst eb Ab.
      eapply sub_weaken_push; [ exact Hwf | apply subenv_refl | exact HyG | exact He' ].
    + eapply sub_weaken_push; [ exact Hwf | apply subenv_refl | exact HyG | ].
      eapply IH; [ exact Hwf' | exact Hb' ].
Qed.

(* A concrete witness that an index-dependent product is a supertype of
   its closed source when the binder's term matches the source domain.     *)

Lemma sub_prod_idx_example : forall x,
  sub (empty & x ~ bind_sub trm_star trm_star)
      (trm_prod trm_star trm_star trm_star)
      (trm_prod (trm_var_f x) trm_star trm_star)
      trm_star.
Proof.
  intros x.
  set (G := empty & x ~ bind_sub trm_star trm_star).
  assert (Hwf : wf G).
  { unfold G. apply wf_cons.
    - apply sub_ax. apply wf_nil.
    - apply sub_ax. apply wf_nil.
    - rewrite dom_empty. apply notin_empty. }
  assert (Hx : sub G (trm_var_f x) (trm_var_f x) trm_star).
  { apply sub_var_refl with (e := trm_star); [ exact Hwf | apply binds_tail ]. }
  assert (Hxs : sub G (trm_var_f x) trm_star trm_star).
  { eapply sub_var_trans; [ apply binds_tail | apply sub_ax; exact Hwf ]. }
  assert (Hax : sub G trm_star trm_star trm_star).
  { apply sub_ax. exact Hwf. }
  apply (@sub_prod \{x} G trm_star trm_star trm_star
                   (trm_var_f x) trm_star trm_star).
  - (* p1 *) exact Hax.
  - (* p2 *) exact Hxs.
  - (* p3 *) exact Hax.
  - (* h4 *) intros y Hy. apply sub_ax.
    apply wf_cons.
    + exact Hax.
    + exact Hax.
    + unfold G; rewrite dom_push, dom_empty; apply notin_union; split; [ exact Hy | apply notin_empty ].
  - (* h5 *) intros y Hy. apply sub_ax.
    apply wf_cons.
    + exact Hx.
    + exact Hax.
    + unfold G; rewrite dom_push, dom_empty; apply notin_union; split; [ exact Hy | apply notin_empty ].
  - (* p6 *) exact Hax.
  - (* p7 *) exact Hx.
Qed.

(* Full component extraction for product subtyping.  Since [sub_sub]
   preserves both terms, any derivation of a product-to-product judgment
   bottoms out in a single [sub_prod] between the very same endpoint
   products, so all the [sub_prod] premises are available for the
   endpoints.  This is used to recover the domain term/type relations and
   the codomain family relation of a product widening.                     *)

Lemma sub_prod_full_gen : forall G d e T,
  sub G d e T ->
  forall p q r p' q' r',
    d = trm_prod p q r -> e = trm_prod p' q' r' ->
    (sub G q' q trm_star) /\
    (sub G p' p q) /\
    (sub G q q trm_star) /\
    (exists L, forall x, x \notin L ->
        sub (G & x ~ bind_sub p q) (r ^ x) (r ^ x) trm_star) /\
    (exists L, forall x, x \notin L ->
        sub (G & x ~ bind_sub p' q') (r ^ x) (r' ^ x) trm_star) /\
    (sub G p p q) /\
    (sub G p' p' q').
Proof.
  intros G d e T H.
  induction H as
    [ G0 Hwf
    | G0 x5 A0 e0 Hwf Hb
    | G0 x5 e2 A0 e1 Hb Hprem IHprem
    | G0 e0 A0 Hprem IHprem
    | G0 A0 Hprem IHprem
    | L G0 e1 A0 e2 e2' B h1 IH1 h2 IH2 hbody IHbody hbs IHbstar
    | G0 e1 A0 e2 C e3 B h1 IH1 h2 IH2
    | L G0 e A0 B e' A' B' h1 IH1 h2 IH2 h3 IH3 h4 IH4 h5 IH5 h6 IH6 h7 IH7
    | G0 B e1 e2 A0 h1 IH1 h2 IH2 hr
    | G0 e1 e2 B A0 h1 IH1 h2 IH2 hr
    | G0 e1 e2 B A0 h1 IH1 h2 IH2 ];
  intros p q r p' q' r' Ed Ee; try discriminate Ed.
  - (* sub_top: the right component is [top] *)
    discriminate Ee.
  - (* sub_prod *)
    injection Ed as He HA HB. injection Ee as He' HA' HB'. subst.
    split. exact h1.
    split. exact h2.
    split. exact h3.
    split. exists L. exact h4.
    split. exists L. exact h5.
    split. exact h6.
    exact h7.
  - (* sub_sub: terms are preserved *)
    exact (IH1 p q r p' q' r' Ed Ee).
Qed.

(* Codomain-family relation of a product widening, in the target product's
   binder context.  This is the [sub_prod] premise needed to advance a
   codomain family along a widening step.                                  *)

Lemma sub_prod_codom_gen : forall G p q r p' q' r',
  sub G (trm_prod p q r) (trm_prod p' q' r') trm_star ->
  exists L, forall x, x \notin L ->
    sub (G & x ~ bind_sub p' q') (r ^ x) (r' ^ x) trm_star.
Proof.
  intros G p q r p' q' r' H.
  destruct (sub_prod_full_gen H eq_refl eq_refl)
    as [H1 [H2 [H3 [H4 [H5 [H6 H7]]]]]].
  exact H5.
Qed.

(* The packaged data of a single product-widening step: domain type and
   term relations, both domain self-typings, the source codomain
   self-typing, and the codomain-family relation in the target binder
   context.  These are exactly the [sub_prod] premises needed to advance
   a codomain family (and hence an opened abstraction body) along one
   step of a widening chain.                                              *)

Lemma sub_prod_step : forall G p q r p' q' r',
  sub G (trm_prod p q r) (trm_prod p' q' r') trm_star ->
  (sub G q' q trm_star) /\
  (sub G p' p q) /\
  (sub G q q trm_star) /\
  (sub G p p q) /\
  (sub G p' p' q') /\
  (exists L, forall x, x \notin L ->
     sub (G & x ~ bind_sub p q) (r ^ x) (r ^ x) trm_star) /\
  (exists L, forall x, x \notin L ->
     sub (G & x ~ bind_sub p' q') (r ^ x) (r' ^ x) trm_star).
Proof.
  intros G p q r p' q' r' H.
  destruct (sub_prod_full_gen H eq_refl eq_refl)
    as [H1 [H2 [H3 [H4 [H5 [H6 H7]]]]]].
  split. exact H1.
  split. exact H2.
  split. exact H3.
  split. exact H6.
  split. exact H7.
  split. exact H4.
  exact H5.
Qed.

(* Both binder contexts associated with the two endpoints of a product
   widening are well formed (for a fresh variable), so the target-context
   codomain relation of [sub_prod_step] can be used directly.              *)

Lemma wf_of_prod_step : forall G p q r p' q' r',
  sub G (trm_prod p q r) (trm_prod p' q' r') trm_star ->
  forall x, x # G ->
    wf (G & x ~ bind_sub p q) /\ wf (G & x ~ bind_sub p' q').
Proof.
  intros G p q r p' q' r' H x Hx.
  destruct (sub_prod_step H) as [H1 [H2 [H3 [H6 [H7 [H4 H5]]]]]].
  split.
  - apply wf_cons; [ exact H6 | exact H3 | exact Hx ].
  - apply wf_cons.
    + exact H7.
    + apply sub_left in H1. exact H1.
    + exact Hx.
Qed.

(* Inversion data for a typing of an abstraction pair: regardless of the
   result type (and of [sub_sub] wrappers), the domain term is self-typed
   at the domain type and the domain type is self-typed at [star].  This
   is exactly what is needed to form the body's binder context.            *)

Lemma sub_abs_wf_ctx_gen : forall G d e T,
  sub G d e T ->
  forall a0 D b b',
    d = trm_abs a0 D b -> e = trm_abs a0 D b' ->
    sub G a0 a0 D /\ sub G D D trm_star.
Proof.
  intros G d e T H.
  induction H as
    [ G0 Hwf
    | G0 x5 A0 e0 Hwf Hb
    | G0 x5 e2 A0 e1 Hb Hprem IHprem
    | G0 e0 A0 Hprem IHprem
    | G0 A0 Hprem IHprem
    | L G0 e1 A0 e2 e2' B h1 IH1 h2 IH2 hbody IHbody hbs IHbstar
    | G0 e1 A0 e2 C e3 B h1 IH1 h2 IH2
    | L G0 e A0 B e' A' B' h1 IH1 h2 IH2 h3 IH3 h4 IH4 h5 IH5 h6 IH6 h7 IH7
    | G0 B e1 e2 A0 h1 IH1 h2 IH2 hr
    | G0 e1 e2 B A0 h1 IH1 h2 IH2 hr
    | G0 e1 e2 B A0 h1 IH1 h2 IH2 ];
  intros a0 D b b' Ed Ee; try discriminate Ed.
  - (* sub_top: right component is [top] *)
    discriminate Ee.
  - (* sub_abs: the annotations are forced by the two terms *)
    injection Ed as He1 HD Hb. injection Ee as He1' HD' Hb'.
    subst. split; [ exact h1 | exact h2 ].
  - (* sub_sub: terms are preserved *)
    exact (IH1 a0 D b b' Ed Ee).
Qed.

Lemma wf_abs_body_ctx : forall G a0 D b b' T,
  sub G (trm_abs a0 D b) (trm_abs a0 D b') T ->
  forall x, x # G -> wf (G & x ~ bind_sub a0 D).
Proof.
  intros G a0 D b b' T H x Hx.
  destruct (sub_abs_wf_ctx_gen H eq_refl eq_refl) as [H1 H2].
  apply wf_cons; [ exact H1 | exact H2 | exact Hx ].
Qed.

(* Scope of bindings in a well-formed environment: the free variables of
   the term and type components of every binding lie in the environment
   domain.  This is the key fact that lets a fresh binder name be treated
   as absent from all inherited bindings.                                *)

Definition fvs (G : env) (e1 e2 A : trm) : Prop :=
  forall z, z \in fv_trm e1 \/ z \in fv_trm e2 \/ z \in fv_trm A -> z \in dom G.

Definition fvw (G : env) : Prop :=
  forall x e A, binds x (bind_sub e A) G ->
    forall z, z \in fv_trm e \/ z \in fv_trm A -> z \in dom G.

Lemma fvw_holds : forall G, wf G -> fvw G.
Proof.
  refine (wf_mut
    (fun (G:env) (e1 e2 A:trm) (s : sub G e1 e2 A) => fvs G e1 e2 A /\ fvw G)
    (fun (G:env) (w : wf G) => fvw G)
    _ _ _ _ _ _ _ _ _ _ _ _ _).
  - (* sub_ax *) intros G w IHw. split.
    + intros z Hz. simpl in Hz. repeat rewrite in_empty in Hz. tauto.
    + exact IHw.
  - (* sub_var_refl *) intros G y A e w IHw Hb. split.
    + intros z Hz. simpl in Hz. repeat rewrite in_union in Hz.
      repeat rewrite in_singleton in Hz.
      destruct Hz as [Heq | [Heq | HA]].
      * subst z. exact (binds_in_dom Hb).
      * subst z. exact (binds_in_dom Hb).
      * apply (IHw y e A Hb z). right. exact HA.
    + exact IHw.
  - (* sub_var_trans *) intros G y e2 A e1 Hb s IHs. destruct IHs as [IHfvs IHfvw]. split.
    + intros z Hz. simpl in Hz. repeat rewrite in_union in Hz.
      repeat rewrite in_singleton in Hz.
      destruct Hz as [Heq | [He2 | HA]].
      * subst z. exact (binds_in_dom Hb).
      * apply (IHfvs z). tauto.
      * apply (IHfvs z). tauto.
    + exact IHfvw.
  - (* sub_top *) intros G e A s IHs. destruct IHs as [IHfvs IHfvw]. split.
    + intros z Hz. simpl in Hz. repeat rewrite in_union in Hz. repeat rewrite in_empty in Hz.
      apply (IHfvs z). tauto.
    + exact IHfvw.
  - (* sub_top_refl *) intros G A s IHs. destruct IHs as [IHfvs IHfvw]. split.
    + intros z Hz. simpl in Hz. repeat rewrite in_union in Hz. repeat rewrite in_empty in Hz.
      apply (IHfvs z). tauto.
    + exact IHfvw.
  - (* sub_abs *) intros L G e1 A e2 e2' B s IHs s0 IHs0 hbody IHbody hbs IHbstar.
    destruct IHs as [IHfvs IHfvw].
    split.
    + intros z Hz. simpl in Hz. set (S := L \u (fv_trm e2 \u (fv_trm e2' \u fv_trm B))).
      destruct (var_fresh S) as [x0 Hx0].
      apply notin_union in Hx0. destruct Hx0 as [Hx0L Hx0r].
      apply notin_union in Hx0r. destruct Hx0r as [Hx0e2 Hx0r].
      apply notin_union in Hx0r. destruct Hx0r as [Hx0e2' Hx0B].
      destruct (IHbody x0 Hx0L) as [HBfvs _].
      assert (L1 : z \in fv_trm e1 -> z \in dom G)
        by (intro H; apply (IHfvs z); tauto).
      assert (LA : z \in fv_trm A -> z \in dom G)
        by (intro H; apply (IHfvs z); tauto).
      assert (L2 : z \in fv_trm e2 -> z \in dom G).
      { intro H2.
        assert (Hop : z \in fv_trm (open_trm_wrt_trm e2 (trm_var_f x0)))
          by (apply fv_open_lower; exact H2).
        assert (Hdom : z \in dom (G & x0 ~ bind_sub e1 A)).
        { apply (HBfvs z). left. exact Hop. }
        rewrite dom_push in Hdom. rewrite in_union in Hdom.
        destruct Hdom as [Heqx | HG].
        - rewrite in_singleton in Heqx. subst z. exfalso. apply Hx0e2. exact H2.
        - exact HG. }
      assert (L2' : z \in fv_trm e2' -> z \in dom G).
      { intro H2.
        assert (Hop : z \in fv_trm (open_trm_wrt_trm e2' (trm_var_f x0)))
          by (apply fv_open_lower; exact H2).
        assert (Hdom : z \in dom (G & x0 ~ bind_sub e1 A)).
        { apply (HBfvs z). right. left. exact Hop. }
        rewrite dom_push in Hdom. rewrite in_union in Hdom.
        destruct Hdom as [Heqx | HG].
        - rewrite in_singleton in Heqx. subst z. exfalso. apply Hx0e2'. exact H2.
        - exact HG. }
      assert (LB : z \in fv_trm B -> z \in dom G).
      { intro H2.
        assert (Hop : z \in fv_trm (open_trm_wrt_trm B (trm_var_f x0)))
          by (apply fv_open_lower; exact H2).
        assert (Hdom : z \in dom (G & x0 ~ bind_sub e1 A)).
        { apply (HBfvs z). right. right. exact Hop. }
        rewrite dom_push in Hdom. rewrite in_union in Hdom.
        destruct Hdom as [Heqx | HG].
        - rewrite in_singleton in Heqx. subst z. exfalso. apply Hx0B. exact H2.
        - exact HG. }
      repeat rewrite in_union in *. tauto.
    + exact IHfvw.
  - (* sub_app *) intros G e1 A e2 C e3 B s IHs s0 IHs0.
    destruct IHs as [IHfvs IHfvw]. destruct IHs0 as [IHfvs0 _].
    split.
    + intros z Hz. simpl in Hz. assert (L1 : z \in fv_trm e1 -> z \in dom G)
        by (intro H; apply (IHfvs z); tauto).
      assert (L2 : z \in fv_trm e2 -> z \in dom G)
        by (intro H; apply (IHfvs z); tauto).
      assert (LA : z \in fv_trm A -> z \in dom G)
        by (intro H; apply (IHfvs0 z); tauto).
      assert (HC : z \in fv_trm (open_trm_wrt_trm C A) -> z \in dom G).
      { intro H. pose proof (@fv_open_upper C A z H) as Hu.
        repeat rewrite in_union in Hu. destruct Hu as [HC' | HA'].
        - apply (IHfvs z). right. right. simpl. repeat rewrite in_union. tauto.
        - apply (IHfvs0 z). left. exact HA'. }
      repeat rewrite in_union in *. tauto.
    + exact IHfvw.
  - (* sub_prod *) intros L G e A B e' A' B' s IHs s0 IHs0 s1 IHs1 s2 IHs2 s3 IHs3 s4 IHs4 s5 IHs5.
    destruct IHs4 as [IHfvs4 IHfvw]. split.
    + intros z Hz. simpl in Hz. set (S := L \u (fv_trm B \u fv_trm B')).
      destruct (var_fresh S) as [x0 Hx0].
      apply notin_union in Hx0. destruct Hx0 as [Hx0L Hx0r].
      apply notin_union in Hx0r. destruct Hx0r as [Hx0B Hx0B'].
      destruct (IHs2 x0 Hx0L) as [H2fvs _].
      destruct (IHs3 x0 Hx0L) as [H3fvs _].
      assert (Le : z \in fv_trm e -> z \in dom G)
        by (intro H; apply (IHfvs4 z); tauto).
      assert (LA : z \in fv_trm A -> z \in dom G)
        by (intro H; apply (IHfvs4 z); tauto).
      destruct IHs5 as [IHfvs5 _].
      assert (Le' : z \in fv_trm e' -> z \in dom G)
        by (intro H; apply (IHfvs5 z); tauto).
      assert (LA' : z \in fv_trm A' -> z \in dom G)
        by (intro H; apply (IHfvs5 z); tauto).
      assert (LB : z \in fv_trm B -> z \in dom G).
      { intro H.
        assert (Hop : z \in fv_trm (open_trm_wrt_trm B (trm_var_f x0)))
          by (apply fv_open_lower; exact H).
        assert (Hdom : z \in dom (G & x0 ~ bind_sub e A)).
        { apply (H2fvs z). left. exact Hop. }
        rewrite dom_push in Hdom. rewrite in_union in Hdom.
        destruct Hdom as [Heqx | HG].
        - rewrite in_singleton in Heqx. subst z. exfalso. apply Hx0B. exact H.
        - exact HG. }
      assert (LB' : z \in fv_trm B' -> z \in dom G).
      { intro H.
        assert (Hop : z \in fv_trm (open_trm_wrt_trm B' (trm_var_f x0)))
          by (apply fv_open_lower; exact H).
        assert (Hdom : z \in dom (G & x0 ~ bind_sub e' A')).
        { apply (H3fvs z). right. left. exact Hop. }
        rewrite dom_push in Hdom. rewrite in_union in Hdom.
        destruct Hdom as [Heqx | HG].
        - rewrite in_singleton in Heqx. subst z. exfalso. apply Hx0B'. exact H.
        - exact HG. }
      repeat rewrite in_union in *. repeat rewrite in_empty in *. tauto.
    + exact IHfvw.
  - (* sub_castup *) intros G B e1 e2 A s IHs s0 IHs0 r.
    destruct IHs as [IHfvs IHfvw]. destruct IHs0 as [IHfvs0 _].
    split.
    + intros z Hz. simpl in Hz.
      assert (LB : z \in fv_trm B -> z \in dom G) by (intro H; apply (IHfvs z); tauto).
      assert (L1 : z \in fv_trm e1 -> z \in dom G) by (intro H; apply (IHfvs0 z); tauto).
      assert (L2 : z \in fv_trm e2 -> z \in dom G) by (intro H; apply (IHfvs0 z); tauto).
      repeat rewrite in_union in *. tauto.
    + exact IHfvw.
  - (* sub_castdn *) intros G e1 e2 B A s IHs s0 IHs0 r.
    destruct IHs as [IHfvs IHfvw]. destruct IHs0 as [IHfvs0 _].
    split.
    + intros z Hz. simpl in Hz.
      assert (LB : z \in fv_trm B -> z \in dom G) by (intro H; apply (IHfvs z); tauto).
      assert (L1 : z \in fv_trm e1 -> z \in dom G) by (intro H; apply (IHfvs0 z); tauto).
      assert (L2 : z \in fv_trm e2 -> z \in dom G) by (intro H; apply (IHfvs0 z); tauto).
      repeat rewrite in_union in *. tauto.
    + exact IHfvw.
  - (* sub_sub *) intros G e1 e2 B A s IHs s0 IHs0.
    destruct IHs as [IHfvs IHfvw]. destruct IHs0 as [IHfvs0 _].
    split.
    + intros z Hz. simpl in Hz. assert (L1 : z \in fv_trm e1 -> z \in dom G) by (intro H; apply (IHfvs z); tauto).
      assert (L2 : z \in fv_trm e2 -> z \in dom G) by (intro H; apply (IHfvs z); tauto).
      assert (LB : z \in fv_trm B -> z \in dom G) by (intro H; apply (IHfvs0 z); tauto).
      repeat rewrite in_union in *. tauto.
    + exact IHfvw.
  - (* wf_nil *) intros x e A Hb z Hz. apply binds_empty_inv in Hb. destruct Hb.
  - (* wf_cons *) intros G x e A s IHs s0 IHs0 Hfresh.
    destruct IHs as [IHfvs IHfvw].
    intros y e' A' Hy z Hz.
    destruct (classic (y = x)) as [Heq | Hneq].
    + subst y. apply binds_push_eq_inv in Hy.
      injection Hy as He HA. subst e' A'.
      assert (HzG : z \in dom G) by (apply (IHfvs z); tauto).
      rewrite dom_push. rewrite in_union. right. exact HzG.
    + apply binds_push_neq_inv in Hy; [| exact Hneq].
      assert (HzG : z \in dom G) by (apply (IHfvw y e' A' Hy z Hz)).
      rewrite dom_push. rewrite in_union. right. exact HzG.
Qed.

(* Capture-avoiding-free substitution into an environment, used by the
   substitution lemma for the binder that occurs before later bindings.  *)

Definition subst_env (v : trm) (x : var) (G : env) : env :=
  LibEnv.EnvOps.map (subst_binding v x) G.

Lemma dom_subst_env : forall G v x, dom (subst_env v x G) = dom G.
Proof. intros. unfold subst_env. apply dom_map. Qed.

Lemma binds_subst_env : forall G v x y b,
  binds y b G -> binds y (subst_binding v x b) (subst_env v x G).
Proof. intros. unfold subst_env. apply binds_map. exact H. Qed.

Lemma subst_env_empty : forall v x, subst_env v x empty = empty.
Proof. intros. unfold subst_env. apply map_empty. Qed.

Lemma subst_env_push : forall G v x y b,
  subst_env v x (G & y ~ b) = (subst_env v x G & y ~ subst_binding v x b).
Proof. intros. unfold subst_env. rewrite map_push. reflexivity. Qed.

(* Basic computation lemma for substitution into a binding. *)

Lemma subst_binding_eq : forall v x e A,
  subst_binding v x (bind_sub e A) =
  bind_sub (subst_trm v x e) (subst_trm v x A).
Proof. intros. reflexivity. Qed.

(* Substitution is the identity on terms that do not mention the variable. *)

Lemma subst_trm_fresh : forall e v x,
  x \notin fv_trm e -> subst_trm v x e = e.
Proof.
  induction e as [n | y | | | e1 IHe1 e2 IHe2 | e1 IHe1 A IHA e2 IHe2
               | e IHe A IHA B IHB | A IHA e IHe | e IHe | e IHe A IHA ];
  intros v x Hfv; simpl in *.
  - reflexivity.
  - apply notin_singleton_r in Hfv.
    simpl. rewrite If_r. reflexivity.
    intro Heq. apply Hfv. symmetry. exact Heq.
  - reflexivity.
  - reflexivity.
  - apply notin_union in Hfv. destruct Hfv as [H1 H2].
    simpl. rewrite (IHe1 v x H1), (IHe2 v x H2). reflexivity.
  - apply notin_union in Hfv. destruct Hfv as [H1 Hrest].
    apply notin_union in Hrest. destruct Hrest as [HA H2].
    simpl. rewrite (IHe1 v x H1), (IHA v x HA), (IHe2 v x H2). reflexivity.
  - apply notin_union in Hfv. destruct Hfv as [H1 Hrest].
    apply notin_union in Hrest. destruct Hrest as [HA HB].
    simpl. rewrite (IHe v x H1), (IHA v x HA), (IHB v x HB). reflexivity.
  - apply notin_union in Hfv. destruct Hfv as [HA H1].
    simpl. rewrite (IHA v x HA), (IHe v x H1). reflexivity.
  - simpl. rewrite (IHe v x Hfv). reflexivity.
  - apply notin_union in Hfv. destruct Hfv as [H1 HA].
    simpl. rewrite (IHe v x H1), (IHA v x HA). reflexivity.
Qed.

Lemma subst_binding_fresh : forall v x e A,
  x \notin fv_trm e -> x \notin fv_trm A ->
  subst_binding v x (bind_sub e A) = bind_sub e A.
Proof.
  intros. rewrite subst_binding_eq.
  rewrite (@subst_trm_fresh e v x H), (@subst_trm_fresh A v x H0).
  reflexivity.
Qed.

(* Chains of type-level (star) product widenings.  A diagonal typing of an
   abstraction at a product may pass through intermediate product types,
   one [sub_sub] step at a time; [sub_chain] records such a chain.       *)

Inductive sub_chain : env -> trm -> trm -> Prop :=
 | sub_chain_refl : forall G P, sub_chain G P P
 | sub_chain_step : forall G P Q R,
     sub G P Q trm_star -> sub_chain G Q R -> sub_chain G P R.

Lemma sub_chain_append : forall G P Q,
  sub_chain G P Q -> forall R, sub G Q R trm_star -> sub_chain G P R.
Proof.
  intros G P Q H. induction H as [G0 P0 | G0 P0 Q0 R0 hstep hrest IH].
  - intros S hS. apply sub_chain_step with (Q := S);
      [ exact hS | apply sub_chain_refl ].
  - intros S hS. apply sub_chain_step with (Q := Q0);
      [ exact hstep | apply (IH S); exact hS ].
Qed.


(* A diagonal typing of an abstraction at [P] passes through a chain of
   product widenings from its canonical product [prod d D B0].  This is
   the structural decomposition needed to reason about widened abstract
   typings.                                                               *)

Lemma sub_abs_diag_chain : forall G d D b P,
  sub G (trm_abs d D b) (trm_abs d D b) P ->
  exists B0, sub_chain G (trm_prod d D B0) P.
Proof.
  intros G d D b P H.
  remember (trm_abs d D b) as lhs eqn:El.
  remember (trm_abs d D b) as rhs eqn:Er.
  revert d D b El Er.
  induction H as
    [ G0 Hwf
    | G0 x5 A0 e0 Hwf Hb
    | G0 x5 e2 A0 e1 Hb Hprem IHprem
    | G0 e0 A0 Hprem IHprem
    | G0 A0 Hprem IHprem
    | L G0 e1 A0 e2 e2' B h1 IH1 h2 IH2 hbody IHbody hbs IHbstar
    | G0 e1 A0 e2 C e3 B h1 IH1 h2 IH2
    | L G0 e A0 B e' A' B' h1 IH1 h2 IH2 h3 IH3 h4 IH4 h5 IH5 h6 IH6 h7 IH7
    | G0 B e1 e2 A0 h1 IH1 h2 IH2 hr
    | G0 e1 e2 B A0 h1 IH1 h2 IH2 hr
    | G0 e1 e2 B A0 h1 IH1 h2 IH2 ];
  intros d D b El Er.
  all: try (exfalso; congruence).
  - (* sub_var_trans *) exact (IHprem d D b El Er).
  - (* sub_abs *)
    assert (Heq : trm_abs e1 A0 e2' = trm_abs d D b)
      by (rewrite El; exact Er).
    injection Heq as Hd HD Hb. subst.
    exists B. apply sub_chain_refl.
  - (* sub_sub *)
    destruct (IH1 d D b El Er) as [B0 Hc].
    exists B0. eapply sub_chain_append; [ exact Hc | exact h2 ].
Qed.


(* Full inversion of a diagonal abstraction typing: it returns the
   canonical codomain family [B0], the abstraction body's self-typing and
   the codomain's self-typing in the canonical binder context, together
   with a widening chain from the canonical product to the result type.
   This is the decomposition used by the beta case of subject reduction. *)

Lemma sub_abs_diag_inv : forall G d D b P,
  sub G (trm_abs d D b) (trm_abs d D b) P ->
  exists L B0,
    (forall x, x \notin L ->
       sub (G & x ~ bind_sub d D) (b ^ x) (b ^ x) (B0 ^ x)) /\
    (forall x, x \notin L ->
       sub (G & x ~ bind_sub d D) (B0 ^ x) (B0 ^ x) trm_star) /\
    sub_chain G (trm_prod d D B0) P.
Proof.
  intros G d D b P H.
  dependent induction H.
  - (* sub_abs *)
    exists L, B. repeat split;
      [ exact H1 | exact H3 | apply sub_chain_refl ].
  - (* sub_sub *)
    destruct (IHsub1 d D b eq_refl eq_refl) as [L [B0 [Hbod [Hcod Hc]]]].
    exists L, B0. repeat split; [ exact Hbod | exact Hcod | ].
    eapply sub_chain_append; [ exact Hc | exact H0 ].
Qed.


(* Non-diagonal inversion of an abstraction typing: two abstractions with
   the same annotation.  Returns the canonical codomain, the (possibly
   non-diagonal) body relation, the codomain self-typing, and the widening
   chain.  This supplies the data for the abstraction case of the
   same-type composition lemma.                                          *)

Lemma sub_abs_inv : forall G d D b1 b2 P,
  sub G (trm_abs d D b1) (trm_abs d D b2) P ->
  exists L B0,
    (forall x, x \notin L ->
       sub (G & x ~ bind_sub d D) (b1 ^ x) (b2 ^ x) (B0 ^ x)) /\
    (forall x, x \notin L ->
       sub (G & x ~ bind_sub d D) (B0 ^ x) (B0 ^ x) trm_star) /\
    sub_chain G (trm_prod d D B0) P.
Proof.
  intros G d D b1 b2 P H.
  dependent induction H.
  - (* sub_abs *)
    exists L, B. repeat split;
      [ exact H1 | exact H3 | apply sub_chain_refl ].
  - (* sub_sub *)
    destruct (IHsub1 d D b1 b2 eq_refl eq_refl) as [L [B0 [Hbod [Hcod Hc]]]].
    exists L, B0. repeat split; [ exact Hbod | exact Hcod | ].
    eapply sub_chain_append; [ exact Hc | exact H0 ].
Qed.

Lemma fvs_holds : forall G e1 e2 A, sub G e1 e2 A -> fvs G e1 e2 A.
Proof.
  intros G e1 e2 A H.
  induction H as
    [ G0 Hwf
    | G0 x5 A0 e0 Hwf Hb
    | G0 x5 e2 A0 e1 Hb Hprem IHprem
    | G0 e0 A0 Hprem IHprem
    | G0 A0 Hprem IHprem
    | L G0 e1 A0 e2 e2' B h1 IH1 h2 IH2 hbody IHbody hbs IHbstar
    | G0 e1 A0 e2 C e3 B h1 IH1 h2 IH2
    | L G0 e A0 B e' A' B' h1 IH1 h2 IH2 h3 IH3 h4 IH4 h5 IH5 h6 IH6 h7 IH7
    | G0 B e1 e2 A0 h1 IH1 h2 IH2 hr
    | G0 e1 e2 B A0 h1 IH1 h2 IH2 hr
    | G0 e1 e2 B A0 h1 IH1 h2 IH2 ].
  - (* sub_ax *) intros z Hz. simpl in Hz. repeat rewrite in_empty in Hz. tauto.
  - (* sub_var_refl *)
    intros z Hz. simpl in Hz. repeat rewrite in_union in Hz.
    repeat rewrite in_singleton in Hz.
    destruct Hz as [Heq | [Heq | HA]].
    + subst z. exact (binds_in_dom Hb).
    + subst z. exact (binds_in_dom Hb).
    + apply (fvw_holds Hwf Hb). right. exact HA.
  - (* sub_var_trans *)
    intros z Hz. simpl in Hz. repeat rewrite in_union in Hz.
    repeat rewrite in_singleton in Hz.
    destruct Hz as [Heq | [He2 | HA]].
    + subst z. exact (binds_in_dom Hb).
    + apply (IHprem z). tauto.
    + apply (IHprem z). tauto.
  - (* sub_top *)
    intros z Hz. simpl in Hz. repeat rewrite in_union in Hz. repeat rewrite in_empty in Hz.
    apply (IHprem z). tauto.
  - (* sub_top_refl *)
    intros z Hz. simpl in Hz. repeat rewrite in_union in Hz. repeat rewrite in_empty in Hz.
    apply (IHprem z). tauto.
  - (* sub_abs *)
    intros z Hz. simpl in Hz.
    set (S := L \u (fv_trm e2 \u (fv_trm e2' \u fv_trm B))).
    destruct (var_fresh S) as [x0 Hx0].
    apply notin_union in Hx0. destruct Hx0 as [Hx0L Hx0r].
    apply notin_union in Hx0r. destruct Hx0r as [Hx0e2 Hx0r].
    apply notin_union in Hx0r. destruct Hx0r as [Hx0e2' Hx0B].
    assert (L1 : z \in fv_trm e1 -> z \in dom G0)
      by (intro H; apply (IH1 z); tauto).
    assert (LA : z \in fv_trm A0 -> z \in dom G0)
      by (intro H; apply (IH1 z); tauto).
    assert (L2 : z \in fv_trm e2 -> z \in dom G0).
    { intro H2.
      assert (Hop : z \in fv_trm (open_trm_wrt_trm e2 (trm_var_f x0)))
        by (apply fv_open_lower; exact H2).
      assert (Hdom : z \in dom (G0 & x0 ~ bind_sub e1 A0)).
      { apply (IHbody x0 Hx0L z). left. exact Hop. }
      rewrite dom_push in Hdom. rewrite in_union in Hdom.
      destruct Hdom as [Heqx | HG].
      - rewrite in_singleton in Heqx. subst z. exfalso. apply Hx0e2. exact H2.
      - exact HG. }
    assert (L2' : z \in fv_trm e2' -> z \in dom G0).
    { intro H2.
      assert (Hop : z \in fv_trm (open_trm_wrt_trm e2' (trm_var_f x0)))
        by (apply fv_open_lower; exact H2).
      assert (Hdom : z \in dom (G0 & x0 ~ bind_sub e1 A0)).
      { apply (IHbody x0 Hx0L z). right. left. exact Hop. }
      rewrite dom_push in Hdom. rewrite in_union in Hdom.
      destruct Hdom as [Heqx | HG].
      - rewrite in_singleton in Heqx. subst z. exfalso. apply Hx0e2'. exact H2.
      - exact HG. }
    assert (LB : z \in fv_trm B -> z \in dom G0).
    { intro H2.
      assert (Hop : z \in fv_trm (open_trm_wrt_trm B (trm_var_f x0)))
        by (apply fv_open_lower; exact H2).
      assert (Hdom : z \in dom (G0 & x0 ~ bind_sub e1 A0)).
      { apply (IHbody x0 Hx0L z). right. right. exact Hop. }
      rewrite dom_push in Hdom. rewrite in_union in Hdom.
      destruct Hdom as [Heqx | HG].
      - rewrite in_singleton in Heqx. subst z. exfalso. apply Hx0B. exact H2.
      - exact HG. }
    repeat rewrite in_union in *. tauto.
  - (* sub_app *)
    intros z Hz. simpl in Hz.
    assert (L1 : z \in fv_trm e1 -> z \in dom G0) by (intro H; apply (IH1 z); tauto).
    assert (L2 : z \in fv_trm e2 -> z \in dom G0) by (intro H; apply (IH1 z); tauto).
    assert (LA : z \in fv_trm A0 -> z \in dom G0) by (intro H; apply (IH2 z); tauto).
    assert (HC : z \in fv_trm (open_trm_wrt_trm C A0) -> z \in dom G0).
    { intro H. pose proof (@fv_open_upper C A0 z H) as Hu.
      repeat rewrite in_union in Hu. destruct Hu as [HC' | HA'].
      - apply (IH1 z). right. right. simpl. repeat rewrite in_union. tauto.
      - apply (IH2 z). left. exact HA'. }
    repeat rewrite in_union in *. tauto.
  - (* sub_prod *)
    intros z Hz. simpl in Hz.
    set (S := L \u (fv_trm B \u fv_trm B')).
    destruct (var_fresh S) as [x0 Hx0].
    apply notin_union in Hx0. destruct Hx0 as [Hx0L Hx0r].
    apply notin_union in Hx0r. destruct Hx0r as [Hx0B Hx0B'].
    assert (Le : z \in fv_trm e -> z \in dom G0) by (intro H; apply (IH6 z); tauto).
    assert (LA : z \in fv_trm A0 -> z \in dom G0) by (intro H; apply (IH6 z); tauto).
    assert (Le' : z \in fv_trm e' -> z \in dom G0) by (intro H; apply (IH7 z); tauto).
    assert (LA' : z \in fv_trm A' -> z \in dom G0) by (intro H; apply (IH7 z); tauto).
    assert (LB : z \in fv_trm B -> z \in dom G0).
    { intro H.
      assert (Hop : z \in fv_trm (open_trm_wrt_trm B (trm_var_f x0)))
        by (apply fv_open_lower; exact H).
      assert (Hdom : z \in dom (G0 & x0 ~ bind_sub e A0)).
      { apply (IH4 x0 Hx0L z). left. exact Hop. }
      rewrite dom_push in Hdom. rewrite in_union in Hdom.
      destruct Hdom as [Heqx | HG].
      - rewrite in_singleton in Heqx. subst z. exfalso. apply Hx0B. exact H.
      - exact HG. }
    assert (LB' : z \in fv_trm B' -> z \in dom G0).
    { intro H.
      assert (Hop : z \in fv_trm (open_trm_wrt_trm B' (trm_var_f x0)))
        by (apply fv_open_lower; exact H).
      assert (Hdom : z \in dom (G0 & x0 ~ bind_sub e' A')).
      { apply (IH5 x0 Hx0L z). right. left. exact Hop. }
      rewrite dom_push in Hdom. rewrite in_union in Hdom.
      destruct Hdom as [Heqx | HG].
      - rewrite in_singleton in Heqx. subst z. exfalso. apply Hx0B'. exact H.
      - exact HG. }
    repeat rewrite in_union in *. repeat rewrite in_empty in *. tauto.
  - (* sub_castup *)
    intros z Hz. simpl in Hz.
    assert (LB : z \in fv_trm B -> z \in dom G0) by (intro H; apply (IH1 z); tauto).
    assert (L1 : z \in fv_trm e1 -> z \in dom G0) by (intro H; apply (IH2 z); tauto).
    assert (L2 : z \in fv_trm e2 -> z \in dom G0) by (intro H; apply (IH2 z); tauto).
    repeat rewrite in_union in *. tauto.
  - (* sub_castdn *)
    intros z Hz. simpl in Hz.
    assert (LB : z \in fv_trm B -> z \in dom G0) by (intro H; apply (IH1 z); tauto).
    assert (L1 : z \in fv_trm e1 -> z \in dom G0) by (intro H; apply (IH2 z); tauto).
    assert (L2 : z \in fv_trm e2 -> z \in dom G0) by (intro H; apply (IH2 z); tauto).
    repeat rewrite in_union in *. tauto.
  - (* sub_sub *)
    intros z Hz. simpl in Hz.
    assert (L1 : z \in fv_trm e1 -> z \in dom G0) by (intro H; apply (IH1 z); tauto).
    assert (L2 : z \in fv_trm e2 -> z \in dom G0) by (intro H; apply (IH1 z); tauto).
    assert (LB : z \in fv_trm B -> z \in dom G0) by (intro H; apply (IH2 z); tauto).
    repeat rewrite in_union in *. tauto.
Qed.

(* Convenience corollaries of the scope invariants. *)

Lemma fvw_of_sub : forall G e1 e2 A, sub G e1 e2 A -> fvw G.
Proof. intros G e1 e2 A H. exact (fvw_holds (sub_wf H)). Qed.

Lemma fvs_of_sub : forall G e1 e2 A, sub G e1 e2 A -> fvs G e1 e2 A.
Proof. intros G e1 e2 A H. exact (@fvs_holds G e1 e2 A H). Qed.

(* Direct eliminator for the free-variable scope of a typing. *)

Lemma sub_fv_dom : forall G e1 e2 A z,
  sub G e1 e2 A ->
  z \in fv_trm e1 \/ z \in fv_trm e2 \/ z \in fv_trm A ->
  z \in dom G.
Proof. intros G e1 e2 A z H Hz. exact (@fvs_holds G e1 e2 A H z Hz). Qed.

(* Basic chain operations. *)

Lemma sub_chain_single : forall G P Q,
  sub G P Q trm_star -> sub_chain G P Q.
Proof.
  intros. apply sub_chain_step with (Q := Q);
    [ exact H | apply sub_chain_refl ].
Qed.

Lemma sub_chain_trans : forall G P Q,
  sub_chain G P Q -> forall R, sub_chain G Q R -> sub_chain G P R.
Proof.
  intros G P Q H. induction H as [G0 P0 | G0 P0 Q0 R0 hstep hrest IH].
  - intros R hR. exact hR.
  - intros R hR. apply sub_chain_step with (Q := Q0);
      [ exact hstep | apply (IH R hR) ].
Qed.

Lemma sub_chain_step_inv : forall G P Q,
  sub_chain G P Q -> P <> Q ->
  exists R, sub G P R trm_star /\ sub_chain G R Q.
Proof.
  intros G P Q H. destruct H as [G0 P0 | G0 P0 Q0 R0 hstep hrest].
  - intro Hne. exfalso. apply Hne. reflexivity.
  - intro Hne2. exists Q0. split; assumption.
Qed.

(* Single-step same-domain collapse: a product widening between products
   with the same domain exposes its codomain-family relation directly in
   that domain's binder context.                                           *)

Lemma sub_prod_same_domain_codom : forall G d D Bv B,
  sub G (trm_prod d D Bv) (trm_prod d D B) trm_star ->
  exists L, forall x, x \notin L ->
    sub (G & x ~ bind_sub d D) (Bv ^ x) (B ^ x) trm_star.
Proof.
  intros G d D Bv B H.
  destruct (sub_prod_full_gen H eq_refl eq_refl)
    as [H1 [H2 [H3 [H4 [H5 [H6 H7]]]]]].
  exact H5.
Qed.

(* Domain component relations of a product widening (monotonicity). *)

Lemma sub_prod_domain_relations : forall G d D Bv e A B,
  sub G (trm_prod d D Bv) (trm_prod e A B) trm_star ->
  sub G A D trm_star /\ sub G e d D.
Proof.
  intros G d D Bv e A B H.
  destruct (sub_prod_full_gen H eq_refl eq_refl)
    as [H1 [H2 [H3 [H4 [H5 [H6 H7]]]]]].
  split; assumption.
Qed.

(* A type that is self-typed at [star] is locally closed. *)

Lemma sub_lc_type_star : forall G A, sub G A A trm_star -> lc_trm A.
Proof.
  intros G A H. destruct (sub_lc_terms H) as [HA _]. exact HA.
Qed.

(* Source codomain self-typing of a same-domain product widening, in the
   common domain's binder context.                                       *)

Lemma sub_prod_same_domain_self : forall G d D Bv B,
  sub G (trm_prod d D Bv) (trm_prod d D B) trm_star ->
  exists L, forall x, x \notin L ->
    sub (G & x ~ bind_sub d D) (Bv ^ x) (Bv ^ x) trm_star.
Proof.
  intros G d D Bv B H.
  destruct (sub_prod_full_gen H eq_refl eq_refl)
    as [H1 [H2 [H3 [H4 [H5 [H6 H7]]]]]].
  exact H4.
Qed.

(* All components of a typing whose type is self-typed at [star] are
   locally closed.                                                      *)

Lemma sub_all_lc : forall G e1 e2 A,
  sub G e1 e2 A -> sub G A A trm_star ->
  lc_trm e1 /\ lc_trm e2 /\ lc_trm A.
Proof.
  intros G e1 e2 A H HA.
  destruct (sub_lc_terms H) as [H1 H2].
  pose proof (sub_lc_type_star HA) as H3.
  auto.
Qed.

(* [top] is a right supertype at any supertype of a type at which the term
   is self-typed.                                                       *)

Lemma sub_top_lift : forall G e A B,
  sub G e e A -> sub G A B trm_star -> sub G e trm_top B.
Proof.
  intros G e A B He HAB. apply sub_top.
  eapply sub_sub; [ exact He | exact HAB ].
Qed.

(* A bound variable is below [top] at its binding type. *)

Lemma sub_var_top : forall G x e A,
  wf G -> binds x (bind_sub e A) G -> sub G (trm_var_f x) trm_top A.
Proof.
  intros G x e A Hwf Hb. apply sub_top.
  apply sub_var_refl with (e := e); assumption.
Qed.

(* Packaged inversion of an abstraction typing: domain self-typings plus
   the canonical codomain, body relation, codomain self-typing, and
   widening chain.                                                      *)

Lemma sub_abs_inv_full : forall G d D b1 b2 P,
  sub G (trm_abs d D b1) (trm_abs d D b2) P ->
  sub G d d D /\
  sub G D D trm_star /\
  exists L B0,
    (forall x, x \notin L ->
       sub (G & x ~ bind_sub d D) (b1 ^ x) (b2 ^ x) (B0 ^ x)) /\
    (forall x, x \notin L ->
       sub (G & x ~ bind_sub d D) (B0 ^ x) (B0 ^ x) trm_star) /\
    sub_chain G (trm_prod d D B0) P.
Proof.
  intros G d D b1 b2 P H.
  destruct (sub_abs_wf_ctx_gen H eq_refl eq_refl) as [Hd HD].
  split; [ exact Hd | split; [ exact HD | exact (sub_abs_inv H) ] ].
Qed.

(* A product type is self-typed at [star] when its components are.  This
   is a regularity ingredient (and an instance of [sub_prod]).           *)

Lemma sub_prod_self_star : forall L G e A B,
  sub G e e A -> sub G A A trm_star ->
  (forall x, x \notin L ->
     sub (G & x ~ bind_sub e A) (B ^ x) (B ^ x) trm_star) ->
  sub G (trm_prod e A B) (trm_prod e A B) trm_star.
Proof.
  intros L G e A B HeeA HAA Hbody.
  apply (sub_prod L G e A B e A B);
    [ exact HAA | exact HeeA | exact HAA | exact Hbody | exact Hbody
    | exact HeeA | exact HeeA ].
Qed.

(* Chaining two type-level widenings on the type of a judgment. *)

Lemma sub_sub_trans : forall G e1 e2 A B C,
  sub G e1 e2 A -> sub G A B trm_star -> sub G B C trm_star ->
  sub G e1 e2 C.
Proof.
  intros G e1 e2 A B C H HAB HBC.
  eapply sub_sub; [ | exact HBC ].
  eapply sub_sub; [ exact H | exact HAB ].
Qed.

(* Diagonal abstraction introduction (specialized [sub_abs] with the same
   body on both sides).                                                  *)

Lemma sub_abs_self : forall L G e A b B,
  sub G e e A -> sub G A A trm_star ->
  (forall x, x \notin L ->
     sub (G & x ~ bind_sub e A) (b ^ x) (b ^ x) (B ^ x)) ->
  (forall x, x \notin L ->
     sub (G & x ~ bind_sub e A) (B ^ x) (B ^ x) trm_star) ->
  sub G (trm_abs e A b) (trm_abs e A b) (trm_prod e A B).
Proof.
  intros L G e A b B He HAA Hbody Hcod.
  apply (sub_abs L G e A b b B); assumption.
Qed.

(* Diagonal application introduction (specialized [sub_app]). *)

Lemma sub_app_self : forall G f a e B C,
  sub G f f (trm_prod e B C) -> sub G a e B ->
  sub G (trm_app f a) (trm_app f a) (C ^^ a).
Proof.
  intros G f a e B C Hf Ha.
  apply (sub_app G f a f C e B); assumption.
Qed.

(* Definitional distribution of substitution over term constructors. *)

Lemma subst_trm_app : forall v x a b,
  subst_trm v x (trm_app a b) = trm_app (subst_trm v x a) (subst_trm v x b).
Proof. reflexivity. Qed.

Lemma subst_trm_abs : forall v x e A b,
  subst_trm v x (trm_abs e A b) =
  trm_abs (subst_trm v x e) (subst_trm v x A) (subst_trm v x b).
Proof. reflexivity. Qed.

Lemma subst_trm_prod : forall v x e A B,
  subst_trm v x (trm_prod e A B) =
  trm_prod (subst_trm v x e) (subst_trm v x A) (subst_trm v x B).
Proof. reflexivity. Qed.

Lemma subst_trm_castup : forall v x A e,
  subst_trm v x (trm_castup A e) =
  trm_castup (subst_trm v x A) (subst_trm v x e).
Proof. reflexivity. Qed.

Lemma subst_trm_castdn : forall v x e,
  subst_trm v x (trm_castdn e) = trm_castdn (subst_trm v x e).
Proof. reflexivity. Qed.

Lemma subst_trm_star : forall v x, subst_trm v x trm_star = trm_star.
Proof. reflexivity. Qed.

Lemma subst_trm_top : forall v x, subst_trm v x trm_top = trm_top.
Proof. reflexivity. Qed.

Lemma subst_trm_anno : forall v x e A,
  subst_trm v x (trm_anno e A) =
  trm_anno (subst_trm v x e) (subst_trm v x A).
Proof. reflexivity. Qed.

(* Replaying a widening chain on a judgment: changing the type of a
   judgment along a chain of type-level widenings.                       *)

Lemma sub_chain_lift : forall G P Q,
  sub_chain G P Q -> forall s t, sub G s t P -> sub G s t Q.
Proof.
  intros G P Q H.
  induction H as [G0 P0 | G0 P0 Q0 R0 hstep hrest IH].
  - intros s t Hs. exact Hs.
  - intros s t Hs. apply (IH s t).
    eapply sub_sub; [ exact Hs | exact hstep ].
Qed.

(* General abstraction introduction (specialized [sub_abs] naming). *)

Lemma sub_abs_intro : forall L G d D b1 b2 B,
  sub G d d D -> sub G D D trm_star ->
  (forall x, x \notin L ->
     sub (G & x ~ bind_sub d D) (b1 ^ x) (b2 ^ x) (B ^ x)) ->
  (forall x, x \notin L ->
     sub (G & x ~ bind_sub d D) (B ^ x) (B ^ x) trm_star) ->
  sub G (trm_abs d D b1) (trm_abs d D b2) (trm_prod d D B).
Proof.
  intros L G d D b1 b2 B Hd HD Hb Hc.
  apply (sub_abs L G d D b1 b2 B); assumption.
Qed.

(* Diagonal cast introduction rules. *)

Lemma sub_castup_self : forall G B e A,
  sub G B B trm_star -> sub G e e A -> reduct B A ->
  sub G (trm_castup B e) (trm_castup B e) B.
Proof.
  intros G B e A HB He hr.
  apply (sub_castup G B e e A); assumption.
Qed.

Lemma sub_castdn_self : forall G e B A,
  sub G B B trm_star -> sub G e e A -> reduct A B ->
  sub G (trm_castdn e) (trm_castdn e) B.
Proof.
  intros G e B A HB He hr.
  apply (sub_castdn G e e B A); assumption.
Qed.

(* Canonical castelim coherence: the term-level reduction determines the
   type up to [reduct_det].                                              *)

Lemma castelim_subject : forall G B e A T,
  sub G B B trm_star -> sub G e e A -> reduct B A ->
  sub G T T trm_star -> reduct B T ->
  sub G e e T.
Proof.
  intros G B e A T HB He hrA HT hrT.
  assert (A = T) as Heq by (eapply reduct_det; [ exact hrA | exact hrT ]).
  subst T. exact He.
Qed.

(* Same-type transitivity with a self-typed middle, for the atomic middle
   terms [top] and [star].                                              *)

Lemma comp_self_top : forall G A,
  sub G trm_top trm_top A ->
  forall v, sub G v trm_top A ->
  forall c, sub G trm_top c A -> sub G v c A.
Proof.
  intros G A Self v Hv c D.
  apply sub_top_inv in D. subst c. exact Hv.
Qed.

Lemma comp_self_star : forall G A,
  sub G trm_star trm_star A ->
  forall v, sub G v trm_star A ->
  forall c, sub G trm_star c A -> sub G v c A.
Proof.
  intros G A Self v Hv c D.
  pose proof (sub_star_type_shape Self) as HA.
  destruct HA as [HA | HA]; subst A.
  - pose proof (sub_star_inv D) as HD.
    destruct HD as [-> | ->].
    + exact Hv.
    + apply sub_top. apply sub_left in Hv. exact Hv.
  - pose proof (sub_star_inv D) as HD.
    destruct HD as [-> | ->].
    + exact Hv.
    + apply sub_top. apply sub_left in Hv. exact Hv.
Qed.

(* CompSelf at the coarse type suffices for the form where the self-typing
   is given at a finer type related by a widening (the [sub_sub] shape).  *)

Lemma comp_gen_of_comp_self :
  (forall G e A, sub G e e A ->
     forall v, sub G v e A -> forall c, sub G e c A -> sub G v c A) ->
  forall G e A0 A,
    sub G e e A0 -> sub G A0 A trm_star ->
    forall v, sub G v e A ->
    forall c, sub G e c A -> sub G v c A.
Proof.
  intros Hcomp G e A0 A Self0 h v Hv c D.
  apply (Hcomp G e A).
  - eapply sub_sub; [ exact Self0 | exact h ].
  - exact Hv.
  - exact D.
Qed.

(* A typing of a variable term at a variable right-hand side exposes a
   binding variable plus a chain from that binding's type to the result
   type.  (All non-variable-right rules are eliminated.)                 *)

Lemma var_typing_chain : forall G v y A,
  sub G v (trm_var_f y) A ->
  exists z e_z A_z,
    v = trm_var_f z /\ binds z (bind_sub e_z A_z) G /\ sub_chain G A_z A.
Proof.
  intros G v y A H.
  dependent induction H.
  - (* var_refl *)
    exists y, e, A. split; [reflexivity|split; [exact H0|apply sub_chain_refl]].
  - (* var_trans *)
    exists x5, e1, A. split; [reflexivity|split; [exact H|apply sub_chain_refl]].
  - (* sub_sub *)
    destruct (IHsub1 y eq_refl) as [z [ez [Az [Hv [Hb Hc]]]]].
    exists z, ez, Az. split; [exact Hv|split; [exact Hb|]].
    eapply sub_chain_append; [exact Hc | exact H0].
Qed.

(* Variable-target base extraction: every typing of a variable right-hand
   side reaches the result type from that variable's own binding type by a
   chain.                                                               *)

Lemma var_target_base : forall G v y A,
  sub G v (trm_var_f y) A ->
  exists e_y A_y, binds y (bind_sub e_y A_y) G /\ sub_chain G A_y A.
Proof.
  intros G v y A H.
  dependent induction H.
  - (* var_refl *) exists e, A. split; [exact H0|apply sub_chain_refl].
  - (* var_trans *) exact (IHsub y eq_refl).
  - (* sub_sub *)
    destruct (IHsub1 y eq_refl) as [ey [Ay [Hb Hc]]].
    exists ey, Ay. split; [exact Hb|].
    eapply sub_chain_append; [exact Hc | exact H0].
Qed.

(* Left-variable decomposition: a typing of a variable left-hand side
   either is that same variable on the right or the stored binding term is
   itself below the right-hand side at the binding type.                *)

Lemma var_lhs_decomp : forall G y c A, sub G (trm_var_f y) c A ->
  exists e_y A_y, binds y (bind_sub e_y A_y) G /\ sub_chain G A_y A /\
    (c = trm_var_f y \/ sub G e_y c A_y).
Proof.
  intros G y c A H.
  dependent induction H.
  - (* var_refl *)
    exists e, A. split; [exact H0|split; [apply sub_chain_refl|left; reflexivity]].
  - (* var_trans *)
    exists e1, A. split; [exact H|split; [apply sub_chain_refl|right; exact H0]].
  - (* sub_top *)
    destruct (var_target_base H) as [ey [Ay [Hb Hc]]].
    exists ey, Ay. split; [exact Hb|split; [exact Hc|right]].
    apply sub_top. apply (wf_binds_sub (sub_wf H) Hb).
  - (* sub_sub *)
    destruct (IHsub1 y eq_refl) as [ey [Ay [Hb [Hc Hd]]]].
    exists ey, Ay. split; [exact Hb|split; [ | exact Hd]].
    eapply sub_chain_append; [exact Hc | exact H0].
Qed.

(* Same-type transitivity with a self-typed middle, variable-middle case
   (a genuine case of the missing composition lemma).                   *)

Lemma comp_var : forall G y A,
  sub G (trm_var_f y) (trm_var_f y) A ->
  forall v, sub G v (trm_var_f y) A ->
  forall c, sub G (trm_var_f y) c A -> sub G v c A.
Proof.
  intros G y A Self v Hv.
  dependent induction Hv.
  - (* var_refl *) intros c D. exact D.
  - (* var_trans *)
    intros c D.
    eapply sub_var_trans; [ exact H | ].
    apply (IHHv y Self eq_refl c D).
  - (* sub_sub *)
    intros c D.
    destruct (var_lhs_decomp D) as [ey [Ay [Hb [Hc Hd]]]].
    destruct (var_target_base Hv1) as [ey2 [Ay2 [Hb2 Hc2]]].
    assert (Heq : bind_sub ey Ay = bind_sub ey2 Ay2)
      by (eapply binds_functional; [ exact Hb | exact Hb2 ]).
    injection Heq as He HA. subst ey2 Ay2.
    assert (HDA : sub G (trm_var_f y) c A).
    { apply (sub_chain_lift Hc2).
      destruct Hd as [-> | Hprem].
      - apply sub_var_refl with (e := ey);
          [ apply sub_wf in Hv1; exact Hv1 | exact Hb2 ].
      - eapply sub_var_trans; [ exact Hb2 | exact Hprem ]. }
    assert (SelfA : sub G (trm_var_f y) (trm_var_f y) A).
    { apply (sub_chain_lift Hc2).
      apply sub_var_refl with (e := ey);
        [ apply sub_wf in Hv1; exact Hv1 | exact Hb2 ]. }
    eapply sub_sub; [ apply (IHHv1 y SelfA eq_refl c HDA) | exact Hv2 ].
Qed.

(* Variable-middle composition when the self-typing is given at a finer
   type and lifted along a chain.                                       *)

Lemma comp_var_chain : forall G y A B,
  sub G (trm_var_f y) (trm_var_f y) A -> sub_chain G A B ->
  forall v, sub G v (trm_var_f y) B ->
  forall c, sub G (trm_var_f y) c B -> sub G v c B.
Proof.
  intros G y A B Self Hc v Hv c D.
  apply (@comp_var G y B
           (@sub_chain_lift G A B Hc (trm_var_f y) (trm_var_f y) Self)
           v Hv c D).
Qed.

(* Right projection follows from full regularity.  The only rule whose
   right-projection case needs the type's self-typing is [sub_top]; every
   other case follows from the induction hypotheses (the abstraction case
   from the body IH, the application case from the function IH, and the
   product case from the codomain-family IH together with [sub_left]).   *)

Lemma RP_of_Reg :
  (forall G e1 e2 A, sub G e1 e2 A -> sub G A A trm_star) ->
  forall G e1 e2 A, sub G e1 e2 A -> sub G e2 e2 A.
Proof.
  intros Hreg G e1 e2 A H.
  induction H as
    [ G0 Hwf
    | G0 x5 A0 e Hwf Hb
    | G0 x5 e2 A0 e1 Hb Hprem IHprem
    | G0 e A0 Hprem IHprem
    | G0 A0 Hprem IHprem
    | L G0 e1 A0 e2 e2' B h1 IH1 h2 IH2 hbody IHbody hbs IHbstar
    | G0 e1 A0 e2 C e3 B h1 IH1 h2 IH2
    | L G0 e A0 B e' A' B' h1 IH1 h2 IH2 h3 IH3 h4 IH4 h5 IH5 h6 IH6 h7 IH7
    | G0 B e1 e2 A0 h1 IH1 h2 IH2 hr
    | G0 e1 e2 B A0 h1 IH1 h2 IH2 hr
    | G0 e1 e2 B A0 h1 IH1 h2 IH2 ].
  - (* ax *) apply sub_ax; exact Hwf.
  - (* var_refl *) apply sub_var_refl with (e := e); assumption.
  - (* var_trans *) exact IHprem.
  - (* top *) apply sub_top_refl. exact (Hreg _ _ _ _ Hprem).
  - (* top_refl *) apply sub_top_refl; exact Hprem.
  - (* abs *)
    refine (sub_abs L G0 e1 A0 e2' e2' B h1 h2 _ hbs).
    intros x Hx. apply (IHbody x Hx).
  - (* app *)
    refine (sub_app G0 e2 A0 e2 C e3 B IH1 h2).
  - (* prod *)
    refine (sub_prod L G0 e' A' B' e' A' B'
              (sub_left h1) h7 (sub_left h1) _ _ h7 h7).
    + intros x Hx. apply (IH5 x Hx).
    + intros x Hx. apply (IH5 x Hx).
  - (* castup *) refine (sub_castup G0 B e2 e2 A0 h1 IH2 hr).
  - (* castdn *) refine (sub_castdn G0 e2 e2 B A0 h1 IH2 hr).
  - (* sub *) eapply sub_sub; [ exact IH1 | exact h2 ].
Qed.

(* Full regularity and right projection both follow from the diagonal
   matching-binder substitution principle.  This is the key reduction of
   the remaining metatheory: the only rule whose regularity case is not
   immediate is [sub_app], where the result type [C ^^ a] needs the
   codomain-family self-typing of the function's product substituted at
   the argument.  Every recursive call is on a rule premise (the
   induction hypotheses), and the substitution principle is used once,
   on the codomain self-typing extracted from the function premise's
   regularity by [sub_prod_full_gen].                                  *)

Lemma RegRP_of_DiagSubst :
  (forall G x e A S T,
      sub (G & x ~ bind_sub e A)
          (open_trm_wrt_trm S (trm_var_f x))
          (open_trm_wrt_trm S (trm_var_f x))
          (open_trm_wrt_trm T (trm_var_f x)) ->
      forall a, sub G a e A ->
      sub G (open_trm_wrt_trm S a) (open_trm_wrt_trm S a)
            (open_trm_wrt_trm T a)) ->
  forall G e1 e2 A, sub G e1 e2 A ->
    (sub G A A trm_star /\ sub G e2 e2 A).
Proof.
  intros Hsub G e1 e2 A H.
  induction H as
    [ G0 Hwf
    | G0 x5 A0 e Hwf Hb
    | G0 x5 e2 A0 e1 Hb Hprem IHprem
    | G0 e A0 Hprem IHprem
    | G0 A0 Hprem IHprem
    | L G0 e1 A0 e2 e2' B h1 IH1 h2 IH2 hbody IHbody hbs IHbstar
    | G0 e1 A0 e2 C e3 B h1 IH1 h2 IH2
    | L G0 e A0 B e' A' B' h1 IH1 h2 IH2 h3 IH3 h4 IH4 h5 IH5 h6 IH6 h7 IH7
    | G0 B e1 e2 A0 h1 IH1 h2 IH2 hr
    | G0 e1 e2 B A0 h1 IH1 h2 IH2 hr
    | G0 e1 e2 B A0 h1 IH1 h2 IH2 ].
  - (* ax *) split; apply sub_ax; exact Hwf.
  - (* var_refl *)
    split.
    + apply wf_binds_type with (x := x5) (e := e); [ exact Hwf | exact Hb ].
    + apply sub_var_refl with (e := e); assumption.
  - (* var_trans *)
    split.
    + apply wf_binds_type with (x := x5) (e := e1);
        [ apply (sub_wf Hprem) | exact Hb ].
    + exact (proj2 IHprem).
  - (* top *)
    split.
    + exact (proj1 IHprem).
    + apply sub_top_refl. exact (proj1 IHprem).
  - (* top_refl *)
    split.
    + exact (proj2 IHprem).
    + apply sub_top_refl; exact (proj2 IHprem).
  - (* abs *)
    split.
    + apply (@sub_prod_self_star L G0 e1 A0 B h1 h2 hbs).
    + refine (sub_abs L G0 e1 A0 e2' e2' B h1 h2 _ hbs).
      intros x Hx. exact (proj2 (IHbody x Hx)).
  - (* app *)
    split.
    + pose proof (proj1 IH1) as HPP.
      destruct (@sub_prod_full_gen G0 (trm_prod e3 B C) (trm_prod e3 B C)
                  trm_star HPP e3 B C e3 B C eq_refl eq_refl)
        as [Hc1 [Hc2 [Hc3 [Hc4 [Hc5 [Hc6 Hc7]]]]]].
      destruct Hc4 as [Lc Hc4].
      destruct (var_fresh Lc) as [z Hz].
      exact (@Hsub G0 z e3 B C trm_star (Hc4 z Hz) A0 h2).
    + refine (sub_app G0 e2 A0 e2 C e3 B (proj2 IH1) h2).
  - (* prod *)
    split.
    + apply sub_ax. apply (sub_wf h1).
    + refine (sub_prod L G0 e' A' B' e' A' B'
                (sub_left h1) h7 (sub_left h1) _ _ h7 h7).
      * intros x Hx. exact (proj2 (IH5 x Hx)).
      * intros x Hx. exact (proj2 (IH5 x Hx)).
  - (* castup *)
    split.
    + exact h1.
    + refine (sub_castup G0 B e2 e2 A0 h1 (proj2 IH2) hr).
  - (* castdn *)
    split.
    + exact h1.
    + refine (sub_castdn G0 e2 e2 B A0 h1 (proj2 IH2) hr).
  - (* sub *)
    split.
    + exact (proj2 IH2).
    + eapply sub_sub; [ exact (proj2 IH1) | exact h2 ].
Qed.

(* The diagonal matching-binder substitution principle as a named
   proposition, together with the two projections it yields.           *)

Definition DiagSubstPrinciple : Prop :=
  forall G x e A S T,
    sub (G & x ~ bind_sub e A)
        (open_trm_wrt_trm S (trm_var_f x))
        (open_trm_wrt_trm S (trm_var_f x))
        (open_trm_wrt_trm T (trm_var_f x)) ->
    forall a, sub G a e A ->
    sub G (open_trm_wrt_trm S a) (open_trm_wrt_trm S a)
          (open_trm_wrt_trm T a).

Lemma Reg_of_DiagSubst : DiagSubstPrinciple ->
  forall G e1 e2 A, sub G e1 e2 A -> sub G A A trm_star.
Proof.
  intros H G e1 e2 A Hj.
  exact (proj1 (@RegRP_of_DiagSubst H G e1 e2 A Hj)).
Qed.

Lemma RP_of_DiagSubst : DiagSubstPrinciple ->
  forall G e1 e2 A, sub G e1 e2 A -> sub G e2 e2 A.
Proof.
  intros H G e1 e2 A Hj.
  exact (proj2 (@RegRP_of_DiagSubst H G e1 e2 A Hj)).
Qed.

(* Codomain self-typing packaged from a diagonal product self-typing.
   This is the component [sub_prod_full_gen] exposes in the product's own
   binder context; it is the source fact used by the codomain-substitution
   step for applications.                                            *)

Lemma sub_prod_diag_codom : forall G p q r,
  sub G (trm_prod p q r) (trm_prod p q r) trm_star ->
  exists L, forall x, x \notin L ->
    sub (G & x ~ bind_sub p q) (open_trm_wrt_trm r (trm_var_f x))
        (open_trm_wrt_trm r (trm_var_f x)) trm_star.
Proof.
  intros G p q r H.
  destruct (@sub_prod_full_gen G (trm_prod p q r) (trm_prod p q r) trm_star H
              p q r p q r eq_refl eq_refl) as [H1 [H2 [H3 [H4 _]]]].
  exact H4.
Qed.

(* Target-codomain self-typing from a product widening together with the
   target product's own self-typing.  (The target self-typing is exactly
   what [sub_prod_diag_codom] consumes.)                               *)

Lemma sub_prod_target_codom : forall G p q r p' q' r',
  sub G (trm_prod p q r) (trm_prod p' q' r') trm_star ->
  sub G (trm_prod p' q' r') (trm_prod p' q' r') trm_star ->
  exists L, forall x, x \notin L ->
    sub (G & x ~ bind_sub p' q') (open_trm_wrt_trm r' (trm_var_f x))
        (open_trm_wrt_trm r' (trm_var_f x)) trm_star.
Proof.
  intros G p q r p' q' r' Hw Hself.
  exact (sub_prod_diag_codom Hself).
Qed.

(* ********************************************************************** *)
(* Targets.                                                               *)
(*                                                                        *)
(* [progress_empty_wh] is proved below via [progress_any]: the argument  *)
(* uses the head-rigidity/type-shape/irreducibility lemmas above and the   *)
(* castup contradictions ([sub_star_prod_false], [sub_prod_prod_false],    *)
(* [sub_castup_prod_false]) to rule out the stuck values at a product      *)
(* type; it needs no transitivity of [sub].                               *)
(*                                                                        *)
(* [subject_reduction_wh] is still open.  The app/castdn congruence     *)
(* cases are provable by induction on the reduction; [castelim] reduces  *)
(* to type-level coherence of [sub] under reduction.  The [beta] case is *)
(* the obstruction: for a diagonal typing of [app (abs e A b) arg] whose *)
(* function type [prod e3 B C] is a [sub_sub]/[sub_prod] widening of the *)
(* canonical [prod e A B0], the body typing is only available in the     *)
(* context [x ~ e : A], while the argument is typed at [e3 : B].         *)
(* Instantiating the body at [arg] needs [arg : e : A], which requires   *)
(* composing [arg : e3 : B] with [e3 : e : A], i.e. same-type            *)
(* transitivity of [sub].  In the [sub_app]/[sub_app] case the two       *)
(* derivations type the shared function term at product types whose      *)
(* domains are a priori unrelated (the shared argument is typed at both  *)
(* domains, and only the opened codomains are related by the target),    *)
(* so no common product type is available to compose the function        *)
(* derivations.  The product well-formedness facts are proved            *)
(* ([sub_prod_components_gen]), but they do not relate the domains, and  *)
(* opening codomain families is not injective (the families [trm_var_b 0]) *)
(* and a self-typed closed [a] both open to [a]), so injectivity cannot  *)
(* recover the alignment.  The general heredity-substitution/            *)
(* parametricity theorem that would discharge this is not available from *)
(* the supplied definitions; the paper's semantic type-soundness         *)
(* development would be needed.                                          *)
(*                                                                        *)
(* The closest syntactic attempt to a substitution lemma -- induct on    *)
(* the derivation of [sub (G & x ~ e : A) (s^x) (t^x) (T^x)] and         *)
(* conclude [sub G (s^a) (t^a) (T^a)] for [a : e : A] -- closes the       *)
(* [sub_app] side-premise, [sub_sub], and diagonal [sub_var_trans] cases *)
(* (using the open/substitution commutation lemmas and [sub_left]).       *)
(* It fails only at non-diagonal [sub_var_trans] on the substituted      *)
(* variable: after substituting [a] for [x], the rule cannot be applied,  *)
(* and one needs [a <: t^a : A] from [a <: e : A] and [e <: t^a : A].    *)
(* That is precisely the same-type composition gap above.                *)
(*                                                                        *)
(* Inverting the canonical [sub_abs] case of the beta obligation shows    *)
(* that no widening is involved there: the target product is forced to    *)
(* equal the rule's product, the body premise is already in the context   *)
(* [x ~ e3 : B] with target [C^x], and the argument typing is             *)
(* [A0 : e3 : B].  So the canonical beta obligation is exactly the tight  *)
(* substitution lemma with matching second component; the widening is     *)
(* confined to the [sub_sub] case of the inversion.                       *)
(*                                                                        *)
(* Following that route: invert [h1]; a [sub_sub] chain is finite, so it   *)
(* ends in a canonical [sub_abs] typing whose body premise lives in       *)
(* [x ~ e_core : A_core] with target [B_core^x], while the argument is    *)
(* typed at the widened [e3 : B].  The [sub_prod] premises of the chain    *)
(* (domain relations and the codomain-family relation [B_core^x <: C^x]   *)
(* under the target context) are exactly the data of a *lifting* lemma     *)
(* that would transport the body typing to the widened context and its    *)
(* target [C^x].  That lifting theorem (context morphism for the unified  *)
(* judgment along a product subtyping) is the actual missing piece; it is  *)
(* what the paper's semantic development would provide.                   *)
(*                                                                        *)
(* [sub_prod_full_gen] and [sub_prod_step] package all the premises of a  *)
(* product widening between two *syntactic* endpoint products (note that  *)
(* [sub_sub] preserves both terms, so the base of any product/product      *)
(* judgment is a single [sub_prod] between the same endpoints).  However, *)
(* a diagonal typing of an abstraction at a widened product may pass      *)
(* through intermediate product *types*: [sub_sub] changes the type of    *)
(* the judgment, and each type step is a separate product/product         *)
(* judgment.  Advancing the opened body along such a chain therefore      *)
(* requires either (a) collapsing the chain (product-transitivity at      *)
(* star), whose codomain-family part composes relations living in         *)
(* different binder contexts, or (b) a context-change theorem for the      *)
(* judgment.  Both (a) and (b) reduce, at non-diagonal [sub_var_trans],   *)
(* to same-type transitivity, so the three are mutually dependent.        *)
(*                                                                        *)
(* Refined reduction (using the verified lemmas above): the beta         *)
(* obligation reduces by induction on the function typing [hf] to the     *)
(* matching-binder substitution lemma plus one domain-conversion step.    *)
(* In that step the [sub_var_trans] case closes using the induction       *)
(* hypothesis and [sub_sub] along the domain-type relation; the [sub_app] *)
(* case reduces to product-level function composition (compose [f <: g]   *)
(* at [P1] with [g <: h] at [P2]).  That composition's abstraction case   *)
(* must align the canonical codomains [B1], [B2] of the three              *)
(* abstractions; the chains only relate the *widened* product codomains   *)
(* in different binder contexts, so this again needs context change.      *)
(* The overall dependency cycle is: substitution -> same-type             *)
(* transitivity (self-typed middle) -> context change -> substitution.    *)
(* [fvw_holds] (binding scope) and the [subst_env]/freshness lemmas now   *)
(* remove the environment bookkeeping from that cycle; the remaining      *)
(* obstacle is the codomain-alignment case, for which no syntactic        *)
(* argument has been found.                                               *)
(*                                                                        *)
(* Same-domain chains are not trivial: e.g. the two-step chain            *)
(* [prod star star Bv] -> [prod star top B1] -> [prod star star B] is     *)
(* realizable (the first step has domain type [star <: top], the second   *)
(* has [top -> star] via contravariance, and both domain terms are        *)
(* [star]).  The two codomain relations live in [y ~ star : top] and      *)
(* [y ~ star : star] respectively, so collapsing them into the base       *)
(* context [x ~ star : star] is exactly the type-changing context         *)
(* transport that requires the substitution lemma.  Thus domain          *)
(* monotonicity alone does not collapse the chain.                       *)
(*                                                                        *)
(* Candidate-counterexample analysis (beta with reduct [star]): if the    *)
(* redex [app (abs e3 A body) star] is typed at a product, the body is    *)
(* either [star] (canonical codomain forced to [star]/[top]) or [var_b 0] *)
(* (canonical codomain = binder type [A], and the codomain chain forces   *)
(* [A] itself to be [star]/[top]).  In both cases the widening chain's    *)
(* codomain relations only ever produce [star]/[top], so the redex's      *)
(* target type cannot be a product.  This is evidence that the theorem is *)
(* true, not a counterexample; a syntactic proof still needs the chain    *)
(* induction, which is the missing piece.                                 *)
(*                                                                        *)
(* Right projection was also explored as a possible shortcut: for a       *)
(* general [sub G e1 e2 T], deriving [sub G e2 e2 T] needs [T : T : star] *)
(* (the [sub_top] case).  Under that hypothesis the base/structural       *)
(* rules and the abstraction case (using [sub_prod_full_gen] for the      *)
(* source codomain self-typing) go through, but the [sub_app] case needs  *)
(* the function product [P : P : star], and the [castup]/[castdn] cases   *)
(* need the premise type [A : A : star]; neither is available from the    *)
(* rule premises.  So right projection is not a viable shortcut either.   *)
(*                                                                        *)
(* Castelim: the canonical case is closed ([castelim_subject], by          *)
(* [reduct_det]); the outer [sub_sub] chain is replayed on the diagonal    *)
(* judgment; the residual case is an *inner* [sub_sub] chain on the        *)
(* [castup] typing combined with a [reduct] of the widened supertype,     *)
(* i.e. type coherence of [sub] under reduction.  This shares the same    *)
(* chain/type-coherence obstruction as the beta case.                     *)
(*                                                                        *)
(* More precisely, in the residual castelim case the cast type [A] is a    *)
(* redex reducing to [A_e], while a widened supertype [A1] (with          *)
(* [A <: A1 : star]) reduces to the target [T].  Since subtyping is       *)
(* shape-directed, a supertype of an application is an application with   *)
(* the *same* argument (or [top], which does not reduce); its reduct is   *)
(* the corresponding abstraction body applied to that argument.  Relating *)
(* [A_e = body^a] and [T = body1^a] is thereby exactly the body-          *)
(* substitution problem of the beta case.  So castelim's residual case is *)
(* not independent; it reduces to the same core.                          *)
(*                                                                        *)
(* Progress on the core: [comp_self_top] and [comp_self_star] are proved. *)
(* The product-middle case at [star] would need domain-type composition   *)
(* (a [star]-level instance whose middle is a product component, hence    *)
(* smaller) together with domain-term composition at the product's domain *)
(* type and codomain-term composition; the latter two are again general   *)
(* same-type composition at types not controlled by a simple term        *)
(* measure, so the product case is not closed by the atomic lemmas.       *)
(*                                                                        *)
(* Variable-middle case: the variable-chain append works for             *)
(* [sub_var_refl]/[sub_var_trans] at a common type, but the [sub_sub]    *)
(* branch has the wrong type direction (the IH lives at the smaller type *)
(* [A0] while the two side derivations are at the larger [A]); changing  *)
(* their type would need [A <: A0].  So even the variable case is blocked *)
(* by the same type-chain direction issue.                               *)
(*                                                                        *)
(* Automated attempt: a full triple [dependent induction] on the three    *)
(* derivations (self-typing, left, right) followed by [eauto] does not    *)
(* terminate in reasonable time; the dependent eliminations on the        *)
(* concrete terms generate a large equation-heavy case tree.  A          *)
(* successful proof would need a hand-crafted, measure-guided mutual      *)
(* induction, not brute force.                                           *)
(*                                                                        *)
(* Product case with a shared middle product [prod p q r]: the domain    *)
(* type/term compositions reduce to CompSelf at the *components* [q] and  *)
(* [v1A] (smaller terms), but the codomain-family composition             *)
(* [v1B^y <: r^y] (context [y ~ p : q]) with [r^y <: c1B^y] (context      *)
(* [y ~ c1e : c1A]) again needs context change along widening bindings    *)
(* ([c1e <: p : q], [c1A <: q]); that context change's non-diagonal       *)
(* [sub_var_trans] case is the same composition.  So even the shared-     *)
(* component product case is not closed syntactically.                    *)
(*                                                                        *)
(* Summary: all one-sided metatheory, decomposition, scope, weakening,     *)
(* chain algebra, diagonal-castelim coherence, and the atomic-middle       *)
(* composition cases are verified.  The remaining obligation is a          *)
(* hereditary-substitution/context-morphism theorem for the unified        *)
(* judgment; every syntactic reduction of beta/castelim/CompSelf ends at   *)
(* that same theorem.  The target is left open and its single open proof  *)
(* obligation is explicit, rather than being replaced by any unsound       *)
(* shortcut.                                                              *)
(*                                                                        *)
(* App/product composition attempt: proving product comparability for two *)
(* products of the same function [g] by induction on the shared argument's*)
(* typing reduces the domain component relations successfully, but the    *)
(* codomain-family comparison (two families with equal openings at the    *)
(* argument, in the target binder context) is still not derivable from    *)
(* the hypotheses; the families can be distinct preimages of the same     *)
(* opening.  Thus the product-comparability route does not close either.  *)
(*                                                                        *)
(* Variable-middle composition IS proved ([comp_var]): dependent         *)
(* induction on the variable-target typing leaves var_refl (immediate),   *)
(* var_trans (IH on the premise + sub_var_trans), and sub_sub.  In the    *)
(* sub_sub case [var_lhs_decomp] builds the third derivation at the       *)
(* smaller premise type, [var_target_base] supplies the binding-type      *)
(* chain, and [sub_chain_lift] rebuilds the diagonal self-typing at that  *)
(* smaller type; the IH then applies and sub_sub restores the type.       *)
(* The previously suspected join problem is thereby avoided.  Remaining   *)
(* [CompSelf] cases: product/abstraction/application/cast middles.  The   *)
(* product case at [top] reduces to the same [sub_sub]-spine analysis with*)
(* a mixed decreasing measure (one of the two side derivations unchanged) *)
(* that is not yet formalized.                                            *)
(* ********************************************************************** *)

Theorem subject_reduction_wh : forall E t t' T,
  sub E t t T -> t --> t' -> sub E t' t' T.
Proof.
Admitted.

Theorem progress_empty_wh : forall t T,
  sub empty t t T ->
  value t \/ exists t', t --> t'.
Proof.
  intros t T H. exact (@progress_any empty t t T H eq_refl).
Qed.
