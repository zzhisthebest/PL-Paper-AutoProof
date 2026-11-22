Require Import syntax_ott.

Require Import Program.Equality.

Require Import Metalib.Metatheory.

Require Import Lia.

Require Import Relation_Operators.

Require Import Operators_Properties.

(* ============================================================ *)
(* Basic context helpers                                        *)
(* ============================================================ *)

Definition flip_pair (p : typ * typ) : typ * typ := (snd p, fst p).

Definition flip_ctx (E : cctx) : cctx := map flip_pair E.

Definition realizes (H : actx) (E : cctx) : Prop :=
  uniq E /\
  (forall p, In p H ->
     (exists x, In (x,p) E) /\ (exists y, In (y, flip_pair p) E)).

Lemma flip_pair_invol : forall p, flip_pair (flip_pair p) = p.
Proof. intros [a b]. reflexivity. Qed.

Lemma flip_pair_eq : forall A B, flip_pair (A,B) = (B,A).
Proof. reflexivity. Qed.

Lemma in_flip_ctx : forall E x p,
  In (x,p) (flip_ctx E) <-> In (x, flip_pair p) E.
Proof.
  intros. unfold flip_ctx. split.
  - intros H. apply binds_map_3 in H.
    destruct H as [q [Heq Hin]].
    rewrite <- Heq. rewrite flip_pair_invol. exact Hin.
  - intros H. pose proof (@binds_map (typ*typ) (typ*typ) flip_pair x (flip_pair p) E H) as H'.
    rewrite flip_pair_invol in H'. exact H'.
Qed.

Lemma in_flip_ctx_inv : forall E x A B,
  In (x,(A,B)) E -> In (x,(B,A)) (flip_ctx E).
Proof.
  intros. apply in_flip_ctx. simpl. exact H.
Qed.

Lemma uniq_flip_ctx : forall E, uniq E -> uniq (flip_ctx E).
Proof. intros. unfold flip_ctx. apply uniq_map_2. exact H. Qed.

Lemma realizes_uniq : forall H E, realizes H E -> uniq E.
Proof. intros H E [Hu _]. exact Hu. Qed.

(* ============================================================ *)
(* Weakening for eqe2                                           *)
(* ============================================================ *)

Lemma eqe2_weaken : forall D H A B,
  eqe2 D H A B -> forall H', (forall p, In p H -> In p H') -> eqe2 D H' A B.
Proof.
  intros D H A B Hd.
  induction Hd; intros H' Hin.
  - apply e2_assump; auto.
  - apply e2_refl; auto.
  - eapply e2_trans; eauto.
  - apply e2_symm; auto.
  - apply e2_fld; auto.
  - apply e2_arrfix.
    + apply IHHd1. intros p Hp.
      simpl in Hp. destruct Hp as [Heq | Hp].
      * left. exact Heq.
      * right. apply Hin. exact Hp.
    + apply IHHd2. intros p Hp.
      simpl in Hp. destruct Hp as [Heq | Hp].
      * left. exact Heq.
      * right. apply Hin. exact Hp.
Qed.

(* ============================================================ *)
(* Soundness                                                    *)
(* ============================================================ *)

Lemma TypCast_sound_gen : forall D E A B c,
  TypCast D E A B c ->
  forall H, (forall x p, In (x,p) E -> In p H) -> eqe2 D H A B.
Proof.
  intros D E A B c Ht.
  induction Ht; intros Hctx Hin.
  - (* id *) apply e2_refl; auto.
  - (* arrow *)
    apply e2_arrfix.
    + apply eqe2_weaken with (H := Hctx).
      * apply IHHt1. intros x p Hinp. exact (Hin x p Hinp).
      * intros p Hp. simpl. right. exact Hp.
    + apply eqe2_weaken with (H := Hctx).
      * apply IHHt2. intros x p Hinp. exact (Hin x p Hinp).
      * intros p Hp. simpl. right. exact Hp.
  - (* unfold *) apply e2_fld; auto.
  - (* fold *) apply e2_symm. apply e2_fld; auto.
  - (* seq *) eapply e2_trans; eauto.
  - (* var *)
    apply e2_assump.
    + exact (Hin cx (A, B) H2).
    + exact H.
    + exact H0.
  - (* fix *)
    destruct (atom_fresh L) as [cx Hfresh].
    apply e2_arrfix.
    + apply H0 with (cx := cx).
      * exact Hfresh.
      * intros x p Hinp. simpl in Hinp. simpl.
        destruct Hinp as [Heq | Hinp].
        -- left. injection Heq as _ Heqp. exact Heqp.
        -- right. exact (Hin x p Hinp).
    + apply H2 with (cx := cx).
      * exact Hfresh.
      * intros x p Hinp. simpl in Hinp. simpl.
        destruct Hinp as [Heq | Hinp].
        -- left. injection Heq as _ Heqp. exact Heqp.
        -- right. exact (Hin x p Hinp).
Qed.

Theorem TypCast_soundness: forall D A B c,
  TypCast D nil A B c ->
  eqe2 D nil A B.
Proof.
  intros. eapply TypCast_sound_gen with (E := nil) (H := nil).
  - exact H.
  - intros x p Hnil. inversion Hnil.
Qed.

(* ============================================================ *)
(* Locally closed cast operators (no free bound variables)      *)
(* ============================================================ *)

Fixpoint lc_b (k:nat) (c:castop) {struct c} : Prop :=
  match c with
  | c_var_b n => n < k
  | c_var_f _ => True
  | c_id => True
  | c_unfold _ => True
  | c_fold _ => True
  | c_arrow c1 c2 => lc_b k c1 /\ lc_b k c2
  | c_seq c1 c2 => lc_b k c1 /\ lc_b k c2
  | c_fixc c => lc_b (S k) c
  end.

Lemma lc_b_mono : forall c k k', lc_b k c -> k <= k' -> lc_b k' c.
Proof.
  induction c as [n|cx| |A|A|c1 IH1 c2 IH2|c1 IH1 c2 IH2|c IHc];
  intros k k' H Hle; simpl in *.
  - lia.
  - exact I.
  - exact I.
  - exact I.
  - exact I.
  - destruct H as [H1 H2]; split;
    [apply IH1 with (k:=k)|apply IH2 with (k:=k)]; auto.
  - destruct H as [H1 H2]; split;
    [apply IH1 with (k:=k)|apply IH2 with (k:=k)]; auto.
  - apply IHc with (k:=S k); auto; lia.
Qed.

Lemma lc_b_open_id : forall c k m v,
  lc_b k c -> open_castop_wrt_castop_rec (k+m) v c = c.
Proof.
  induction c as [n|cx| |A|A|c1 IH1 c2 IH2|c1 IH1 c2 IH2|c IHc];
  intros k m v H; simpl in *.
  - destruct (lt_eq_lt_dec n (k+m)) as [[H1|H2]|H3].
    + reflexivity.
    + lia.
    + lia.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - destruct H as [H1 H2].
    rewrite (IH1 k m v H1). rewrite (IH2 k m v H2). reflexivity.
  - destruct H as [H1 H2].
    rewrite (IH1 k m v H1). rewrite (IH2 k m v H2). reflexivity.
  - simpl. apply f_equal. exact (IHc (S k) m v H).
Qed.

Lemma open_closed_cast : forall c k v, lc_b 0 c -> open_castop_wrt_castop_rec k v c = c.
Proof. intros. exact (lc_b_open_id c 0 k v H). Qed.

Lemma lc_b_almost : forall c k v,
  lc_b (S k) v -> lc_b k (open_castop_wrt_castop_rec k v c) -> lc_b (S k) c.
Proof.
  induction c as [n|cx| |A|A|c1 IH1 c2 IH2|c1 IH1 c2 IH2|c IHc];
  intros k v Hv Hop; simpl in *.
  - destruct (lt_eq_lt_dec n k) as [[H1|H2]|H3].
    + lia.
    + lia.
    + simpl in Hop; lia.
  - exact I.
  - exact I.
  - exact I.
  - exact I.
  - destruct Hop as [H1 H2]; split;
    [apply IH1 with (v:=v)|apply IH2 with (v:=v)]; auto.
  - destruct Hop as [H1 H2]; split;
    [apply IH1 with (v:=v)|apply IH2 with (v:=v)]; auto.
  - apply IHc with (k:=S k) (v:=v).
    + apply lc_b_mono with (k:=S k) (k':=S (S k)); auto; lia.
    + exact Hop.
Qed.

Lemma lc_b_castsubst : forall a x c k,
  lc_b 0 a -> lc_b k c -> lc_b k (castsubst_castop a x c).
Proof.
  intros a x c. induction c as [n|cx| |A|A|c1 IH1 c2 IH2|c1 IH1 c2 IH2|c IHc];
  intros k Ha Hc; simpl in *.
  - exact Hc.
  - destruct (eq_dec cx x).
    + apply lc_b_mono with (k:=0) (k':=k); auto; lia.
    + exact I.
  - exact I.
  - exact I.
  - exact I.
  - destruct Hc as [H1 H2]; split;
    [apply IH1 with (k:=k)|apply IH2 with (k:=k)]; auto.
  - destruct Hc as [H1 H2]; split;
    [apply IH1 with (k:=k)|apply IH2 with (k:=k)]; auto.
  - apply IHc with (k:=S k); auto.
Qed.

(* equations exposing the definitions on variables *)
Lemma open_rec_var_b : forall k v n,
  open_castop_wrt_castop_rec k v (c_var_b n) =
  match lt_eq_lt_dec n k with
  | inleft (left _) => c_var_b n
  | inleft (right _) => v
  | inright _ => c_var_b (n - 1)
  end.
Proof. intros. reflexivity. Qed.

Lemma close_rec_var_b : forall k x n,
  close_castop_wrt_castop_rec k x (c_var_b n) =
  (if lt_dec n k then c_var_b n else c_var_b (S n)).
Proof. intros. reflexivity. Qed.

Lemma close_rec_var_f : forall k x cx,
  close_castop_wrt_castop_rec k x (c_var_f cx) =
  (if eq_dec x cx then c_var_b k else c_var_f cx).
Proof. intros. reflexivity. Qed.

Lemma castsubst_var_f : forall a x cx,
  castsubst_castop a x (c_var_f cx) =
  (if eq_dec cx x then a else c_var_f cx).
Proof. intros. reflexivity. Qed.

Lemma castsubst_var_b : forall a x n,
  castsubst_castop a x (c_var_b n) = c_var_b n.
Proof. intros. reflexivity. Qed.

Lemma open_rec_var_f : forall k v cx,
  open_castop_wrt_castop_rec k v (c_var_f cx) = c_var_f cx.
Proof. intros. reflexivity. Qed.

(* close/open identity: opening a closed atom at the same level is renaming *)
Lemma open_close_rename : forall c k x y,
  open_castop_wrt_castop_rec k (c_var_f y) (close_castop_wrt_castop_rec k x c)
  = castsubst_castop (c_var_f y) x c.
Proof.
  induction c as [n|cx| |A|A|c1 IH1 c2 IH2|c1 IH1 c2 IH2|c IHc];
  intros k x y.
  - (* c_var_b *)
    rewrite close_rec_var_b.
    destruct (lt_dec n k) as [Hlt|Hnlt].
    + rewrite open_rec_var_b.
      destruct (lt_eq_lt_dec n k) as [[H1|H2]|H3].
      * simpl. reflexivity.
      * lia.
      * lia.
    + rewrite open_rec_var_b.
      destruct (lt_eq_lt_dec (S n) k) as [[H1|H2]|H3].
      * exfalso. apply Hnlt. lia.
      * exfalso. apply Hnlt. lia.
      * simpl. apply f_equal. lia.
  - (* c_var_f *)
    rewrite close_rec_var_f.
    destruct (eq_dec x cx) as [Heq|Hne].
    + subst. rewrite open_rec_var_b. rewrite castsubst_var_f.
      destruct (lt_eq_lt_dec k k) as [[H1|H2]|H3].
      * lia.
      * simpl. destruct (eq_dec cx cx) as [Heq'|Hne'].
        -- reflexivity.
        -- congruence.
      * lia.
    + rewrite castsubst_var_f.
      destruct (eq_dec cx x) as [Heq'|Hne'].
      * exfalso. apply Hne. symmetry. exact Heq'.
      * reflexivity.
  - (* c_id *) reflexivity.
  - (* c_unfold *) reflexivity.
  - (* c_fold *) reflexivity.
  - (* c_arrow *) simpl. rewrite IH1. rewrite IH2. reflexivity.
  - (* c_seq *) simpl. rewrite IH1. rewrite IH2. reflexivity.
  - (* c_fixc *) simpl. rewrite IHc. reflexivity.
Qed.

(* substitution commutes with opening, for a locally closed replacement *)
Lemma castsubst_open : forall c a x y k,
  lc_b 0 a -> x <> y ->
  castsubst_castop a x (open_castop_wrt_castop_rec k (c_var_f y) c)
  = open_castop_wrt_castop_rec k (c_var_f y) (castsubst_castop a x c).
Proof.
  induction c as [n|cx| |A|A|c1 IH1 c2 IH2|c1 IH1 c2 IH2|c IHc];
  intros a x y k Ha Hxy.
  - (* c_var_b *)
    rewrite castsubst_var_b.
    rewrite open_rec_var_b.
    destruct (lt_eq_lt_dec n k) as [[H1|H2]|H3].
    + simpl. reflexivity.
    + subst. rewrite castsubst_var_f.
      destruct (eq_dec y x) as [Heq|Hne].
      * exfalso. apply Hxy. symmetry. exact Heq.
      * reflexivity.
    + simpl. reflexivity.
  - (* c_var_f *)
    rewrite open_rec_var_f.
    rewrite !castsubst_var_f.
    destruct (eq_dec cx x) as [Heq|Hne].
    + subst. simpl.
      rewrite open_closed_cast with (c:=a) (k:=k) (v:=c_var_f y) by exact Ha.
      reflexivity.
    + reflexivity.
  - (* c_id *) reflexivity.
  - (* c_unfold *) reflexivity.
  - (* c_fold *) reflexivity.
  - (* c_arrow *) simpl. rewrite IH1; auto. rewrite IH2; auto.
  - (* c_seq *) simpl. rewrite IH1; auto. rewrite IH2; auto.
  - (* c_fixc *) simpl. rewrite IHc; auto.
Qed.


(* ============================================================ *)
(* Every derivable cast is locally closed                       *)
(* ============================================================ *)

Lemma TypCast_lc_b : forall D E A B c, TypCast D E A B c -> lc_b 0 c.
Proof.
  intros D E A B c H.
  induction H as [D E A Hwf Huniq
                | D E A1 B1 A2 B2 c1 c2 H1 IH1 H2 IH2
                | D E A Hwf Huniq
                | D E A Hwf Huniq
                | D E A C c1 c2 B H1 IH1 H2 IH2
                | D E A B cx H1 H2 H3 H4
                | L D E A1 B1 A2 B2 c1 c2 H1 IH1 H2 IH2].
  - (* id *) simpl. exact I.
  - (* arrow *) simpl. split; assumption.
  - (* unfold *) simpl. exact I.
  - (* fold *) simpl. exact I.
  - (* seq *) simpl. split; assumption.
  - (* var *) simpl. exact I.
  - (* fix *) simpl. split.
    + destruct (atom_fresh L) as [cx Hf].
      apply (lc_b_almost c1 0 (c_var_f cx)).
      * simpl. exact I.
      * exact (IH1 cx Hf).
    + destruct (atom_fresh L) as [cx Hf].
      apply (lc_b_almost c2 0 (c_var_f cx)).
      * simpl. exact I.
      * exact (IH2 cx Hf).
Qed.

(* ============================================================ *)
(* Structural properties of TypCast                             *)
(* ============================================================ *)

Lemma TypCast_weaken : forall D E A B c, TypCast D E A B c ->
  forall E', uniq E' ->
  (forall x p, In (x,p) E -> In (x,p) E') ->
  TypCast D E' A B c.
Proof.
  intros D E A B c H.
  induction H as [D E A Hwf Huniq
                | D E A1 B1 A2 B2 c1 c2 H1 IH1 H2 IH2
                | D E A Hwf Huniq
                | D E A Hwf Huniq
                | D E A C c1 c2 B H1 IH1 H2 IH2
                | D E A B cx H1 H2 H3 H4
                | L D E A1 B1 A2 B2 c1 c2 H1 IH1 H2 IH2];
  intros E' Hu Hin.
  - apply TCast_id; auto.
  - apply TCast_arrow; auto.
  - apply TCast_unfold; auto.
  - apply TCast_fold; auto.
  - eapply TCast_seq; [apply IH1 with (E':=E')|apply IH2 with (E':=E')]; auto.
  - eapply TCast_var; eauto.
  - apply TCast_fix with (L := L \u dom E').
    + intros cx Hf.
      apply (IH1 cx (notin_union_1 _ _ _ Hf)).
      * apply uniq_cons_3.
        -- exact Hu.
        -- apply notin_union_2 in Hf. exact Hf.
      * intros x p Hinp. simpl in Hinp. simpl.
        destruct Hinp as [Heq|Hinp].
        -- left. exact Heq.
        -- right. apply Hin. exact Hinp.
    + intros cx Hf.
      apply (IH2 cx (notin_union_1 _ _ _ Hf)).
      * apply uniq_cons_3.
        -- exact Hu.
        -- apply notin_union_2 in Hf. exact Hf.
      * intros x p Hinp. simpl in Hinp. simpl.
        destruct Hinp as [Heq|Hinp].
        -- left. exact Heq.
        -- right. apply Hin. exact Hinp.
Qed.

Lemma TypCast_perm : forall D E A B c, TypCast D E A B c ->
  forall E', (forall x p, In (x,p) E <-> In (x,p) E') -> uniq E' ->
  TypCast D E' A B c.
Proof.
  intros D E A B c H.
  induction H as [D E A Hwf Huniq
                | D E A1 B1 A2 B2 c1 c2 H1 IH1 H2 IH2
                | D E A Hwf Huniq
                | D E A Hwf Huniq
                | D E A C c1 c2 B H1 IH1 H2 IH2
                | D E A B cx H1 H2 H3 H4
                | L D E A1 B1 A2 B2 c1 c2 H1 IH1 H2 IH2];
  intros E' Hiff Hu.
  - apply TCast_id; auto.
  - apply TCast_arrow; auto.
  - apply TCast_unfold; auto.
  - apply TCast_fold; auto.
  - eapply TCast_seq; [apply IH1 with (E':=E')|apply IH2 with (E':=E')]; auto.
  - eapply TCast_var; eauto. apply Hiff. exact H4.
  - apply TCast_fix with (L := L \u (dom E \u dom E')).
    + intros cx Hf.
      apply (IH1 cx (notin_union_1 cx L (dom E \u dom E') Hf)).
      * intros x p. simpl. split.
        -- intros [Heq|Hinp]. left; exact Heq. right. apply Hiff. exact Hinp.
        -- intros [Heq|Hinp]. left; exact Heq. right. apply Hiff. exact Hinp.
      * apply uniq_cons_3.
        -- exact Hu.
        -- exact (notin_union_2 cx (dom E) (dom E')
                    (notin_union_2 cx L (dom E \u dom E') Hf)).
    + intros cx Hf.
      apply (IH2 cx (notin_union_1 cx L (dom E \u dom E') Hf)).
      * intros x p. simpl. split.
        -- intros [Heq|Hinp]. left; exact Heq. right. apply Hiff. exact Hinp.
        -- intros [Heq|Hinp]. left; exact Heq. right. apply Hiff. exact Hinp.
      * apply uniq_cons_3.
        -- exact Hu.
        -- exact (notin_union_2 cx (dom E) (dom E')
                    (notin_union_2 cx L (dom E \u dom E') Hf)).
Qed.

(* ============================================================ *)
(* Renaming cast variables in a context                         *)
(* ============================================================ *)

Definition subst_ctx (x y : atom) (E : cctx) : cctx :=
  List.map (fun z => ((if eq_dec (fst z) x then y else fst z), snd z)) E.

Lemma subst_ctx_cons : forall x y a p E,
  subst_ctx x y ((a,p)::E) =
  (((if eq_dec a x then y else a), p) :: subst_ctx x y E).
Proof. intros. reflexivity. Qed.

Lemma subst_ctx_cons_same : forall (x y:atom) (P:typ*typ) E,
  subst_ctx x y ((x,P)::E) = ((y,P)::subst_ctx x y E).
Proof.
  intros. rewrite subst_ctx_cons.
  destruct (eq_dec x x) as [e|n].
  - reflexivity.
  - exfalso. exact (n eq_refl).
Qed.

Lemma in_subst_ctx : forall x y E a p,
  In (a,p) E ->
  In (((if eq_dec a x then y else a), p)) (subst_ctx x y E).
Proof.
  intros. unfold subst_ctx.
  exact (List.in_map
           (fun z => ((if eq_dec (fst z) x then y else fst z), snd z)) E (a,p) H).
Qed.

Lemma in_subst_ctx_same : forall x y E p,
  In (x,p) E -> In (y,p) (subst_ctx x y E).
Proof.
  intros x y E. induction E as [| [z q] E' IH]; intros p H.
  - inversion H.
  - rewrite subst_ctx_cons. simpl in H. destruct H as [Heq|H].
    + injection Heq as Hz Hp. subst z q.
      simpl. destruct (eq_dec x x) as [e|n].
      * left. reflexivity.
      * exfalso. exact (n eq_refl).
    + right. apply IH. exact H.
Qed.

Lemma in_subst_ctx_diff : forall x y E a p,
  a <> x -> In (a,p) E -> In (a,p) (subst_ctx x y E).
Proof.
  intros x y E. induction E as [| [z q] E' IH]; intros a p Hne H.
  - inversion H.
  - rewrite subst_ctx_cons. simpl in H. destruct H as [Heq|H].
    + injection Heq as Hz Hp. subst z q.
      simpl. destruct (eq_dec a x) as [e|n].
      * exfalso. exact (Hne e).
      * left. reflexivity.
    + right. apply IH; auto.
Qed.

Lemma castsubst_var_same : forall a (x:atom),
  castsubst_castop a x (c_var_f x) = a.
Proof.
  intros. change ((if eq_dec x x then a else c_var_f x) = a).
  destruct (eq_dec x x) as [e|n].
  - reflexivity.
  - exfalso. exact (n eq_refl).
Qed.

Lemma castsubst_var_diff : forall a (x cx:atom), cx <> x ->
  castsubst_castop a x (c_var_f cx) = c_var_f cx.
Proof.
  intros. change ((if eq_dec cx x then a else c_var_f cx) = c_var_f cx).
  destruct (eq_dec cx x) as [e|n].
  - exfalso. exact (H e).
  - reflexivity.
Qed.

Lemma notin_add_s : forall z a (s:atoms), z `notin` AtomSetImpl.add a s -> z `notin` s.
Proof.
  intros z a s H Hin. apply H. apply AtomSetImpl.add_2. exact Hin.
Qed.

Lemma in_dom_add : forall (A:Type) (a:atom) (p:A) (E:list (atom*A)) z,
  z `in` dom E -> z `in` dom ((a,p)::E).
Proof. intros. simpl. apply AtomSetImpl.add_2. exact H. Qed.

Lemma dom_subst_ctx_mem : forall x y E b,
  b `in` dom (subst_ctx x y E) ->
  (b = y /\ x `in` dom E) \/ b `in` dom E.
Proof.
  intros x y E. induction E as [| [a p] E' IH]; intros b H.
  - simpl in H. apply empty_iff in H. destruct H.
  - rewrite subst_ctx_cons in H. simpl in H.
    destruct (eq_dec a x) as [Hax|Hax].
    + (* head atom is y *)
      destruct (eq_dec b y) as [Hby|Hby].
      * left. split; [exact Hby|].
        simpl. rewrite <- Hax. apply AtomSetImpl.add_1. reflexivity.
      * right.
        assert (Hin : b `in` dom (subst_ctx x y E')).
        { apply (AtomSetImpl.add_3 (s := dom (subst_ctx x y E')) (x := y) (y := b)).
          - intro Heq. apply Hby. symmetry. exact Heq.
          - exact H. }
        destruct (IH b Hin) as [[H1 _]|H2].
        -- exfalso. apply Hby. exact H1.
        -- apply in_dom_add with (a:=a) (p:=p). exact H2.
    + (* head atom is a *)
      destruct (eq_dec b a) as [Hba|Hba].
      * right. simpl. rewrite <- Hba. apply AtomSetImpl.add_1. reflexivity.
      * assert (Hin : b `in` dom (subst_ctx x y E')).
        { apply (AtomSetImpl.add_3 (s := dom (subst_ctx x y E')) (x := a) (y := b)).
          - intro Heq. apply Hba. symmetry. exact Heq.
          - exact H. }
        destruct (IH b Hin) as [[H1 H2]|H2].
        -- left. split; [exact H1 | apply in_dom_add with (a:=a) (p:=p); exact H2].
        -- right. apply in_dom_add with (a:=a) (p:=p). exact H2.
Qed.

Lemma uniq_subst_ctx : forall x y E, uniq E -> y `notin` dom E -> uniq (subst_ctx x y E).
Proof.
  intros x y E. induction E as [| [a p] E' IH]; intros Hu Hy.
  - simpl. apply uniq_nil.
  - rewrite subst_ctx_cons. apply uniq_cons_iff. split.
    + apply IH.
      * apply (uniq_cons_1 (typ*typ) a p E' Hu).
      * apply notin_add_s with (a:=a). exact Hy.
    + destruct (eq_dec a x) as [Hax|Hax].
      * (* head atom y *) intro Hin.
        pose proof (uniq_cons_2 (typ*typ) a p E' Hu) as Ha.
        destruct (dom_subst_ctx_mem x y E' y Hin) as [[H1 H2]|H2].
        -- rewrite <- Hax in H2. exact (Ha H2).
        -- apply Hy. apply in_dom_add with (a:=a) (p:=p). exact H2.
      * (* head atom a *) intro Hin.
        pose proof (uniq_cons_2 (typ*typ) a p E' Hu) as Ha.
        destruct (dom_subst_ctx_mem x y E' a Hin) as [[H1 H2]|H2].
        -- (* a = y *) exfalso. apply Hy. rewrite <- H1. simpl.
           apply AtomSetImpl.add_1. reflexivity.
        -- exact (Ha H2).
Qed.

Lemma castfv_open_var_f : forall c cy k x,
  x `in` castfv_castop (open_castop_wrt_castop_rec k (c_var_f cy) c) ->
  x = cy \/ x `in` castfv_castop c.
Proof.
  induction c as [n|cx| |A|A|c1 IH1 c2 IH2|c1 IH1 c2 IH2|c IHc];
  intros cy k x H.
  - (* c_var_b *)
    rewrite open_rec_var_b in H.
    destruct (lt_eq_lt_dec n k) as [[H1|H2]|H3]; simpl in H.
    + apply empty_iff in H. destruct H.
    + left. symmetry. apply AtomSetImpl.singleton_1. exact H.
    + apply empty_iff in H. destruct H.
  - (* c_var_f *) simpl in *. right. exact H.
  - (* c_id *) simpl in H. apply empty_iff in H. destruct H.
  - (* c_unfold *) simpl in H. apply empty_iff in H. destruct H.
  - (* c_fold *) simpl in H. apply empty_iff in H. destruct H.
  - (* c_arrow *)
    simpl in *. apply AtomSetImpl.union_1 in H. destruct H as [H|H].
    + destruct (IH1 cy k x H) as [Heq|Hin]; [left; exact Heq|right].
      apply AtomSetImpl.union_2. exact Hin.
    + destruct (IH2 cy k x H) as [Heq|Hin]; [left; exact Heq|right].
      apply AtomSetImpl.union_3. exact Hin.
  - (* c_seq *)
    simpl in *. apply AtomSetImpl.union_1 in H. destruct H as [H|H].
    + destruct (IH1 cy k x H) as [Heq|Hin]; [left; exact Heq|right].
      apply AtomSetImpl.union_2. exact Hin.
    + destruct (IH2 cy k x H) as [Heq|Hin]; [left; exact Heq|right].
      apply AtomSetImpl.union_3. exact Hin.
  - (* c_fixc *) simpl in *. apply IHc in H. exact H.
Qed.

Lemma notin_singleton_neq : forall z w, z `notin` singleton w -> w <> z.
Proof.
  intros z w H Heq. apply H. apply AtomSetImpl.singleton_2. exact Heq.
Qed.

Lemma subst_ctx_cons_not : forall x y a p E, a <> x ->
  subst_ctx x y ((a,p)::E) = ((a,p)::subst_ctx x y E).
Proof.
  intros. rewrite subst_ctx_cons.
  destruct (eq_dec a x) as [Heq|Hne]; [exfalso; exact (H Heq)|reflexivity].
Qed.

Lemma not_castfv_open : forall c cy y,
  y `notin` castfv_castop c -> y <> cy ->
  y `notin` castfv_castop (open_castop_wrt_castop c (c_var_f cy)).
Proof.
  intros c cy y Hc Hyc Hin.
  apply castfv_open_var_f in Hin.
  destruct Hin as [Heq|Hin].
  - apply Hyc. exact Heq.
  - exact (Hc Hin).
Qed.


Lemma open_castop_unfold : forall c v,
  open_castop_wrt_castop c v = open_castop_wrt_castop_rec 0 v c.
Proof. intros. reflexivity. Qed.

Lemma notin_dom_cons : forall (z a:atom) (p:typ*typ) E,
  z <> a -> z `notin` dom E -> z `notin` dom ((a,p)::E).
Proof.
  intros z a p E Hza Hz H. simpl in H.
  destruct (eq_dec z a) as [e|n].
  - exfalso. exact (Hza e).
  - apply Hz. apply (AtomSetImpl.add_3 (s:=dom E) (x:=a) (y:=z)).
    + intro h. apply n. symmetry. exact h.
    + exact H.
Qed.

Lemma TypCast_rename : forall D E A B c, TypCast D E A B c ->
  forall x y, y `notin` dom E -> y `notin` castfv_castop c ->
  TypCast D (subst_ctx x y E) A B (castsubst_castop (c_var_f y) x c).
Proof.
  intros D E A B c H.
  induction H as [D E A Hwf Huniq
                | D E A1 B1 A2 B2 c1 c2 H1 IH1 H2 IH2
                | D E A Hwf Huniq
                | D E A Hwf Huniq
                | D E A C c1 c2 B H1 IH1 H2 IH2
                | D E A B cx H1 H2 H3 H4
                | L D E A1 B1 A2 B2 c1 c2 H1 IH1 H2 IH2];
  intros x y HyE Hyc.
  - (* id *) simpl. apply TCast_id; auto. apply uniq_subst_ctx; auto.
  - (* arrow *)
    simpl. apply TCast_arrow.
    + apply IH1; auto.
      apply notin_union_1 with (s' := castfv_castop c2). exact Hyc.
    + apply IH2; auto.
      apply notin_union_2 with (s := castfv_castop c1). exact Hyc.
  - (* unfold *) simpl. apply TCast_unfold; auto. apply uniq_subst_ctx; auto.
  - (* fold *) simpl. apply TCast_fold; auto. apply uniq_subst_ctx; auto.
  - (* seq *)
    simpl. eapply TCast_seq.
    + apply IH1; auto.
      apply notin_union_1 with (s' := castfv_castop c2). exact Hyc.
    + apply IH2; auto.
      apply notin_union_2 with (s := castfv_castop c1). exact Hyc.
  - (* var *)
    destruct (eq_dec cx x) as [Heq|Hne].
    + subst cx.
      rewrite castsubst_var_same.
      apply TCast_var with (cx := y).
      * exact H1.
      * exact H2.
      * apply uniq_subst_ctx; auto.
      * exact (in_subst_ctx_same x y E (A,B) H4).
    + rewrite castsubst_var_diff with (a:=c_var_f y) (x:=x) (cx:=cx) by exact Hne.
      apply TCast_var with (cx := cx).
      * exact H1.
      * exact H2.
      * apply uniq_subst_ctx; auto.
      * exact (in_subst_ctx_diff x y E cx (A,B) Hne H4).
  - (* fix *)
    simpl in Hyc.
    assert (Hy1 : y `notin` castfv_castop c1)
      by (apply notin_union_1 with (s' := castfv_castop c2); exact Hyc).
    assert (Hy2 : y `notin` castfv_castop c2)
      by (apply notin_union_2 with (s := castfv_castop c1); exact Hyc).
    simpl.
    apply TCast_fix with (L := L \u (singleton x \u singleton y)).
    + intros cy Hf.
      assert (HcyL : cy \notin L)
        by (apply notin_union_1 with (s' := singleton x \u singleton y); exact Hf).
      assert (Hcs : cy \notin (singleton x \u singleton y))
        by (apply notin_union_2 with (s := L); exact Hf).
      assert (Hcyx : x <> cy)
        by (apply notin_singleton_neq; apply notin_union_1 with (s':=singleton y); exact Hcs).
      assert (Hcyy : y <> cy)
        by (apply notin_singleton_neq; apply notin_union_2 with (s:=singleton x); exact Hcs).
      assert (Hydom : y \notin dom ((cy, (t_arrow A1 B1, t_arrow A2 B2)) :: E))
        by (apply notin_dom_cons; auto).
      assert (Hyopen : y \notin castfv_castop (open_castop_wrt_castop c1 (c_var_f cy))).
      { apply not_castfv_open; auto. }
      pose proof (IH1 cy HcyL x y Hydom Hyopen) as R1.
      rewrite subst_ctx_cons_not in R1
        by (intro he; apply Hcyx; symmetry; exact he).
      rewrite open_castop_unfold in R1.
      rewrite castsubst_open in R1.
      2: { simpl. exact I. }
      2: { exact Hcyx. }
      exact R1.
    + intros cy Hf.
      assert (HcyL : cy \notin L)
        by (apply notin_union_1 with (s' := singleton x \u singleton y); exact Hf).
      assert (Hcs : cy \notin (singleton x \u singleton y))
        by (apply notin_union_2 with (s := L); exact Hf).
      assert (Hcyx : x <> cy)
        by (apply notin_singleton_neq; apply notin_union_1 with (s':=singleton y); exact Hcs).
      assert (Hcyy : y <> cy)
        by (apply notin_singleton_neq; apply notin_union_2 with (s:=singleton x); exact Hcs).
      assert (Hydom : y \notin dom ((cy, (t_arrow A1 B1, t_arrow A2 B2)) :: E))
        by (apply notin_dom_cons; auto).
      assert (Hyopen : y \notin castfv_castop (open_castop_wrt_castop c2 (c_var_f cy))).
      { apply not_castfv_open; auto. }
      pose proof (IH2 cy HcyL x y Hydom Hyopen) as R2.
      rewrite subst_ctx_cons_not in R2
        by (intro he; apply Hcyx; symmetry; exact he).
      rewrite open_castop_unfold in R2.
      rewrite castsubst_open in R2.
      2: { simpl. exact I. }
      2: { exact Hcyx. }
      exact R2.
Qed.

(* ============================================================ *)
(* Substitution of a context variable by an actual cast         *)
(* ============================================================ *)

Lemma in_dom_iff : forall (E:cctx) z, z `in` dom E <-> exists p, In (z,p) E.
Proof.
  intros E. induction E as [| [a q] E' IH]; intro z.
  - simpl. split.
    + intro H. apply empty_iff in H. destruct H.
    + intros [p H]. inversion H.
  - simpl. split.
    + intro H. destruct (eq_dec z a) as [Heq|Hne].
      * subst. exists q. left. reflexivity.
      * apply (AtomSetImpl.add_3 (s:=dom E') (x:=a) (y:=z)) in H.
        -- apply IH in H. destruct H as [p Hp]. exists p. right. exact Hp.
        -- intro he. apply Hne. symmetry. exact he.
    + intros [p H]. simpl in H. destruct H as [Heq|H].
      * injection Heq as Hz Hp. subst. apply AtomSetImpl.add_1. reflexivity.
      * apply AtomSetImpl.add_2. apply IH. exists p. exact H.
Qed.

Lemma uniq_in_eq : forall (E:cctx) x p q,
  uniq E -> In (x,p) E -> In (x,q) E -> p = q.
Proof.
  intros E. induction E as [| [a r] E' IH]; intros x p q Hu H1 H2.
  - inversion H1.
  - apply uniq_cons_iff in Hu. destruct Hu as [Hu Ha].
    simpl in H1, H2. destruct H1 as [Heq1|H1]; destruct H2 as [Heq2|H2].
    + injection Heq1 as _ Hp. injection Heq2 as _ Hq. subst. reflexivity.
    + injection Heq1 as Hx Hp. subst x p.
      exfalso. apply Ha. apply in_dom_iff. exists q. exact H2.
    + injection Heq2 as Hx Hq. subst x q.
      exfalso. apply Ha. apply in_dom_iff. exists p. exact H1.
    + apply (IH x p q); auto.
Qed.

Lemma in_app_cons_split : forall (E1 E2:cctx) x A B cx p,
  In (cx,p) (E1 ++ (x,(A,B))::E2) ->
  (cx = x /\ p = (A,B)) \/ In (cx,p) (E1++E2).
Proof.
  intros E1 E2 x A B cx p H.
  apply List.in_app_iff in H. destruct H as [H|H].
  - right. apply List.in_app_iff. left. exact H.
  - simpl in H. destruct H as [Heq|H].
    + left. injection Heq as Hcx Hp. split; symmetry; assumption.
    + right. apply List.in_app_iff. right. exact H.
Qed.

Lemma uniq_remove_mid : forall (E1 E2:cctx) x A B,
  uniq (E1 ++ (x,(A,B))::E2) -> uniq (E1++E2).
Proof.
  intros E1. induction E1 as [| [a p] E1' IH]; intros E2 x A B H.
  - simpl in *. apply (uniq_cons_1 (typ*typ) x (A,B) E2 H).
  - simpl in H. apply uniq_cons_iff in H. destruct H as [Hu Ha].
    simpl. apply (uniq_cons_3 (typ*typ) a p (E1'++E2)).
    + exact (IH E2 x A B Hu).
    + intro Hin. apply Ha. apply in_dom_iff in Hin. destruct Hin as [q Hq].
      apply in_dom_iff. exists q.
      apply List.in_app_iff in Hq. destruct Hq as [Hq|Hq].
      * apply List.in_app_iff. left. exact Hq.
      * apply List.in_app_iff. right. simpl. right. exact Hq.
Qed.

Lemma notin_dom_dist : forall (E1 E2:cctx) x A B z,
  z `notin` dom (E1++E2) -> z <> x -> z `notin` dom (E1++(x,(A,B))::E2).
Proof.
  intros E1 E2 x A B z Hd Hzx Hin.
  apply in_dom_iff in Hin. destruct Hin as [p Hp].
  apply in_app_cons_split in Hp. destruct Hp as [[Heq _]|Hp].
  - exfalso. exact (Hzx Heq).
  - apply Hd. apply in_dom_iff. exists p. exact Hp.
Qed.

Lemma TypCast_subst_gen : forall D E P Q c,
  TypCast D E P Q c ->
  forall E1 x A B E2, E = E1 ++ (x,(A,B))::E2 ->
  uniq (E1 ++ (x,(A,B))::E2) ->
  forall c0, TypCast D (E1++E2) A B c0 ->
  TypCast D (E1++E2) P Q (castsubst_castop c0 x c).
Proof.
  intros D E P Q c H.
  induction H as [D E P0 Hwf Huniq
                | D E P1 Q1 P2 Q2 c1 c2 H1 IH1 H2 IH2
                | D E T Hwf Huniq
                | D E T Hwf Huniq
                | D E P0 R c1 c2 Q0 H1 IH1 H2 IH2
                | D E P0 Q0 cx H1 H2 H3 H4
                | L D E A1 B1 A2 B2 c1 c2 H1 IH1 H2 IH2];
  intros E1 x A B E2 HE Hu c0 Hc0; subst E.
  - (* id *)
    simpl. apply TCast_id; auto.
    apply uniq_remove_mid with (x:=x) (A:=A) (B:=B). exact Hu.
  - (* arrow *)
    simpl. apply TCast_arrow.
    + apply (IH1 E1 x A B E2); auto.
    + apply (IH2 E1 x A B E2); auto.
  - (* unfold *)
    simpl. apply TCast_unfold; auto.
    apply uniq_remove_mid with (x:=x) (A:=A) (B:=B). exact Hu.
  - (* fold *)
    simpl. apply TCast_fold; auto.
    apply uniq_remove_mid with (x:=x) (A:=A) (B:=B). exact Hu.
  - (* seq *)
    simpl. eapply TCast_seq.
    + apply (IH1 E1 x A B E2); auto.
    + apply (IH2 E1 x A B E2); auto.
  - (* var *)
    destruct (in_app_cons_split E1 E2 x A B cx (P0,Q0) H4) as [[Hcx Hp]|Hin].
    + subst cx. injection Hp as HP HQ. subst.
      rewrite castsubst_var_same. exact Hc0.
    + destruct (eq_dec cx x) as [Hcx|Hcx].
      * subst cx.
        assert (Hpq : (P0,Q0) = (A,B)).
        { apply (uniq_in_eq (E1++(x,(A,B))::E2) x (P0,Q0) (A,B) Hu).
          - exact H4.
          - apply List.in_app_iff. right. left. reflexivity. }
        injection Hpq as HP HQ. subst.
        rewrite castsubst_var_same. exact Hc0.
      * rewrite castsubst_var_diff with (a:=c0) (x:=x) (cx:=cx) by exact Hcx.
        eapply TCast_var.
        -- exact H1.
        -- exact H2.
        -- apply uniq_remove_mid with (x:=x) (A:=A) (B:=B). exact Hu.
        -- exact Hin.
  - (* fix *)
    simpl in *.
    assert (Huniq0 : uniq (E1++E2)).
    { apply uniq_remove_mid with (x:=x) (A:=A) (B:=B). exact Hu. }
    apply TCast_fix with (L := L \u (singleton x \u dom (E1++E2))).
    + intros cy Hf.
      assert (HcyL : cy \notin L)
        by (apply notin_union_1 with (s' := singleton x \u dom (E1++E2)); exact Hf).
      assert (Hcs : cy \notin (singleton x \u dom (E1++E2)))
        by (apply notin_union_2 with (s := L); exact Hf).
      assert (Hcyx : x <> cy)
        by (apply notin_singleton_neq; apply notin_union_1 with (s':=dom (E1++E2)); exact Hcs).
      assert (Hcyd : cy \notin dom (E1++E2))
        by (apply notin_union_2 with (s:=singleton x); exact Hcs).
      assert (HuP : uniq ((cy, (t_arrow A1 B1, t_arrow A2 B2)) :: (E1++(x,(A,B))::E2))).
      { apply (uniq_cons_3 (typ*typ) cy (t_arrow A1 B1, t_arrow A2 B2) (E1++(x,(A,B))::E2)).
        - exact Hu.
        - exact (notin_dom_dist E1 E2 x A B cy Hcyd (fun he => Hcyx (eq_sym he))). }
      assert (Hc0w : TypCast D ((cy, (t_arrow A1 B1, t_arrow A2 B2)) :: (E1++E2)) A B c0).
      { apply (TypCast_weaken D (E1++E2) A B c0 Hc0
                 ((cy, (t_arrow A1 B1, t_arrow A2 B2)) :: (E1++E2))).
        - apply (uniq_cons_3 (typ*typ) cy (t_arrow A1 B1, t_arrow A2 B2) (E1++E2)).
          + exact Huniq0.
          + exact Hcyd.
        - intros z p Hz. right. exact Hz. }
      pose proof (IH1 cy HcyL ((cy, (t_arrow A1 B1, t_arrow A2 B2))::E1)
                    x A B E2 eq_refl HuP c0 Hc0w) as R1.
      rewrite open_castop_unfold in R1.
      rewrite (castsubst_open c1 c0 x cy 0 (TypCast_lc_b D (E1++E2) A B c0 Hc0) Hcyx) in R1.
      exact R1.
    + intros cy Hf.
      assert (HcyL : cy \notin L)
        by (apply notin_union_1 with (s' := singleton x \u dom (E1++E2)); exact Hf).
      assert (Hcs : cy \notin (singleton x \u dom (E1++E2)))
        by (apply notin_union_2 with (s := L); exact Hf).
      assert (Hcyx : x <> cy)
        by (apply notin_singleton_neq; apply notin_union_1 with (s':=dom (E1++E2)); exact Hcs).
      assert (Hcyd : cy \notin dom (E1++E2))
        by (apply notin_union_2 with (s:=singleton x); exact Hcs).
      assert (HuP : uniq ((cy, (t_arrow A1 B1, t_arrow A2 B2)) :: (E1++(x,(A,B))::E2))).
      { apply (uniq_cons_3 (typ*typ) cy (t_arrow A1 B1, t_arrow A2 B2) (E1++(x,(A,B))::E2)).
        - exact Hu.
        - exact (notin_dom_dist E1 E2 x A B cy Hcyd (fun he => Hcyx (eq_sym he))). }
      assert (Hc0w : TypCast D ((cy, (t_arrow A1 B1, t_arrow A2 B2)) :: (E1++E2)) A B c0).
      { apply (TypCast_weaken D (E1++E2) A B c0 Hc0
                 ((cy, (t_arrow A1 B1, t_arrow A2 B2)) :: (E1++E2))).
        - apply (uniq_cons_3 (typ*typ) cy (t_arrow A1 B1, t_arrow A2 B2) (E1++E2)).
          + exact Huniq0.
          + exact Hcyd.
        - intros z p Hz. right. exact Hz. }
      pose proof (IH2 cy HcyL ((cy, (t_arrow A1 B1, t_arrow A2 B2))::E1)
                    x A B E2 eq_refl HuP c0 Hc0w) as R2.
      rewrite open_castop_unfold in R2.
      rewrite (castsubst_open c2 c0 x cy 0 (TypCast_lc_b D (E1++E2) A B c0 Hc0) Hcyx) in R2.
      exact R2.
Qed.

(* ============================================================ *)
(* Auxiliaries for the completeness proof                       *)
(* ============================================================ *)

Lemma subst_ctx_fresh : forall (x y:atom) (E:cctx),
  x `notin` dom E -> subst_ctx x y E = E.
Proof.
  intros x y E. induction E as [| [a p] E' IH]; intro Hx.
  - reflexivity.
  - rewrite subst_ctx_cons.
    destruct (eq_dec a x) as [e|n].
    + exfalso. apply Hx. subst a. simpl. apply AtomSetImpl.add_1. reflexivity.
    + f_equal. apply IH. apply notin_add_s with (a:=a). exact Hx.
Qed.

Lemma fresh_elements_notin : forall (s:atoms), fresh (AtomSetImpl.elements s) `notin` s.
Proof.
  intros s H. apply AtomSetImpl.elements_1 in H.
  apply InA_iff_In in H.
  exact (fresh_not_in (AtomSetImpl.elements s) H).
Qed.

Lemma fresh_cons_elements_notin : forall (a:atom) (s:atoms),
  fresh (a :: AtomSetImpl.elements s) `notin` s.
Proof.
  intros a s H. apply AtomSetImpl.elements_1 in H.
  apply InA_iff_In in H.
  apply (fresh_not_in (a :: AtomSetImpl.elements s)).
  simpl. right. exact H.
Qed.

Lemma fresh_cons_neq : forall (a:atom) (l:list atom), a <> fresh (a :: l).
Proof.
  intros a l he. apply (fresh_not_in (a :: l)).
  rewrite <- he. left. reflexivity.
Qed.

Lemma uniq_cons2 : forall (a:atom) (P:typ*typ) (b:atom) (Q:typ*typ) (E:cctx),
  uniq E -> a `notin` dom E -> b `notin` dom E -> a <> b ->
  uniq ((a,P)::(b,Q)::E).
Proof.
  intros a P b Q E Hu Ha Hb Hab.
  apply (uniq_cons_3 (typ*typ) a P ((b,Q)::E)).
  - apply (uniq_cons_3 (typ*typ) b Q E).
    + exact Hu.
    + exact Hb.
  - apply (notin_dom_cons a b Q E).
    + exact Hab.
    + exact Ha.
Qed.

Lemma realizes_cons2 : forall (P0 Q0:typ*typ) H E a b,
  realizes H E -> P0 = flip_pair Q0 ->
  a `notin` dom E -> b `notin` dom E -> a <> b ->
  realizes (P0::H) ((a,P0)::(b,Q0)::E).
Proof.
  intros P0 Q0 H E a b [Hu Hcov] Hflip Ha Hb Hab. split.
  - apply uniq_cons2; auto.
  - intros p [Hp|Hp].
    + subst p. split.
      * exists a. left. reflexivity.
      * exists b. right. left. rewrite Hflip. rewrite flip_pair_invol. reflexivity.
    + destruct (Hcov p Hp) as [[x Hx] [y Hy]]. split.
      * exists x. right. right. exact Hx.
      * exists y. right. right. exact Hy.
Qed.

Lemma realizes_cons_swap : forall (P0 Q0:typ*typ) H E a b,
  realizes H E -> P0 = flip_pair Q0 ->
  a `notin` dom E -> b `notin` dom E -> a <> b ->
  realizes (P0::H) ((b,Q0)::(a,P0)::E).
Proof.
  intros P0 Q0 H E a b [Hu Hcov] Hflip Ha Hb Hab. split.
  - apply (uniq_cons2 b Q0 a P0 E).
    + exact Hu.
    + exact Hb.
    + exact Ha.
    + intro he. apply Hab. symmetry. exact he.
  - intros p [Hp|Hp].
    + subst p. split.
      * exists a. right. left. reflexivity.
      * exists b. left. rewrite Hflip. rewrite flip_pair_invol. reflexivity.
    + destruct (Hcov p Hp) as [[x Hx] [y Hy]]. split.
      * exists x. right. right. exact Hx.
      * exists y. right. right. exact Hy.
Qed.

(* ============================================================ *)
(* Completeness: every equivalence has a cast, both directions  *)
(* ============================================================ *)

Lemma eqe2_complete_both : forall D H A B,
  eqe2 D H A B ->
  forall E, realizes H E ->
  (exists c, TypCast D E A B c) /\ (exists c, TypCast D E B A c).
Proof.
  intros D H A B Hd.
  induction Hd as [D H A B Hin HwfA HwfB
                | D H A Hwf
                | D H A C B H1 IH1 H2 IH2
                | D H B A H1 IH1
                | D H A Hwf
                | D H A1 A2 B1 B2 H1 IH1 H2 IH2];
  intros E [Hu Hcov].
  - (* assump *)
    destruct (Hcov (A,B) Hin) as [[x Hx] [y Hy]]. split.
    + exists (c_var_f x). apply TCast_var with (cx:=x); auto.
    + exists (c_var_f y). apply TCast_var with (cx:=y); auto.
  - (* refl *)
    split.
    + exists c_id. apply TCast_id; auto.
    + exists c_id. apply TCast_id; auto.
  - (* trans *)
    destruct (IH1 E (conj Hu Hcov)) as [[c1 Hc1] [d1 Hd1]].
    destruct (IH2 E (conj Hu Hcov)) as [[c2 Hc2] [d2 Hd2]].
    split.
    + exists (c_seq c1 c2). eapply TCast_seq; eauto.
    + exists (c_seq d2 d1). eapply TCast_seq; eauto.
  - (* symm *)
    destruct (IH1 E (conj Hu Hcov)) as [[c Hc] [d Hd]]. split.
    + exists d. exact Hd.
    + exists c. exact Hc.
  - (* fld *)
    split.
    + exists (c_unfold (t_mu A)). apply TCast_unfold; auto.
    + exists (c_fold (t_mu A)). apply TCast_fold; auto.
  - (* arrfix *)
    pose (a := fresh (AtomSetImpl.elements (dom E))).
    pose (b := fresh (a :: AtomSetImpl.elements (dom E))).
    assert (Ha : a `notin` dom E) by (apply fresh_elements_notin).
    assert (Hb : b `notin` dom E) by (apply fresh_cons_elements_notin).
    assert (Hab : a <> b) by (apply fresh_cons_neq).
    set (P0 := (t_arrow A1 A2, t_arrow B1 B2)).
    set (Q0 := (t_arrow B1 B2, t_arrow A1 A2)).
    assert (HflipPQ : P0 = flip_pair Q0) by (unfold P0, Q0; reflexivity).
    assert (HflipQP : Q0 = flip_pair P0) by (unfold P0, Q0; reflexivity).
    assert (HRP : realizes (P0::H) ((a,P0)::(b,Q0)::E)).
    { apply (realizes_cons2 P0 Q0 H E a b).
      - split; assumption.
      - exact HflipPQ.
      - exact Ha.
      - exact Hb.
      - exact Hab. }
    assert (HRQ : realizes (P0::H) ((b,Q0)::(a,P0)::E)).
    { apply (realizes_cons_swap P0 Q0 H E a b).
      - split; assumption.
      - exact HflipPQ.
      - exact Ha.
      - exact Hb.
      - exact Hab. }
    destruct (IH1 ((a,P0)::(b,Q0)::E) HRP) as [[F1 HF1] [G1 HG1]].
    destruct (IH2 ((a,P0)::(b,Q0)::E) HRP) as [[F2 HF2] [G2 HG2]].
    destruct (IH1 ((b,Q0)::(a,P0)::E) HRQ) as [[F1q HF1q] [G1q HG1q]].
    destruct (IH2 ((b,Q0)::(a,P0)::E) HRQ) as [[F2q HF2q] [G2q HG2q]].
    (* -------- forward direction -------- *)
    set (flipP := c_fixc (c_arrow (close_castop_wrt_castop b G1q)
                                  (close_castop_wrt_castop b G2q))).
    assert (HflipP : TypCast D ((a,P0)::E) (t_arrow B1 B2) (t_arrow A1 A2) flipP).
    { apply TCast_fix with
        (L := dom E \u (singleton a \u (singleton b \u
                 (castfv_castop G1q \u castfv_castop G2q)))).
      + intros cz Hf.
        assert (HzL : cz \notin dom E)
          by (apply notin_union_1 with (s' := singleton a \u (singleton b \u
                    (castfv_castop G1q \u castfv_castop G2q))); exact Hf).
        assert (Hcs : cz \notin (singleton a \u (singleton b \u
                    (castfv_castop G1q \u castfv_castop G2q))))
          by (apply notin_union_2 with (s := dom E); exact Hf).
        assert (Hza : a <> cz)
          by (apply notin_singleton_neq; apply notin_union_1 with
                (s' := singleton b \u (castfv_castop G1q \u castfv_castop G2q)); exact Hcs).
        assert (Hcs2 : cz \notin (singleton b \u (castfv_castop G1q \u castfv_castop G2q)))
          by (apply notin_union_2 with (s := singleton a); exact Hcs).
        assert (Hzb : b <> cz)
          by (apply notin_singleton_neq; apply notin_union_1 with
                (s' := castfv_castop G1q \u castfv_castop G2q); exact Hcs2).
        assert (Hcs3 : cz \notin (castfv_castop G1q \u castfv_castop G2q))
          by (apply notin_union_2 with (s := singleton b); exact Hcs2).
        assert (Hzf1 : cz \notin castfv_castop G1q)
          by (apply notin_union_1 with (s' := castfv_castop G2q); exact Hcs3).
        assert (Hzf2 : cz \notin castfv_castop G2q)
          by (apply notin_union_2 with (s := castfv_castop G1q); exact Hcs3).
        assert (Hzdom : cz `notin` dom ((b,Q0)::(a,P0)::E)).
        { apply (notin_dom_cons cz b Q0 ((a,P0)::E)).
          - intro he. apply Hzb. symmetry. exact he.
          - apply (notin_dom_cons cz a P0 E).
            + intro he. apply Hza. symmetry. exact he.
            + exact HzL. }
        pose proof (TypCast_rename D ((b,Q0)::(a,P0)::E) B1 A1 G1q HG1q
                      b cz Hzdom Hzf1) as R1.
        rewrite subst_ctx_cons_same in R1.
        rewrite subst_ctx_cons_not in R1 by exact Hab.
        rewrite (subst_ctx_fresh b cz E Hb) in R1.
        rewrite <- (open_close_rename G1q 0 b cz) in R1.
        exact R1.
      + intros cz Hf.
        assert (HzL : cz \notin dom E)
          by (apply notin_union_1 with (s' := singleton a \u (singleton b \u
                    (castfv_castop G1q \u castfv_castop G2q))); exact Hf).
        assert (Hcs : cz \notin (singleton a \u (singleton b \u
                    (castfv_castop G1q \u castfv_castop G2q))))
          by (apply notin_union_2 with (s := dom E); exact Hf).
        assert (Hza : a <> cz)
          by (apply notin_singleton_neq; apply notin_union_1 with
                (s' := singleton b \u (castfv_castop G1q \u castfv_castop G2q)); exact Hcs).
        assert (Hcs2 : cz \notin (singleton b \u (castfv_castop G1q \u castfv_castop G2q)))
          by (apply notin_union_2 with (s := singleton a); exact Hcs).
        assert (Hzb : b <> cz)
          by (apply notin_singleton_neq; apply notin_union_1 with
                (s' := castfv_castop G1q \u castfv_castop G2q); exact Hcs2).
        assert (Hcs3 : cz \notin (castfv_castop G1q \u castfv_castop G2q))
          by (apply notin_union_2 with (s := singleton b); exact Hcs2).
        assert (Hzf1 : cz \notin castfv_castop G1q)
          by (apply notin_union_1 with (s' := castfv_castop G2q); exact Hcs3).
        assert (Hzf2 : cz \notin castfv_castop G2q)
          by (apply notin_union_2 with (s := castfv_castop G1q); exact Hcs3).
        assert (Hzdom : cz `notin` dom ((b,Q0)::(a,P0)::E)).
        { apply (notin_dom_cons cz b Q0 ((a,P0)::E)).
          - intro he. apply Hzb. symmetry. exact he.
          - apply (notin_dom_cons cz a P0 E).
            + intro he. apply Hza. symmetry. exact he.
            + exact HzL. }
        pose proof (TypCast_rename D ((b,Q0)::(a,P0)::E) B2 A2 G2q HG2q
                      b cz Hzdom Hzf2) as R2.
        rewrite subst_ctx_cons_same in R2.
        rewrite subst_ctx_cons_not in R2 by exact Hab.
        rewrite (subst_ctx_fresh b cz E Hb) in R2.
        rewrite <- (open_close_rename G2q 0 b cz) in R2.
        exact R2. }
    assert (HF1' : TypCast D ((a,P0)::E) A1 B1
              (castsubst_castop flipP b F1)).
    { exact (TypCast_subst_gen D ((a,P0)::(b,Q0)::E) A1 B1 F1 HF1
               ((a,P0)::nil) b (fst Q0) (snd Q0) E eq_refl (proj1 HRP)
               flipP HflipP). }
    assert (HF2' : TypCast D ((a,P0)::E) A2 B2
              (castsubst_castop flipP b F2)).
    { exact (TypCast_subst_gen D ((a,P0)::(b,Q0)::E) A2 B2 F2 HF2
               ((a,P0)::nil) b (fst Q0) (snd Q0) E eq_refl (proj1 HRP)
               flipP HflipP). }
    (* -------- backward direction -------- *)
    set (fwdP := c_fixc (c_arrow (close_castop_wrt_castop a F1)
                                  (close_castop_wrt_castop a F2))).
    assert (HfwdP : TypCast D ((b,Q0)::E) (t_arrow A1 A2) (t_arrow B1 B2) fwdP).
    { apply TCast_fix with
        (L := dom E \u (singleton b \u (singleton a \u
                 (castfv_castop F1 \u castfv_castop F2)))).
      + intros cz Hf.
        assert (HzL : cz \notin dom E)
          by (apply notin_union_1 with (s' := singleton b \u (singleton a \u
                    (castfv_castop F1 \u castfv_castop F2))); exact Hf).
        assert (Hcs : cz \notin (singleton b \u (singleton a \u
                    (castfv_castop F1 \u castfv_castop F2))))
          by (apply notin_union_2 with (s := dom E); exact Hf).
        assert (Hzb : b <> cz)
          by (apply notin_singleton_neq; apply notin_union_1 with
                (s' := singleton a \u (castfv_castop F1 \u castfv_castop F2)); exact Hcs).
        assert (Hcs2 : cz \notin (singleton a \u (castfv_castop F1 \u castfv_castop F2)))
          by (apply notin_union_2 with (s := singleton b); exact Hcs).
        assert (Hza : a <> cz)
          by (apply notin_singleton_neq; apply notin_union_1 with
                (s' := castfv_castop F1 \u castfv_castop F2); exact Hcs2).
        assert (Hcs3 : cz \notin (castfv_castop F1 \u castfv_castop F2))
          by (apply notin_union_2 with (s := singleton a); exact Hcs2).
        assert (Hzf1 : cz \notin castfv_castop F1)
          by (apply notin_union_1 with (s' := castfv_castop F2); exact Hcs3).
        assert (Hzf2 : cz \notin castfv_castop F2)
          by (apply notin_union_2 with (s := castfv_castop F1); exact Hcs3).
        assert (Hzdom : cz `notin` dom ((a,P0)::(b,Q0)::E)).
        { apply (notin_dom_cons cz a P0 ((b,Q0)::E)).
          - intro he. apply Hza. symmetry. exact he.
          - apply (notin_dom_cons cz b Q0 E).
            + intro he. apply Hzb. symmetry. exact he.
            + exact HzL. }
        pose proof (TypCast_rename D ((a,P0)::(b,Q0)::E) A1 B1 F1 HF1
                      a cz Hzdom Hzf1) as R1.
        rewrite subst_ctx_cons_same in R1.
        rewrite subst_ctx_cons_not in R1
          by (intro he; apply Hab; symmetry; exact he).
        rewrite (subst_ctx_fresh a cz E Ha) in R1.
        rewrite <- (open_close_rename F1 0 a cz) in R1.
        exact R1.
      + intros cz Hf.
        assert (HzL : cz \notin dom E)
          by (apply notin_union_1 with (s' := singleton b \u (singleton a \u
                    (castfv_castop F1 \u castfv_castop F2))); exact Hf).
        assert (Hcs : cz \notin (singleton b \u (singleton a \u
                    (castfv_castop F1 \u castfv_castop F2))))
          by (apply notin_union_2 with (s := dom E); exact Hf).
        assert (Hzb : b <> cz)
          by (apply notin_singleton_neq; apply notin_union_1 with
                (s' := singleton a \u (castfv_castop F1 \u castfv_castop F2)); exact Hcs).
        assert (Hcs2 : cz \notin (singleton a \u (castfv_castop F1 \u castfv_castop F2)))
          by (apply notin_union_2 with (s := singleton b); exact Hcs).
        assert (Hza : a <> cz)
          by (apply notin_singleton_neq; apply notin_union_1 with
                (s' := castfv_castop F1 \u castfv_castop F2); exact Hcs2).
        assert (Hcs3 : cz \notin (castfv_castop F1 \u castfv_castop F2))
          by (apply notin_union_2 with (s := singleton a); exact Hcs2).
        assert (Hzf1 : cz \notin castfv_castop F1)
          by (apply notin_union_1 with (s' := castfv_castop F2); exact Hcs3).
        assert (Hzf2 : cz \notin castfv_castop F2)
          by (apply notin_union_2 with (s := castfv_castop F1); exact Hcs3).
        assert (Hzdom : cz `notin` dom ((a,P0)::(b,Q0)::E)).
        { apply (notin_dom_cons cz a P0 ((b,Q0)::E)).
          - intro he. apply Hza. symmetry. exact he.
          - apply (notin_dom_cons cz b Q0 E).
            + intro he. apply Hzb. symmetry. exact he.
            + exact HzL. }
        pose proof (TypCast_rename D ((a,P0)::(b,Q0)::E) A2 B2 F2 HF2
                      a cz Hzdom Hzf2) as R2.
        rewrite subst_ctx_cons_same in R2.
        rewrite subst_ctx_cons_not in R2
          by (intro he; apply Hab; symmetry; exact he).
        rewrite (subst_ctx_fresh a cz E Ha) in R2.
        rewrite <- (open_close_rename F2 0 a cz) in R2.
        exact R2. }
    assert (HG1' : TypCast D ((b,Q0)::E) B1 A1
              (castsubst_castop fwdP a G1)).
    { exact (TypCast_subst_gen D ((a,P0)::(b,Q0)::E) B1 A1 G1 HG1
               nil a (fst P0) (snd P0) ((b,Q0)::E) eq_refl (proj1 HRP)
               fwdP HfwdP). }
    assert (HG2' : TypCast D ((b,Q0)::E) B2 A2
              (castsubst_castop fwdP a G2)).
    { exact (TypCast_subst_gen D ((a,P0)::(b,Q0)::E) B2 A2 G2 HG2
               nil a (fst P0) (snd P0) ((b,Q0)::E) eq_refl (proj1 HRP)
               fwdP HfwdP). }
    (* -------- assemble -------- *)
    split.
    + (* forward: A1->A2 to B1->B2 *)
      exists (c_fixc (c_arrow (close_castop_wrt_castop a (castsubst_castop flipP b F1))
                              (close_castop_wrt_castop a (castsubst_castop flipP b F2)))).
      apply TCast_fix with
        (L := dom E \u (singleton a \u
                 (castfv_castop (castsubst_castop flipP b F1) \u
                  castfv_castop (castsubst_castop flipP b F2)))).
      * intros cz Hf.
        assert (HzL : cz \notin dom E)
          by (apply notin_union_1 with (s' := singleton a \u
                    (castfv_castop (castsubst_castop flipP b F1) \u
                     castfv_castop (castsubst_castop flipP b F2))); exact Hf).
        assert (Hcs : cz \notin (singleton a \u
                    (castfv_castop (castsubst_castop flipP b F1) \u
                     castfv_castop (castsubst_castop flipP b F2))))
          by (apply notin_union_2 with (s := dom E); exact Hf).
        assert (Hza : a <> cz)
          by (apply notin_singleton_neq; apply notin_union_1 with
                (s' := castfv_castop (castsubst_castop flipP b F1) \u
                       castfv_castop (castsubst_castop flipP b F2)); exact Hcs).
        assert (Hcs2 : cz \notin (castfv_castop (castsubst_castop flipP b F1) \u
                       castfv_castop (castsubst_castop flipP b F2)))
          by (apply notin_union_2 with (s := singleton a); exact Hcs).
        assert (Hzf1 : cz \notin castfv_castop (castsubst_castop flipP b F1))
          by (apply notin_union_1 with (s' := castfv_castop (castsubst_castop flipP b F2)); exact Hcs2).
        assert (Hzf2 : cz \notin castfv_castop (castsubst_castop flipP b F2))
          by (apply notin_union_2 with (s := castfv_castop (castsubst_castop flipP b F1)); exact Hcs2).
        assert (Hzdom : cz `notin` dom ((a,P0)::E)).
        { apply (notin_dom_cons cz a P0 E).
          - intro he. apply Hza. symmetry. exact he.
          - exact HzL. }
        pose proof (TypCast_rename D ((a,P0)::E) A1 B1
                      (castsubst_castop flipP b F1) HF1' a cz Hzdom Hzf1) as R.
        rewrite subst_ctx_cons_same in R.
        rewrite (subst_ctx_fresh a cz E Ha) in R.
        rewrite <- (open_close_rename (castsubst_castop flipP b F1) 0 a cz) in R.
        exact R.
      * intros cz Hf.
        assert (HzL : cz \notin dom E)
          by (apply notin_union_1 with (s' := singleton a \u
                    (castfv_castop (castsubst_castop flipP b F1) \u
                     castfv_castop (castsubst_castop flipP b F2))); exact Hf).
        assert (Hcs : cz \notin (singleton a \u
                    (castfv_castop (castsubst_castop flipP b F1) \u
                     castfv_castop (castsubst_castop flipP b F2))))
          by (apply notin_union_2 with (s := dom E); exact Hf).
        assert (Hza : a <> cz)
          by (apply notin_singleton_neq; apply notin_union_1 with
                (s' := castfv_castop (castsubst_castop flipP b F1) \u
                       castfv_castop (castsubst_castop flipP b F2)); exact Hcs).
        assert (Hcs2 : cz \notin (castfv_castop (castsubst_castop flipP b F1) \u
                       castfv_castop (castsubst_castop flipP b F2)))
          by (apply notin_union_2 with (s := singleton a); exact Hcs).
        assert (Hzf1 : cz \notin castfv_castop (castsubst_castop flipP b F1))
          by (apply notin_union_1 with (s' := castfv_castop (castsubst_castop flipP b F2)); exact Hcs2).
        assert (Hzf2 : cz \notin castfv_castop (castsubst_castop flipP b F2))
          by (apply notin_union_2 with (s := castfv_castop (castsubst_castop flipP b F1)); exact Hcs2).
        assert (Hzdom : cz `notin` dom ((a,P0)::E)).
        { apply (notin_dom_cons cz a P0 E).
          - intro he. apply Hza. symmetry. exact he.
          - exact HzL. }
        pose proof (TypCast_rename D ((a,P0)::E) A2 B2
                      (castsubst_castop flipP b F2) HF2' a cz Hzdom Hzf2) as R.
        rewrite subst_ctx_cons_same in R.
        rewrite (subst_ctx_fresh a cz E Ha) in R.
        rewrite <- (open_close_rename (castsubst_castop flipP b F2) 0 a cz) in R.
        exact R.
    + (* backward: B1->B2 to A1->A2 *)
      exists (c_fixc (c_arrow (close_castop_wrt_castop b (castsubst_castop fwdP a G1))
                              (close_castop_wrt_castop b (castsubst_castop fwdP a G2)))).
      apply TCast_fix with
        (L := dom E \u (singleton b \u
                 (castfv_castop (castsubst_castop fwdP a G1) \u
                  castfv_castop (castsubst_castop fwdP a G2)))).
      * intros cz Hf.
        assert (HzL : cz \notin dom E)
          by (apply notin_union_1 with (s' := singleton b \u
                    (castfv_castop (castsubst_castop fwdP a G1) \u
                     castfv_castop (castsubst_castop fwdP a G2))); exact Hf).
        assert (Hcs : cz \notin (singleton b \u
                    (castfv_castop (castsubst_castop fwdP a G1) \u
                     castfv_castop (castsubst_castop fwdP a G2))))
          by (apply notin_union_2 with (s := dom E); exact Hf).
        assert (Hzb : b <> cz)
          by (apply notin_singleton_neq; apply notin_union_1 with
                (s' := castfv_castop (castsubst_castop fwdP a G1) \u
                       castfv_castop (castsubst_castop fwdP a G2)); exact Hcs).
        assert (Hcs2 : cz \notin (castfv_castop (castsubst_castop fwdP a G1) \u
                       castfv_castop (castsubst_castop fwdP a G2)))
          by (apply notin_union_2 with (s := singleton b); exact Hcs).
        assert (Hzf1 : cz \notin castfv_castop (castsubst_castop fwdP a G1))
          by (apply notin_union_1 with (s' := castfv_castop (castsubst_castop fwdP a G2)); exact Hcs2).
        assert (Hzf2 : cz \notin castfv_castop (castsubst_castop fwdP a G2))
          by (apply notin_union_2 with (s := castfv_castop (castsubst_castop fwdP a G1)); exact Hcs2).
        assert (Hzdom : cz `notin` dom ((b,Q0)::E)).
        { apply (notin_dom_cons cz b Q0 E).
          - intro he. apply Hzb. symmetry. exact he.
          - exact HzL. }
        pose proof (TypCast_rename D ((b,Q0)::E) B1 A1
                      (castsubst_castop fwdP a G1) HG1' b cz Hzdom Hzf1) as R.
        rewrite subst_ctx_cons_same in R.
        rewrite (subst_ctx_fresh b cz E Hb) in R.
        rewrite <- (open_close_rename (castsubst_castop fwdP a G1) 0 b cz) in R.
        exact R.
      * intros cz Hf.
        assert (HzL : cz \notin dom E)
          by (apply notin_union_1 with (s' := singleton b \u
                    (castfv_castop (castsubst_castop fwdP a G1) \u
                     castfv_castop (castsubst_castop fwdP a G2))); exact Hf).
        assert (Hcs : cz \notin (singleton b \u
                    (castfv_castop (castsubst_castop fwdP a G1) \u
                     castfv_castop (castsubst_castop fwdP a G2))))
          by (apply notin_union_2 with (s := dom E); exact Hf).
        assert (Hzb : b <> cz)
          by (apply notin_singleton_neq; apply notin_union_1 with
                (s' := castfv_castop (castsubst_castop fwdP a G1) \u
                       castfv_castop (castsubst_castop fwdP a G2)); exact Hcs).
        assert (Hcs2 : cz \notin (castfv_castop (castsubst_castop fwdP a G1) \u
                       castfv_castop (castsubst_castop fwdP a G2)))
          by (apply notin_union_2 with (s := singleton b); exact Hcs).
        assert (Hzf1 : cz \notin castfv_castop (castsubst_castop fwdP a G1))
          by (apply notin_union_1 with (s' := castfv_castop (castsubst_castop fwdP a G2)); exact Hcs2).
        assert (Hzf2 : cz \notin castfv_castop (castsubst_castop fwdP a G2))
          by (apply notin_union_2 with (s := castfv_castop (castsubst_castop fwdP a G1)); exact Hcs2).
        assert (Hzdom : cz `notin` dom ((b,Q0)::E)).
        { apply (notin_dom_cons cz b Q0 E).
          - intro he. apply Hzb. symmetry. exact he.
          - exact HzL. }
        pose proof (TypCast_rename D ((b,Q0)::E) B2 A2
                      (castsubst_castop fwdP a G2) HG2' b cz Hzdom Hzf2) as R.
        rewrite subst_ctx_cons_same in R.
        rewrite (subst_ctx_fresh b cz E Hb) in R.
        rewrite <- (open_close_rename (castsubst_castop fwdP a G2) 0 b cz) in R.
        exact R.
Qed.

Theorem TypCast_completeness: forall D A B,
  eqe2 D nil A B ->
  exists c, TypCast D nil A B c.
Proof.
  intros D A B H.
  destruct (eqe2_complete_both D nil A B H nil) as [[c Hc] _].
  - split.
    + apply uniq_nil.
    + intros p Hp. inversion Hp.
  - exists c. exact Hc.
Qed.
