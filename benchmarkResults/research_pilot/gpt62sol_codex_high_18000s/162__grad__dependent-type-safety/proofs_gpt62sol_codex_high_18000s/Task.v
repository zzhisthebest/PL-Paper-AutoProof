Require Import ssreflect.

Require Import Coq.Classes.EquivDec.

Require Import Metalib.Metatheory.

Require Import Coq.Structures.Orders.

Require Import Stdlib.Init.Sumbool.

Require Import Coq.Program.Equality.

Require Import Coq.Classes.RelationClasses.

Require Import dqtt_ott.

Require Export beta.
(* Use the standard Ltac rewrite syntax. *)
Local Unset SsrRewrite.

From Stdlib Require Import Lia.

Local Open Scope usage_scope.

(* Opening removes one de Bruijn level, so indices above it decrease. *)
Fixpoint scoped (k : nat) (a : tm) : Prop :=
  match a with
  | a_Var_b n => (n < k)%nat
  | a_Pi _ A B | a_Lam _ A B | a_Sigma _ A B =>
      scoped k A /\ scoped (S k) B
  | a_LetBoxB a b B | a_Spread a b B =>
      scoped k a /\ scoped (S k) b /\ scoped k B
  | a_Let a b => scoped k a /\ scoped (S k) b
  | a_letunitB a b B => scoped k a /\ scoped k b /\ scoped k B
  | a_App a b | a_Sum a b | a_Tensor a b => scoped k a /\ scoped k b
  | a_Box _ a | a_box _ a | a_Inj1 a | a_Inj2 a => scoped k a
  | a_Case _ a b c B => scoped k a /\ scoped k b /\ scoped k c /\ scoped k B
  | _ => True
  end.

Lemma scoped_open_inv : forall a k u,
  scoped k (open_tm_wrt_tm_rec k u a) -> scoped (S k) a.
Proof.
  induction a; simpl; intros; try firstorder.
  match goal with |- context [lt_eq_lt_dec ?i ?j] => destruct (lt_eq_lt_dec i j) as [[?|?]|?] | H : context [lt_eq_lt_dec ?i ?j] |- _ => destruct (lt_eq_lt_dec i j) as [[?|?]|?] end; simpl in *; lia.
Qed.

Lemma scoped_open : forall a k u,
  scoped (S k) a -> scoped k u -> scoped k (open_tm_wrt_tm_rec k u a).
Proof.
  assert (mono : forall a j k, scoped j a -> (j <= k)%nat -> scoped k a).
  { induction a; simpl; intros; try solve [eauto 7 with arith | lia | firstorder eauto with arith]. }
  induction a; simpl; intros;
    try solve [firstorder eauto using Nat.le_succ_diag_r].
  match goal with |- context [lt_eq_lt_dec ?i ?j] => destruct (lt_eq_lt_dec i j) as [[?|?]|?] | H : context [lt_eq_lt_dec ?i ?j] |- _ => destruct (lt_eq_lt_dec i j) as [[?|?]|?] end; simpl in *; auto; lia.
Qed.


Lemma lc_scoped : forall a, lc_tm a -> scoped 0 a.
Proof.
  induction 1; simpl; try tauto;
    repeat split; auto;
    destruct (atom_fresh {}) as [z _]; eapply scoped_open_inv with (u := a_Var_f z); eauto.
Qed.

Fixpoint tm_size (a : tm) : nat :=
  match a with
  | a_Pi _ a b | a_Lam _ a b | a_Sigma _ a b
  | a_Let a b | a_App a b | a_Sum a b | a_Tensor a b => S (tm_size a + tm_size b)%nat
  | a_LetBoxB a b B | a_Spread a b B | a_letunitB a b B =>
       S (tm_size a + tm_size b + tm_size B)%nat
  | a_Box _ a | a_box _ a | a_Inj1 a | a_Inj2 a => S (tm_size a)
  | a_Case _ a b c B => S (tm_size a + tm_size b + tm_size c + tm_size B)%nat
  | _ => 1%nat
  end.

Lemma tm_size_open_var : forall a k x,
  tm_size (open_tm_wrt_tm_rec k (a_Var_f x) a) = tm_size a.
Proof.
  induction a; simpl; intros; try solve [f_equal; eauto].
  match goal with |- context [lt_eq_lt_dec ?i ?j] => destruct (lt_eq_lt_dec i j) as [[?|?]|?] end; reflexivity.
Qed.

Lemma scoped_lc : forall a, scoped 0 a -> lc_tm a.
Proof.
  assert (H : forall n a, (tm_size a < n)%nat -> scoped 0 a -> lc_tm a).
  { induction n; intros a Hn Ha; [lia|].
    destruct a; simpl in *; try lia.
    all: decompose [and] Ha.
    all: constructor.
    all: try solve [apply IHn; [lia|assumption]].
    all: intros x; unfold open_tm_wrt_tm; apply IHn.
    all: try solve [rewrite tm_size_open_var; lia].
    all: apply scoped_open; simpl; auto. }
  intros; eapply H; [apply Nat.lt_succ_diag_r|eassumption].
Qed.

Lemma open_scoped_id : forall a j k u,
  scoped j a -> (j <= k)%nat -> open_tm_wrt_tm_rec k u a = a.
Proof.
  induction a; simpl; intros; try solve [f_equal; firstorder eauto with arith].
  match goal with |- context [lt_eq_lt_dec ?i ?j] => destruct (lt_eq_lt_dec i j) as [[?|?]|?] end; auto; lia.
Qed.

Lemma subst_open_rec : forall a k u v x,
  scoped 0 u ->
  subst_tm_tm u x (open_tm_wrt_tm_rec k v a) =
  open_tm_wrt_tm_rec k (subst_tm_tm u x v) (subst_tm_tm u x a).
Proof.
  induction a; simpl; intros; try solve [f_equal; eauto].
  - match goal with |- context [lt_eq_lt_dec ?i ?j] => destruct (lt_eq_lt_dec i j) as [[?|?]|?] end; reflexivity.
  - destruct (eq_var x x0); simpl; auto. symmetry. eapply open_scoped_id with (j := 0%nat); eauto with arith.
Qed.

Lemma subst_open : forall a u v x,
  lc_tm u ->
  subst_tm_tm u x (open_tm_wrt_tm a v) =
  open_tm_wrt_tm (subst_tm_tm u x a) (subst_tm_tm u x v).
Proof. intros; apply subst_open_rec, lc_scoped; auto. Qed.

Lemma subst_fresh : forall a u x,
  x \notin fv_tm_tm a -> subst_tm_tm u x a = a.
Proof.
  induction a; simpl; intros; try solve [f_equal; auto using notin_union].
  destruct (eq_var x x0); subst; auto; exfalso; fsetdec.
Qed.

Lemma open_intro_rec : forall a k u x,
  x \notin fv_tm_tm a ->
  open_tm_wrt_tm_rec k u a =
  subst_tm_tm u x (open_tm_wrt_tm_rec k (a_Var_f x) a).
Proof.
  induction a; simpl; intros; try solve [f_equal; auto using notin_union].
  - match goal with |- context [lt_eq_lt_dec ?i ?j] => destruct (lt_eq_lt_dec i j) as [[?|?]|?] end;
      simpl; try reflexivity. destruct (eq_var (x : tmvar) x); congruence.
  - destruct (eq_var x x0); subst; auto; exfalso; fsetdec.
Qed.

Lemma open_intro : forall a u x,
  x \notin fv_tm_tm a ->
  open_tm_wrt_tm a u = subst_tm_tm u x (open_tm_wrt_tm a (a_Var_f x)).
Proof. intros; apply open_intro_rec; auto. Qed.

Lemma fv_open_lower : forall a k u x,
  x \notin fv_tm_tm (open_tm_wrt_tm_rec k u a) -> x \notin fv_tm_tm a.
Proof.
  induction a; simpl; intros; try solve [auto | fsetdec | repeat apply notin_union; firstorder eauto using notin_union].
Qed.

Lemma subst_close_rec : forall a k u x y,
  x <> y -> y \notin fv_tm_tm u -> scoped 0 u ->
  subst_tm_tm u x (close_tm_wrt_tm_rec k y a) =
  close_tm_wrt_tm_rec k y (subst_tm_tm u x a).
Proof.
  assert (H : forall a k y, scoped k a -> y \notin fv_tm_tm a -> close_tm_wrt_tm_rec k y a = a).
  { induction a; simpl; intros; try solve [f_equal; firstorder eauto using notin_union].
    - match goal with |- context [lt_ge_dec ?i ?j] => destruct (lt_ge_dec i j) end; auto; lia.
    - destruct (eq_var (y : tmvar) x); subst; auto. exfalso; fsetdec. }
  assert (M : forall a j k, scoped j a -> (j <= k)%nat -> scoped k a).
  { induction a; simpl; intros; try solve [lia | firstorder eauto with arith]. }
  induction a; simpl; intros; try solve [f_equal; eauto].
  - match goal with |- context [lt_ge_dec ?i ?j] => destruct (lt_ge_dec i j) end; reflexivity.
  - destruct (eq_var (y : tmvar) x); destruct (eq_var x x0); subst; try contradiction; auto.
    + simpl; destruct (eq_var (x : tmvar) x); congruence.
    + simpl; destruct (eq_var (x0 : tmvar) x0); [|congruence]. symmetry. apply H; [eapply M with (j:=0%nat); [assumption|lia]|assumption].
    + simpl. destruct (eq_var x x0), (eq_var (y : tmvar) x); congruence.
Qed.

Lemma subst_close : forall a u x y,
  x <> y -> y \notin fv_tm_tm u -> lc_tm u ->
  subst_tm_tm u x (close_tm_wrt_tm y a) =
  close_tm_wrt_tm y (subst_tm_tm u x a).
Proof. intros; apply subst_close_rec; auto using lc_scoped. Qed.

Lemma open_close_rec : forall a k y u,
  open_tm_wrt_tm_rec k u (close_tm_wrt_tm_rec k y a) = subst_tm_tm u y a.
Proof.
  induction a; simpl; intros; try solve [f_equal; eauto].
  - match goal with |- context [lt_ge_dec ?i ?j] => destruct (lt_ge_dec i j) end;
      cbn [open_tm_wrt_tm_rec]; repeat match goal with |- context [lt_eq_lt_dec ?i ?j] => destruct (lt_eq_lt_dec i j) as [[?|?]|?] end;
      try reflexivity; try lia; f_equal; lia.
  - destruct (eq_var (y : tmvar) x) as [->|Ne].
    + cbn [open_tm_wrt_tm_rec]. destruct (lt_eq_lt_dec k k) as [[?|?]|?]; try lia.
      destruct (eq_var x x); congruence.
    + cbn [open_tm_wrt_tm_rec]. destruct (eq_var x y); congruence.
Qed.

Lemma open_close : forall a y u,
  open_tm_wrt_tm (close_tm_wrt_tm y a) u = subst_tm_tm u y a.
Proof. intros; apply open_close_rec. Qed.

(* Usage vectors, indexed by the names in an ungraded context. *)
Fixpoint grade (G : context) (x : atom) : usage :=
  match G with
  | nil => 0
  | (y,(r,_)) :: G => match (x == y) with left _ => r | right _ => grade G x end
  end.

Definition pack (E : D) (f : atom -> usage) : context :=
  List.map (fun p => (fst p, (f (fst p), snd p))) E.

Lemma pack_ext : forall E f g,
  (forall x, x `in` dom E -> f x = g x) -> pack E f = pack E g.
Proof.
  induction E as [|[x A] E IH]; simpl; intros; auto.
  f_equal; [f_equal; f_equal|apply IH]; intros; apply H; fsetdec.
Qed.

Lemma ctx_pack : forall E G, ctx E G -> pack E (grade G) = G.
Proof.
  induction 1; auto. simpl. destruct (x == x); [|congruence].
  f_equal. lazymatch type of IHctx with ?p = _ => transitivity p end; [apply pack_ext|exact IHctx].
  intros y Hy. destruct (y == x); subst; [contradiction|reflexivity].
Qed.

Lemma grade_fresh : forall E G x, ctx E G -> x `notin` dom E -> grade G x = 0.
Proof.
  induction 1; simpl; intros; auto.
  destruct (x == x0); subst; [exfalso; fsetdec|apply IHctx; fsetdec].
Qed.

Lemma pack_plus : forall E f g,
  ctx_plus (pack E f) (pack E g) = pack E (fun x => f x + g x).
Proof. induction E as [|[x A] E IH]; simpl; intros; auto; now rewrite IH. Qed.

Lemma pack_mul : forall E f q,
  ctx_mul q (pack E f) = pack E (fun x => q * f x).
Proof. induction E as [|[x A] E IH]; simpl; intros; auto; now rewrite IH. Qed.

Lemma grade_plus : forall E G H x, ctx E G -> ctx E H ->
  grade (ctx_plus G H) x = grade G x + grade H x.
Proof.
  intros E G H z HG. revert H.
  induction HG; intros H0 HH; inversion HH; subst; simpl; [now rewrite qplus_0_l|].
  destruct (z == x); auto.
Qed.

Lemma grade_mul : forall G q x, grade (ctx_mul q G) x = q * grade G x.
Proof.
  induction G as [|[y [r A]] G IH]; simpl; intros; [now rewrite qmul_0_r|].
  destruct (x == y); auto.
Qed.

Lemma pack_grade_mul : forall F G q,
  pack F (grade (ctx_mul q G)) = ctx_mul q (pack F (grade G)).
Proof. intros; rewrite pack_mul; apply pack_ext; intros; apply grade_mul. Qed.

Lemma pack_grade_plus : forall E F G H, ctx E G -> ctx E H ->
  pack F (grade (ctx_plus G H)) = ctx_plus (pack F (grade G)) (pack F (grade H)).
Proof. intros; rewrite pack_plus; apply pack_ext; intros; eapply grade_plus; eauto. Qed.

Lemma ctx_add : forall (E : D) G H, ctx E G -> ctx E H -> ctx E (ctx_plus G H).
Proof.
  intros E G H HG. revert H. induction HG; intros H0 HH; inversion HH; subst; simpl; constructor; auto.
Qed.

Lemma ctx_scale : forall (E : D) G q, ctx E G -> ctx E (ctx_mul q G).
Proof. induction 1; simpl; constructor; auto. Qed.

Lemma ctx_sub_left : forall (E : D) G H, ctx_sub E G H -> ctx E G.
Proof. induction 1; constructor; auto. Qed.

Lemma ctx_sub_right : forall (E : D) G H, ctx_sub E G H -> ctx E H.
Proof. induction 1; constructor; auto. Qed.

Lemma grade_sub : forall E G H x, ctx_sub E G H -> grade G x <= grade H x.
Proof.
  induction 1; simpl; [apply qleb_refl|]; destruct (x == x0); auto.
Qed.

Lemma pack_sub : forall E G f g, ctx E G ->
  (forall x, x `in` dom E -> f x <= g x) ->
  ctx_sub E (pack E f) (pack E g).
Proof.
  induction 1; simpl; intros LE.
  - constructor.
  - constructor.
    + apply LE; fsetdec.
    + apply IHctx; intros; apply LE; fsetdec.
    + assumption.
Qed.

Lemma plus_0_r : forall q, q + 0 = q.
Proof. intros; rewrite qplus_comm; apply qplus_0_l. Qed.

Lemma usage_interchange : forall f g h k,
  (f + g) + (h + k) = (f + h) + (g + k).
Proof.
  intros. rewrite <- !qplus_assoc. f_equal.
  rewrite (qplus_assoc g h k), (qplus_comm g h), <- qplus_assoc. reflexivity.
Qed.

Lemma ctx_plus_comm : forall (E : D) G H, ctx E G -> ctx E H ->
  ctx_plus G H = ctx_plus H G.
Proof.
  intros E G H HG HH. rewrite <- (ctx_pack _ _ HG), <- (ctx_pack _ _ HH), !pack_plus.
  apply pack_ext; intros; apply qplus_comm.
Qed.

Ltac fresh_atom z L := let H := fresh "Fresh" in destruct (atom_fresh L) as [z H].
Ltac set_fresh := simpl in *; repeat rewrite dom_app in *; simpl in *; fsetdec.

Lemma Typing_ctx : forall E G a A, Typing E G a A -> ctx E G.
Proof.
  induction 1; simpl in *; eauto using ctx, ctx_add, ctx_scale, ctx_sub_right.
  all: try solve [constructor; eauto using ctx_scale].
  all: match goal with
  | H : forall x, x `notin` ?L -> ctx ((x,_) :: _) ((x,_) :: _) |- _ =>
      let z := fresh "z" in fresh_atom z L; specialize (H z ltac:(assumption));
      inversion H; subst; solve [eauto using ctx_add]
  | H : forall x, x `notin` ?L -> forall y, y `notin` _ -> ctx ((x,_) :: _) ((x,_) :: _) |- _ =>
      let z := fresh "z" in let w := fresh "w" in
      fresh_atom z L; fresh_atom w (L \u {{z}});
      specialize (H z ltac:(assumption) w ltac:(assumption));
      inversion H; subst; solve [eauto using ctx_add]
  end.
Qed.

Lemma cofinite_scope : forall L a,
  (forall x, x \notin L -> scoped 0 (open_tm_wrt_tm a (a_Var_f x))) ->
  scoped 1 a.
Proof. intros L a H. fresh_atom z L. eapply scoped_open_inv; eauto. Qed.

Lemma scoped_open_zero : forall a u,
  scoped 1 a -> scoped 0 u -> scoped 0 (open_tm_wrt_tm a u).
Proof. intros; apply scoped_open; auto. Qed.

Ltac split_typing_ih :=
  repeat match goal with
  | H : _ /\ _ |- _ => destruct H
  end.

Ltac cofinite_component :=
  eapply cofinite_scope;
  let x := fresh "x" in let Fx := fresh "Fx" in intros x Fx;
  match goal with
  | H : forall z, z \notin _ -> _ /\ _ |- _ => destruct (H x Fx); assumption
  | H : forall z, z \notin ?L -> forall y, y \notin _ -> _ /\ _ |- _ =>
      let y := fresh "y" in fresh_atom y (L \u {{x}});
      destruct (H x Fx y ltac:(assumption)); assumption
  end.

Lemma Typing_scoped : forall E G a A, Typing E G a A -> scoped 0 a /\ scoped 0 A.
Proof.
  induction 1; subst; simpl in *; split_typing_ih;
    repeat split; auto; try solve [cofinite_component].
  all: apply scoped_open_zero; auto using scoped_open_zero; cofinite_component.
Qed.

Lemma Typing_lc : forall E G a A, Typing E G a A -> lc_tm a.
Proof. intros E G a A T; apply scoped_lc; exact (proj1 (Typing_scoped E G a A T)). Qed.

Lemma Typing_lc_type : forall E G a A, Typing E G a A -> lc_tm A.
Proof. intros E G a A T; apply scoped_lc; exact (proj2 (Typing_scoped E G a A T)). Qed.

Lemma fv_open_upper : forall a k u x,
  x \notin fv_tm_tm a -> x \notin fv_tm_tm u ->
  x \notin fv_tm_tm (open_tm_wrt_tm_rec k u a).
Proof.
  induction a; simpl; intros; repeat apply notin_union; try assumption.
  all: try solve [
    match goal with
    | IH : forall k u x, _ -> _ -> x \notin fv_tm_tm (open_tm_wrt_tm_rec k u _) |- _ =>
      apply IH; [fsetdec|assumption]
    end].
  match goal with |- context [lt_eq_lt_dec ?i ?j] => destruct (lt_eq_lt_dec i j) as [[?|?]|?] end;
    simpl; auto.
Qed.

Lemma fv_open_zero : forall a u x,
  x \notin fv_tm_tm a -> x \notin fv_tm_tm u ->
  x \notin fv_tm_tm (open_tm_wrt_tm a u).
Proof. intros; apply fv_open_upper; auto. Qed.

Ltac typing_fv_cofinite :=
  match goal with
  | H : forall x, x \notin ?L -> forall z, _ -> _ /\ _,
    F : ?z \notin dom _ |- ?z \notin fv_tm_tm ?b =>
      let x := fresh "x" in fresh_atom x (L \u {{z}});
      specialize (H x ltac:(set_fresh) z ltac:(set_fresh));
      destruct H;
      eapply fv_open_lower with (k:=0%nat) (u:=a_Var_f x); eassumption
  | H : forall x, x \notin ?L -> forall y, y \notin _ -> forall z, _ -> _ /\ _,
    F : ?z \notin dom _ |- ?z \notin fv_tm_tm ?b =>
      let x := fresh "x" in let y := fresh "y" in
      fresh_atom x (L \u {{z}}); fresh_atom y (L \u {{x}});
      specialize (H x ltac:(set_fresh) y ltac:(set_fresh) z ltac:(set_fresh));
      destruct H;
      eapply fv_open_lower with (k:=0%nat) (u:=a_Var_f x); eassumption
  end.

Lemma Typing_fresh : forall E G a A, Typing E G a A ->
  forall x, x \notin dom E -> x \notin fv_tm_tm a /\ x \notin fv_tm_tm A.
Proof.
  induction 1; subst; intros z F;
    repeat match goal with
    | H : forall x, x \notin dom ?E -> _ /\ _ |- _ =>
      let HF := fresh in
      first [assert (HF : z \notin dom E) by set_fresh; specialize (H z HF) | fail 1]
    end; simpl in *; split_typing_ih;
    split; repeat apply notin_union; try solve [assumption | set_fresh | typing_fv_cofinite].
  all: apply fv_open_zero;
    try solve [assumption | set_fresh | typing_fv_cofinite].
Qed.

Lemma pack_lift : forall E G x r A C,
  x \notin dom E ->
  pack ((x,Tm C)::E) (grade ((x,(r,Tm A))::G)) =
  (x,(r,Tm C)) :: pack E (grade G).
Proof.
  intros. simpl. destruct (x == x); [|congruence].
  f_equal. apply pack_ext; intros y Hy.
  destruct (y == x); subst; [contradiction|reflexivity].
Qed.

Lemma pack_insert_zero : forall E G x A,
  grade G x = 0 ->
  pack ((x,Tm A)::E) (grade G) = (x,(0,Tm A)) :: pack E (grade G).
Proof. intros; simpl; now rewrite H. Qed.

(* An embedding inserts fresh, well-typed declarations with grade zero. *)
Inductive env_embed : D -> D -> Prop :=
| emb_nil : env_embed nil nil
| emb_insert : forall E F x A G,
    env_embed E F -> x \notin dom F -> Typing F G A a_Type ->
    env_embed E ((x,Tm A)::F)
| emb_keep : forall E F x A,
    env_embed E F -> x \notin dom F ->
    env_embed ((x,Tm A)::E) ((x,Tm A)::F).

Lemma embed_refl : forall E G, ctx E G -> env_embed E E.
Proof. induction 1; [constructor|]. destruct a; constructor; auto. Qed.

Lemma embed_dom : forall E F, env_embed E F ->
  forall x, x \notin dom F -> x \notin dom E.
Proof.
  induction 1; simpl in *; intros z Hz; try assumption.
  all: specialize (IHenv_embed z ltac:(fsetdec)); fsetdec.
Qed.

Lemma embed_ctx : forall E F, env_embed E F -> ctx F (pack F (fun _ => 0)).
Proof. induction 1; simpl; constructor; auto. Qed.

Lemma embed_constant : forall E F a A,
  env_embed E F -> E = nil -> Typing nil nil a A ->
  Typing F (pack F (fun _ => 0)) a A.
Proof.
  induction 1; intros He T; inversion He; subst; simpl; auto.
  eapply T_weak; eauto.
Qed.

Lemma embed_var : forall E F G x A,
  env_embed ((x,Tm A)::E) F ->
  x \notin dom E -> Typing E G A a_Type ->
  (forall F, env_embed E F -> Typing F (pack F (grade G)) A a_Type) ->
  Typing F (pack F (grade ((x,(1,Tm A))::ctx_mul 0 G))) (a_Var_f x) A.
Proof.
  intros E F G x A H. remember ((x,Tm A)::E) as Src eqn:He.
  induction H; inversion He; subst; intros Fx TA IH.
  - rewrite pack_insert_zero.
    + eapply T_weak; eauto.
    + eapply grade_fresh.
      * constructor; eauto using ctx_scale, Typing_ctx.
      * eapply embed_dom; eauto.
  - rewrite pack_lift by assumption. rewrite pack_grade_mul.
    apply T_var; auto.
Qed.

Lemma embed_weak : forall E F G H x A a B,
  env_embed ((x,Tm A)::E) F ->
  x \notin dom E -> Typing E G a B ->
  (forall F, env_embed E F -> Typing F (pack F (grade G)) a B) ->
  (forall F, env_embed E F -> Typing F (pack F (grade H)) A a_Type) ->
  Typing F (pack F (grade ((x,(0,Tm A))::G))) a B.
Proof.
  intros E F G H x A a B M. remember ((x,Tm A)::E) as Src eqn:He.
  induction M; inversion He; subst; intros Fx Ta IHa IHA.
  - rewrite pack_insert_zero.
    + eapply T_weak; eauto.
    + eapply grade_fresh.
      * constructor; eauto using Typing_ctx.
      * eapply embed_dom; eauto.
  - rewrite pack_lift by assumption. eapply T_weak; eauto.
Qed.

Ltac ctx_fact :=
  first [solve [eauto 4 using Typing_ctx, ctx_add, ctx_scale, ctx_sub_left, ctx_sub_right]
  | match goal with
    | H : forall z, z \notin ?L -> Typing _ _ _ _ |- ctx _ _ =>
        let z := fresh "z" in let C := fresh "C" in
        fresh_atom z L;
        pose proof (Typing_ctx _ _ _ _ (H z ltac:(assumption))) as C;
        inversion C; subst; solve [assumption]
    | H : forall z, z \notin ?L -> forall w, w \notin _ -> Typing _ _ _ _ |- ctx _ _ =>
        let z := fresh "z" in let w := fresh "w" in let C := fresh "C" in
        fresh_atom z L; fresh_atom w (L \u {{z}});
        pose proof (Typing_ctx _ _ _ _ (H z ltac:(assumption) w ltac:(assumption))) as C;
        inversion C; subst; solve [assumption]
    end].

Ltac normalize_grades :=
  repeat (erewrite pack_grade_plus by ctx_fact);
  rewrite ?pack_grade_mul.

Ltac embed_binder :=
  intros; cbn [one List.app] in *;
  match goal with
  | M : env_embed ?E ?F,
    IH : forall x, x \notin ?L -> forall F, env_embed ((x,Tm ?A)::?E) F -> _,
    Fx : ?x \notin _ |- Typing ((?x,Tm ?A)::?F) _ _ _ =>
      let F0 := fresh "F0" in
      assert (F0 : x \notin dom F) by set_fresh;
      specialize (IH x ltac:(set_fresh) _ (emb_keep E F x A M F0));
      rewrite pack_lift in IH by exact F0; exact IH
  | M : env_embed ?E ?F,
    IH : forall x, x \notin ?L -> forall y, y \notin _ ->
         forall F, env_embed ((x,Tm ?A)::?E) F -> _,
    Fx : ?x \notin _, Fy : ?y \notin _ |- Typing ((?x,Tm ?A)::?F) _ _ _ =>
      let F0 := fresh "F0" in
      assert (F0 : x \notin dom F) by set_fresh;
      specialize (IH x ltac:(set_fresh) y ltac:(set_fresh) _ (emb_keep E F x A M F0));
      rewrite pack_lift in IH by exact F0; exact IH
  end.

Lemma typing_embed : forall E G a A, Typing E G a A ->
  forall F, env_embed E F -> Typing F (pack F (grade G)) a A.
Proof.
  induction 1; intros F M; subst; normalize_grades.
  - eapply T_sub; [eauto|]. eapply pack_sub; eauto using embed_ctx, grade_sub.
  - eapply embed_constant; eauto using T_type.
  - exact (embed_var D5 F G x A M H H0 IHTyping).
  - eapply (embed_weak D5 F G1 G2 x A a B M); eassumption.
  - eapply T_pi with (L := L \u dom F); [eauto|embed_binder].
  - eapply T_lam with (L := L \u dom F); [embed_binder|eauto].
  - eapply T_app; eauto.
  - eapply T_conv; eauto.
  - eapply embed_constant; eauto using T_unit.
  - eapply embed_constant; eauto using T_Unit.
  - eapply T_UnitE with (L := L \u dom F); [eauto|reflexivity|eauto|embed_binder].
  - eapply T_Box; eauto.
  - eapply T_box; eauto.
  - eapply T_letbox with (L := L \u dom F); [eauto|embed_binder|embed_binder].
  - eapply T_sum; eauto.
  - eapply T_inj1; eauto.
  - eapply T_inj2; eauto.
  - eapply T_case with (L := L \u dom F); try solve [eauto | intros; eauto using notin_union_1 | embed_binder].
  - eapply T_Sigma with (L := L \u dom F); [eauto|embed_binder].
  - eapply T_Tensor with (L := L \u dom F); [eauto|eauto|embed_binder].
  - eapply T_Spread with (L := L \u dom F); [reflexivity|eauto|embed_binder|embed_binder].
Qed.

(* Only declarations newer than the substituted binder can depend on it.
   Each target grade combines its original usage and the scaled argument usage. *)
Definition subst_env (u : tm) (x : atom) (P E : D) : D :=
  List.map (fun p => (fst p, subst_tm_sort u x (snd p))) P ++ E.

Lemma subst_env_dom : forall u x P E,
  dom (subst_env u x P E) [=] dom (P ++ E).
Proof.
  intros u x P. induction P as [|[y [A]] P IH]; simpl; intros; [reflexivity|].
  specialize (IH E). fsetdec.
Qed.

Definition subst_budget (F : D) (x : atom) (U G : context) : context :=
  pack F (fun y => grade G y + grade G x * grade U y).

Lemma budget_plus : forall E F x U G H,
  ctx E G -> ctx E H ->
  subst_budget F x U (ctx_plus G H) =
  ctx_plus (subst_budget F x U G) (subst_budget F x U H).
Proof.
  unfold subst_budget; intros; rewrite pack_plus; apply pack_ext; intros.
  rewrite !(grade_plus E) by assumption. rewrite distr_l, usage_interchange. reflexivity.
Qed.

Lemma budget_mul : forall F x U G q,
  subst_budget F x U (ctx_mul q G) = ctx_mul q (subst_budget F x U G).
Proof.
  unfold subst_budget; intros; rewrite pack_mul; apply pack_ext; intros.
  rewrite !grade_mul, distr_r, qmul_assoc. reflexivity.
Qed.

Lemma budget_sub : forall E F x U G H K,
  ctx F K -> ctx_sub E G H ->
  ctx_sub F (subst_budget F x U G) (subst_budget F x U H).
Proof.
  unfold subst_budget; intros. eapply pack_sub; [eassumption|]. intros.
  eapply qleb_trans.
  - apply po_semiring1. eapply grade_sub; eassumption.
  - rewrite (qplus_comm (grade H x0)), (qplus_comm (grade H x0)).
    apply po_semiring1, po_semiring2. eapply grade_sub; eassumption.
Qed.

Lemma budget_keep : forall E F x y U G r A C,
  x <> y -> y \notin dom F -> y \notin dom E -> ctx E U ->
  subst_budget ((y,Tm C)::F) x U ((y,(r,Tm A))::G) =
  (y,(r,Tm C)) :: subst_budget F x U G.
Proof.
  unfold subst_budget; simpl; intros.
  destruct (x == y), (y == y); try congruence.
  rewrite (grade_fresh E U) by assumption. rewrite qmul_0_r, plus_0_r.
  f_equal. apply pack_ext; intros z Hz. destruct (z == y); subst; [contradiction|reflexivity].
Qed.

Lemma budget_drop : forall E x U G r A, ctx E G -> ctx E U ->
  x \notin dom E ->
  subst_budget E x U ((x,(r,Tm A))::G) = ctx_plus G (ctx_mul r U).
Proof.
  intros E x U G r A HG HU Fx. unfold subst_budget.
  replace (ctx_plus G (ctx_mul r U)) with
    (ctx_plus (pack E (grade G)) (ctx_mul r (pack E (grade U))))
    by now rewrite (ctx_pack E G HG), (ctx_pack E U HU).
  rewrite pack_mul, pack_plus. apply pack_ext; simpl; intros y Hy.
  destruct (x == x), (y == x); subst; try congruence.
Qed.

Lemma ctx_plus_zero : forall (E : D) G H,
  ctx E G -> ctx E H -> ctx_plus G (ctx_mul 0 H) = G.
Proof.
  intros E G H HG. revert H.
  induction HG; intros H0 HH; inversion HH; subst; simpl; auto.
  rewrite qmul_0_l, plus_0_r, IHHG by assumption. reflexivity.
Qed.

Lemma ctx_beta_var : forall (E : D) G U,
  ctx E G -> ctx E U -> ctx_plus (ctx_mul 0 G) (ctx_mul 1 U) = U.
Proof.
  intros E G U HG. revert U.
  induction HG; intros U HU; inversion HU; subst; simpl; auto.
  rewrite qmul_0_l, qmul_1_l, qplus_0_l, IHHG by assumption. reflexivity.
Qed.

Lemma subst_var_same : forall u x, subst_tm_tm u x (a_Var_f x) = u.
Proof. simpl; intros; destruct (eq_var x x); congruence. Qed.

Lemma subst_var_other : forall u x y, x <> y -> subst_tm_tm u x (a_Var_f y) = a_Var_f y.
Proof. simpl; intros; destruct (eq_var y x); congruence. Qed.

Section Substitution.
  Context (E : D) (U : context) (u A : tm) (x : atom).
  Hypothesis Tu : Typing E U u A.
  Hypothesis Fx : x \notin dom E.

  Local Ltac subst_budget_normalize :=
    repeat (erewrite budget_plus by ctx_fact);
    rewrite ?budget_mul, ?subst_open by eauto using Typing_lc.

  Local Ltac subst_under_binder :=
    intros; cbn [one List.app] in *;
    match goal with
    | Eq : ?Src = ?P ++ _,
      IH : forall z, z \notin _ -> forall Q, _ = Q ++ _ -> _,
      Fz : ?z \notin _ |- Typing ((?z,Tm _)::_) _ _ _ =>
        let N := fresh "N" in
        assert (N : x <> z) by set_fresh;
        let Ty := match type of IH with forall z, _ -> forall Q, ((z,?ty) :: _) = _ -> _ => ty end in
        specialize (IH z ltac:(set_fresh) ((z,Ty) :: P) ltac:(simpl; now rewrite Eq));
        cbn [subst_env List.map List.app fst snd subst_tm_sort] in IH;
        fold (subst_env u x P E) in IH;
        rewrite (budget_keep E) in IH by
          (solve [assumption | eapply Typing_ctx; exact Tu | apply notin_union_2 in Fz; set_fresh
                 | rewrite subst_env_dom; rewrite Eq in Fz; set_fresh | rewrite Eq in Fz; set_fresh]);
        rewrite ?subst_open in IH by eauto using Typing_lc;
        cbn [subst_tm_tm] in IH;
        destruct (eq_var (z : tmvar) x); [congruence|exact IH]
    | Eq : ?Src = ?P ++ _,
      IH : forall z, z \notin _ -> forall w, w \notin _ -> forall Q, _ = Q ++ _ -> _,
      Fz : ?z \notin _, Fw : ?w \notin _ |- Typing ((?z,Tm _)::_) _ _ _ =>
        let N := fresh "N" in let N' := fresh "N" in
        assert (N : x <> z) by set_fresh;
        assert (N' : x <> w) by set_fresh;
        let Ty := match type of IH with forall z, _ -> forall w, _ -> forall Q, ((z,?ty) :: _) = _ -> _ => ty end in
        specialize (IH z ltac:(set_fresh) w ltac:(set_fresh) ((z,Ty) :: P) ltac:(simpl; now rewrite Eq));
        cbn [subst_env List.map List.app fst snd subst_tm_sort] in IH;
        fold (subst_env u x P E) in IH;
        rewrite (budget_keep E) in IH by
          (solve [assumption | eapply Typing_ctx; exact Tu
                 | rewrite subst_env_dom; rewrite Eq in Fz; set_fresh | rewrite Eq in Fz; set_fresh]);
        cbn [subst_tm_tm] in IH;
        rewrite ?subst_close, ?subst_open in IH by
          (solve [eauto using Typing_lc | set_fresh]);
        cbn [subst_tm_tm] in IH;
        destruct (eq_var (z : tmvar) x), (eq_var (w : tmvar) x);
          try congruence; exact IH
    end.

  Local Ltac subst_branch_eq :=
    intros z Fz;
    match goal with
    | H : forall x, _ -> open_tm_wrt_tm _ _ = open_tm_wrt_tm _ _ |- _ =>
      let K := fresh "K" in
      let N := fresh "N" in
      assert (N : x <> z) by set_fresh;
      pose proof (f_equal (subst_tm_tm u x) (H z ltac:(set_fresh))) as K;
      rewrite !subst_open in K by eauto using Typing_lc;
      cbn [subst_tm_tm] in K;
      destruct (eq_var (z : tmvar) x); [congruence | exact K]
    end.

  Lemma typing_subst_general : forall K G a B, Typing K G a B ->
    forall P, K = P ++ (x,Tm A)::E ->
    Typing (subst_env u x P E) (subst_budget (subst_env u x P E) x U G)
      (subst_tm_tm u x a) (subst_tm_tm u x B).
  Proof.
    induction 1; intros P Eq; try subst B1; try subst A0.
    all: cbn [subst_tm_tm]; subst_budget_normalize.
    all: repeat match goal with
    | Eq : ?K = ?P ++ _,
      IH : forall Q, ?K = Q ++ _ -> Typing _ _ _ _ |- _ =>
        specialize (IH P Eq); rewrite ?subst_open in IH by eauto using Typing_lc
    end.
    - eapply T_sub; [exact IHTyping|].
      eapply budget_sub; eauto using Typing_ctx.
    - destruct P; discriminate.
    - destruct P as [|[y [C]] P]; inversion Eq; subst; clear Eq.
      + destruct (eq_var (x : tmvar) x); [|congruence].
        cbn [subst_env List.map List.app one].
        rewrite budget_drop by (ctx_fact || assumption).
        erewrite ctx_beta_var by ctx_fact.
        rewrite (subst_fresh A) by exact (proj1 (Typing_fresh _ _ _ _ H0 x Fx)).
        exact Tu.
      + assert (N : x <> y) by set_fresh.
        destruct (eq_var (y : tmvar) x); [congruence|].
        cbn [subst_env List.map List.app fst snd subst_tm_sort].
        fold (subst_env u x P E). cbn [one List.app].
        rewrite (budget_keep E) by (solve [assumption | ctx_fact | rewrite subst_env_dom; set_fresh | set_fresh]).
        rewrite budget_mul. apply T_var; [rewrite subst_env_dom; set_fresh|].
        apply IHTyping; reflexivity.
    - destruct P as [|[y [C]] P]; inversion Eq; subst; clear Eq.
      + cbn [subst_env List.map List.app one].
        rewrite budget_drop by (ctx_fact || assumption). erewrite ctx_plus_zero by ctx_fact.
        match goal with T : Typing E G1 a B |- _ =>
          destruct (Typing_fresh _ _ _ _ T x Fx)
        end.
        rewrite (subst_fresh a), (subst_fresh B) by assumption. assumption.
      + cbn [subst_env List.map List.app fst snd subst_tm_sort].
        fold (subst_env u x P E). cbn [one List.app].
        rewrite (budget_keep E) by (solve [assumption | ctx_fact | rewrite subst_env_dom; set_fresh | set_fresh]).
        eapply T_weak; [rewrite subst_env_dom; set_fresh| |]; eauto.
    - eapply T_pi with (L := L \u dom D5 \u {{x}} \u fv_tm_tm u); [eauto|subst_under_binder].
    - eapply T_lam with (L := L \u dom D5 \u {{x}} \u fv_tm_tm u); [subst_under_binder|eauto].
    - eapply T_app; eauto.
    - eapply T_conv; eauto using subst_Beta1, Typing_lc.
    - destruct P; discriminate.
    - destruct P; discriminate.
    - eapply T_UnitE with (L := L \u dom D5 \u {{x}} \u fv_tm_tm u);
        [eauto|reflexivity|eauto|subst_under_binder].
    - eapply T_Box; eauto.
    - eapply T_box; eauto.
    - eapply T_letbox with (L := L \u dom D5 \u {{x}} \u fv_tm_tm u);
        [eauto|subst_under_binder|subst_under_binder].
    - eapply T_sum; eauto.
    - eapply T_inj1; eauto.
    - eapply T_inj2; eauto.
    - eapply T_case with (L := L \u dom D5 \u {{x}} \u fv_tm_tm u);
        [assumption|eauto|subst_branch_eq|subst_branch_eq|eauto|eauto|subst_under_binder].
    - eapply T_Sigma with (L := L \u dom D5 \u {{x}} \u fv_tm_tm u); [eauto|subst_under_binder].
    - eapply T_Tensor with (L := L \u dom D5 \u {{x}} \u fv_tm_tm u);
        [eauto|eauto|subst_under_binder].
    - eapply T_Spread with (L := L \u dom D5 \u {{x}} \u fv_tm_tm u);
        [reflexivity|eauto|subst_under_binder|subst_under_binder].
  Qed.
End Substitution.

Lemma typing_subst_head : forall E G U a A b B x r,
  x \notin dom E -> Typing E U a A ->
  Typing ((x,Tm A)::E) ((x,(r,Tm A))::G) b B ->
  Typing E (ctx_plus G (ctx_mul r U)) (subst_tm_tm a x b) (subst_tm_tm a x B).
Proof.
  intros E G U a A b B x r Fx Tu Tb.
  pose proof (typing_subst_general E U a A x Tu Fx _ _ _ _ Tb nil Logic.eq_refl) as H.
  simpl in H. rewrite budget_drop in H by
    (solve [assumption | ctx_fact | pose proof (Typing_ctx _ _ _ _ Tb) as C; inversion C; auto]).
  exact H.
Qed.

Lemma typing_open : forall E G U u A b B r L,
  Typing E U u A ->
  (forall x, x \notin L ->
    Typing ((x,Tm A)::E) ((x,(r,Tm A))::G)
      (open_tm_wrt_tm b (a_Var_f x)) (open_tm_wrt_tm B (a_Var_f x))) ->
  Typing E (ctx_plus G (ctx_mul r U)) (open_tm_wrt_tm b u) (open_tm_wrt_tm B u).
Proof.
  intros E G U u A b B r L Tu Tb.
  fresh_atom x (L \u dom E \u fv_tm_tm b \u fv_tm_tm B).
  rewrite (open_intro b u x), (open_intro B u x) by set_fresh.
  eapply typing_subst_head; [set_fresh|exact Tu|apply Tb; set_fresh].
Qed.

Lemma ctx_sub_refl : forall (E : D) G, ctx E G -> ctx_sub E G G.
Proof. induction 1; constructor; auto using qleb_refl. Qed.

Lemma ctx_sub_trans : forall (E : D) G H K, ctx_sub E G H -> ctx_sub E H K -> ctx_sub E G K.
Proof.
  intros E G H K C. revert K. induction C; intros K C'; inversion C'; subst;
    constructor; eauto using qleb_trans.
Qed.

Lemma ctx_sub_add : forall (E : D) G G' H H',
  ctx_sub E G G' -> ctx_sub E H H' ->
  ctx_sub E (ctx_plus G H) (ctx_plus G' H').
Proof.
  intros E G G' H H' C. revert H H'. induction C; intros K K' C'; inversion C'; subst;
    simpl; constructor; auto.
  eapply qleb_trans; [apply po_semiring1; eassumption|].
  rewrite (qplus_comm q2), (qplus_comm q2).
  apply po_semiring1; assumption.
Qed.

Lemma ctx_sub_mul : forall (E : D) G H q,
  ctx_sub E G H -> ctx_sub E (ctx_mul q G) (ctx_mul q H).
Proof. induction 1; simpl; constructor; auto using po_semiring3. Qed.

Lemma ctx_plus_assoc : forall (E : D) G H K, ctx E G -> ctx E H -> ctx E K ->
  ctx_plus G (ctx_plus H K) = ctx_plus (ctx_plus G H) K.
Proof.
  intros E G H K HG HH HK.
  rewrite <- (ctx_pack E G HG), <- (ctx_pack E H HH), <- (ctx_pack E K HK), !pack_plus.
  apply pack_ext; intros; apply qplus_assoc.
Qed.

Lemma typing_weak_under : forall E x A H P a B G,
  x \notin dom (P ++ E) ->
  Typing E H A a_Type -> Typing (P ++ E) G a B ->
  Typing (P ++ (x,Tm A)::E) (pack (P ++ (x,Tm A)::E) (grade G)) a B.
Proof.
  intros E x A H P a B G Fx TA T. apply typing_embed with (E := P ++ E); auto.
  pose proof (Typing_ctx _ _ _ _ T) as HC.
  clear T. revert G HC Fx. induction P as [|[y [C]] P IH]; simpl; intros.
  - eapply emb_insert; eauto using embed_refl.
  - inversion HC; subst. apply emb_keep; [eapply IH; eauto; set_fresh|].
    rewrite !dom_app in *. set_fresh.
Qed.

Lemma typing_weak_binder : forall E x A C H y G r a B,
  x <> y -> x \notin dom E ->
  Typing E H A a_Type ->
  Typing ((y,Tm C)::E) ((y,(r,Tm C))::G) a B ->
  Typing ((y,Tm C)::(x,Tm A)::E) ((y,(r,Tm C))::(x,(0,Tm A))::G) a B.
Proof.
  intros E x A C H y G r a B N Fx TA T.
  pose proof (typing_weak_under E x A H ((y,Tm C)::nil) a B _ ltac:(set_fresh) TA T) as W.
  change (Typing ((y,Tm C)::(x,Tm A)::E)
     (pack ((y,Tm C)::(x,Tm A)::E) (grade ((y,(r,Tm C))::G))) a B) in W.
  pose proof (Typing_ctx _ _ _ _ T) as HC. inversion HC; subst.
  rewrite pack_lift in W by set_fresh.
  rewrite pack_insert_zero, ctx_pack in W by eauto using grade_fresh. exact W.
Qed.

Lemma ctx_mul_assoc : forall (G : context) r q,
  ctx_mul r (ctx_mul q G) = ctx_mul (r * q) G.
Proof.
  induction G as [|[x [s C]] G IH]; simpl; intros; auto.
  now rewrite qmul_assoc, IH.
Qed.

Lemma typing_rename_open : forall E G H x y r C b B,
  x \notin dom E -> y \notin dom E -> y <> x ->
  x \notin fv_tm_tm b -> x \notin fv_tm_tm B ->
  Typing E H C a_Type ->
  Typing ((x,Tm C)::E) ((x,(r,Tm C))::G) (open_tm_wrt_tm b (a_Var_f x)) (open_tm_wrt_tm B (a_Var_f x)) ->
  Typing ((y,Tm C)::E) ((y,(r,Tm C))::G) (open_tm_wrt_tm b (a_Var_f y)) (open_tm_wrt_tm B (a_Var_f y)).
Proof.
  intros E G H x y r C b B Fx Fy N Fb FB TC T.
  pose proof (typing_weak_binder E y C C H x G r _ _ N Fy TC T) as W.
  pose proof (T_var E y C H Fy TC) as V.
  assert (Fxy : x \notin dom ((y,Tm C)::E)) by set_fresh.
  pose proof (typing_subst_head _ _ _ _ _ _ _ _ _ Fxy V W) as R.
  rewrite <- (open_intro b (a_Var_f y) x), <- (open_intro B (a_Var_f y) x) in R by assumption.
  simpl in R. rewrite qplus_0_l, qmul_1_r, ctx_mul_assoc, qmul_0_r in R.
  rewrite (ctx_plus_zero E) in R by
    (eauto using Typing_ctx, ctx_scale || pose proof (Typing_ctx _ _ _ _ T) as HC; inversion HC; assumption).
  exact R.
Qed.

(* Inverting a kinding derivation through conversion, subsumption and weakening. *)
Definition components (E : D) (t : tm) : Prop :=
  match t with
  | a_Pi _ A B | a_Sigma _ A B =>
      (exists G, Typing E G A a_Type) /\
      (exists L r H, forall x, x \notin L ->
        Typing ((x,Tm A)::E) ((x,(r,Tm A))::H) (open_tm_wrt_tm B (a_Var_f x)) a_Type)
  | a_Box _ A => exists G, Typing E G A a_Type
  | a_Sum A B => (exists G, Typing E G A a_Type) /\ (exists H, Typing E H B a_Type)
  | _ => True
  end.

Lemma components_weak : forall E x A G t,
  x \notin dom E -> Typing E G A a_Type -> components E t -> components ((x,Tm A)::E) t.
Proof.
  intros E x A G t Fx TA. destruct t; simpl; intro C; try exact I.
  all: try solve [destruct C as [H TH]; eexists; eapply T_weak; eassumption].
  all: destruct C as [[H TH] C]; split; [eexists; eapply T_weak; eassumption|].
  all: try solve [destruct C as [K TK]; eexists; eapply T_weak; eassumption].
  all: destruct C as [L [r [K TK]]]; exists (L \u {{x}}), r, ((x,(0,Tm A))::K);
    intros y Fy; eapply typing_weak_binder; [set_fresh|assumption|eassumption|apply TK; set_fresh].
Qed.

Lemma typing_components : forall E G t T, Typing E G t T -> components E t.
Proof.
  induction 1; simpl; eauto using components_weak.
  all: split; [eauto|exists L, r, G2; exact H0].
Qed.

Lemma kind_open : forall E A U u B L r H,
  Typing E U u A ->
  (forall x, x \notin L ->
    Typing ((x,Tm A)::E) ((x,(r,Tm A))::H) (open_tm_wrt_tm B (a_Var_f x)) a_Type) ->
  exists G, Typing E G (open_tm_wrt_tm B u) a_Type.
Proof.
  intros. exists (ctx_plus H (ctx_mul r U)).
  change (Typing E (ctx_plus H (ctx_mul r U)) (open_tm_wrt_tm B u) (open_tm_wrt_tm a_Type u)).
  eapply typing_open; eauto.
Qed.

Lemma typing_regular : forall E G a A, Typing E G a A -> exists H, Typing E H A a_Type.
Proof.
  induction 1; subst; try solve [eauto using T_type, T_Unit, T_weak, T_Box, T_sum].
  all: try solve [eapply kind_open with (L:=L) (r:=r) (H:=G3); eassumption].
  all: try solve [destruct IHTyping; eexists; apply T_Box; eassumption].
  all: try solve [destruct IHTyping; eexists; eapply T_sum; eassumption].
  - destruct IHTyping1. eexists. eapply T_weak; eassumption.
  - fresh_atom z (L \u dom D5 \u fv_tm_tm B).
    destruct (H0 z ltac:(set_fresh)) as [K TK].
    pose proof (Typing_ctx _ _ _ _ TK) as HC. inversion HC; subst.
    exists (ctx_plus G2 G).
    eapply T_pi with (L:=dom D5 \u {{z}}) (r:=q0); [eassumption|].
    intros y Fy.
    change (Typing ((y,Tm A)::D5) ((y,(q0,Tm A))::G)
      (open_tm_wrt_tm B (a_Var_f y)) (open_tm_wrt_tm a_Type (a_Var_f y))).
    eapply typing_rename_open with (x:=z); try eassumption; set_fresh.
  - destruct IHTyping1 as [K TK].
    pose proof (typing_components _ _ _ _ TK) as [_ [L [r [HC TH]]]].
    eapply kind_open with (L:=L) (r:=r) (H:=HC); eassumption.
  - destruct IHTyping1 as [K TK]. eexists. eapply T_sum; eassumption.
  - destruct IHTyping1 as [K TK]. eexists. eapply T_sum; eassumption.
  - destruct IHTyping1 as [K TK]. eexists. eapply T_Sigma; eassumption.
Qed.

(* A value's introduction rule provides the premises for its reduction
   and a usage context bounded by the original typing context. *)
Inductive introduction (E : D) : context -> tm -> tm -> Prop :=
| intro_type : forall G t, ty t -> introduction E G t a_Type
| intro_unit : introduction E (pack E (fun _ => 0)) a_TmUnit a_TyUnit
| intro_lam : forall L G q A a B H,
    Typing E H A a_Type ->
    (forall x, x \notin L ->
      Typing ((x,Tm A)::E) ((x,(q,Tm A))::G)
        (open_tm_wrt_tm a (a_Var_f x)) (open_tm_wrt_tm B (a_Var_f x))) ->
    introduction E G (a_Lam q A a) (a_Pi q A B)
| intro_box : forall G q a A,
    Typing E G a A ->
    introduction E (ctx_mul q G) (a_box q a) (a_Box q A)
| intro_inj1 : forall G a A B,
    Typing E G a A -> introduction E G (a_Inj1 a) (a_Sum A B)
| intro_inj2 : forall G a A B,
    Typing E G a B -> introduction E G (a_Inj2 a) (a_Sum A B)
| intro_tensor : forall G H q a b A B,
    Typing E G a A -> Typing E H b (open_tm_wrt_tm B a) ->
    introduction E (ctx_plus (ctx_mul q G) H) (a_Tensor a b) (a_Sigma q A B).

Lemma introduction_weak : forall E x C K G a A,
  x \notin dom E -> Typing E K C a_Type -> introduction E G a A ->
  introduction ((x,Tm C)::E) ((x,(0,Tm C))::G) a A.
Proof.
  intros E x C K G a A Fx TC I. destruct I.
  - constructor; assumption.
  - constructor.
  - eapply intro_lam with (L:=L \u {{x}}); [eapply T_weak; eassumption|].
    intros y Fy; eapply typing_weak_binder;
      [set_fresh|assumption|eassumption|apply H1; set_fresh].
  - replace ((x,(0,Tm C))::ctx_mul q G) with (ctx_mul q ((x,(0,Tm C))::G))
      by (simpl; now rewrite qmul_0_r).
    apply intro_box. eapply T_weak; eassumption.
  - apply intro_inj1. eapply T_weak; eassumption.
  - apply intro_inj2. eapply T_weak; eassumption.
  - replace ((x,(0,Tm C))::ctx_plus (ctx_mul q G) H) with
      (ctx_plus (ctx_mul q ((x,(0,Tm C))::G)) ((x,(0,Tm C))::H))
        by (simpl; now rewrite qmul_0_r, qplus_0_l).
    apply intro_tensor; eapply T_weak; eassumption.
Qed.

Lemma intro_refl : forall E G a A,
  Typing E G a A -> introduction E G a A ->
  exists H C, introduction E H a C /\ ctx_sub E H G /\ Beta C A.
Proof.
  intros. exists G, A. repeat split; eauto using ctx_sub_refl, Typing_ctx, B_Refl, Typing_lc_type.
Qed.

Lemma typing_introduction : forall E G a A,
  Typing E G a A -> value a ->
  exists H C, introduction E H a C /\ ctx_sub E H G /\ Beta C A.
Proof.
  induction 1; intros V.
  - destruct (IHTyping V) as [J [C [I [HC BC]]]].
    exists J, C. eauto using ctx_sub_trans.
  - eapply intro_refl; [apply T_type|constructor; constructor].
  - inversion V; subst; match goal with H : ty (a_Var_f _) |- _ => inversion H end.
  - destruct (IHTyping1 V) as [J [C [I [HC BC]]]].
    exists ((x,(0,Tm A))::J), C.
    repeat split; [eapply introduction_weak; eassumption|constructor; auto using qleb_refl|assumption].
  - eapply intro_refl; [eapply T_pi; eassumption|constructor; constructor].
  - eapply intro_refl; [eapply T_lam; eassumption|eapply intro_lam; eassumption].
  - inversion V; subst; match goal with H : ty (a_App _ _) |- _ => inversion H end.
  - destruct (IHTyping1 V) as [J [C [I [HC BC]]]].
    exists J, C. eauto using B_Trans.
  - eapply intro_refl; [apply T_unit|constructor].
  - eapply intro_refl; [apply T_Unit|constructor; constructor].
  - inversion V; subst; match goal with H : ty (a_letunitB _ _ _) |- _ => inversion H end.
  - eapply intro_refl; [eapply T_Box; eassumption|constructor; constructor].
  - eapply intro_refl; [eapply T_box; eassumption|apply intro_box; assumption].
  - inversion V; subst; match goal with H : ty (a_LetBoxB _ _ _) |- _ => inversion H end.
  - eapply intro_refl; [eapply T_sum; eassumption|constructor; constructor].
  - eapply intro_refl; [eapply T_inj1; eassumption|apply intro_inj1; assumption].
  - eapply intro_refl; [eapply T_inj2; eassumption|apply intro_inj2; assumption].
  - inversion V; subst; match goal with H : ty (a_Case _ _ _ _ _) |- _ => inversion H end.
  - eapply intro_refl; [eapply T_Sigma; eassumption|constructor; constructor].
  - eapply intro_refl; [eapply T_Tensor; eassumption|eapply intro_tensor; eassumption].
  - inversion V; subst; match goal with H : ty (a_Spread _ _ _) |- _ => inversion H end.
Qed.

Lemma retype : forall E G a A B,
  Typing E G a A -> (exists H, Typing E H B a_Type) -> Beta A B ->
  Typing E G a B.
Proof. intros E G a A B T [H K] C. eapply T_conv; eassumption. Qed.

Lemma type_components : forall E G a A, Typing E G a A -> components E A.
Proof.
  intros. destruct (typing_regular _ _ _ _ H) as [K TK].
  eapply typing_components; eassumption.
Qed.

Lemma beta_open_same : forall L B C u,
  lc_tm u ->
  (forall x, x \notin L -> Beta (open_tm_wrt_tm B (a_Var_f x)) (open_tm_wrt_tm C (a_Var_f x))) ->
  Beta (open_tm_wrt_tm B u) (open_tm_wrt_tm C u).
Proof.
  intros L B C u Hu H. fresh_atom x (L \u fv_tm_tm B \u fv_tm_tm C).
  rewrite (open_intro B u x), (open_intro C u x) by set_fresh.
  apply subst_Beta1; [exact Hu|apply H; set_fresh].
Qed.

Lemma beta_pi_open : forall q A B r C F u,
  Beta (a_Pi q A B) (a_Pi r C F) -> lc_tm u ->
  Beta (open_tm_wrt_tm B u) (open_tm_wrt_tm F u).
Proof. intros; eapply beta_open_same; eauto using invert_Beta_a_Pi2. Qed.

Lemma beta_sigma_open : forall q A B r C F u,
  Beta (a_Sigma q A B) (a_Sigma r C F) -> lc_tm u ->
  Beta (open_tm_wrt_tm B u) (open_tm_wrt_tm F u).
Proof. intros; eapply beta_open_same; eauto using invert_Beta_a_Sigma2. Qed.

Lemma beta_motive_step : forall E G t B a a',
  Typing E G t (open_tm_wrt_tm B a) -> Step a a' ->
  Beta (open_tm_wrt_tm B a') (open_tm_wrt_tm B a).
Proof.
  intros E G t B a a' T S.
  pose proof (lc_scoped _ (Typing_lc_type _ _ _ _ T)) as H.
  apply scoped_open_inv in H.
  fresh_atom x (fv_tm_tm B).
  rewrite (open_intro B a x), (open_intro B a' x) by assumption.
  apply subst_Beta2.
  - apply scoped_lc, scoped_open_zero; [assumption|exact I].
  - apply B_Sym, B_Step; assumption.
Qed.

Lemma ctx_zero_left : forall E G, ctx E G ->
  ctx_plus (pack E (fun _ => 0)) G = G.
Proof.
  induction 1; simpl; auto. rewrite qplus_0_l, IHctx. reflexivity.
Qed.

Lemma preservation_app_beta : forall E F U q A B r C b u,
  Typing E F (a_Lam r C b) (a_Pi q A B) ->
  Typing E U u A ->
  Typing E (ctx_plus F (ctx_mul q U)) (open_tm_wrt_tm b u) (open_tm_wrt_tm B u).
Proof.
  intros E F U q A B r C b u T V.
  destruct (typing_introduction _ _ _ _ T (val_lam r C b)) as [G [K [I [Le BC]]]].
  inversion I; subst; clear I; try match goal with H : ty _ |- _ => inversion H end.
  match goal with H : Beta (a_Pi ?r _ _) (a_Pi ?q _ _) |- _ =>
    pose proof (invert_Beta_a_Pi0 H); subst r
  end.
  assert (VC : Typing E U u C).
  { eapply retype; [exact V|eauto|]. apply B_Sym. eapply invert_Beta_a_Pi1; eassumption. }
  eapply T_sub.
  - eapply retype.
    + eapply typing_open; eassumption.
    + eapply typing_regular. eapply T_app; eassumption.
    + eapply beta_pi_open; eauto using Typing_lc.
  - apply ctx_sub_add; eauto using ctx_sub_refl, ctx_scale, Typing_ctx.
Qed.

Lemma preservation_unit_beta : forall E G H b B,
  Typing E G a_TmUnit a_TyUnit ->
  Typing E H b (open_tm_wrt_tm B a_TmUnit) ->
  Typing E (ctx_plus G H) b (open_tm_wrt_tm B a_TmUnit).
Proof.
  intros E G H b B T V.
  destruct (typing_introduction _ _ _ _ T val_unit) as [J [C [I [Le BC]]]].
  inversion I; subst; try match goal with H : ty _ |- _ => inversion H end.
  eapply T_sub; [exact V|].
  rewrite <- ctx_zero_left at 1 by ctx_fact.
  apply ctx_sub_add; eauto using ctx_sub_refl, Typing_ctx.
Qed.

Lemma preservation_box_beta : forall E F G q r u A b B L,
  Typing E F (a_box r u) (a_Box q A) ->
  (forall x, x \notin L -> Typing ((x,Tm A)::E) ((x,(q,Tm A))::G)
     (open_tm_wrt_tm b (a_Var_f x)) (open_tm_wrt_tm B (a_box q (a_Var_f x)))) ->
  Typing E (ctx_plus F G) (open_tm_wrt_tm b u) (open_tm_wrt_tm B (a_box r u)).
Proof.
  intros E F G q r u A b B L T Tb.
  destruct (typing_introduction _ _ _ _ T (val_box r u)) as [J [C [I [Le BC]]]].
  inversion I; subst; clear I; try match goal with H : ty _ |- _ => inversion H end.
  pose proof (invert_Beta_Box2 BC); subst r.
  assert (U : exists K, Typing E K u A /\ ctx_sub E (ctx_mul q K) F).
  { eexists; split; [|exact Le]. eapply retype; [eassumption| |eapply invert_Beta_Box1; exact BC].
    exact (type_components _ _ _ _ T). }
  destruct U as [K [TK LK]].
  fresh_atom x (L \u dom E \u fv_tm_tm B \u fv_tm_tm b).
  assert (Fx : x \notin dom E) by set_fresh.
  pose proof (typing_subst_head _ _ _ _ _ _ _ _ _ Fx TK (Tb x ltac:(set_fresh))) as S.
  rewrite <- (open_intro b u x) in S by set_fresh.
  rewrite subst_open, (subst_fresh B) in S by (solve [set_fresh | eauto using Typing_lc]).
  change (subst_tm_tm u x (a_box q (a_Var_f x))) with (a_box q (subst_tm_tm u x (a_Var_f x))) in S.
  rewrite subst_var_same in S.
  eapply T_sub; [exact S|].
  assert (CG : ctx E G).
  { pose proof (Typing_ctx _ _ _ _ (Tb x ltac:(set_fresh))) as HC. inversion HC; assumption. }
  rewrite (ctx_plus_comm E G (ctx_mul q K)) by ctx_fact.
  apply ctx_sub_add; auto using ctx_sub_refl.
Qed.

Lemma eq_open_inj1 : forall L B C u,
  lc_tm u ->
  (forall x, x \notin L ->
    open_tm_wrt_tm C (a_Var_f x) = open_tm_wrt_tm B (a_Inj1 (a_Var_f x))) ->
  open_tm_wrt_tm C u = open_tm_wrt_tm B (a_Inj1 u).
Proof.
  intros L B C u Hu H.
  fresh_atom x (L \u fv_tm_tm B \u fv_tm_tm C).
  rewrite (open_intro C u x) by set_fresh. rewrite H by set_fresh.
  rewrite subst_open, (subst_fresh B) by (assumption || set_fresh).
  change (subst_tm_tm u x (a_Inj1 (a_Var_f x))) with (a_Inj1 (subst_tm_tm u x (a_Var_f x))).
  now rewrite subst_var_same.
Qed.

Lemma eq_open_inj2 : forall L B C u,
  lc_tm u ->
  (forall x, x \notin L ->
    open_tm_wrt_tm C (a_Var_f x) = open_tm_wrt_tm B (a_Inj2 (a_Var_f x))) ->
  open_tm_wrt_tm C u = open_tm_wrt_tm B (a_Inj2 u).
Proof.
  intros L B C u Hu H.
  fresh_atom x (L \u fv_tm_tm B \u fv_tm_tm C).
  rewrite (open_intro C u x) by set_fresh. rewrite H by set_fresh.
  rewrite subst_open, (subst_fresh B) by (assumption || set_fresh).
  change (subst_tm_tm u x (a_Inj2 (a_Var_f x))) with (a_Inj2 (subst_tm_tm u x (a_Var_f x))).
  now rewrite subst_var_same.
Qed.

Lemma case_budget : forall (E : D) F G H q,
  ctx_sub E G F -> ctx E H ->
  ctx_sub E (ctx_plus H (ctx_mul q G)) (ctx_plus (ctx_mul q F) H).
Proof.
  intros. rewrite (ctx_plus_comm E H (ctx_mul q G)) by ctx_fact.
  apply ctx_sub_add; auto using ctx_sub_mul, ctx_sub_refl.
Qed.

Lemma preservation_case1_beta : forall E F G A C b B B1 u L q,
  Typing E F (a_Inj1 u) (a_Sum A C) ->
  Typing E G b (a_Pi q A B1) ->
  (forall x, x \notin L ->
    open_tm_wrt_tm B1 (a_Var_f x) = open_tm_wrt_tm B (a_Inj1 (a_Var_f x))) ->
  Typing E (ctx_plus (ctx_mul q F) G) (a_App b u) (open_tm_wrt_tm B (a_Inj1 u)).
Proof.
  intros E F G A C b B B1 u L q T Tb He.
  destruct (typing_introduction _ _ _ _ T (val_inj1 u)) as [J [K [I [Le BC]]]].
  inversion I; subst; clear I; try match goal with H : ty _ |- _ => inversion H end.
  assert (TU : Typing E J u A).
  { eapply retype; [eassumption| |eauto using invert_Beta_Sum1].
    exact (proj1 (type_components _ _ _ _ T)). }
  rewrite <- (eq_open_inj1 L B B1 u) by eauto using Typing_lc.
  eapply T_sub; [eapply T_app; eassumption|].
  apply case_budget; eauto using Typing_ctx.
Qed.

Lemma preservation_case2_beta : forall E F G A C b B B2 u L q,
  Typing E F (a_Inj2 u) (a_Sum A C) ->
  Typing E G b (a_Pi q C B2) ->
  (forall x, x \notin L ->
    open_tm_wrt_tm B2 (a_Var_f x) = open_tm_wrt_tm B (a_Inj2 (a_Var_f x))) ->
  Typing E (ctx_plus (ctx_mul q F) G) (a_App b u) (open_tm_wrt_tm B (a_Inj2 u)).
Proof.
  intros E F G A C b B B2 u L q T Tb He.
  destruct (typing_introduction _ _ _ _ T (val_inj2 u)) as [J [K [I [Le BC]]]].
  inversion I; subst; clear I; try match goal with H : ty _ |- _ => inversion H end.
  assert (TU : Typing E J u C).
  { eapply retype; [eassumption| |eauto using invert_Beta_Sum2].
    exact (proj2 (type_components _ _ _ _ T)). }
  rewrite <- (eq_open_inj2 L B B2 u) by eauto using Typing_lc.
  eapply T_sub; [eapply T_app; eassumption|].
  apply case_budget; eauto using Typing_ctx.
Qed.

Lemma ctx_mul_one : forall G : context, ctx_mul 1 G = G.
Proof. induction G as [|[x [r A]] G IH]; simpl; auto. now rewrite qmul_1_l, IH. Qed.

Lemma subst_tensor_motive1 : forall B a x y,
  x <> y -> x \notin fv_tm_tm B -> lc_tm a ->
  subst_tm_tm a x (open_tm_wrt_tm B (a_Tensor (a_Var_f x) (a_Var_f y))) =
  open_tm_wrt_tm B (a_Tensor a (a_Var_f y)).
Proof.
  intros. rewrite subst_open, (subst_fresh B) by assumption.
  change (open_tm_wrt_tm B (a_Tensor (subst_tm_tm a x (a_Var_f x)) (subst_tm_tm a x (a_Var_f y))) = open_tm_wrt_tm B (a_Tensor a (a_Var_f y))).
  now rewrite subst_var_same, subst_var_other.
Qed.

Lemma subst_tensor_motive2 : forall B a b y,
  y \notin fv_tm_tm B -> y \notin fv_tm_tm a -> lc_tm b ->
  subst_tm_tm b y (open_tm_wrt_tm B (a_Tensor a (a_Var_f y))) =
  open_tm_wrt_tm B (a_Tensor a b).
Proof.
  intros. rewrite subst_open, (subst_fresh B) by assumption.
  change (open_tm_wrt_tm B (a_Tensor (subst_tm_tm b y a) (subst_tm_tm b y (a_Var_f y))) = open_tm_wrt_tm B (a_Tensor a b)).
  now rewrite (subst_fresh a), subst_var_same.
Qed.

Lemma preservation_spread_beta : forall E F G a0 a1 b A1 A2 B L q,
  Typing E F (a_Tensor a0 a1) (a_Sigma q A1 A2) ->
  (forall x, x \notin L -> forall y, y \notin L \u {{x}} ->
     Typing ((x,Tm A1)::E) ((x,(q,Tm A1))::G) (open_tm_wrt_tm b (a_Var_f x))
       (a_Pi 1 (open_tm_wrt_tm A2 (a_Var_f x))
         (close_tm_wrt_tm y (open_tm_wrt_tm B (a_Tensor (a_Var_f x) (a_Var_f y)))))) ->
  Typing E (ctx_plus F G) (a_App (open_tm_wrt_tm b a0) a1)
    (open_tm_wrt_tm B (a_Tensor a0 a1)).
Proof.
  intros E F G a0 a1 b A1 A2 B L q T Tb.
  destruct (typing_introduction _ _ _ _ T (val_tensor a0 a1)) as [J [C [I [Le BC]]]].
  inversion I; subst; clear I; try match goal with H : ty _ |- _ => inversion H end.
  match goal with H : Beta (a_Sigma ?r _ _) (a_Sigma ?q _ _) |- _ =>
    pose proof (invert_Beta_a_Sigma0 H); subst r
  end.
  destruct (type_components _ _ _ _ T) as [KA [L' [r [K KB]]]].
  assert (W : exists G0 G1, Typing E G0 a0 A1 /\
    Typing E G1 a1 (open_tm_wrt_tm A2 a0) /\ ctx_sub E (ctx_plus (ctx_mul q G0) G1) F).
  { do 2 eexists. split.
    - eapply retype; [eassumption|exact KA|eauto using invert_Beta_a_Sigma1].
    - split; [|exact Le].
      eapply retype; [eassumption|eauto using kind_open, retype, invert_Beta_a_Sigma1|].
      eapply beta_sigma_open; eauto using Typing_lc. }
  destruct W as [U0 [U1 [T0 [T1 LW]]]].
  fresh_atom x (L \u dom E \u fv_tm_tm b \u fv_tm_tm A2 \u fv_tm_tm B).
  fresh_atom y (L \u {{x}} \u fv_tm_tm B \u fv_tm_tm a0).
  pose proof (Tb x ltac:(set_fresh) y ltac:(set_fresh)) as TF.
  assert (Fx : x \notin dom E) by set_fresh.
  pose proof (typing_subst_head _ _ _ _ _ _ _ _ _ Fx T0 TF) as S.
  rewrite <- (open_intro b a0 x) in S by set_fresh.
  cbn [subst_tm_tm] in S.
  rewrite <- (open_intro A2 a0 x) in S by set_fresh.
  rewrite subst_close, subst_tensor_motive1 in S by
    (solve [set_fresh | eauto using Typing_lc]).
  pose proof (T_app _ _ _ _ _ _ _ _ S T1) as V.
  rewrite open_close, subst_tensor_motive2, ctx_mul_one in V by
    (solve [set_fresh | eauto using Typing_lc]).
  assert (CG : ctx E G).
  { pose proof (Typing_ctx _ _ _ _ TF) as HC. inversion HC; assumption. }
  eapply T_sub; [exact V|].
  rewrite <- (ctx_plus_assoc E G (ctx_mul q U0) U1) by ctx_fact.
  rewrite (ctx_plus_comm E G (ctx_plus (ctx_mul q U0) U1)) by ctx_fact.
  apply ctx_sub_add; auto using ctx_sub_refl.
Qed.

Ltac preserve_dependent original rule :=
  eapply retype;
  [ solve [eapply rule; eassumption || eauto; reflexivity]
  | eapply typing_regular; exact original
  | eapply beta_motive_step; [exact original|eassumption] ].

Theorem preservation: forall D G a A, Typing D G a A -> forall a', Step a a' -> Typing D G a' A.
Proof.
  intros E G a A T. induction T; intros v S;
    try solve [eapply T_sub; eauto | eapply T_weak; eauto | eapply T_conv; eauto];
    inversion S; subst.
  - eapply T_app; eauto.
  - eapply preservation_app_beta; eassumption.
  - assert (Old : Typing D5 (ctx_plus G1 G2) (a_letunitB a b (a_Lam r a_TyUnit B))
        (open_tm_wrt_tm B a)) by (eapply T_UnitE; eauto).
    preserve_dependent Old T_UnitE.
  - eapply preservation_unit_beta; eassumption.
  - assert (Old : Typing D5 (ctx_plus G1 G2) (a_LetBoxB a b (a_Lam r (a_Box q A) B))
        (open_tm_wrt_tm B a)) by (eapply T_letbox; eauto).
    preserve_dependent Old T_letbox.
  - eapply preservation_box_beta; eassumption.
  - assert (Old : Typing D5 (ctx_plus (ctx_mul q G1) G2)
       (a_Case q a b1 b2 (a_Lam r (a_Sum A1 A2) B)) (open_tm_wrt_tm B a))
        by (eapply T_case; eauto).
    preserve_dependent Old T_case.
  - eapply preservation_case1_beta; eassumption.
  - eapply preservation_case2_beta; eassumption.
  - assert (Old : Typing D5 (ctx_plus G1 G2)
        (a_Spread a b (a_Lam r (a_Sigma q A1 A2) B)) (open_tm_wrt_tm B a))
        by (eapply T_Spread; eauto).
    preserve_dependent Old T_Spread.
  - eapply preservation_spread_beta; eassumption.
Qed.

Ltac canonical T V :=
  let G := fresh "G" in let A := fresh "A" in let I := fresh "I" in
  let Le := fresh "Le" in let B := fresh "B" in
  destruct (typing_introduction _ _ _ _ T V) as [G [A [I [Le B]]]];
  inversion I; subst; clear I;
  match type of B with
  | Beta ?C ?D =>
      let X := fresh "X" in
      pose proof (Beta_consistent C D B ltac:(repeat constructor) ltac:(repeat constructor)) as X;
      inversion X; subst; eauto 8
  end.

Lemma canonical_pi : forall E G a q A B,
  Typing E G a (a_Pi q A B) -> value a ->
  exists r C b, a = a_Lam r C b.
Proof. intros E G a q A B T V; canonical T V. Qed.

Lemma canonical_unit : forall E G a,
  Typing E G a a_TyUnit -> value a -> a = a_TmUnit.
Proof. intros E G a T V; canonical T V. Qed.

Lemma canonical_box : forall E G a q A,
  Typing E G a (a_Box q A) -> value a ->
  exists r b, a = a_box r b.
Proof. intros E G a q A T V; canonical T V. Qed.

Lemma canonical_sum : forall E G a A B,
  Typing E G a (a_Sum A B) -> value a ->
  (exists b, a = a_Inj1 b) \/ (exists b, a = a_Inj2 b).
Proof. intros E G a A B T V; canonical T V. Qed.

Lemma canonical_sigma : forall E G a q A B,
  Typing E G a (a_Sigma q A B) -> value a ->
  exists b c, a = a_Tensor b c.
Proof. intros E G a q A B T V; canonical T V. Qed.

Theorem progress : forall a A,
  Typing nil nil a A -> value a \/ exists a', Step a a'.
Proof.
  enough (H : forall E G a A, Typing E G a A -> E = nil ->
    value a \/ exists a', Step a a') by eauto.
  induction 1; intros Eq; subst; try discriminate;
    try solve [auto | left; repeat constructor].
  - destruct (IHTyping1 Logic.eq_refl) as [V|[a' S]]; right.
    + destruct (canonical_pi _ _ _ _ _ _ H V) as [r [C [b0 ->]]].
      eexists. apply S_Beta; eauto using Typing_lc.
      pose proof (Typing_lc _ _ _ _ H) as LC. inversion LC; assumption.
    + eexists; eapply S_AppCong; eauto using Typing_lc.
  - assert (LM : lc_tm (a_Lam r a_TyUnit B)).
    { eapply Typing_lc.
      eapply (T_lam L nil G3 r a_TyUnit B a_Type nil); [eassumption|apply T_Unit]. }
    destruct (IHTyping1 Logic.eq_refl) as [V|[a' S]]; right.
    + pose proof (canonical_unit _ _ _ H V); subst a.
      exists b. apply S_UnitBeta; eauto using Typing_lc.
    + eexists; eapply S_UnitCong; eauto using Typing_lc.
  - assert (LC : lc_tm (a_LetBoxB a b (a_Lam r (a_Box q A) B))).
    { eapply Typing_lc. eapply T_letbox; eassumption. }
    assert (LM : lc_tm (a_Lam r (a_Box q A) B)) by (inversion LC; assumption).
    destruct (IHTyping Logic.eq_refl) as [V|[a' S]]; right.
    + destruct (canonical_box _ _ _ _ _ H V) as [r' [u ->]].
      eexists; eapply S_BoxBeta; eauto.
      pose proof (Typing_lc _ _ _ _ H) as LU. inversion LU; assumption.
    + eexists; eapply S_BoxCong; eauto.
  - assert (LC : lc_tm (a_Case q a b1 b2 (a_Lam r (a_Sum A1 A2) B))).
    { eapply Typing_lc. eapply T_case; eassumption. }
    inversion LC; subst.
    destruct (IHTyping1 Logic.eq_refl) as [V|[a' S]]; right.
    + destruct (canonical_sum _ _ _ _ _ H0 V) as [[u ->]|[u ->]];
        [eexists; eapply S_Case1Beta|eexists; eapply S_Case2Beta]; eauto;
        match goal with H : lc_tm (a_Inj1 _) |- _ => inversion H; assumption
                       | H : lc_tm (a_Inj2 _) |- _ => inversion H; assumption end.
    + eexists; eapply S_CaseCong; eauto.
  - assert (LC : lc_tm (a_Spread a b (a_Lam r (a_Sigma q A1 A2) B))).
    { eapply Typing_lc. eapply T_Spread; eauto. }
    assert (LM : lc_tm (a_Lam r (a_Sigma q A1 A2) B)) by (inversion LC; assumption).
    destruct (IHTyping Logic.eq_refl) as [V|[a' S]]; right.
    + match goal with T : Typing nil _ a (a_Sigma _ _ _) |- _ =>
        destruct (canonical_sigma _ _ _ _ _ _ T V) as [u [w ->]]
      end.
      eexists; eapply S_SpreadBeta; eauto;
        match goal with H : Typing _ _ (a_Tensor _ _) _ |- _ =>
          pose proof (Typing_lc _ _ _ _ H) as LT; inversion LT; assumption end.
    + eexists; eapply S_SpreadCong; eauto.
Qed.
