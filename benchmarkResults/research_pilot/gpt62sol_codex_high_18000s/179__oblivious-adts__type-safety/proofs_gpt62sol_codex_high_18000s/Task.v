From oadt Require Import lang_oadt.base.

From oadt Require Import lang_oadt.syntax.

From oadt Require Import lang_oadt.semantics.

From oadt Require Import lang_oadt.typing.

Import syntax.notations.

Import semantics.notations.

Import typing.notations.

Implicit Types (b : bool) (x X y Y : atom) (L : aset).

Definition stuck (Σ : gctx) (e : expr) : Prop :=
  nf (@step Σ) e /\ ¬val e.

#[local] Coercion EFVar : atom >-> expr.

Fixpoint names (e : expr) : aset :=
  match e with
  | EFVar x => {[x]}
  | EPi _ a b | EAbs _ a b | EProd a b | ESum _ a b | EApp a b
  | ELet a b | EPair a b | EInj _ _ a b => names a ∪ names b
  | EIte _ a b c | ECase _ a b c | EMux a b c => names a ∪ names b ∪ names c
  | EProj _ a | EFold _ a | EUnfold _ a | ESec a | ETape a => names a
  | _ => ∅
  end.

Fixpoint scoped (k : nat) (e : expr) : Prop :=
  match e with
  | EBVar n => n < k
  | EPi _ a b | EAbs _ a b | ELet a b => scoped k a /\ scoped (S k) b
  | ECase _ a b c => scoped k a /\ scoped (S k) b /\ scoped (S k) c
  | EProd a b | ESum _ a b | EApp a b | EPair a b | EInj _ _ a b =>
      scoped k a /\ scoped k b
  | EIte _ a b c | EMux a b c => scoped k a /\ scoped k b /\ scoped k c
  | EProj _ a | EFold _ a | EUnfold _ a | ESec a | ETape a => scoped k a
  | EBoxedInj _ a b => otval a /\ oval b
  | _ => True
  end.

Lemma scoped_open_inv e s k : scoped k (open_ k s e) -> scoped (S k) e.
Proof.
  revert k. induction e; intros d; simpl; try tauto;
    try solve [intuition eauto].
  case_decide; simpl; lia.
Qed.

Lemma scoped_mono e i j : scoped i e -> i <= j -> scoped j e.
Proof.
  revert i j. induction e; simpl; intros i j H N;
    try solve [tauto | lia];
    repeat match goal with H : _ /\ _ |- _ => destruct H end; repeat split; eauto using le_n_S.
Qed.

Lemma scoped_open e s k : scoped (S k) e -> scoped 0 s -> scoped k (open_ k s e).
Proof.
  revert k. induction e; intros d; simpl; try tauto;
    try solve [intuition eauto].
  case_decide; simpl; intros; [eapply scoped_mono; eauto; lia|lia].
Qed.

Lemma lc_scoped e : lc e -> scoped 0 e.
Proof.
  induction 1; simpl; try tauto;
    repeat match goal with
    | H : forall x : atom, x ∉ ?L -> scoped 0 (open _ ?e) |- _ =>
        let F := fresh "F" in
        pose proof (is_fresh L) as F;
        specialize (H (fresh L) F); apply scoped_open_inv in H
    end; tauto.
Qed.

Lemma open_scoped_id e s k : scoped k e -> open_ k s e = e.
Proof.
  revert k. induction e; intros d; simpl; try solve [intuition f_equal; eauto].
  case_decide; intros; [lia|reflexivity].
Qed.

Lemma open_lc e s k : lc e -> open_ k s e = e.
Proof. intros H. apply open_scoped_id, (scoped_mono _ 0); eauto using lc_scoped; lia. Qed.

Lemma subst_fresh x s e : x ∉ names e -> subst x s e = e.
Proof.
  induction e; simpl; intros H; try reflexivity;
    try solve [case_decide; [subst; set_solver|reflexivity]];
    f_equal; first [apply IHe | apply IHe1 | apply IHe2 | apply IHe3]; set_solver.
Qed.

Lemma subst_open_rec x s e t k :
  scoped 0 s -> subst x s (open_ k t e) = open_ k (subst x s t) (subst x s e).
Proof.
  revert k. induction e; intros; simpl; try solve [f_equal; eauto].
  - now case_decide.
  - case_decide; simpl; [symmetry; apply open_scoped_id; eapply scoped_mono; eauto; lia|reflexivity].
Qed.

Lemma subst_open x s e t :
  lc s -> subst x s (open t e) = open (subst x s t) (subst x s e).
Proof. unfold open. eauto using subst_open_rec, lc_scoped. Qed.

Lemma open_intro x s e k :
  x ∉ names e -> open_ k s e = subst x s (open_ k x e).
Proof.
  revert k. induction e; intros d H; simpl; try reflexivity.
  all: try solve [case_decide; simpl; [case_decide; congruence|reflexivity]].
  all: try solve [case_decide; [subst; exfalso; set_solver|reflexivity]].
  all: f_equal; first [apply IHe | apply IHe1 | apply IHe2 | apply IHe3]; set_solver.
Qed.

Fixpoint close_name (k : nat) (x : atom) (e : expr) : expr :=
  match e with
  | EFVar y => if decide (x = y) then EBVar k else e
  | <{ Π:{l}τ1, τ2 }> => <{ Π:{l}(,(close_name k x τ1)), ,(close_name (S k) x τ2) }>
  | <{ \:{l}τ => e }> => <{ \:{l}(,(close_name k x τ)) => ,(close_name (S k) x e) }>
  | <{ let e1 in e2 }> => <{ let ,(close_name k x e1) in ,(close_name (S k) x e2) }>
  | <{ case{l} e0 of e1 | e2 }> => <{ case{l} ,(close_name k x e0) of ,(close_name (S k) x e1) | ,(close_name (S k) x e2) }>

  | <{ e1 e2 }> => <{ (,(close_name k x e1)) (,(close_name k x e2)) }>
  | <{ s𝔹 e }> => <{ s𝔹 (,(close_name k x e)) }>
  | <{ if{l} e0 then e1 else e2 }> => <{ if{l} ,(close_name k x e0) then ,(close_name k x e1) else ,(close_name k x e2) }>
  | <{ τ1 * τ2 }> => <{ (,(close_name k x τ1)) * (,(close_name k x τ2)) }>
  | <{ (e1, e2) }> => <{ (,(close_name k x e1), ,(close_name k x e2)) }>
  | <{ π@b e }> => <{ π@b (,(close_name k x e)) }>
  | <{ τ1 +{l} τ2 }> => <{ (,(close_name k x τ1)) +{l} (,(close_name k x τ2)) }>
  | <{ inj{l}@b<τ> e }> => <{ inj{l}@b<(,(close_name k x τ))> (,(close_name k x e)) }>
  | <{ fold<X> e }> => <{ fold<X> (,(close_name k x e)) }>
  | <{ unfold<X> e }> => <{ unfold<X> (,(close_name k x e)) }>
  | <{ tape e }> => <{ tape (,(close_name k x e)) }>
  | <{ mux e0 e1 e2 }> => <{ mux (,(close_name k x e0)) (,(close_name k x e1)) (,(close_name k x e2)) }>
  | _ => e
  end.

Lemma open_close_subst e k x y :
  scoped k e -> open_ k y (close_name k x e) = subst x y e.
Proof.
  revert k. induction e; intros d H; simpl in *; try reflexivity.
  all: try solve [case_decide; [lia|reflexivity]].
  all: try solve [case_decide; simpl; [case_decide; congruence|reflexivity]].
  all: f_equal; intuition eauto.
Qed.

Fixpoint expr_size (e : expr) : nat :=
  match e with
  | EPi _ a b | EAbs _ a b | ELet a b | EProd a b | ESum _ a b
  | EApp a b | EPair a b | EInj _ _ a b => S (expr_size a + expr_size b)
  | EIte _ a b c | ECase _ a b c | EMux a b c =>
      S (expr_size a + expr_size b + expr_size c)
  | EProj _ a | EFold _ a | EUnfold _ a | ESec a | ETape a => S (expr_size a)
  | _ => 1
  end.

Lemma size_open_name e k x : expr_size (open_ k x e) = expr_size e.
Proof.
  revert k. induction e; intros; simpl; try case_decide;
    try rewrite ?IHe, ?IHe1, ?IHe2, ?IHe3; reflexivity.
Qed.

Lemma scoped_lc e : scoped 0 e -> lc e.
Proof.
  remember (expr_size e) as n eqn:E.
  revert e E. induction n as [n IH] using lt_wf_ind.
  destruct e; simpl in *; intros E H; simpl in E; try lia;
    repeat match goal with H : _ /\ _ |- _ => destruct H end;
    first [eapply LCPi with (L := ∅) | eapply LCAbs with (L := ∅)
          | eapply LCLet with (L := ∅) | eapply LCCase with (L1 := ∅) (L2 := ∅)
          | constructor]; try assumption.
  all: try solve [match goal with |- lc ?a => eapply (IH (expr_size a)); [lia| reflexivity | assumption] end].
  all: intros x _; match goal with |- lc ?a => eapply (IH (expr_size a)); [unfold open; rewrite size_open_name; lia |reflexivity|] end.
  all: apply scoped_open; simpl; tauto.
Qed.

Lemma scoped_subst x s e k : scoped 0 s -> scoped k e -> scoped k (subst x s e).
Proof.
  intros H. revert k. induction e; intros k' G; simpl in *; try tauto;
    try solve [intuition eauto].
  case_decide; eauto using scoped_mono, Nat.le_0_l.
Qed.

Lemma lc_subst x s e : lc s -> lc e -> lc (subst x s e).
Proof. intros. apply scoped_lc. auto using scoped_subst, lc_scoped. Qed.

Lemma otval_inert ω : otval ω ->
  lc ω /\ names ω = ∅ /\ (forall x s, subst x s ω = ω) /\
  (forall k s, open_ k s ω = ω).
Proof.
  induction 1; simpl in *; intuition (eauto using lc).
  all: try solve [f_equal; eauto].
  all: rewrite H5, H2; set_solver.
Qed.

Lemma oval_inert v : oval v ->
  lc v /\ names v = ∅ /\ (forall x s, subst x s v = v) /\
  (forall k s, open_ k s v = v).
Proof.
  induction 1; simpl in *; intuition (eauto using lc).
  all: try solve [f_equal; eauto].
  all: match goal with
    | A : names ?a = ∅, B : names ?b = ∅ |- names ?a ∪ names ?b = ∅ =>
        rewrite A, B; set_solver
    end.
Qed.

Lemma oval_lc v : oval v -> lc v.
Proof. intros H. exact (proj1 (oval_inert _ H)). Qed.

Lemma otval_lc v : otval v -> lc v.
Proof. intros H. exact (proj1 (otval_inert _ H)). Qed.

Lemma ovalty_values v ω : ovalty v ω -> oval v /\ otval ω.
Proof.
  induction 1; destruct b || idtac; simpl in *; intuition eauto 6 using oval, otval.
Qed.

Lemma names_open_sup e s k : names e ⊆ names (open_ k s e).
Proof.
  revert k. induction e; intros; simpl;
    try solve [set_solver | set_solver by eauto 2].
  all: try (case_decide; set_solver).
Qed.

Definition locally_named (Γ : tctx) e :=
  lc e /\ names e ⊆ (dom Γ : aset).

Lemma locally_named_binder Γ l τ L e :
  (forall x : atom, x ∉ L -> locally_named (<[x:=(l, τ)]>Γ) (open x e)) ->
  scoped 1 e /\ names e ⊆ (dom Γ : aset).
Proof.
  intros H. pose proof (is_fresh (L ∪ names e)) as F.
  set (x := fresh (L ∪ names e)) in *.
  destruct (H x ltac:(set_solver)) as [C N].
  split.
  - exact (scoped_open_inv _ _ _ (lc_scoped _ C)).
  - rewrite dom_insert_L in N.
    pose proof (names_open_sup e (EFVar x) 0) as U. unfold open in N. set_solver.
Qed.

Local Ltac split_hyps :=
  repeat match goal with H : _ /\ _ |- _ => destruct H end.

Lemma typing_names Σ :
  (forall Γ e l τ, typing Σ Γ e l τ -> locally_named Γ e) /\
  (forall Γ τ κ, kinding Σ Γ τ κ -> locally_named Γ τ).
Proof.
  apply typing_kinding_mutind; intros; unfold locally_named in *;
    repeat match goal with
    | H : forall x : atom, x ∉ ?L -> lc (open (EFVar x) ?a) /\
            names (open (EFVar x) ?a) ⊆ dom (<[x:=(?l,?t)]>?Γ) |- _ =>
        let B := fresh "B" in pose proof (locally_named_binder Γ l t L a H) as B;
        clear H
    end;
    split_hyps; split.
  all: try solve [eauto using lc].
  all: try solve [apply scoped_lc; simpl; intuition eauto using lc_scoped].
  all: try solve [apply elem_of_subseteq; intros z Z; simpl in Z;
                  apply elem_of_singleton in Z; subst; apply elem_of_dom; eauto].
  all: try solve [match goal with |- _ ⊆ _ =>
    repeat match goal with
    | H : _ ⊆ _ |- _ => revert H
    end;
    repeat match goal with
    | H : Prop |- _ => clear H
    | H : ?P |- _ => let T := type of P in unify T Prop; clear H
    end;
    intros; simpl; set_solver
  end].
  all: match goal with H : ovalty (EBoxedInj _ _ _) _ |- _ =>
    destruct (ovalty_values _ _ H) as [V _]; inversion V; eauto using lc
  end.
Qed.

Section WellFormed.
Context (Σ : gctx) (G : gctx_typing Σ).

Lemma global_fun x l τ e : Σ !! x = Some (DFun (l,τ) e) ->
  typing Σ ∅ e l τ /\ lc e /\ names e = ∅ /\ exists κ, kinding Σ ∅ τ κ.
Proof.
  intros H. pose proof (map_Forall_lookup_1 _ _ _ _ G H) as D.
  inversion D; subst.
  destruct (proj1 (typing_names Σ) _ _ _ _ ltac:(eassumption)) as [C N].
  rewrite dom_empty_L in N. split; [assumption|].
  split; [assumption|]. split; [set_solver|eauto].
Qed.

Lemma global_oadt x τ e : Σ !! x = Some (DOADT τ e) ->
  scoped 1 e /\ names e = ∅.
Proof.
  intros H. pose proof (map_Forall_lookup_1 _ _ _ _ G H) as D.
  inversion D; subst.
  match goal with
  | H : forall x : atom, x ∉ ?L -> kinding _ _ _ _ |- _ =>
    assert (forall x : atom, x ∉ L -> locally_named (<[x:=(false, τ)]>∅) (open x e))
      by (intros; apply (proj2 (typing_names Σ)) with (κ := KObliv);
          eapply H; eassumption)
  end.
  destruct (locally_named_binder _ _ _ _ _ ltac:(eassumption)) as [C N].
  rewrite dom_empty_L in N. split; [assumption|set_solver].
Qed.

Lemma binder_lc L e :
  (forall x : atom, x ∉ L -> lc (open x e)) -> scoped 1 e.
Proof.
  intros H. exact (scoped_open_inv _ _ _ (lc_scoped _ (H (fresh L) (is_fresh L)))).
Qed.

Lemma pared_lc e e' : pared Σ e e' -> lc e /\ lc e'.
Proof.
  induction 1; try match goal with T : lexpr |- _ => destruct T end; split_hyps;
    repeat match goal with
    | H : forall x : atom, x ∉ ?L -> lc (open (EFVar x) ?a) /\ lc (open (EFVar x) ?b) |- _ =>
      assert (scoped 1 a) by (eapply binder_lc; intros; apply (H _ ltac:(eassumption)));
      assert (scoped 1 b) by (eapply binder_lc; intros; apply (H _ ltac:(eassumption)));
      clear H
    | H : Σ !! _ = Some (DFun (?l, ?t) ?a) |- _ =>
      let C := fresh "C" in pose proof (global_fun _ _ _ _ H) as C; clear H
    | H : Σ !! _ = Some (DOADT _ _) |- _ =>
      let C := fresh "C" in pose proof (global_oadt _ _ _ H) as C; clear H
    | H : ovalty _ _ |- _ => apply ovalty_values in H
    | H : otval _ |- _ =>
      let C := fresh "C" in pose proof (proj1 (otval_inert _ H)) as C;
      let H' := fresh "H" in rename H into H'; revert H'
    | H : oval _ |- _ =>
      let C := fresh "C" in pose proof (proj1 (oval_inert _ H)) as C;
      let H' := fresh "H" in rename H into H'; revert H'
    end;
    intros; split_hyps; split; try solve [eauto 8 using lc].
  all: destruct b || idtac;
    apply scoped_lc; unfold open; simpl;
    intuition eauto 8 using lc_scoped, scoped_open, ovalty_values, oval_lc, otval_lc, otval.
Qed.

Lemma woval_subst x s v : woval v -> woval (subst x s v).
Proof. induction 1; simpl; eauto using woval. Qed.

Local Hint Constructors lc : oadt_lc.
Local Hint Constructors pared : oadt_par.

Local Ltac apply_subst_binder :=
  let y := fresh "y" in let N := fresh "N" in
  intros y N;
  match goal with H : forall z : atom, z ∉ ?L -> pared _ _ _ |- _ =>
    let F := fresh "F" in
    assert (F : y ∉ L) by (clear - N; set_solver);
    let Q := fresh "Q" in pose proof (H y F) as Q;
    rewrite !subst_open in Q by tauto; simpl in Q;
    rewrite !decide_False in Q by (clear - N; set_solver);
    exact Q
  end.

Lemma pared_subst_refl x s t e : pared Σ s t -> lc e ->
  pared Σ (subst x s e) (subst x t e).
Proof.
  intros P C. pose proof (pared_lc _ _ P) as LC.
  induction C; simpl; try solve [eauto 3 with oadt_par oadt_lc].
  - case_decide; eauto with oadt_par oadt_lc.
  - eapply RCgrPi with (L:=L ∪ {[x]}); [assumption|apply_subst_binder].
  - eapply RCgrAbs with (L:=L ∪ {[x]}); [assumption|apply_subst_binder].
  - eapply RCgrLet with (L:=L ∪ {[x]}); [assumption|apply_subst_binder].
  - eapply RCgrCase with (L1:=L1 ∪ {[x]}) (L2:=L2 ∪ {[x]});
      [assumption|apply_subst_binder|apply_subst_binder].
Qed.

Lemma subst_choose x s b e f :
  subst x s (if b then e else f) = if b then subst x s e else subst x s f.
Proof. by destruct b. Qed.

Lemma pared_subst x s t e e' : pared Σ s t -> pared Σ e e' ->
  pared Σ (subst x s e) (subst x t e').
Proof.
  intros P R. pose proof (pared_lc _ _ P) as LC.
  induction R; simpl; rewrite ?subst_choose, ?subst_open by tauto;
    try solve [eauto 4 using lc_subst, woval_subst, pared_subst_refl with oadt_par].
  all: try solve [eapply RApp with (L:=L ∪ {[x]});
      [assumption|apply_subst_binder|intuition eauto using lc_subst]].
  all: try solve [eapply RLet with (L:=L ∪ {[x]}); [assumption|apply_subst_binder]].
  all: try solve [eapply RCase with (L1:=L1 ∪ {[x]}) (L2:=L2 ∪ {[x]});
      [assumption|apply_subst_binder|apply_subst_binder|intuition eauto using lc_subst]].
  all: try solve [eapply ROIfCase with (L1:=L1 ∪ {[x]}) (L2:=L2 ∪ {[x]});
      [assumption|assumption|apply_subst_binder|apply_subst_binder]].
  all: try solve [first [eapply RCgrPi with (L:=L ∪ {[x]}) |
                        eapply RCgrAbs with (L:=L ∪ {[x]}) |
                        eapply RCgrLet with (L:=L ∪ {[x]})];
      [assumption|apply_subst_binder]].
  all: try solve [eapply RCgrCase with (L1:=L1 ∪ {[x]}) (L2:=L2 ∪ {[x]});
      [assumption|apply_subst_binder|apply_subst_binder]].
  all: try solve [
    match goal with T : lexpr |- _ => destruct T as [l τ] end;
    match goal with H : _ = Some (DFun (_,_) _) |- _ =>
      destruct (global_fun _ _ _ _ H) as [_ [_ [N _]]]
    end;
    rewrite subst_fresh by (rewrite N; set_solver); eauto with oadt_par].
  all: try solve [
    match goal with H : _ = Some (DOADT _ ?a) |- _ =>
      destruct (global_oadt _ _ _ H) as [_ N];
      rewrite (subst_fresh x t a) by (rewrite N; set_solver)
    end;
    eauto with oadt_par].
  all: try match goal with H : ovalty ?v1 _, H' : ovalty ?v2 _ |- _ =>
    destruct (ovalty_values _ _ H); destruct (ovalty_values _ _ H')
  end.
  all: repeat match goal with
    | H : oval ?v |- context[subst _ _ ?v] =>
        rewrite (proj1 (proj2 (proj2 (oval_inert _ H))))
    | H : otval ?v |- context[subst _ _ ?v] =>
        rewrite (proj1 (proj2 (proj2 (otval_inert _ H))))
    end.
  all: try solve [eauto 4 with oadt_par].
  all: try solve [eapply ROCase with (L1:=L1 ∪ {[x]}) (L2:=L2 ∪ {[x]});
    try assumption; apply_subst_binder].
Qed.

Lemma pared_open e e' a a' L :
  (forall x : atom, x ∉ L -> pared Σ (open x e) (open x e')) ->
  pared Σ a a' -> pared Σ (open a e) (open a' e').
Proof.
  intros H A. pose proof (is_fresh (L ∪ names e ∪ names e')) as F.
  set (x := fresh (L ∪ names e ∪ names e')) in *.
  unfold open at 1 2. rewrite (open_intro x a e), (open_intro x a' e') by set_solver.
  apply pared_subst; auto. apply H. set_solver.
Qed.

Lemma pared_binder_join e e1 e2 L1 L2 :
  (forall x : atom, x ∉ L1 -> forall z,
    pared Σ (open x e) z -> exists w, pared Σ (open x e1) w /\ pared Σ z w) ->
  (forall x : atom, x ∉ L2 -> pared Σ (open x e) (open x e2)) ->
  exists w L, forall x : atom, x ∉ L ->
    pared Σ (open x e1) (open x w) /\ pared Σ (open x e2) (open x w).
Proof.
  intros H P. pose proof (is_fresh (L1 ∪ L2 ∪ names e1 ∪ names e2)) as F.
  set (x := fresh (L1 ∪ L2 ∪ names e1 ∪ names e2)) in *.
  destruct (H x ltac:(set_solver) _ (P x ltac:(set_solver))) as [w [A B]].
  pose proof (lc_scoped _ (proj2 (pared_lc _ _ A))) as C.
  exists (close_name 0 x w), (∅ : aset). intros y _.
  unfold open. rewrite open_close_subst by assumption.
  rewrite (open_intro x y e1), (open_intro x y e2) by set_solver.
  split; eapply pared_subst; eauto with oadt_par oadt_lc.
Qed.

Lemma pared_box_lit b e : pared Σ (EBoxedLit b) e -> e = EBoxedLit b.
Proof. inversion 1; reflexivity. Qed.

Lemma pared_box_inj b ω v e : pared Σ (EBoxedInj b ω v) e -> e = EBoxedInj b ω v.
Proof. inversion 1; reflexivity. Qed.

Lemma pared_lit b e : pared Σ (ELit b) e -> e = ELit b.
Proof. inversion 1; reflexivity. Qed.

Lemma woval_pared v v' : woval v -> pared Σ v v' -> woval v'.
Proof.
  intros W. revert v'. induction W; intros v' P; inversion P; subst;
    eauto using woval.
  all: try match goal with H : pared _ (EBoxedLit _) _ |- _ => apply pared_box_lit in H; subst end.
  all: try destruct b; eauto using woval.
Qed.

Lemma otval_irreducible e t : otval e -> pared Σ e t -> t = e.
Proof.
  intros V. revert t. induction V; intros t P; inversion P; subst;
    f_equal; eauto.
Qed.

Lemma oval_irreducible e t : oval e -> pared Σ e t -> t = e.
Proof.
  intros V. revert t. induction V; intros t P; inversion P; subst;
    f_equal; eauto.
Qed.

Lemma pared_unit_v e : pared Σ EUnitV e -> e = EUnitV.
Proof. inversion 1; reflexivity. Qed.

Lemma reflexive_body t L : scoped 1 t -> forall x : atom, x ∉ L -> pared Σ (open x t) (open x t).
Proof. intros C x _. apply RRefl, scoped_lc, scoped_open; simpl; auto. Qed.

Lemma pared_open_same t a c : scoped 1 t -> pared Σ a c -> pared Σ (open a t) (open c t).
Proof. intros C P. eapply pared_open with (L := ∅ : aset); eauto using reflexive_body. Qed.

Lemma ovalty_lc v ω : ovalty v ω -> lc v.
Proof. intros O. exact (oval_lc _ (proj1 (ovalty_values _ _ O))). Qed.

Local Ltac invert_pared :=
  repeat match goal with
  | H : pared _ (ELit _) _ |- _ => apply pared_lit in H; subst
  | H : pared _ (EBoxedLit _) _ |- _ => apply pared_box_lit in H; subst
  | H : pared _ (EBoxedInj _ _ _) _ |- _ => apply pared_box_inj in H; subst
  | H : pared _ EUnitV _ |- _ => apply pared_unit_v in H; subst
  | H : pared _ ?a _, V : otval ?a |- _ => apply (otval_irreducible _ _ V) in H; subst
  | H : pared _ ?a _, V : oval ?a |- _ => apply (oval_irreducible _ _ V) in H; subst
  end.

Lemma pared_choose b a a' c c' :
  pared Σ a a' -> pared Σ c c' ->
  pared Σ (if b then a else c) (if b then a' else c').
Proof. by destruct b. Qed.

Local Ltac make_join :=
  solve [eauto 7 using pared_choose, pared_open, woval_pared with oadt_par oadt_lc].

Lemma pared_left_lc e e' : pared Σ e e' -> lc e.
Proof. intro H. exact (proj1 (pared_lc _ _ H)). Qed.

Lemma pared_right_lc e e' : pared Σ e e' -> lc e'.
Proof. intro H. exact (proj2 (pared_lc _ _ H)). Qed.

Local Ltac common_binder e f :=
  lazymatch goal with
  | A : forall x : atom, x ∉ _ -> pared _ (open (EFVar x) e) (open (EFVar x) ?m),
    B : forall x : atom, x ∉ _ -> pared _ (open (EFVar x) f) (open (EFVar x) ?m) |- _ =>
      constr:(m)
  | _ => lazymatch constr:((e,f)) with (?a, ?a) => constr:(a) end
  end.

Local Ltac common_term e f :=
  lazymatch goal with
  | A : pared _ e ?m, B : pared _ f ?m |- _ => constr:(m)
  | A : pared _ e f |- _ => constr:(f)
  | A : pared _ f e |- _ => constr:(e)
  | _ =>
    lazymatch constr:((e,f)) with
    | (?a, ?a) => constr:(a)
    | (EApp ?a ?b, EApp ?c ?d) =>
      let u := common_term a c in let v := common_term b d in constr:(EApp u v)
    | (EIte ?l ?a ?b ?p, EIte ?l ?c ?d ?q) =>
      let u := common_term a c in let v := common_term b d in let w := common_term p q in
      constr:(EIte l u v w)
    | (ECase ?l ?a ?b ?p, ECase ?l ?c ?d ?q) =>
      let u := common_term a c in let v := common_binder b d in let w := common_binder p q in
      constr:(ECase l u v w)
    | (ESec ?a, ESec ?c) => let u := common_term a c in constr:(ESec u)
    | (EProj ?b ?a, EProj ?b ?c) => let u := common_term a c in constr:(EProj b u)
    | (EUnfold ?b ?a, EUnfold ?b ?c) => let u := common_term a c in constr:(EUnfold b u)
    | (ETape ?a, ETape ?c) => let u := common_term a c in constr:(ETape u)
    | (EMux ?a ?b ?p, EMux ?c ?d ?q) =>
      let u := common_term a c in let v := common_term b d in let w := common_term p q in
      constr:(EMux u v w)
    | (EPair ?a ?b, EPair ?c ?d) =>
      let u := common_term a c in let v := common_term b d in constr:(EPair u v)
    | (open ?a ?b, open ?c ?d) =>
      let u := common_term a c in let v := common_binder b d in constr:(open u v)
    end
  end.

Local Ltac strip_cond e :=
  lazymatch e with
  | EIte true (EBoxedLit true) ?a _ => constr:(a)
  | EIte true (EBoxedLit false) _ ?c => constr:(c)
  | EMux (EBoxedLit true) ?a _ => constr:(a)
  | EMux (EBoxedLit false) _ ?c => constr:(c)
  | _ => constr:(e)
  end.

Local Ltac spread_cond e :=
  lazymatch e with
  | EApp (EIte true ?q ?a ?c) ?u => constr:(EIte true q (EApp a u) (EApp c u))
  | ESec (EIte true ?q ?a ?c) => constr:(EIte true q (ESec a) (ESec c))
  | EIte false (EIte true ?q ?a ?c) ?u ?v =>
      constr:(EIte true q (EIte false a u v) (EIte false c u v))
  | EProj ?k (EIte true ?q ?a ?c) => constr:(EIte true q (EProj k a) (EProj k c))
  | ECase false (EIte true ?q ?a ?c) ?u ?v =>
      constr:(EIte true q (ECase false a u v) (ECase false c u v))
  | EUnfold ?k (EIte true ?q ?a ?c) => constr:(EIte true q (EUnfold k a) (EUnfold k c))
  | ETape (EIte true ?q ?a ?c) => constr:(EMux q (ETape a) (ETape c))
  | ETape (EPair ?a ?c) => constr:(EPair (ETape a) (ETape c))
  | ECase false (EInj false true _ ?a) ?u _ => constr:(open a u)
  | ECase false (EInj false false _ ?a) _ ?v => constr:(open a v)
  | _ => constr:(e)
  end.

Lemma pared_oif_selected b a c q :
  pared Σ (if b then a else c) q -> lc (if b then c else a) ->
  pared Σ (EIte true (EBoxedLit b) a c) q.
Proof.
  destruct b; simpl; intros P C.
  - exact (ROIf Σ true a c q c P (RRefl _ _ C)).
  - exact (ROIf Σ false a c a q (RRefl _ _ C) P).
Qed.

Lemma pared_mux_selected b a c q :
  pared Σ (if b then a else c) q -> lc (if b then c else a) ->
  pared Σ (EMux (EBoxedLit b) a c) q.
Proof.
  destruct b; simpl; intros P C.
  - exact (RMux Σ true a c q c P (RRefl _ _ C)).
  - exact (RMux Σ false a c a q (RRefl _ _ C) P).
Qed.

Local Ltac finish_join :=
  solve [eauto 8 using pared_choose, pared_open, pared_open_same, woval_pared, ovalty_lc, oval_lc,
    pared_left_lc, pared_right_lc, pared_oif_selected, pared_mux_selected with oadt_par oadt_lc].

Local Ltac join_rules A B :=
  eexists; split; [eapply A|eapply B]; finish_join.

Local Ltac join_common :=
  match goal with |- exists c, pared _ ?a c /\ pared _ ?b c =>
    first [
      let w := common_term a b in exists w; split; finish_join
    | let a' := strip_cond a in let b' := strip_cond b in
      let w := common_term a' b' in exists w; split; finish_join
    | let a' := spread_cond a in let b' := spread_cond b in
      let w := common_term a' b' in exists w; split; finish_join]
  end.

Lemma pared_diamond (e a b : expr) : pared Σ e a -> pared Σ e b ->
  exists c, pared Σ a c /\ pared Σ b c.
Proof.
  remember (expr_size e) as n eqn:E.
  revert e E a b. induction n as [n IH] using lt_wf_ind.
  intros e E a b P Q.
  pose proof (pared_lc _ _ P) as [_ CA].
  pose proof (pared_lc _ _ Q) as [_ CB].
  assert (J : forall e a b : expr, expr_size e < n -> pared Σ e a -> pared Σ e b ->
    exists c, pared Σ a c /\ pared Σ b c).
  { intros. eapply (IH (expr_size e0)); eauto. }
  clear IH.
  inversion P; subst; clear P; try solve [eauto 4 with oadt_par].
  all: inversion Q; subst; clear Q; try solve [eauto 5 with oadt_par].
  all: simpl in *.
  all: repeat match goal with
    | P : Σ !! ?x = Some ?a, Q : Σ !! ?x = Some ?b |- _ =>
      let E := fresh "E" in assert (E : a = b) by congruence;
      inversion E; subst; clear E Q
    end.
  all: invert_pared.
  (* Each overlap with a congruence rule reduces to joins of immediate subterms. *)
  all: try solve [exfalso; congruence].
  all: repeat match goal with
  | H : pared _ (EAbs _ _ _) _ |- _ =>
      inversion H; subst; clear H
  | H : pared _ (EInj false _ _ _) _ |- _ =>
      inversion H; subst; clear H
  | H : pared _ (EPair _ _) _ |- _ =>
      inversion H; subst; clear H
  | H : pared _ (EFold _ _) _ |- _ =>
      inversion H; subst; clear H
  | H : pared _ (EIte true (EBoxedLit _) _ _) _ |- _ =>
      inversion H; subst; clear H
  | H : pared _ (EGVar _) _ |- _ =>
      inversion H; subst; clear H
  end.
  all: invert_pared.
  all: try solve [exfalso; congruence].
  all: repeat match goal with
  | H : lc (EAbs _ _ _) |- _ => inversion H; subst; clear H
  | H : lc (EInj _ _ _ _) |- _ => inversion H; subst; clear H
  | H : lc (EPair _ _) |- _ => inversion H; subst; clear H
  | H : lc (EFold _ _) |- _ => inversion H; subst; clear H
  | H : lc (EIte _ _ _ _) |- _ => inversion H; subst; clear H
  end.
  all: repeat match goal with
  | H : forall x : atom, x ∉ ?L -> lc (open (EFVar x) ?e) |- _ =>
    let P := fresh "P" in
    assert (P : forall x : atom, x ∉ L -> pared Σ (open x e) (open x e))
      by (intros; apply RRefl; auto);
    clear H
  end.
  all: repeat match goal with
  | H1 : forall x : atom, x ∉ ?L1 -> pared _ (open (EFVar x) ?s) (open (EFVar x) ?a),
    H2 : forall x : atom, x ∉ ?L2 -> pared _ (open (EFVar x) ?s) (open (EFVar x) ?b) |- _ =>
    let P := fresh "P" in
    assert (P : exists w L, forall x : atom, x ∉ L ->
      pared Σ (open x a) (open x w) /\ pared Σ (open x b) (open x w)) by
      (eapply (pared_binder_join s a b L1 L2);
        [let y := fresh "y" in intros y N z R;
         eapply (J (open (EFVar y) s)); [unfold open; rewrite size_open_name; lia|apply H1; exact N|exact R]
        |exact H2]);
    let w := fresh "w" in let L := fresh "L" in
    destruct P as [w [L P]];
    let A := fresh "A" in let B := fresh "B" in
    assert (A : forall x : atom, x ∉ L -> pared Σ (open x a) (open x w))
      by (intros y N; exact (proj1 (P y N)));
    assert (B : forall x : atom, x ∉ L -> pared Σ (open x b) (open x w))
      by (intros y N; exact (proj2 (P y N)));
    clear H1 H2 P
  end.
  all: do 4 (try match goal with
  | W : woval ?v, P : pared _ ?v ?u |- _ =>
    let U := fresh "U" in
    tryif (match goal with _ : woval u |- _ => idtac end)
    then fail else pose proof (woval_pared _ _ W P) as U
  end).
  all: repeat match goal with
  | H1 : pared _ ?s ?a, H2 : pared _ ?s ?b |- _ =>
      let A := fresh "A" in let B := fresh "B" in
      destruct (J s a b ltac:(simpl; lia) H1 H2) as [? [A B]];
      clear H1 H2
  end.
  all: try match goal with
  | H : _ = Some (DOADT _ _) |- _ =>
    let C := fresh "C" in pose proof (proj1 (global_oadt _ _ _ H)) as C
  end.
  all: try make_join.
  all: try solve [eexists; split; eapply pared_open; eassumption].
  all: try solve [eexists; split; eapply pared_open_same; eassumption].
  all: try solve [join_rules pared_open RApp | join_rules RApp pared_open |
                  join_rules pared_open RLet | join_rules RLet pared_open].
  all: try solve [join_rules RCgrPi RCgrPi | join_rules RCgrAbs RCgrAbs |
                  join_rules RCgrLet RCgrLet | join_rules RCgrCase RCgrCase].
  all: try solve [join_rules RCgrIf ROIfApp | join_rules ROIfApp RCgrIf |
                  join_rules RCgrIf ROIfSec | join_rules ROIfSec RCgrIf |
                  join_rules RCgrIf ROIfIf | join_rules ROIfIf RCgrIf |
                  join_rules RCgrIf ROIfProj | join_rules ROIfProj RCgrIf |
                  join_rules RCgrIf ROIfCase | join_rules ROIfCase RCgrIf |
                  join_rules RCgrIf ROIfUnfold | join_rules ROIfUnfold RCgrIf |
                  join_rules RCgrMux RTapeOIf | join_rules RTapeOIf RCgrMux].
  all: try solve [join_rules pared_choose RProj | join_rules RProj pared_choose |
                  join_rules pared_choose RIf | join_rules RIf pared_choose |
                  join_rules pared_choose ROIf | join_rules ROIf pared_choose |
                  join_rules pared_choose RCase | join_rules RCase pared_choose |
                  join_rules pared_choose RMux | join_rules RMux pared_choose].
  all: try solve [join_rules RCgrIf ROCase | join_rules ROCase RCgrIf].
  all: try solve [join_rules RCgrPair RTapePair | join_rules RTapePair RCgrPair].
  all: try solve [match goal with |- context[if ?k then _ else _] => destruct k; finish_join end].
  all: try solve [match goal with |- context[if ?k then _ else _] => destruct k;
                  first [join_rules ROIf RCgrApp | join_rules RCgrApp ROIf |
                         join_rules ROIf RCgrSec | join_rules RCgrSec ROIf |
                         join_rules ROIf RCgrIf | join_rules RCgrIf ROIf |
                         join_rules ROIf RCgrProj | join_rules RCgrProj ROIf |
                         join_rules ROIf RCgrCase | join_rules RCgrCase ROIf |
                         join_rules ROIf RCgrUnfold | join_rules RCgrUnfold ROIf |
                         join_rules RMux RCgrTape | join_rules RCgrTape RMux |
                         join_rules ROIf ROIf] end].
  all: try solve [
    match goal with K : scoped 1 ?t, A : pared _ ?a ?v, B : pared _ ?b ?v |- _ =>
      exists (open v t); split;
        first [eapply pared_open_same; eassumption | eapply ROADT; eassumption]
    end].
  all: try join_common.
  all: try solve [match goal with |- context [EBoxedLit ?k] => destruct k; simpl in *; join_common end].
  all: try solve [match goal with |- context [EBoxedLit ?k] => destruct k; simpl in *;
                  first [join_rules ROIf RRefl | join_rules ROIf ROIf |
                         join_rules ROIf RCgrApp | join_rules RCgrApp ROIf |
                         join_rules ROIf RCgrSec | join_rules RCgrSec ROIf |
                         join_rules ROIf RCgrIf | join_rules RCgrIf ROIf |
                         join_rules ROIf RCgrProj | join_rules RCgrProj ROIf |
                         join_rules ROIf RCgrCase | join_rules RCgrCase ROIf |
                         join_rules ROIf RCgrUnfold | join_rules RCgrUnfold ROIf |
                         join_rules RMux RCgrTape | join_rules RCgrTape RMux] end].
  - exists <{ ite b0 (w0 ^ x) (w ^ x) }>. split.
    + apply pared_choose; eapply pared_open; eassumption.
    + eapply RCase; eauto using pared_right_lc.
  - exists <{ ite b0 (w0 ^ e0') (w ^ e0') }>. split.
    + apply pared_choose; eapply pared_open; eauto using RRefl, pared_right_lc.
    + eapply RCase; eassumption.
  - exists <{ ~if [b0] then ite b0 (w0 ^ v) (w0 ^ v1) else ite b0 (w ^ v2) (w ^ v) }>.
    split.
    + apply RCgrIf; [apply RRefl; assumption| |];
        apply pared_choose; eapply pared_open; eauto using RRefl, oval_lc, ovalty_lc.
    + eapply ROCase; eassumption.
  - exists <{ ~if [b0] then e1' x else e2' x }>.
    split.
    + apply RCgrIf; [apply RRefl; assumption | |];
        apply RCgrApp; eauto using RRefl, pared_right_lc.
    + apply ROIfApp; assumption.
  - exists <{ ~if [b0] then case e1' of w0 | w else case e2' of w0 | w }>.
    split.
    + apply RCgrIf; [apply RRefl; assumption | |];
        eapply RCgrCase; eauto using RRefl, pared_right_lc.
    + eapply ROIfCase; eassumption.
Qed.

Lemma pared_strip (e a b : expr) : pared Σ e a -> rtc (pared Σ) e b ->
  exists c, rtc (pared Σ) a c /\ pared Σ b c.
Proof.
  intros P R. revert a P. induction R; intros a P.
  - exists a. split; eauto using rtc_refl.
  - destruct (pared_diamond _ _ _ P H) as [u [A B]].
    destruct (IHR _ B) as [c [C D]].
    exists c. split; eauto using rtc_l.
Qed.

Lemma pared_confluence (e a b : expr) : rtc (pared Σ) e a -> rtc (pared Σ) e b ->
  exists c, rtc (pared Σ) a c /\ rtc (pared Σ) b c.
Proof.
  intros P. revert b. induction P; intros b Q.
  - exists b. split; eauto using rtc_refl.
  - destruct (pared_strip _ _ _ H Q) as [u [A B]].
    destruct (IHP _ A) as [c [C D]]. exists c. split; eauto using rtc_l.
Qed.

Lemma equivalent_join e a : pared_equiv Σ e a <-> pared_equiv_join Σ e a.
Proof.
  split.
  - induction 1; [exists e; auto using rtc_refl| |];
      destruct IHpared_equiv as [c [A B]]; exists c; eauto using rtc_l.
  - intros [c [A B]]. induction A; eauto using QRRedL.
    induction B; eauto using QRRefl, QRRedR.
Qed.

Lemma equivalent_sym e a : pared_equiv Σ e a -> pared_equiv Σ a e.
Proof. induction 1; eauto using QRRefl, QRRedL, QRRedR. Qed.

Lemma equivalent_trans (e a b : expr) : pared_equiv Σ e a -> pared_equiv Σ a b ->
  pared_equiv Σ e b.
Proof.
  rewrite !equivalent_join. intros [p [E A]] [q [B C]].
  destruct (pared_confluence _ _ _ A B) as [c [P Q]].
  exists c. split; eauto using rtc_trans.
Qed.

Lemma pared_equivalent e a : pared Σ e a -> pared_equiv Σ e a.
Proof. eauto using QRRedL, QRRefl. Qed.

Lemma equivalent_subst x s e a : lc s -> pared_equiv Σ e a ->
  pared_equiv Σ (subst x s e) (subst x s a).
Proof.
  induction 2; eauto using QRRefl, QRRedL, QRRedR, RRefl, pared_subst.
Qed.

Lemma equivalent_map (f : expr -> expr) e a :
  (forall s t, pared Σ s t -> pared Σ (f s) (f t)) ->
  pared_equiv Σ e a -> pared_equiv Σ (f e) (f a).
Proof. intros F. induction 1; eauto using QRRefl, QRRedL, QRRedR. Qed.

Lemma equivalent_open (e a b : expr) :
  scoped 1 e -> pared_equiv Σ a b -> pared_equiv Σ (open a e) (open b e).
Proof.
  intros C. apply (equivalent_map (fun a : expr => open a e)). intros s t H.
  eapply pared_open with (L := ∅ : aset); auto.
  intros x _. apply RRefl, scoped_lc, scoped_open; simpl; auto.
Qed.

Lemma rtc_pared_prod (a b e : expr) : rtc (pared Σ) (EProd a b) e ->
  exists a' b' : expr, e = EProd a' b' /\ rtc (pared Σ) a a' /\ rtc (pared Σ) b b'.
Proof.
  revert e. apply rtc_ind_r.
  - exists a, b. repeat split; auto using rtc_refl.
  - intros y z _ P [a' [b' [-> [A B]]]].
    inversion P; subst.
    all: do 2 eexists; split; [reflexivity|]; split; eauto using rtc_r.
Qed.

Lemma rtc_pared_sum l (a b e : expr) : rtc (pared Σ) (ESum l a b) e ->
  exists a' b' : expr, e = ESum l a' b' /\ rtc (pared Σ) a a' /\ rtc (pared Σ) b b'.
Proof.
  revert e. apply rtc_ind_r.
  - exists a, b. repeat split; auto using rtc_refl.
  - intros y z _ P [a' [b' [-> [A B]]]].
    inversion P; subst.
    all: do 2 eexists; split; [reflexivity|]; split; eauto using rtc_r.
Qed.

Lemma rtc_pared_pi l (a b e : expr) : rtc (pared Σ) (EPi l a b) e ->
  exists a' b' : expr, e = EPi l a' b' /\ rtc (pared Σ) a a' /\
    (forall v, lc v -> rtc (pared Σ) (open v b) (open v b')).
Proof.
  revert e. apply rtc_ind_r.
  - exists a, b. repeat split; auto using rtc_refl.
  - intros y z _ P [a' [b' [-> [A B]]]].
    inversion P; subst; [|exists a', b'; repeat split; eauto].
    do 2 eexists. split; [reflexivity|]. split; [eauto using rtc_r|].
    intros. eapply rtc_r; [eauto|eapply pared_open; eauto using RRefl].
Qed.

Lemma equivalent_prod (a b a' b' : expr) : pared_equiv Σ (EProd a b) (EProd a' b') ->
  pared_equiv Σ a a' /\ pared_equiv Σ b b'.
Proof.
  intros [c [A B]]%equivalent_join.
  destruct (rtc_pared_prod _ _ _ A) as [u [v [-> [U V]]]].
  destruct (rtc_pared_prod _ _ _ B) as [u' [v' [E [U' V']]]].
  injection E as Ueq Veq. subst u' v'. rewrite !equivalent_join. split; [exists u|exists v]; auto.
Qed.

Lemma equivalent_sum l l' (a b a' b' : expr) : pared_equiv Σ (ESum l a b) (ESum l' a' b') ->
  l = l' /\ pared_equiv Σ a a' /\ pared_equiv Σ b b'.
Proof.
  intros [c [A B]]%equivalent_join.
  destruct (rtc_pared_sum _ _ _ _ A) as [u [v [-> [U V]]]].
  destruct (rtc_pared_sum _ _ _ _ B) as [u' [v' [E [U' V']]]].
  injection E as Lq Ueq Veq. subst l' u' v'. rewrite !equivalent_join. split; [reflexivity|]. split; [exists u|exists v]; auto.
Qed.

Lemma equivalent_pi l l' (a b a' b' : expr) : pared_equiv Σ (EPi l a b) (EPi l' a' b') ->
  l = l' /\ pared_equiv Σ a a' /\
  (forall v, lc v -> pared_equiv Σ (open v b) (open v b')).
Proof.
  intros [c [A B]]%equivalent_join.
  destruct (rtc_pared_pi _ _ _ _ A) as [u [v [-> [U V]]]].
  destruct (rtc_pared_pi _ _ _ _ B) as [u' [v' [E [U' V']]]].
  injection E as Lq Ueq Veq. subst l' u' v'. rewrite !equivalent_join. split; [done|].
  split; [exists u; auto|intros v0 Lv; apply equivalent_join; exists (open v0 v); eauto].
Qed.


(* Oblivious type positions are independent of the terms used as indices. *)
Fixpoint oblivious_shape e : Prop :=
  match e with
  | EUnitT | EBool true => True
  | EProd a b | ESum true a b | EIte _ _ a b | ECase _ _ a b =>
      oblivious_shape a /\ oblivious_shape b
  | ELet _ b => oblivious_shape b
  | EApp (EGVar x) _ => exists t body, Σ !! x = Some (DOADT t body)
  | _ => False
  end.

Lemma shape_open e a k : oblivious_shape e -> oblivious_shape (open_ k a e).
Proof.
  revert k. induction e; intros k'; try destruct l; simpl; try solve [intuition eauto].
  destruct e1; simpl; tauto.
Qed.

Lemma shape_open_name e x k : oblivious_shape (open_ k (EFVar x) e) -> oblivious_shape e.
Proof.
  revert k. induction e; intros k'; try destruct l; simpl; try solve [intuition eauto].
  - case_decide; simpl; tauto.
  - destruct e1; simpl; try tauto. case_decide; simpl; tauto.
Qed.

Lemma shape_subst x s e : oblivious_shape e -> oblivious_shape (subst x s e).
Proof.
  induction e; try destruct l; simpl; try solve [intuition eauto].
  destruct e1; simpl; tauto.
Qed.

Lemma kind_shape Γ e κ : kinding Σ Γ e κ -> κ ⊑ KObliv -> oblivious_shape e.
Proof.
  induction 1; intros N; simpl.
  all: try solve [tauto | discriminate].
  all: try solve [destruct l; simpl in *; [exact I|discriminate]].
  all: try solve [do 2 eexists; eassumption].
  all: try solve [split; eauto].
  all: try solve [destruct κ; discriminate].
  all: repeat match goal with
  | H : forall x : atom, x ∉ ?L -> KObliv ⊑ KObliv -> oblivious_shape (open (EFVar x) ?t) |- _ =>
    specialize (H (fresh L) (is_fresh L) ltac:(reflexivity));
    unfold open in H; apply shape_open_name in H
  end.
  all: try solve [tauto].
  all: try solve [destruct κ, κ'; simpl in *; try discriminate; auto].
Qed.

Lemma shape_oadt x t e : Σ !! x = Some (DOADT t e) -> oblivious_shape e.
Proof.
  intros H. pose proof (map_Forall_lookup_1 _ _ _ _ G H) as D. inversion D; subst.
  match goal with H : forall x : atom, x ∉ ?L -> _ |- _ =>
    specialize (H (fresh L) (is_fresh L));
    eapply shape_open_name; apply (kind_shape _ _ _ H); reflexivity
  end.
Qed.

Lemma shape_pared e e' : pared Σ e e' -> oblivious_shape e -> oblivious_shape e'.
Proof.
  induction 1; simpl; intros Q; try contradiction; split_hyps.
  all: repeat match goal with H : forall x : atom, x ∉ ?L -> oblivious_shape (open (EFVar x) ?a) -> _,
                            B : oblivious_shape ?a |- _ =>
        specialize (H (fresh L) (is_fresh L) (shape_open _ _ _ B));
        apply shape_open_name in H
       end.
  all: destruct b || idtac; simpl in *; try tauto; try solve [eauto using shape_open, shape_oadt].
  all: try (destruct e1; simpl in *; try contradiction).
  all: try solve [
    match goal with H : pared _ (EGVar _) _ |- _ =>
      inversion H; subst; clear H; split_hyps; try reflexivity; try congruence; eauto
    end].
  all: try solve [destruct l; simpl in *; tauto].
  all: match goal with
  | H : exists a b : expr, Σ !! _ = Some (DOADT a b), P : pared _ (EGVar _) _ |- _ =>
    destruct H as [? [? H]]; inversion P; subst; try congruence; do 2 eexists; eassumption
  end.
Qed.

Definition oblivious_type e := exists t, pared_equiv Σ e t /\ oblivious_shape t.

Lemma oblivious_type_conv e e' :
  pared_equiv Σ e e' -> oblivious_type e' -> oblivious_type e.
Proof. intros P [a [Q A]]. exists a. eauto using equivalent_trans. Qed.

Lemma oblivious_type_subst x s e : lc s ->
  oblivious_type e -> oblivious_type (subst x s e).
Proof. intros C [a [Q A]]. exists (subst x s a). eauto using equivalent_subst, shape_subst. Qed.

Lemma shape_rtc e e' : rtc (pared Σ) e e' -> oblivious_shape e -> oblivious_shape e'.
Proof. induction 1; eauto using shape_pared. Qed.

Lemma oblivious_product (a b : expr) :
  oblivious_type (EProd a b) -> oblivious_type a /\ oblivious_type b.
Proof.
  intros [t [[j [P Q]]%equivalent_join A]].
  destruct (rtc_pared_prod _ _ _ P) as [a' [b' [-> [B C]]]].
  pose proof (shape_rtc _ _ Q A) as [D E].
  split.
  - exists a'. split; [apply equivalent_join; exists a'; eauto using rtc_refl|exact D].
  - exists b'. split; [apply equivalent_join; exists b'; eauto using rtc_refl|exact E].
Qed.

Inductive type_head :=
| HUnit | HBool (o : bool) | HProd | HSum (o : bool) | HPi (l : bool) | HADT (x : atom).

Definition type_head_of e :=
  match e with
  | EUnitT => Some HUnit
  | EBool o => Some (HBool o)
  | EProd _ _ => Some HProd
  | ESum o _ _ => Some (HSum o)
  | EPi l _ _ => Some (HPi l)
  | EGVar x => match Σ !! x with Some (DADT _) => Some (HADT x) | _ => None end
  | _ => None
  end.

Lemma head_pared e e' h :
  type_head_of e = Some h -> pared Σ e e' -> type_head_of e' = Some h.
Proof.
  intros H P. inversion P; subst; simpl in *; try congruence.
  match goal with E : Σ !! _ = Some (DFun _ _) |- _ => rewrite E in H; discriminate end.
Qed.

Lemma head_rtc e e' h : rtc (pared Σ) e e' ->
  type_head_of e = Some h -> type_head_of e' = Some h.
Proof. induction 1; eauto using head_pared. Qed.

Lemma equivalent_heads e e' h h' :
  type_head_of e = Some h -> type_head_of e' = Some h' ->
  pared_equiv Σ e e' -> h = h'.
Proof.
  intros H H' [j [P Q]]%equivalent_join.
  pose proof (head_rtc _ _ _ P H).
  pose proof (head_rtc _ _ _ Q H'). congruence.
Qed.

Lemma oblivious_head e h : oblivious_type e -> type_head_of e = Some h ->
  h = HUnit \/ h = HBool true \/ h = HProd \/ h = HSum true.
Proof.
  intros [t [[j [P Q]]%equivalent_join A]] H.
  apply (head_rtc _ _ _ P) in H.
  apply (shape_rtc _ _ Q) in A.
  destruct j; simpl in *; try contradiction; try discriminate;
    repeat match goal with l : bool |- _ => destruct l end;
    simpl in *; try contradiction; inversion H; subst; eauto.
Qed.

Lemma equivalent_otval (a b : expr) : otval a -> otval b -> pared_equiv Σ a b -> a = b.
Proof.
  assert (F : forall a b : expr, rtc (pared Σ) a b -> otval a -> b = a).
  { induction 1; eauto. intros V. pose proof (otval_irreducible _ _ V H) as ->. eauto. }
  intros A B [j [P Q]]%equivalent_join. pose proof (F _ _ P A). pose proof (F _ _ Q B). congruence.
Qed.
(* Runtime typing keeps the kinds of annotations that can be evaluated.
   Type conversion uses local closure and parallel convertibility. *)
Inductive runtime_typing : tctx -> expr -> bool -> expr -> Prop :=
| RTFVar Γ x l τ :
    Γ !! x = Some (l, τ) ->
    lc τ ->
    runtime_typing Γ <{ fvar x }> l <{ τ }>
| RTUnit Γ : runtime_typing Γ <{ () }> ⊥ <{ 𝟙 }>
| RTLit Γ b : runtime_typing Γ <{ lit b }> ⊥ <{ 𝔹 }>
| RTFun Γ x l τ e :
    Σ !! x = Some (DFun (l, τ) e) ->
    lc τ ->
    runtime_typing Γ <{ gvar x }> l <{ τ }>
| RTAbs Γ l1 l2 e τ1 τ2 L :
    (forall x, x ∉ L -> runtime_typing (<[x:=(l2, τ2)]>Γ) <{ e^x }> l1 <{ τ1^x }>) ->
    lc τ2 ->
    runtime_typing Γ <{ \:{l2}τ2 => e }> l1 <{ (Π:{l2}τ2, τ1) }>
| RTLet Γ l1 l2 l e1 e2 τ1 τ2 L :
    runtime_typing Γ <{ e1 }> l1 <{ τ1 }> ->
    (forall x, x ∉ L -> runtime_typing (<[x:=(l1, τ1)]>Γ) <{ e2^x }> l2 <{ τ2^x }>) ->
    l = l1 ⊔ l2 ->
    runtime_typing Γ <{ let e1 in e2 }> l <{ τ2^e1 }>
| RTApp Γ l1 l2 e1 e2 τ1 τ2 :
    runtime_typing Γ <{ e1 }> l1 <{ (Π:{l2}τ2, τ1) }> ->
    runtime_typing Γ <{ e2 }> l2 <{ τ2 }> ->
    runtime_typing Γ <{ e1 e2 }> l1 <{ τ1^e2 }>
| RTPair Γ l1 l2 l e1 e2 τ1 τ2 :
    runtime_typing Γ <{ e1 }> l1 <{ τ1 }> ->
    runtime_typing Γ <{ e2 }> l2 <{ τ2 }> ->
    l = l1 ⊔ l2 ->
    runtime_typing Γ <{ (e1, e2) }> l <{ τ1 * τ2 }>
| RTProj Γ l b e τ1 τ2 :
    runtime_typing Γ <{ e }> l <{ τ1 * τ2 }> ->
    runtime_typing Γ <{ π@b e }> l <{ ite b τ1 τ2 }>
| RTInj Γ l b e τ1 τ2 :
    runtime_typing Γ <{ e }> l <{ ite b τ1 τ2 }> ->
    lc (ESum false τ1 τ2) ->
    runtime_typing Γ <{ inj@b<τ1 + τ2> e }> l <{ τ1 + τ2 }>
| RTIf Γ l1 l2 l e0 e1 e2 τ :
    runtime_typing Γ <{ e0 }> ⊥ <{ 𝔹 }> ->
    runtime_typing Γ <{ e1 }> l1 <{ τ^(lit true) }> ->
    runtime_typing Γ <{ e2 }> l2 <{ τ^(lit false) }> ->
    scoped 1 τ ->
    l = l1 ⊔ l2 ->
    runtime_typing Γ <{ if e0 then e1 else e2 }> l <{ τ^e0 }>
| RTIfNoDep Γ l0 l1 l2 l e0 e1 e2 τ :
    runtime_typing Γ <{ e0 }> l0 <{ 𝔹 }> ->
    runtime_typing Γ <{ e1 }> l1 <{ τ }> ->
    runtime_typing Γ <{ e2 }> l2 <{ τ }> ->
    l = l0 ⊔ l1 ⊔ l2 ->
    runtime_typing Γ <{ if e0 then e1 else e2 }> l <{ τ }>
| RTCase Γ l1 l2 l e0 e1 e2 τ1 τ2 τ L1 L2 :
    runtime_typing Γ <{ e0 }> ⊥ <{ τ1 + τ2 }> ->
    (forall x, x ∉ L1 -> runtime_typing (<[x:=(⊥, τ1)]>Γ) <{ e1^x }> l1 <{ τ^(inl<τ1 + τ2> x) }>) ->
    (forall x, x ∉ L2 -> runtime_typing (<[x:=(⊥, τ2)]>Γ) <{ e2^x }> l2 <{ τ^(inr<τ1 + τ2> x) }>) ->
    scoped 1 τ ->
    l = l1 ⊔ l2 ->
    runtime_typing Γ <{ case e0 of e1 | e2 }> l <{ τ^e0 }>
| RTCaseNoDep Γ l0 l1 l2 l e0 e1 e2 τ1 τ2 τ L1 L2 :
    runtime_typing Γ <{ e0 }> l0 <{ τ1 + τ2 }> ->
    (forall x, x ∉ L1 -> runtime_typing (<[x:=(l0, τ1)]>Γ) <{ e1^x }> l1 <{ τ }>) ->
    (forall x, x ∉ L2 -> runtime_typing (<[x:=(l0, τ2)]>Γ) <{ e2^x }> l2 <{ τ }>) ->
    lc τ ->
    l = l0 ⊔ l1 ⊔ l2 ->
    runtime_typing Γ <{ case e0 of e1 | e2 }> l <{ τ }>
| RTFold Γ l X e τ :
    Σ !! X = Some (DADT τ) ->
    runtime_typing Γ <{ e }> l <{ τ }> ->
    runtime_typing Γ <{ fold<X> e }> l <{ gvar X }>
| RTUnfold Γ l X e τ :
    Σ !! X = Some (DADT τ) ->
    runtime_typing Γ <{ e }> l <{ gvar X }> ->
    lc τ ->
    runtime_typing Γ <{ unfold<X> e }> l <{ τ }>
| RTSec Γ l e :
    runtime_typing Γ <{ e }> l <{ 𝔹 }> ->
    runtime_typing Γ <{ s𝔹 e }> l <{ ~𝔹 }>
| RTMux Γ e0 e1 e2 τ :
    runtime_typing Γ <{ e0 }> ⊥ <{ ~𝔹 }> ->
    runtime_typing Γ <{ e1 }> ⊥ <{ τ }> ->
    runtime_typing Γ <{ e2 }> ⊥ <{ τ }> ->
    oblivious_type τ ->
    runtime_typing Γ <{ mux e0 e1 e2 }> ⊥ <{ τ }>
| RTOInj Γ b e τ1 τ2 :
    runtime_typing Γ <{ e }> ⊥ <{ ite b τ1 τ2 }> ->
    runtime_otype Γ (ESum true τ1 τ2) ->
    runtime_typing Γ <{ ~inj@b<τ1 ~+ τ2> e }> ⊥ <{ τ1 ~+ τ2 }>
| RTOIf Γ l1 l2 e0 e1 e2 τ :
    runtime_typing Γ <{ e0 }> ⊥ <{ ~𝔹 }> ->
    runtime_typing Γ <{ e1 }> l1 <{ τ }> ->
    runtime_typing Γ <{ e2 }> l2 <{ τ }> ->
    lc τ ->
    runtime_typing Γ <{ ~if e0 then e1 else e2 }> ⊤ <{ τ }>
| RTOCase Γ l1 l2 e0 e1 e2 τ1 τ2 τ L1 L2 :
    runtime_typing Γ <{ e0 }> ⊥ <{ τ1 ~+ τ2 }> ->
    (forall x, x ∉ L1 -> runtime_typing (<[x:=(⊥, τ1)]>Γ) <{ e1^x }> l1 <{ τ }>) ->
    (forall x, x ∉ L2 -> runtime_typing (<[x:=(⊥, τ2)]>Γ) <{ e2^x }> l2 <{ τ }>) ->
    lc τ ->
    runtime_typing Γ <{ ~case e0 of e1 | e2 }> ⊤ <{ τ }>
| RTTape Γ l e τ :
    runtime_typing Γ <{ e }> l <{ τ }> ->
    oblivious_type τ ->
    runtime_typing Γ <{ tape e }> ⊥ <{ τ }>

| RTBoxedLit Γ b : runtime_typing Γ <{ [b] }> ⊥ <{ ~𝔹 }>
| RTBoxedInj Γ b v ω :
    ovalty <{ [inj@b<ω> v] }> ω ->
    runtime_typing Γ <{ [inj@b<ω> v] }> ⊥ <{ ω }>

| RTConv Γ l l' e τ τ' :
    runtime_typing Γ <{ e }> l' <{ τ' }> ->
    pared_equiv Σ τ' τ ->
    lc τ ->
    l' ⊑ l ->
    runtime_typing Γ <{ e }> l <{ τ }>

with runtime_otype : tctx -> expr -> Prop :=
| RKUnit Γ : runtime_otype Γ EUnitT
| RKBool Γ : runtime_otype Γ (EBool true)
| RKProd Γ (a b : expr) : runtime_otype Γ a -> runtime_otype Γ b -> runtime_otype Γ (EProd a b)
| RKSum Γ (a b : expr) : runtime_otype Γ a -> runtime_otype Γ b -> runtime_otype Γ (ESum true a b)
| RKOADT Γ X τ e t : Σ !! X = Some (DOADT τ t) -> lc τ ->
    runtime_typing Γ e false τ -> runtime_otype Γ (EApp (EGVar X) e)
| RKIf Γ e t1 t2 : runtime_typing Γ e false (EBool false) ->
    runtime_otype Γ t1 -> runtime_otype Γ t2 -> runtime_otype Γ (EIte false e t1 t2)
| RKCase Γ e t1 t2 (a b : expr) L1 L2 :
    runtime_typing Γ e false (ESum false a b) ->
    (forall x : atom, x ∉ L1 -> runtime_otype (<[x:=(false,a)]>Γ) (open x t1)) ->
    (forall x : atom, x ∉ L2 -> runtime_otype (<[x:=(false,b)]>Γ) (open x t2)) ->
    runtime_otype Γ (ECase false e t1 t2)
| RKLet Γ e t τ L :
    runtime_typing Γ e false τ ->
    (forall x : atom, x ∉ L -> runtime_otype (<[x:=(false,τ)]>Γ) (open x t)) ->
    runtime_otype Γ (ELet e t).

Scheme runtime_typing_ind' := Minimality for runtime_typing Sort Prop
  with runtime_otype_ind' := Minimality for runtime_otype Sort Prop.
Combined Scheme runtime_mutind from runtime_typing_ind', runtime_otype_ind'.

Lemma global_def x D : Σ !! x = Some D -> gdef_typing Σ D.
Proof. intros H. exact (map_Forall_lookup_1 _ _ _ _ G H). Qed.

Lemma declared_adt_lc x t : Σ !! x = Some (DADT t) -> lc t.
Proof.
  intros H. apply global_def in H. inversion H; subst.
  match goal with H : kinding _ _ t _ |- _ => exact (proj1 (proj2 (typing_names Σ) _ _ _ H)) end.
Qed.

Lemma declared_fun_lc x l t e : Σ !! x = Some (DFun (l,t) e) -> lc t.
Proof.
  intros H. destruct (global_fun _ _ _ _ H) as [_ [_ [_ [κ K]]]].
  exact (proj1 (proj2 (typing_names Σ) _ _ _ K)).
Qed.

Lemma declared_oadt_lc x t e : Σ !! x = Some (DOADT t e) -> lc t.
Proof.
  intros H. apply global_def in H. inversion H; subst.
  match goal with H : kinding _ _ t _ |- _ => exact (proj1 (proj2 (typing_names Σ) _ _ _ H)) end.
Qed.

Lemma kind_lc Γ e κ : kinding Σ Γ e κ -> lc e.
Proof. intros H. exact (proj1 (proj2 (typing_names Σ) _ _ _ H)). Qed.

Lemma kind_motive Γ a t κ : kinding Σ Γ (open a t) κ -> scoped 1 t.
Proof.
  intros H. exact (scoped_open_inv _ _ _ (lc_scoped _ (kind_lc _ _ _ H))).
Qed.

Local Hint Resolve RTFVar RTUnit RTLit RTFun RTAbs RTLet RTApp RTPair RTProj RTInj RTIf
  RTIfNoDep RTCase RTCaseNoDep RTFold RTUnfold RTSec RTMux RTOInj RTOIf RTOCase RTTape
  RTBoxedLit RTBoxedInj RKUnit RKBool RKProd RKSum RKOADT RKIf RKCase RKLet : oadt_rt.

Lemma translate_typing :
  (forall Γ e l τ, typing Σ Γ e l τ -> runtime_typing Γ e l τ) /\
  (forall Γ t κ, kinding Σ Γ t κ -> κ ⊑ KObliv -> runtime_otype Γ t).
Proof.
  apply typing_kinding_mutind; intros;
    try solve [eauto 5 using RTConv, kind_lc, kind_motive, declared_adt_lc, declared_fun_lc,
      declared_oadt_lc, QRRefl with oadt_rt].
  all: try solve [
    match goal with H : kinding _ _ ?t KObliv |- _ =>
        assert (oblivious_type t) by (exists t; split; eauto using QRRefl, kind_shape)
    end; eauto 4 with oadt_rt].
  all: try solve [discriminate].
  all: try solve [destruct l; [apply RKBool|discriminate]].
  all: try solve [destruct κ; discriminate].
  all: try solve [
    eapply RKCase; [eassumption|intros; eauto|intros; eauto] |
    eapply RKLet; [eassumption|intros; eauto] |
    destruct κ, κ'; simpl in *; try discriminate; eauto].
Qed.

Lemma runtime_lc :
  (forall Γ e l τ, runtime_typing Γ e l τ -> lc e /\ lc τ) /\
  (forall Γ e, runtime_otype Γ e -> lc e).
Proof.
  apply runtime_mutind; intros; split_hyps.
  all: repeat match goal with
  | H : forall x : atom, x ∉ ?L -> lc (open (EFVar x) ?a) /\ lc (open (EFVar x) ?b) |- _ =>
    assert (scoped 1 a) by (eapply binder_lc; intros; apply (H _ ltac:(eassumption)));
    assert (scoped 1 b) by (eapply binder_lc; intros; apply (H _ ltac:(eassumption)));
    clear H
  | H : forall x : atom, x ∉ ?L -> lc (open (EFVar x) ?a) /\ lc _ |- _ =>
    assert (scoped 1 a) by (eapply binder_lc; intros; apply (H _ ltac:(eassumption)));
    clear H
  | H : forall x : atom, x ∉ ?L -> lc (open (EFVar x) ?a) |- _ =>
    let C := fresh "C" in pose proof (binder_lc _ _ H) as C; clear H
  | H : ovalty _ _ |- _ =>
    apply ovalty_values in H; destruct H
  end.
  all: try match goal with H : lc (EPi _ _ _) |- _ => apply lc_scoped in H; simpl in H; destruct H end.
  all: try match goal with H : lc (EProd _ _) |- _ => inversion H; clear H; subst end.
  all: try split; try solve [eauto with oadt_lc].
  all: destruct b || idtac; apply scoped_lc; unfold open; simpl;
    intuition eauto 5 using lc_scoped, scoped_open, oval_lc, otval_lc.
  all: match goal with H : oval (EBoxedInj _ _ _) |- _ => inversion H; assumption end.
Qed.

Lemma rt_lc Γ e l τ : runtime_typing Γ e l τ -> lc e.
Proof. intros H. exact (proj1 (proj1 runtime_lc _ _ _ _ H)). Qed.

Lemma rt_type_lc Γ e l τ : runtime_typing Γ e l τ -> lc τ.
Proof. intros H. exact (proj2 (proj1 runtime_lc _ _ _ _ H)). Qed.

Lemma rt_otype_lc Γ t : runtime_otype Γ t -> lc t.
Proof. exact (proj2 runtime_lc Γ t). Qed.

Lemma rt_conv Γ e l l' τ τ' : runtime_typing Γ e l τ ->
  pared_equiv Σ τ τ' -> lc τ' -> l ⊑ l' -> runtime_typing Γ e l' τ'.
Proof. eauto using RTConv. Qed.

Lemma rt_label Γ e l l' τ : runtime_typing Γ e l τ ->
  l ⊑ l' -> runtime_typing Γ e l' τ.
Proof. eauto using RTConv, QRRefl, rt_type_lc. Qed.

Lemma rt_eqtype Γ e l τ τ' : runtime_typing Γ e l τ ->
  pared_equiv Σ τ τ' -> lc τ' -> runtime_typing Γ e l τ'.
Proof. intros. eapply RTConv; eauto; destruct l; reflexivity. Qed.

Lemma context_insert (Γ Δ : tctx) x (a : lexpr) : Γ ⊆ Δ -> (<[x:=a]>Γ) ⊆ (<[x:=a]>Δ).
Proof.
  rewrite !map_subseteq_spec. intros H y t P.
  destruct (decide (x = y)) as [E|N].
  - subst y. rewrite lookup_insert in P |- *. rewrite !decide_True in P |- * by reflexivity. exact P.
  - rewrite lookup_insert_ne in P |- * by congruence. exact (H y t P).
Qed.

Lemma runtime_weaken :
  (forall Γ e l τ, runtime_typing Γ e l τ -> forall Δ, Γ ⊆ Δ -> runtime_typing Δ e l τ) /\
  (forall Γ t, runtime_otype Γ t -> forall Δ, Γ ⊆ Δ -> runtime_otype Δ t).
Proof.
  apply runtime_mutind; intros;
    repeat match goal with
    | H : forall x : atom, x ∉ ?L -> forall Ξ : tctx, (<[x:=(?l,?t)]>?Γ) ⊆ Ξ -> @?P x Ξ,
      N : ?Γ ⊆ ?Δ |- _ =>
      let B := fresh "B" in
      assert (B : forall x : atom, x ∉ L -> P x (<[x:=(l,t)]>Δ))
        by (intros y F; apply (H y F); apply context_insert; exact N);
      clear H
    end;
    eauto 6 using RTConv, map_subseteq_spec with oadt_rt.
  eapply RTFVar; [eapply (proj1 (map_subseteq_spec Γ Δ)); eassumption | assumption].
Qed.

Definition subst_context x s l τ (Γ Δ : tctx) :=
  forall y ly ty, Γ !! y = Some (ly, ty) ->
    if decide (x = y) then ly = l /\ subst x s ty = τ
    else Δ !! y = Some (ly, subst x s ty).

Lemma subst_context_insert x s l τ Γ Δ y ly ty :
  subst_context x s l τ Γ Δ -> x <> y ->
  subst_context x s l τ (<[y:=(ly,ty)]>Γ) (<[y:=(ly,subst x s ty)]>Δ).
Proof.
  unfold subst_context. intros C N z lz tz H.
  destruct (decide (y = z)) as [->|N'].
  - rewrite lookup_insert, decide_True in H by reflexivity. injection H as -> ->.
    case_decide; [contradiction|rewrite lookup_insert, decide_True; reflexivity].
  - rewrite lookup_insert_ne in H by auto.
    specialize (C _ _ _ H). case_decide; auto. rewrite lookup_insert_ne; auto.
Qed.

Lemma subst_open_name x s e y :
  lc s -> x <> y -> subst x s (open (EFVar y) e) = open (EFVar y) (subst x s e).
Proof. intros C N. rewrite subst_open by auto. simpl. rewrite decide_False; auto. Qed.

Lemma subst_open_inj_name x s e y b a c :
  lc s -> x <> y ->
  subst x s (open (EInj false b (ESum false a c) (EFVar y)) e) =
  open (EInj false b (ESum false (subst x s a) (subst x s c)) (EFVar y)) (subst x s e).
Proof. intros C N. rewrite subst_open by auto. simpl. rewrite decide_False; auto. Qed.

Local Ltac runtime_subst_binder x s C :=
  let y := fresh "y" in let N := fresh "N" in
  intros y N;
  let D := fresh "D" in assert (D : x <> y) by (clear - N; set_solver);
  rewrite <- ?(subst_open_name x s _ y C D), <- ?(subst_open_inj_name x s _ y _ _ _ C D);
  match goal with
  | H : forall u : atom, u ∉ ?L -> forall Ξ : tctx, subst_context _ _ _ _ _ Ξ -> _ -> _ |- _ =>
      let F := fresh "F" in assert (F : y ∉ L) by (clear - N; set_solver);
      eapply (H y F);
      [apply subst_context_insert; assumption |
       eapply (proj1 runtime_weaken); [eassumption|apply insert_subseteq; apply not_elem_of_dom;
          clear - N; set_solver]]
  end.

Lemma kind_closed_names t κ : kinding Σ ∅ t κ -> names t = ∅.
Proof.
  intros K. pose proof (proj2 (proj2 (typing_names Σ) _ _ _ K)) as N.
  rewrite dom_empty_L in N. set_solver.
Qed.

Lemma declared_type_closed x d :
  Σ !! x = Some d ->
  match d with DADT t | DFun (_,t) _ | DOADT t _ => names t = ∅ end.
Proof.
  intros H. apply global_def in H. inversion H; subst; eauto using kind_closed_names.
Qed.

Lemma runtime_subst x s l τ :
  (forall Γ e k t, runtime_typing Γ e k t -> forall Δ,
    subst_context x s l τ Γ Δ -> runtime_typing Δ s l τ ->
    runtime_typing Δ (subst x s e) k (subst x s t)) /\
  (forall Γ t, runtime_otype Γ t -> forall Δ,
    subst_context x s l τ Γ Δ -> runtime_typing Δ s l τ ->
    runtime_otype Δ (subst x s t)).
Proof.
  apply runtime_mutind; intros; simpl;
    match goal with H : runtime_typing _ s _ _ |- _ =>
      let C := fresh "C" in pose proof (rt_lc _ _ _ _ H) as C
    end;
    rewrite ?subst_open, ?subst_choose by assumption;
    repeat match goal with
    | IH : forall Ξ : tctx, subst_context _ _ _ _ _ Ξ -> runtime_typing Ξ _ _ _ -> _,
      H : subst_context _ _ _ _ _ ?Δ,
      A : runtime_typing ?Δ s _ _ |- _ =>
        let P := fresh "P" in pose proof (IH Δ H A) as P;
        clear IH;
        rewrite ?subst_open, ?subst_choose in P by assumption;
        cbn in P
    end;
    try solve [eauto 6 using RTConv, equivalent_subst, oblivious_type_subst, lc_subst,
      scoped_subst, lc_scoped with oadt_rt].
  all: try solve [
    match goal with H : subst_context _ _ _ _ ?Γ _, P : ?Γ !! _ = _ |- _ =>
      specialize (H _ _ _ P); case_decide;
        [destruct H as [-> ->]; assumption|eapply RTFVar; eauto using lc_subst]
    end].
  all: try solve [
    eapply RTAbs with (L:=L ∪ {[x]} ∪ dom Δ);
      [runtime_subst_binder x s C|eauto using lc_subst] |
    eapply RTLet with (L:=L ∪ {[x]} ∪ dom Δ);
      [eauto|runtime_subst_binder x s C|assumption] |
    eapply RKLet with (L:=L ∪ {[x]} ∪ dom Δ);
      [eauto|runtime_subst_binder x s C]].
  all: try solve [
    first [eapply RTCase with (L1:=L1 ∪ {[x]} ∪ dom Δ) (L2:=L2 ∪ {[x]} ∪ dom Δ) |
           eapply RTCaseNoDep with (L1:=L1 ∪ {[x]} ∪ dom Δ) (L2:=L2 ∪ {[x]} ∪ dom Δ) |
           eapply RTOCase with (L1:=L1 ∪ {[x]} ∪ dom Δ) (L2:=L2 ∪ {[x]} ∪ dom Δ) |
           eapply RKCase with (L1:=L1 ∪ {[x]} ∪ dom Δ) (L2:=L2 ∪ {[x]} ∪ dom Δ)];
      try solve [eauto using lc_subst, scoped_subst, lc_scoped | runtime_subst_binder x s C]].
  all: try solve [
    match goal with H : _ = Some (DADT ?t) |- _ =>
      let D := fresh "D" in pose proof (global_def _ _ H) as D; inversion D; subst;
      match goal with K : kinding _ ∅ t _ |- _ =>
        let N := fresh "N" in pose proof (proj2 (proj2 (typing_names Σ) _ _ _ K)) as N;
        rewrite dom_empty_L in N;
        repeat (rewrite (subst_fresh x s t) in * by (clear - N; set_solver))
      end
    end;
    eauto using lc_subst with oadt_rt].
  all: try solve [
    match goal with H : Σ !! _ = Some (DFun (_,?t) _) |- _ =>
      let N := fresh "N" in pose proof (declared_type_closed _ _ H) as N; simpl in N;
      rewrite (subst_fresh x s t) by (clear - N; set_solver);
      eapply RTFun; eassumption
    end].
  all: try solve [
    match goal with H : Σ !! _ = Some (DOADT ?t _) |- _ =>
      let N := fresh "N" in pose proof (declared_type_closed _ _ H) as N; simpl in N;
      rewrite (subst_fresh x s t) in * by (clear - N; set_solver);
      eapply RKOADT; eassumption
    end].
  all: try solve [
    match goal with H : ovalty _ ?t |- _ =>
      rewrite (proj1 (proj2 (proj2 (otval_inert _ (proj2 (ovalty_values _ _ H))))));
      eapply RTBoxedInj; eassumption
    end].
  all: try solve [destruct b; simpl in *; eauto 4 using RTConv, equivalent_subst,
                  oblivious_type_subst, lc_subst, scoped_subst, lc_scoped with oadt_rt].
  all: eapply RTInj; [eassumption|].
  all: match goal with H : lc (ESum false ?a ?c) |- _ =>
    change (lc (subst x s (ESum false a c))); now apply lc_subst
  end.
Qed.

Definition context_names (Γ : tctx) : aset :=
  list_to_set (flat_map (fun p : atom * lexpr => elements (names p.2.2)) (map_to_list Γ)).

Lemma lookup_context_names Γ y l τ : Γ !! y = Some (l, τ) ->
  names τ ⊆ context_names Γ.
Proof.
  intros H. apply elem_of_subseteq. intros z Z.
  unfold context_names. apply elem_of_list_to_set, list_elem_of_In, List.in_flat_map.
  exists (y, (l, τ)). split.
  - apply list_elem_of_In, elem_of_map_to_list; assumption.
  - apply list_elem_of_In, elem_of_elements; assumption.
Qed.

Lemma subst_context_single Γ x s l τ :
  x ∉ names τ -> x ∉ context_names Γ ->
  subst_context x s l τ (<[x:=(l,τ)]>Γ) Γ.
Proof.
  intros T N y ly ty H. case_decide; subst.
  - rewrite lookup_insert, decide_True in H by reflexivity. injection H as -> ->.
    rewrite subst_fresh by assumption. auto.
  - rewrite lookup_insert_ne in H by auto.
    rewrite subst_fresh; [exact H|].
    pose proof (lookup_context_names _ _ _ _ H). set_solver.
Qed.

Lemma runtime_otype_open Γ s l τ L t :
  runtime_typing Γ s l τ ->
  (forall x : atom, x ∉ L -> runtime_otype (<[x:=(l,τ)]>Γ) (open x t)) ->
  runtime_otype Γ (open s t).
Proof.
  intros A B.
  pose proof (is_fresh (L ∪ names τ ∪ names t ∪ context_names Γ)) as F.
  set (x := fresh (L ∪ names τ ∪ names t ∪ context_names Γ)) in *.
  unfold open at 1. rewrite (open_intro x s t) by set_solver.
  eapply (proj2 (runtime_subst x s l τ));
    [apply B; set_solver|apply subst_context_single; set_solver|exact A].
Qed.

Lemma runtime_type_open Γ s l τ L e t k :
  runtime_typing Γ s l τ ->
  (forall x : atom, x ∉ L -> runtime_typing (<[x:=(l,τ)]>Γ) (open x e) k (open x t)) ->
  runtime_typing Γ (open s e) k (open s t).
Proof.
  intros A B.
  pose proof (is_fresh (L ∪ names τ ∪ names e ∪ names t ∪ context_names Γ)) as F.
  set (x := fresh (L ∪ names τ ∪ names e ∪ names t ∪ context_names Γ)) in *.
  unfold open at 1 2. rewrite (open_intro x s e), (open_intro x s t) by set_solver.
  eapply (proj1 (runtime_subst x s l τ));
    [apply B; set_solver|apply subst_context_single; set_solver|exact A].
Qed.

(* Inversion exposes the rule underneath a sequence of conversions. *)
Inductive runtime_core : tctx -> expr -> bool -> expr -> Prop :=
| CTFVar Γ x l τ :
    Γ !! x = Some (l, τ) ->
    lc τ ->
    runtime_core Γ <{ fvar x }> l <{ τ }>
| CTUnit Γ : runtime_core Γ <{ () }> ⊥ <{ 𝟙 }>
| CTLit Γ b : runtime_core Γ <{ lit b }> ⊥ <{ 𝔹 }>
| CTFun Γ x l τ e :
    Σ !! x = Some (DFun (l, τ) e) ->
    lc τ ->
    runtime_core Γ <{ gvar x }> l <{ τ }>
| CTAbs Γ l1 l2 e τ1 τ2 L :
    (forall x, x ∉ L -> runtime_typing (<[x:=(l2, τ2)]>Γ) <{ e^x }> l1 <{ τ1^x }>) ->
    lc τ2 ->
    runtime_core Γ <{ \:{l2}τ2 => e }> l1 <{ (Π:{l2}τ2, τ1) }>
| CTLet Γ l1 l2 l e1 e2 τ1 τ2 L :
    runtime_typing Γ <{ e1 }> l1 <{ τ1 }> ->
    (forall x, x ∉ L -> runtime_typing (<[x:=(l1, τ1)]>Γ) <{ e2^x }> l2 <{ τ2^x }>) ->
    l = l1 ⊔ l2 ->
    runtime_core Γ <{ let e1 in e2 }> l <{ τ2^e1 }>
| CTApp Γ l1 l2 e1 e2 τ1 τ2 :
    runtime_typing Γ <{ e1 }> l1 <{ (Π:{l2}τ2, τ1) }> ->
    runtime_typing Γ <{ e2 }> l2 <{ τ2 }> ->
    runtime_core Γ <{ e1 e2 }> l1 <{ τ1^e2 }>
| CTPair Γ l1 l2 l e1 e2 τ1 τ2 :
    runtime_typing Γ <{ e1 }> l1 <{ τ1 }> ->
    runtime_typing Γ <{ e2 }> l2 <{ τ2 }> ->
    l = l1 ⊔ l2 ->
    runtime_core Γ <{ (e1, e2) }> l <{ τ1 * τ2 }>
| CTProj Γ l b e τ1 τ2 :
    runtime_typing Γ <{ e }> l <{ τ1 * τ2 }> ->
    runtime_core Γ <{ π@b e }> l <{ ite b τ1 τ2 }>
| CTInj Γ l b e τ1 τ2 :
    runtime_typing Γ <{ e }> l <{ ite b τ1 τ2 }> ->
    lc (ESum false τ1 τ2) ->
    runtime_core Γ <{ inj@b<τ1 + τ2> e }> l <{ τ1 + τ2 }>
| CTIf Γ l1 l2 l e0 e1 e2 τ :
    runtime_typing Γ <{ e0 }> ⊥ <{ 𝔹 }> ->
    runtime_typing Γ <{ e1 }> l1 <{ τ^(lit true) }> ->
    runtime_typing Γ <{ e2 }> l2 <{ τ^(lit false) }> ->
    scoped 1 τ ->
    l = l1 ⊔ l2 ->
    runtime_core Γ <{ if e0 then e1 else e2 }> l <{ τ^e0 }>
| CTIfNoDep Γ l0 l1 l2 l e0 e1 e2 τ :
    runtime_typing Γ <{ e0 }> l0 <{ 𝔹 }> ->
    runtime_typing Γ <{ e1 }> l1 <{ τ }> ->
    runtime_typing Γ <{ e2 }> l2 <{ τ }> ->
    l = l0 ⊔ l1 ⊔ l2 ->
    runtime_core Γ <{ if e0 then e1 else e2 }> l <{ τ }>
| CTCase Γ l1 l2 l e0 e1 e2 τ1 τ2 τ L1 L2 :
    runtime_typing Γ <{ e0 }> ⊥ <{ τ1 + τ2 }> ->
    (forall x, x ∉ L1 -> runtime_typing (<[x:=(⊥, τ1)]>Γ) <{ e1^x }> l1 <{ τ^(inl<τ1 + τ2> x) }>) ->
    (forall x, x ∉ L2 -> runtime_typing (<[x:=(⊥, τ2)]>Γ) <{ e2^x }> l2 <{ τ^(inr<τ1 + τ2> x) }>) ->
    scoped 1 τ ->
    l = l1 ⊔ l2 ->
    runtime_core Γ <{ case e0 of e1 | e2 }> l <{ τ^e0 }>
| CTCaseNoDep Γ l0 l1 l2 l e0 e1 e2 τ1 τ2 τ L1 L2 :
    runtime_typing Γ <{ e0 }> l0 <{ τ1 + τ2 }> ->
    (forall x, x ∉ L1 -> runtime_typing (<[x:=(l0, τ1)]>Γ) <{ e1^x }> l1 <{ τ }>) ->
    (forall x, x ∉ L2 -> runtime_typing (<[x:=(l0, τ2)]>Γ) <{ e2^x }> l2 <{ τ }>) ->
    lc τ ->
    l = l0 ⊔ l1 ⊔ l2 ->
    runtime_core Γ <{ case e0 of e1 | e2 }> l <{ τ }>
| CTFold Γ l X e τ :
    Σ !! X = Some (DADT τ) ->
    runtime_typing Γ <{ e }> l <{ τ }> ->
    runtime_core Γ <{ fold<X> e }> l <{ gvar X }>
| CTUnfold Γ l X e τ :
    Σ !! X = Some (DADT τ) ->
    runtime_typing Γ <{ e }> l <{ gvar X }> ->
    lc τ ->
    runtime_core Γ <{ unfold<X> e }> l <{ τ }>
| CTSec Γ l e :
    runtime_typing Γ <{ e }> l <{ 𝔹 }> ->
    runtime_core Γ <{ s𝔹 e }> l <{ ~𝔹 }>
| CTMux Γ e0 e1 e2 τ :
    runtime_typing Γ <{ e0 }> ⊥ <{ ~𝔹 }> ->
    runtime_typing Γ <{ e1 }> ⊥ <{ τ }> ->
    runtime_typing Γ <{ e2 }> ⊥ <{ τ }> ->
    oblivious_type τ ->
    runtime_core Γ <{ mux e0 e1 e2 }> ⊥ <{ τ }>
| CTOInj Γ b e τ1 τ2 :
    runtime_typing Γ <{ e }> ⊥ <{ ite b τ1 τ2 }> ->
    runtime_otype Γ (ESum true τ1 τ2) ->
    runtime_core Γ <{ ~inj@b<τ1 ~+ τ2> e }> ⊥ <{ τ1 ~+ τ2 }>
| CTOIf Γ l1 l2 e0 e1 e2 τ :
    runtime_typing Γ <{ e0 }> ⊥ <{ ~𝔹 }> ->
    runtime_typing Γ <{ e1 }> l1 <{ τ }> ->
    runtime_typing Γ <{ e2 }> l2 <{ τ }> ->
    lc τ ->
    runtime_core Γ <{ ~if e0 then e1 else e2 }> ⊤ <{ τ }>
| CTOCase Γ l1 l2 e0 e1 e2 τ1 τ2 τ L1 L2 :
    runtime_typing Γ <{ e0 }> ⊥ <{ τ1 ~+ τ2 }> ->
    (forall x, x ∉ L1 -> runtime_typing (<[x:=(⊥, τ1)]>Γ) <{ e1^x }> l1 <{ τ }>) ->
    (forall x, x ∉ L2 -> runtime_typing (<[x:=(⊥, τ2)]>Γ) <{ e2^x }> l2 <{ τ }>) ->
    lc τ ->
    runtime_core Γ <{ ~case e0 of e1 | e2 }> ⊤ <{ τ }>
| CTTape Γ l e τ :
    runtime_typing Γ <{ e }> l <{ τ }> ->
    oblivious_type τ ->
    runtime_core Γ <{ tape e }> ⊥ <{ τ }>

| CTBoxedLit Γ b : runtime_core Γ <{ [b] }> ⊥ <{ ~𝔹 }>
| CTBoxedInj Γ b v ω :
    ovalty <{ [inj@b<ω> v] }> ω ->
    runtime_core Γ <{ [inj@b<ω> v] }> ⊥ <{ ω }>.

Local Hint Constructors runtime_core : oadt_core.

Lemma label_reflexive (l : bool) : l ⊑ l.
Proof. by destruct l. Qed.

Lemma label_transitive (l k j : bool) : l ⊑ k -> k ⊑ j -> l ⊑ j.
Proof. by destruct l, k, j. Qed.

Lemma runtime_invert Γ e l τ : runtime_typing Γ e l τ ->
  exists k t, runtime_core Γ e k t /\ pared_equiv Σ t τ /\ k ⊑ l.
Proof.
  induction 1; try solve [do 2 eexists; repeat split; eauto using QRRefl, label_reflexive with oadt_core].
  destruct IHruntime_typing as [m [t [C [P N]]]].
  exists m, t. eauto using equivalent_trans, label_transitive.
Qed.

Inductive value_at : type_head -> expr -> Prop :=
| AtUnit : value_at HUnit EUnitV
| AtLit b : value_at (HBool false) (ELit b)
| AtPair (a b : expr) : wval a -> wval b -> value_at HProd (EPair a b)
| AtAbs l t e : value_at (HPi l) (EAbs l t e)
| AtInj b t e : wval e -> value_at (HSum false) (EInj false b t e)
| AtFold x e : wval e -> value_at (HADT x) (EFold x e)
| AtBoxLit b : value_at (HBool true) (EBoxedLit b)
| AtBoxInj b a c v : otval a -> otval c -> oval v ->
    value_at (HSum true) (EBoxedInj b (ESum true a c) v).

Definition weak_conditional v :=
  exists b a c, v = EIte true (EBoxedLit b) a c /\ wval a /\ wval c.

Lemma wval_form Γ v l t h :
  runtime_typing Γ v l t -> type_head_of t = Some h -> wval v ->
  value_at h v \/ (l = true /\ weak_conditional v).
Proof.
  intros [k [u [C [E N]]]]%runtime_invert H W.
  inversion W; subst; inversion C; subst;
    try solve [right; split; [now destruct l|do 3 eexists; eauto]].
  all: try match goal with O : ovalty (EBoxedInj _ _ _) _ |- _ => inversion O; subst end.
  all: try match goal with H : otval (ESum true _ _) |- _ => inversion H; subst end.
  all: match goal with E : pared_equiv _ ?a ?t |- value_at ?h ?v \/ _ =>
    let Q := fresh "Q" in
    assert (Q : exists j, type_head_of a = Some j /\ value_at j v) by
      (eexists; split;
        [simpl; try reflexivity;
           match goal with H : _ = Some (DADT _) |- _ => rewrite H; reflexivity end
        | eauto using value_at, ovalty_values, otval]);
    destruct Q as [j [A B]];
    left; replace h with j; eauto using equivalent_heads
  end.
Qed.

Lemma safe_wval Γ v t : runtime_typing Γ v false t -> wval v -> val v.
Proof.
  intros T W. revert t T. induction W; intros t [k [u [C [E N]]]]%runtime_invert;
    inversion C; subst; eauto using val; try discriminate.
  all: repeat match goal with l : bool |- _ => destruct l end;
    cbv in N;
    try contradiction; eauto using val.
Qed.

Lemma rt_woval Γ v l t : runtime_typing Γ v l t ->
  oblivious_type t -> wval v -> woval v.
Proof.
  intros T O W. revert l t T O. induction W;
    intros leak t [k [u [C [E N]]]]%runtime_invert O;
    inversion C; subst; eauto using woval.
  all: match goal with E : pared_equiv _ ?u ?t |- _ =>
    assert (U : oblivious_type u) by (eapply oblivious_type_conv; eassumption)
  end.
  all: try solve [
    match goal with H : runtime_typing _ _ _ ?a, K : runtime_typing _ _ _ ?b |- woval (EPair _ _) =>
      destruct (oblivious_product a b U); eauto using woval
    end].
  all: try solve [eauto using woval].
  all: match goal with U : oblivious_type ?u |- _ =>
    assert (Q : exists h, type_head_of u = Some h /\
      h <> HUnit /\ h <> HBool true /\ h <> HProd /\ h <> HSum true)
      by (eexists; split;
            [simpl; try reflexivity;
             match goal with H : _ = Some (DADT _) |- _ => rewrite H; reflexivity end
            | repeat split; discriminate]);
    destruct Q as [h [A Bad]]; let S := fresh "S" in pose proof (oblivious_head _ _ U A) as S; tauto
  end.
Qed.

Lemma runtime_ovalty Γ v ω :
  runtime_typing Γ v false ω -> otval ω -> wval v -> ovalty v ω.
Proof.
  intros T O W. revert ω T O. induction W;
    intros w [k [t [C [E N]]]]%runtime_invert O;
    inversion C; subst; try (cbv in N; contradiction).
  all: try solve [
    match goal with H : ovalty (EBoxedInj _ ?t _) ?t,
      O : otval ?w, E : pared_equiv _ ?t ?w |- _ =>
      let F := fresh "F" in
      pose proof (equivalent_otval t w (proj2 (ovalty_values _ _ H)) O E) as F;
      rewrite <- F; exact H
    end].
  all: inversion O; subst.
  all: try solve [constructor; eauto].
  all: try solve [
    match goal with E : pared_equiv _ ?a ?c |- _ =>
      let A := eval cbn in (type_head_of a) in
      let C := eval cbn in (type_head_of c) in
      lazymatch constr:((A,C)) with
      | (Some ?u, Some ?v) =>
          let R := fresh "R" in pose proof (equivalent_heads a c u v eq_refl eq_refl E) as R;
          discriminate R
      end
    end].
  all: try solve [
    match goal with E : pared_equiv _ (EGVar ?x) ?c, H : Σ !! ?x = Some (DADT _) |- _ =>
      let C := eval cbn in (type_head_of c) in
      lazymatch C with Some ?v =>
        let R := fresh "R" in
        assert (R : HADT x = v) by (eapply (equivalent_heads (EGVar x) c); [simpl; rewrite H; reflexivity | reflexivity | exact E]);
        discriminate R
      end
    end].
  all: match goal with
    | H : pared_equiv _ (EProd _ _) (EProd _ _) |- _ => apply equivalent_prod in H; destruct H
    end;
    destruct l1, l2; cbv in N; try contradiction;
    constructor; eauto 7 using rt_eqtype, otval_lc.
Qed.

Lemma ovalty_runtime Γ v ω : ovalty v ω -> runtime_typing Γ v false ω.
Proof.
  induction 1; try solve [eauto with oadt_rt].
  apply RTBoxedInj, OTOSum; assumption.
Qed.

Lemma otval_has_value ω : otval ω -> exists v, ovalty v ω.
Proof.
  induction 1.
  - exists EUnitV. apply OTUnit.
  - exists (EBoxedLit true). apply OTOBool.
  - destruct IHotval1 as [a A], IHotval2 as [c C].
    exists (EPair a c). now apply OTProd.
  - destruct IHotval1 as [a A].
    exists (EBoxedInj true (ESum true ω1 ω2) a). now apply OTOSum.
Qed.

Lemma red_context f e : ectx f -> red (step Σ) e -> red (step Σ) (f e).
Proof. intros C [a P]. exists (f a). eauto using SCtx. Qed.

Local Hint Constructors step ectx lectx wval otval : oadt_step.
Local Hint Resolve red_context : oadt_step.

Lemma step_pared e e' : step Σ e e' -> lc e -> pared Σ e e'.
Proof.
  induction 1; intros C;
    try match goal with C : ectx _ |- _ => destruct C end;
    try match goal with C : lectx _ |- _ => destruct C end;
    cbn in *;
    try match goal with C : lc _ |- _ => inversion C; subst; clear C end;
    try solve [eauto 4 using oval_lc, otval_lc with oadt_par oadt_lc].
  all: repeat match goal with
  | H : lc (EAbs _ _ _) |- _ => inversion H; subst; clear H
  | H : lc (EInj _ _ _ _) |- _ => inversion H; subst; clear H
  | H : lc (EPair _ _) |- _ => inversion H; subst; clear H
  | H : lc (EFold _ _) |- _ => inversion H; subst; clear H
  | H : lc (EIte true (EBoxedLit _) _ _) |- _ => inversion H; subst; clear H
  | H : forall x : atom, x ∉ ?L -> lc (open (EFVar x) ?a) |- _ =>
    let R := fresh "R" in
    assert (R : forall x : atom, x ∉ L -> pared Σ (open x a) (open x a))
      by (intros; apply RRefl; auto); clear H
  end;
  try solve [eauto 4 using oval_lc, otval_lc with oadt_par oadt_lc].
  all: first [apply ROIfApp | apply ROIfIf | apply RCgrIf | apply RCgrMux];
    eauto using RRefl.
Qed.

Lemma red_app_cond b a c v : wval a -> wval c -> wval v ->
  red (step Σ) (EApp (EIte true (EBoxedLit b) a c) v).
Proof.
  intros. eexists. eapply (SOIf Σ b a c (fun e => EApp e v)); eauto with oadt_step.
Qed.

Lemma red_sec_cond b a c : wval a -> wval c ->
  red (step Σ) (ESec (EIte true (EBoxedLit b) a c)).
Proof.
  intros. eexists. eapply (SOIf Σ b a c ESec); eauto with oadt_step.
Qed.

Lemma red_if_cond b a c p q : wval a -> wval c ->
  red (step Σ) (EIte false (EIte true (EBoxedLit b) a c) p q).
Proof.
  intros. eexists. eapply (SOIf Σ b a c (fun e => EIte false e p q)); eauto with oadt_step.
Qed.

Lemma red_proj_cond b a c p : wval a -> wval c ->
  red (step Σ) (EProj p (EIte true (EBoxedLit b) a c)).
Proof.
  intros. eexists. eapply (SOIf Σ b a c (EProj p)); eauto with oadt_step.
Qed.

Lemma red_case_cond b a c p q : wval a -> wval c ->
  red (step Σ) (ECase false (EIte true (EBoxedLit b) a c) p q).
Proof.
  intros. eexists. eapply (SOIf Σ b a c (fun e => ECase false e p q)); eauto with oadt_step.
Qed.

Lemma red_unfold_cond b a c x : wval a -> wval c ->
  red (step Σ) (EUnfold x (EIte true (EBoxedLit b) a c)).
Proof.
  intros. eexists. eapply (SOIf Σ b a c (EUnfold x)); eauto with oadt_step.
Qed.

Local Hint Resolve red_app_cond red_sec_cond red_if_cond red_proj_cond red_case_cond red_unfold_cond : oadt_step.

Local Ltac lift_red :=
  match goal with
  | H : red _ ?e |- red _ (EProd ?e ?a) =>
      apply (red_context (fun z : expr => EProd z a)); [apply CtxProd1; try assumption|exact H]
  | H : red _ ?e |- red _ (EProd ?a ?e) =>
      apply (red_context (fun z : expr => EProd a z)); [apply CtxProd2; try assumption|exact H]
  | H : red _ ?e |- red _ (ESum true ?e ?a) =>
      apply (red_context (fun z : expr => ESum true z a)); [apply CtxOSum1; try assumption|exact H]
  | H : red _ ?e |- red _ (ESum true ?a ?e) =>
      apply (red_context (fun z : expr => ESum true a z)); [apply CtxOSum2; try assumption|exact H]
  | H : red _ ?e |- red _ (EApp ?e ?a) =>
      apply (red_context (fun z : expr => EApp z a)); [apply CtxApp1; try assumption|exact H]
  | H : red _ ?e |- red _ (EApp ?a ?e) =>
      apply (red_context (fun z : expr => EApp a z)); [apply CtxApp2; try assumption|exact H]
  | H : red _ ?e |- red _ (ELet ?e ?a) =>
      apply (red_context (fun z : expr => ELet z a)); [apply CtxLet; try assumption|exact H]
  | H : red _ ?e |- red _ (ESec ?e) =>
      apply (red_context (fun z : expr => ESec z)); [apply CtxSec; try assumption|exact H]
  | H : red _ ?e |- red _ (EIte false ?e ?a ?c) =>
      apply (red_context (fun z : expr => EIte false z a c)); [apply CtxIf; try assumption|exact H]
  | H : red _ ?e |- red _ (EIte true ?e ?a ?c) =>
      apply (red_context (fun z : expr => EIte true z a c)); [apply CtxOIf1; try assumption|exact H]
  | H : red _ ?e |- red _ (EIte true ?a ?e ?c) =>
      apply (red_context (fun z : expr => EIte true a z c)); [apply CtxOIf2; try assumption|exact H]
  | H : red _ ?e |- red _ (EIte true ?a ?c ?e) =>
      apply (red_context (fun z : expr => EIte true a c z)); [apply CtxOIf3; try assumption|exact H]
  | H : red _ ?e |- red _ (EPair ?e ?a) =>
      apply (red_context (fun z : expr => EPair z a)); [apply CtxPair1; try assumption|exact H]
  | H : red _ ?e |- red _ (EPair ?a ?e) =>
      apply (red_context (fun z : expr => EPair a z)); [apply CtxPair2; try assumption|exact H]
  | H : red _ ?e |- red _ (EProj ?b ?e) =>
      apply (red_context (fun z : expr => EProj b z)); [apply CtxProj; try assumption|exact H]
  | H : red _ ?e |- red _ (EInj false ?b ?a ?e) =>
      apply (red_context (fun z : expr => EInj false b a z)); [apply CtxInj; try assumption|exact H]
  | H : red _ ?e |- red _ (EInj true ?b ?e ?a) =>
      apply (red_context (fun z : expr => EInj true b z a)); [apply CtxOInj1; try assumption|exact H]
  | H : red _ ?e |- red _ (EInj true ?b ?a ?e) =>
      apply (red_context (fun z : expr => EInj true b a z)); [apply CtxOInj2; try assumption|exact H]
  | H : red _ ?e |- red _ (ECase false ?e ?a ?c) =>
      apply (red_context (fun z : expr => ECase false z a c)); [apply CtxCase; try assumption|exact H]
  | H : red _ ?e |- red _ (ECase true ?e ?a ?c) =>
      apply (red_context (fun z : expr => ECase true z a c)); [apply CtxOCase; try assumption|exact H]
  | H : red _ ?e |- red _ (EFold ?x ?e) =>
      apply (red_context (fun z : expr => EFold x z)); [apply CtxFold; try assumption|exact H]
  | H : red _ ?e |- red _ (EUnfold ?x ?e) =>
      apply (red_context (fun z : expr => EUnfold x z)); [apply CtxUnfold; try assumption|exact H]
  | H : red _ ?e |- red _ (ETape ?e) =>
      apply (red_context (fun z : expr => ETape z)); [apply CtxTape; try assumption|exact H]
  | H : red _ ?e |- red _ (EMux ?e ?a ?c) =>
      apply (red_context (fun z : expr => EMux z a c)); [apply CtxMux1; try assumption|exact H]
  | H : red _ ?e |- red _ (EMux ?a ?e ?c) =>
      apply (red_context (fun z : expr => EMux a z c)); [apply CtxMux2; try assumption|exact H]
  | H : red _ ?e |- red _ (EMux ?a ?c ?e) =>
      apply (red_context (fun z : expr => EMux a c z)); [apply CtxMux3; try assumption|exact H]
  end.

Lemma runtime_progress :
  (forall Γ e l τ, runtime_typing Γ e l τ -> Γ = ∅ -> wval e \/ red (step Σ) e) /\
  (forall Γ t, runtime_otype Γ t -> Γ = ∅ -> otval t \/ red (step Σ) t).
Proof.
  apply runtime_mutind; intros; subst;
    repeat match goal with
    | H : ?Γ = ?Γ -> _ |- _ => specialize (H eq_refl); destruct H
    end;
    try solve [rewrite lookup_empty in *; discriminate];
    try solve [right; lift_red];
    try solve [eauto 5 with oadt_step];
    try solve [right; eexists; eauto 6 with oadt_step].
  all: try solve [right; eapply red_context with (f:=fun e => EApp (EGVar _) e);
                  eauto with oadt_step].
  all: try solve [
    match goal with H : ovalty (EBoxedInj _ _ _) _ |- _ =>
      destruct (ovalty_values _ _ H) as [V O]; inversion V; subst;
      left; apply WBoxedInj; assumption
    end].
  all: try solve [
    match goal with H : runtime_typing _ ?e _ ?t, W : wval ?e, O : oblivious_type ?t
      |- _ \/ red _ (ETape ?e) =>
      pose proof (rt_woval _ _ _ _ H O W) as V; inversion V; subst;
      right; eexists; eauto 6 with oadt_step
    end].
  all: try solve [
    match goal with H : runtime_typing _ ?e false (if ?b then ?a else ?c),
                    W : wval ?e, O : otval (ESum true ?a ?c) |- _ =>
      assert (otval (if b then a else c)) by (inversion O; subst; destruct b; assumption);
      destruct (ovalty_values _ _ (runtime_ovalty _ _ _ H ltac:(assumption) W));
      right; eexists; eauto with oadt_step
    end].
  all: repeat match goal with
  | T : runtime_typing _ ?e ?l ?t, V : wval ?e |- _ =>
    let C := fresh "C" in
    assert (C : exists h, type_head_of t = Some h) by
      (eexists; simpl; try reflexivity; congruence);
    let h := fresh "h" in let E := fresh "E" in
    destruct C as [h E];
    let F := fresh "F" in let L := fresh "L" in
    destruct (wval_form _ _ _ _ _ T E V) as [F|[L [?[?[?[? [? ?]]]]]]];
    [simpl in E; try (match goal with H : _ = Some (DADT _) |- context[_] =>
            rewrite H in E end); injection E as <-; inversion F; subst; clear V
    | discriminate L || (subst; clear V)]
  end;
  try solve [eauto 6 with oadt_step];
  try solve [right; eexists; eauto 6 with oadt_step].
  all: try solve [
    match goal with A : otval ?a, B : otval ?b |- _ =>
      destruct (otval_has_value _ A); destruct (otval_has_value _ B);
      right; eexists; eauto 6 with oadt_step
    end].
  all: try solve [right; lift_red].
  all: try solve [right; eexists; first [eapply SApp | eapply SLet | eapply SIf |
    eapply SCase | eapply SProj | eapply SUnfold | eapply SFun | eapply SOADT |
    eapply SSec | eapply SMux]; eassumption].
  - destruct (wval_form _ _ _ _ (HADT X) H0 ltac:(simpl; rewrite H; reflexivity) H1)
      as [F|[_ [c [a [q [-> [A B]]]]]]].
    + inversion F; subst. right. eexists. eapply SUnfold; eassumption.
    + right. eapply red_unfold_cond; eassumption.
  - assert (O : otval (if b then τ1 else τ2)) by (inversion H2; subst; destruct b; assumption).
    destruct (ovalty_values _ _ (runtime_ovalty _ _ _ H O H0)) as [V _].
    right. eexists. apply SOInj; assumption.
Qed.

Lemma rt_inj_payload Γ b t v l a c :
  runtime_typing Γ (EInj false b t v) l (ESum false a c) ->
  runtime_typing Γ v l (if b then a else c) /\ pared_equiv Σ t (ESum false a c).
Proof.
  intros T. pose proof (rt_type_lc _ _ _ _ T) as L.
  inversion L; subst.
  destruct (runtime_invert _ _ _ _ T) as [k [u [C [E N]]]].
  inversion C; subst.
  destruct (equivalent_sum _ _ _ _ _ _ E) as [_ [A B]].
  split; [destruct b; eauto using rt_conv|exact E].
Qed.

Lemma rt_box_payload Γ b a c v l (u w : expr) :
  runtime_typing Γ (EBoxedInj b (ESum true a c) v) l (ESum true u w) ->
  runtime_typing Γ v false (if b then u else w) /\
  pared_equiv Σ a u /\ pared_equiv Σ c w.
Proof.
  intros T. pose proof (rt_type_lc _ _ _ _ T) as L. inversion L; subst.
  destruct (runtime_invert _ _ _ _ T) as [k [t [C [E N]]]].
  inversion C; subst.
  match goal with O : ovalty (EBoxedInj _ _ _) _ |- _ => inversion O; subst end.
  destruct (equivalent_sum _ _ _ _ _ _ E) as [_ [A B]].
  repeat split; eauto.
  destruct b; eauto using rt_eqtype, ovalty_runtime.
Qed.

Lemma rt_weak_branches Γ b a c l t :
  runtime_typing Γ (EIte true (EBoxedLit b) a c) l t ->
  l = true /\ exists l1 l2, runtime_typing Γ a l1 t /\ runtime_typing Γ c l2 t.
Proof.
  intros T. pose proof (rt_type_lc _ _ _ _ T) as L.
  destruct (runtime_invert _ _ _ _ T) as [k [u [C [E N]]]].
  inversion C; subst.
  split; [now destruct l|]. do 2 eexists; split; eauto using rt_eqtype.
Qed.

Lemma rt_beta Γ l k t e a c v :
  runtime_typing Γ (EAbs l t e) k (EPi l a c) ->
  runtime_typing Γ v l a ->
  runtime_typing Γ (open v e) k (open v c).
Proof.
  intros T V.
  pose proof (rt_type_lc _ _ _ _ T) as P.
  pose proof (rt_lc _ _ _ _ V) as L.
  pose proof (lc_scoped _ P) as [_ B].
  destruct (runtime_invert _ _ _ _ T) as [j [u [C [E N]]]].
  inversion C; subst.
  destruct (equivalent_pi _ _ _ _ _ _ E) as [_ [D F]].
  eapply rt_conv; [eapply runtime_type_open | apply F; assumption | | exact N].
  - eapply rt_eqtype; eauto using equivalent_sym.
  - eassumption.
  - apply scoped_lc, scoped_open; eauto using lc_scoped.
Qed.

Lemma runtime_open_constant Γ s l τ L e k t :
  runtime_typing Γ s l τ -> lc t ->
  (forall x : atom, x ∉ L -> runtime_typing (<[x:=(l,τ)]>Γ) (open x e) k t) ->
  runtime_typing Γ (open s e) k t.
Proof.
  intros A C B. rewrite <- (open_lc t s 0 C). eapply runtime_type_open; [exact A|].
  intros x N. unfold open at 2. rewrite open_lc by assumption. eauto.
Qed.

Lemma runtime_open_case Γ v l τ L e k t b (a c : expr) :
  runtime_typing Γ v l τ ->
  (forall x : atom, x ∉ L -> runtime_typing (<[x:=(l,τ)]>Γ) (open x e) k
     (open (EInj false b (ESum false a c) (EFVar x)) t)) ->
  runtime_typing Γ (open v e) k (open (EInj false b (ESum false a c) v) t).
Proof.
  intros A B. pose proof (rt_lc _ _ _ _ A) as C.
  set (F := L ∪ names τ ∪ names e ∪ names t ∪ names a ∪ names c ∪ context_names Γ).
  pose proof (is_fresh F) as N. set (x := fresh F) in *. unfold F in N.
  pose proof (B x ltac:(clear - N; set_solver)) as Q.
  assert (R : subst_context x v l τ (<[x:=(l,τ)]>Γ) Γ)
    by (apply subst_context_single; clear - N; set_solver).
  pose proof (proj1 (runtime_subst x v l τ) _ _ _ _ Q _ R A) as S.
  rewrite !subst_open in S by assumption.
  simpl in S. rewrite !decide_True in S by reflexivity.
  rewrite (subst_fresh x v e), (subst_fresh x v t), (subst_fresh x v a), (subst_fresh x v c) in S
    by (clear - N; set_solver).
  exact S.
Qed.

Lemma equivalent_inj_annotation b v t u :
  lc v -> pared_equiv Σ t u ->
  pared_equiv Σ (EInj false b t v) (EInj false b u v).
Proof.
  intros C. apply (equivalent_map (fun a : expr => EInj false b a v)). intros a c H.
  apply RCgrInj; auto using RRefl.
Qed.

Lemma rt_case_beta Γ b t v l1 l2 a c e1 e2 τ L1 L2 :
  runtime_typing Γ (EInj false b t v) false (ESum false a c) ->
  (forall x : atom, x ∉ L1 -> runtime_typing (<[x:=(false,a)]>Γ) (open x e1) l1
       (open (EInj false true (ESum false a c) (EFVar x)) τ)) ->
  (forall x : atom, x ∉ L2 -> runtime_typing (<[x:=(false,c)]>Γ) (open x e2) l2
       (open (EInj false false (ESum false a c) (EFVar x)) τ)) ->
  scoped 1 τ ->
  runtime_typing Γ (if b then open v e1 else open v e2) (l1 ⊔ l2)
     (open (EInj false b t v) τ).
Proof.
  intros T A B M. destruct (rt_inj_payload _ _ _ _ _ _ _ T) as [V E].
  assert (Q : pared_equiv Σ (open (EInj false b (ESum false a c) v) τ)
                           (open (EInj false b t v) τ)).
  { apply equivalent_open; auto. apply equivalent_inj_annotation;
      eauto using rt_lc, equivalent_sym. }
  assert (C : lc (open (EInj false b t v) τ)).
  { apply scoped_lc, scoped_open; eauto using rt_lc, lc_scoped. }
  destruct b; simpl in *; eapply rt_conv;
    try solve [eapply runtime_open_case; eassumption | exact Q | exact C |
               destruct l1, l2; reflexivity].
Qed.

Lemma oadt_unfold_type Γ x t e v :
  Σ !! x = Some (DOADT t e) -> runtime_typing Γ v false t ->
  runtime_otype Γ (open v e).
Proof.
  intros H T. pose proof (global_def _ _ H) as D. inversion D; subst.
  eapply runtime_otype_open; [exact T|]. intros x0 N.
  eapply (proj2 runtime_weaken).
  - eapply (proj2 translate_typing); eauto.
  - apply context_insert, map_empty_subseteq.
Qed.

Lemma core_runtime Γ e l τ : runtime_core Γ e l τ -> runtime_typing Γ e l τ.
Proof. inversion 1; subst; eauto 6 with oadt_rt. Qed.

Local Ltac solve_labels :=
  repeat match goal with l : bool |- _ => destruct l end;
  repeat match goal with N : _ ⊑ _ |- _ =>
    cbv in N
  end;
  cbv; tauto || congruence.

Lemma equivalent_after_step Γ a a' l t :
  runtime_typing Γ a l t -> step Σ a a' -> pared_equiv Σ a a'.
Proof. eauto using pared_equivalent, step_pared, rt_lc. Qed.

Lemma global_step x e : step Σ (EGVar x) e ->
  exists T, Σ !! x = Some (DFun T e).
Proof.
  inversion 1; subst; eauto.
  all: repeat match goal with H : ectx _ |- _ => destruct H | H : lectx _ |- _ => destruct H end;
    discriminate.
Qed.

Lemma rtc_type_sum_step (Γ : tctx) p (a c : expr) :
  runtime_otype Γ (ESum true a c) -> step Σ (ESum true a c) p ->
  exists a' c', p = ESum true a' c' /\
    pared_equiv Σ a a' /\ pared_equiv Σ c c'.
Proof.
  intros K S. apply step_pared in S; eauto using rt_otype_lc.
  inversion S; subst; do 2 eexists; repeat split; eauto using pared_equivalent, QRRefl.
Qed.

Lemma scoped_pi_body Γ f l k t a :
  runtime_typing Γ f l (EPi k t a) -> scoped 1 a.
Proof. intros H. exact (proj2 (lc_scoped _ (rt_type_lc _ _ _ _ H))). Qed.

Lemma oval_wval v : oval v -> wval v.
Proof. induction 1; eauto using wval. Qed.

Lemma runtime_motive Γ l τ e k t L :
  (forall x : atom, x ∉ L -> runtime_typing (<[x:=(l,τ)]>Γ) (open x e) k (open x t)) ->
  scoped 1 t.
Proof. intros H. eapply binder_lc with (L:=L); eauto using rt_type_lc. Qed.

Local Ltac retarget_runtime new :=
  eapply rt_eqtype with (τ:=new);
  [eauto 6 with oadt_rt |
   apply equivalent_open; [eauto using scoped_pi_body, runtime_motive | apply equivalent_sym; eauto using equivalent_after_step] |
   assumption].

Lemma runtime_preservation e e' : step Σ e e' ->
  (forall Γ l τ, runtime_typing Γ e l τ -> runtime_typing Γ e' l τ) /\
  (forall Γ, runtime_otype Γ e -> runtime_otype Γ e').
Proof.
  induction 1;
    try match goal with C : ectx _ |- _ => destruct C end;
    try match goal with C : lectx _ |- _ => destruct C end;
    split_hyps; simpl;
    split.
  all: try solve [
    intros Γ K; inversion K; subst;
    solve [eauto 6 with oadt_rt |
           eapply runtime_otype_open; eassumption |
           match goal with H : runtime_typing _ (EInj false ?b _ _) _ (ESum false _ _) |- _ =>
             apply rt_inj_payload in H; destruct H as [H _];
             destruct b; simpl in *; eapply runtime_otype_open; eassumption
           end |
           match goal with H : Σ !! ?x = Some (DOADT ?a ?t), Q : Σ !! ?x = Some (DOADT ?c ?u) |- _ =>
             let E := fresh "E" in assert (E : a = c) by congruence;
             let F := fresh "F" in assert (F : t = u) by congruence;
             subst; eapply oadt_unfold_type; eassumption
           end |
           match goal with H : runtime_typing _ (EIte true (EBoxedLit _) _ _) false _ |- _ =>
             apply rt_weak_branches in H; destruct H; discriminate
           end |
           match goal with H : step _ (EGVar _) _ |- _ =>
             apply global_step in H; destruct H; congruence
           end |
           destruct b; simpl in *; eauto with oadt_rt]].
  all: try (let T := fresh "Ty" in intros Γ leak target T;
    first [match type of T with runtime_typing _ _ _ _ =>
      let L := fresh "L" in pose proof (rt_type_lc _ _ _ _ T) as L;
      let C := fresh "C" in let P := fresh "P" in let N := fresh "N" in
      destruct (runtime_invert _ _ _ _ T) as [? [? [C [P N]]]];
      let B := fresh "B" in pose proof (rt_type_lc _ _ _ _ (core_runtime _ _ _ _ C)) as B;
      eapply rt_conv; [|exact P|exact L|exact N];
      inversion C; subst; clear C T
    end |
    inversion T]).
  all: try solve [eauto 6 using rt_beta, rt_case_beta, ovalty_runtime with oadt_rt].
  all: try solve [
    match goal with H : Σ !! ?x = Some (DFun ?T ?e) |- _ =>
      destruct T as [l t] || idtac;
      match goal with H0 : Σ !! x = Some (DFun (_,_) e) |- _ =>
        destruct (global_fun _ _ _ _ H0) as [F _]; eapply (proj1 runtime_weaken);
        [eapply (proj1 translate_typing); exact F|apply map_empty_subseteq]
      end
    end].
  all: try solve [eapply rt_label; [eapply runtime_type_open; eassumption|solve_labels]].
  all: try solve [destruct b; assumption].
  all: try solve [destruct b; simpl in *; solve [eapply rt_label; [eassumption|solve_labels]]].
  all: try solve [eapply rt_label; [apply RTBoxedLit|solve_labels]].
  all: try solve [
    match goal with H : runtime_typing _ (EPair _ _) _ (EProd _ _) |- _ =>
      destruct (runtime_invert _ _ _ _ H) as [p [t [C [E N]]]];
      inversion C; subst; clear C;
      let F := fresh "F" in pose proof (rt_type_lc _ _ _ _ H) as F;
      inversion F; subst; apply equivalent_prod in E; destruct E;
      destruct b; simpl in *; eapply rt_conv; try eassumption; solve_labels
    end].
  all: try solve [
    match goal with H : runtime_typing _ (EFold ?Y _) _ (EGVar ?X) |- _ =>
      destruct (runtime_invert _ _ _ _ H) as [p [t [C [E N]]]];
      inversion C; subst; clear C;
      let I := fresh "I" in assert (I : HADT Y = HADT X) by
        (eapply equivalent_heads; [simpl; congruence|simpl; congruence|exact E]);
      injection I as R; subst X;
      match goal with H : Σ !! ?Y0 = Some (DADT ?t), H' : Σ !! ?Y0 = Some (DADT ?u) |- _ =>
        let E := fresh "E" in assert (E : t=u) by congruence; subst
      end;
      eapply rt_label; eassumption
    end].
  all: try solve [
    match goal with H : runtime_typing _ (EInj false ?b _ _) _ (ESum false _ _) |- _ =>
      apply rt_inj_payload in H; destruct H as [H _];
      destruct b; simpl in *;
      solve [eapply rt_label; [eapply runtime_open_constant; eassumption | solve_labels]]
    end].
  all: try solve [
    match goal with H : runtime_typing _ _ _ (if ?b then ?a else ?c),
                    O : otval (ESum true ?a ?c) |- _ =>
      let C := fresh "C" in assert (C : otval (if b then a else c))
        by (inversion O; subst; destruct b; assumption);
      apply RTBoxedInj, OTOSum;
      [eapply runtime_ovalty; eauto using oval_wval|
       inversion O; subst; destruct b; assumption]
    end].
  all: try solve [
    match goal with T : runtime_typing _ (EBoxedInj _ _ _) _ (ESum true _ _) |- _ =>
      apply rt_box_payload in T; destruct T as [V [P Q]];
      destruct b; simpl in *; eapply RTOIf;
      [apply RTBoxedLit | eapply runtime_open_constant | eapply runtime_open_constant | assumption];
      eauto 6 using rt_eqtype, ovalty_runtime, rt_type_lc, otval_lc, ovalty_values
    end].
  all: try solve [
    match goal with H : runtime_typing _ (EIte true (EBoxedLit _) _ _) _ _ |- _ =>
      apply rt_weak_branches in H;
      destruct H as [M [? [? [? ?]]]];
      try discriminate M; subst;
      eauto 8 using rt_label, label_reflexive with oadt_rt
    end].
  all: try solve [
    match goal with H : runtime_typing _ (EPair _ _) _ _, O : oblivious_type _ |- _ =>
      destruct (runtime_invert _ _ _ _ H) as [p [t [C [E N]]]];
      inversion C; subst; clear C;
      match type of E with pared_equiv _ (EProd ?a ?c) _ =>
        let Q := fresh "Q" in assert (Q : oblivious_type (EProd a c))
          by (eapply oblivious_type_conv; [exact E|exact O]);
        apply oblivious_product in Q; destruct Q;
        eapply rt_eqtype with (τ:=EProd a c);
        [eapply RTPair with (l1:=false) (l2:=false); [eapply RTTape; eassumption|eapply RTTape; eassumption|reflexivity]
           |exact E|assumption]
      end
    end].
  all: try solve [
    match goal with K : runtime_otype ?Γ (ESum true ?a ?c), S : step _ (ESum true ?a ?c) _ |- _ =>
      destruct (rtc_type_sum_step _ _ _ _ K S) as [a' [c' [-> [P Q]]]];
      eapply rt_eqtype; [apply RTOInj | apply equivalent_sym, pared_equivalent, step_pared; eauto using rt_otype_lc | assumption];
      [destruct b; simpl in *; eapply rt_eqtype; eauto using rt_otype_lc |
       eauto]
    end].
  all: try solve [
    match goal with |- runtime_typing _ (EApp _ ?a') _ (open _ ?M) => retarget_runtime (open a' M)
    | |- runtime_typing _ (ELet ?a' _) _ (open _ ?M) => retarget_runtime (open a' M)
    | |- runtime_typing _ (EIte false ?a' _ _) _ (open _ ?M) => retarget_runtime (open a' M)
    | |- runtime_typing _ (ECase false ?a' _ _) _ (open _ ?M) => retarget_runtime (open a' M)
    end].
  all: try solve [
    match goal with T : runtime_typing ?Γ ?e _ ?t |- runtime_typing ?Γ ?e false ?t =>
      destruct (runtime_invert _ _ _ _ T) as [n [u [C [E F]]]];
      inversion C; subst; clear C;
      eapply rt_eqtype; [first [apply RTUnit | apply RTBoxedLit | apply RTBoxedInj; assumption] | exact E | assumption]
    end].
  all: try solve [
    match goal with H : runtime_typing _ (EGVar ?x) _ _, N : Σ !! ?x = Some (DOADT _ _) |- _ =>
      destruct (runtime_invert _ _ _ _ H) as [? [? [F _]]];
      inversion F; subst; congruence
    end].
  - destruct (runtime_invert _ _ _ _ H3) as [k [t [C [E F]]]].
    inversion C; subst. apply equivalent_pi in E. destruct E as [E _]. subst l2.
    eapply rt_beta; eassumption.
  - pose proof (rt_type_lc _ _ _ _ H6) as Q. inversion Q; subst.
    destruct (runtime_invert _ _ _ _ H6) as [k [t [C [E F]]]].
    inversion C; subst. apply equivalent_prod in E. destruct E as [E1 E2].
    destruct b; simpl in *; solve [eapply rt_conv; try eassumption; solve_labels].
  - destruct (runtime_invert _ _ _ _ H4) as [k [t [C [E F]]]].
    inversion C; subst.
    assert (I : HADT X' = HADT X).
    { eapply (equivalent_heads (EGVar X') (EGVar X)); [| |exact E].
      all: simpl; match goal with H : Σ !! _ = Some (DADT _) |- _ => rewrite H; reflexivity end. }
    injection I as I. subst X'.
    match goal with H : Σ !! X = Some (DADT ?a), H' : Σ !! X = Some (DADT ?c) |- _ =>
      assert (a = c) by congruence; subst
    end.
    eapply rt_label; eassumption.
  - assert (E : T = (x0, x1)) by congruence.
    assert (E' : e = e0) by congruence. subst T e.
    destruct (global_fun _ _ _ _ H1) as [A _].
    eapply (proj1 runtime_weaken) with (Γ:=∅).
    + exact (proj1 translate_typing _ _ _ _ A).
    + apply map_empty_subseteq.
  - pose proof (rt_type_lc _ _ _ _ H5) as SumL. inversion SumL; subst.
    destruct (rt_box_payload _ _ _ _ _ _ _ _ H5) as [A [E1 E2]].
    eapply RTOIf with (l1:=l1) (l2:=l2).
    + apply RTBoxedLit.
    + destruct b.
      * eapply runtime_open_constant; eassumption.
      * eapply runtime_open_constant; [|exact B|exact H7].
        eapply rt_eqtype; eauto using ovalty_runtime.
    + destruct b.
      * eapply runtime_open_constant; [|exact B|exact H10].
        eapply rt_eqtype; eauto using ovalty_runtime.
      * eapply runtime_open_constant; eassumption.
    + exact B.
  - destruct (runtime_invert _ _ _ _ H2) as [k [t [C [E F]]]].
    inversion C; subst.
    match type of E with pared_equiv _ (EProd ?a ?c) _ =>
      assert (O : oblivious_type (EProd a c))
        by (eapply oblivious_type_conv; [exact E|exact H4]);
      destruct (oblivious_product _ _ O) as [O1 O2];
      eapply rt_eqtype with (τ:=EProd a c)
    end.
    + eapply RTPair with (l1:=false) (l2:=false).
      * eapply RTTape; eassumption.
      * eapply RTTape; eassumption.
      * reflexivity.
    + exact E.
    + exact B.
  - destruct (runtime_invert _ _ _ _ H0) as [k [t [C [E F]]]].
    inversion C; subst. eapply rt_eqtype; [apply RTUnit|exact E|exact B].
  - destruct (runtime_invert _ _ _ _ H0) as [k [t [C [E F]]]].
    inversion C; subst. eapply rt_eqtype; [apply RTBoxedLit|exact E|exact B].
  - destruct (runtime_invert _ _ _ _ H2) as [k [t [C [E F]]]].
    inversion C; subst. eapply rt_eqtype; [apply RTBoxedInj; assumption|exact E|exact B].
  - destruct (rt_weak_branches _ _ _ _ _ _ H4) as [-> [k1 [k2 [A C]]]].
    eapply RTOIf.
    + apply RTBoxedLit.
    + eapply RTCaseNoDep with (l0:=true) (l1:=l1) (l2:=l2).
      * eapply rt_label; [exact A|destruct k1; reflexivity].
      * exact H5.
      * exact H7.
      * exact B.
      * reflexivity.
    + eapply RTCaseNoDep with (l0:=true) (l1:=l1) (l2:=l2).
      * eapply rt_label; [exact C|destruct k2; reflexivity].
      * exact H5.
      * exact H7.
      * exact B.
      * reflexivity.
    + exact B.
  - pose proof (H1 _ H9) as K.
    destruct (rtc_type_sum_step _ _ _ _ H9 H0) as [a [c [-> [E1 E2]]]].
    pose proof (rt_otype_lc _ _ K) as Q. inversion Q; subst.
    eapply rt_eqtype with (τ:=ESum true a c).
    + apply RTOInj; [|exact K].
      destruct b; simpl in *; eapply rt_eqtype; eassumption.
    + apply equivalent_sym, pared_equivalent, step_pared; assumption.
    + exact B.
Qed.

End WellFormed.

Theorem soundness e Σ τ e' :
  Σ; e ▷ τ ->
  Σ ⊨ e -->* e' ->
  ¬(stuck Σ e').
Proof.
  intros [G T] P [N V].
  pose proof (proj1 (translate_typing Σ G) _ _ _ _ T) as RT.
  assert (F : runtime_typing Σ ∅ e' false τ).
  { clear T N V. revert RT. induction P; intros RT; [exact RT|].
    apply IHP. eapply (proj1 (runtime_preservation Σ G _ _ H)); exact RT. }
  destruct (proj1 (runtime_progress Σ G) _ _ _ _ F eq_refl) as [W|R].
  - apply V. eapply safe_wval; eassumption.
  - exact (N R).
Qed.
