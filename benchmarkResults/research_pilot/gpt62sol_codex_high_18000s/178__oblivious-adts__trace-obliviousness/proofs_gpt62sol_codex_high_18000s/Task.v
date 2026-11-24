From oadt Require Import lang_oadt.base.

From oadt Require Import lang_oadt.syntax.

From oadt Require Import lang_oadt.semantics.

From oadt Require Import lang_oadt.typing.

Import syntax.notations.

Import semantics.notations.

Import typing.notations.


(* A finite-observation model for conversion. Function observations record
   a finite set of input observations and one output observation. *)
Inductive observation :=
| Mark (tag : nat)
| Field (side : bool) (o : observation)
| Arrow (input : list observation) (output : observation)
| Nominal (name : atom).

Definition den := observation -> Prop.
Definition dle (d d' : den) := forall o, d o -> d' o.
Definition deq (d d' : den) := forall o, d o <-> d' o.
Definition dzero : den := fun _ => False.
Definition dlist (xs : list observation) : den := fun o => List.In o xs.
Definition dmark (n : nat) : den := fun o => o = Mark n.
Definition dnominal (x : atom) : den := fun o => o = Nominal x.
Definition dnode (n : nat) (a b : den) : den :=
  fun o => match o with
           | Mark m => m = n
           | Field true p => a p
           | Field false p => b p
           | _ => False
           end.
Definition dfield (s : bool) (d : den) : den := fun o => d (Field s o).
Definition dlam (f : den -> den) : den :=
  fun o => match o with Arrow xs p => f (dlist xs) p | _ => False end.
Definition dapp (f a : den) : den :=
  fun o => exists xs, f (Arrow xs o) /\ dle (dlist xs) a.
Definition dguard (c : den) (o : observation) (d : den) : den :=
  fun p => c o /\ d p.
Definition dunion (a b : den) : den := fun o => a o \/ b o.

Definition dunit := dmark 0.
Definition dbool (l : bool) := dmark (if l then 2 else 1).
Definition dprod := dnode 3.
Definition dsum (l : bool) := dnode (if l then 5 else 4).
Definition dpi (l : bool) := dnode (if l then 7 else 6).
Definition dtype := dmark 8.
Definition dlit (b : bool) := dmark (if b then 9 else 10).
Definition dpair := dnode 11.
Definition dinj (b : bool) a := dnode (if b then 9 else 10) a dzero.
Definition dite (c a b : den) := dunion (dguard c (Mark 9) a) (dguard c (Mark 10) b).
Definition dcase (c : den) (f g : den -> den) := dite c (f (dfield true c)) (g (dfield true c)).

Inductive slot := Bound (k : nat) | Free (x : atom) | Global (x : atom).
Definition env := slot -> den.
Definition ele (r s : env) := forall i, dle (r i) (s i).
Definition eeq (r s : env) := forall i, deq (r i) (s i).
Definition push (r : env) (d : den) : env :=
  fun i => match i with
           | Bound 0 => d
           | Bound (S k) => r (Bound k)
           | _ => r i
           end.
Definition ezero : env := fun _ => dzero.
Definition put (r : env) x (d : den) : env :=
  fun i => match i with
           | Free y => if decide (x = y) then d else r i
           | _ => r i
           end.

Fixpoint meaning (r : env) (e : expr) : den :=
  match e with
  | EBVar k => r (Bound k)
  | EFVar x => r (Free x)
  | EGVar x => r (Global x)
  | EUnitT => dunit
  | EBool l => dbool l
  | EProd a b => dprod (meaning r a) (meaning r b)
  | ESum l a b => dsum l (meaning r a) (meaning r b)
  | EPi l a b => dpi l (meaning r a) (dlam (fun d => meaning (push r d) b))
  | EUnitV => dmark 12
  | ELit b | EBoxedLit b => dlit b
  | EAbs _ _ b => dlam (fun d => meaning (push r d) b)
  | EApp f a => dapp (meaning r f) (meaning r a)
  | ELet a b => meaning (push r (meaning r a)) b
  | EIte _ c a b | EMux c a b => dite (meaning r c) (meaning r a) (meaning r b)
  | EPair a b => dpair (meaning r a) (meaning r b)
  | EProj b a => dfield b (meaning r a)
  | EInj _ b _ a => dinj b (meaning r a)
  | EBoxedInj b _ a => dinj b (meaning ezero a)
  | ECase _ c a b =>
      dcase (meaning r c) (fun d => meaning (push r d) a)
                         (fun d => meaning (push r d) b)
  | EFold _ a | EUnfold _ a | ESec a | ETape a => meaning r a
  end.

Local Instance deq_equiv : Equivalence deq.
Proof. split; unfold deq; firstorder. Qed.

Local Instance eeq_refl : Reflexive eeq.
Proof. intros r i; reflexivity. Qed.

Local Lemma dle_refl d : dle d d.
Proof. firstorder. Qed.

Local Lemma dle_trans a b c : dle a b -> dle b c -> dle a c.
Proof. firstorder. Qed.

Local Lemma push_le r s a b :
  ele r s -> dle a b -> ele (push r a) (push s b).
Proof. intros Hr H i; destruct i as [[|k]|x|x]; simpl; auto. Qed.

Local Lemma node_le n a b a' b' :
  dle a a' -> dle b b' -> dle (dnode n a b) (dnode n a' b').
Proof. intros Ha Hb [m|[] p|xs p|x]; simpl; auto. Qed.

Local Lemma app_le f a g b :
  dle f g -> dle a b -> dle (dapp f a) (dapp g b).
Proof. intros Hf Ha o (xs & H & Hxs); exists xs; eauto using dle_trans. Qed.

Local Lemma lam_le f g :
  (forall d, dle (f d) (g d)) -> dle (dlam f) (dlam g).
Proof. intros H [n|s o|xs o|x]; simpl; try tauto; apply H. Qed.

Local Lemma field_le b a a' : dle a a' -> dle (dfield b a) (dfield b a').
Proof. firstorder. Qed.

Local Lemma ite_le c a b c' a' b' :
  dle c c' -> dle a a' -> dle b b' -> dle (dite c a b) (dite c' a' b').
Proof. unfold dite, dunion, dguard, dle; firstorder. Qed.

Local Lemma meaning_le e r s : ele r s -> dle (meaning r e) (meaning s e).
Proof.
  revert r s; induction e; intros r s H; cbn [meaning];
    unfold dcase, dprod, dsum, dpi, dinj, dpair;
    eauto 12 using dle_refl, push_le, node_le, app_le, lam_le, field_le, ite_le.
Qed.

Local Lemma deq_le a b : deq a b -> dle a b.
Proof. firstorder. Qed.

Local Lemma deq_sym a b : deq a b -> deq b a.
Proof. symmetry; assumption. Qed.

Local Lemma eq_of_le a b : dle a b -> dle b a -> deq a b.
Proof. firstorder. Qed.

Local Lemma meaning_eq e r s : eeq r s -> deq (meaning r e) (meaning s e).
Proof.
  intros H; apply eq_of_le; apply meaning_le; intro i;
    apply deq_le; [apply H | symmetry; apply H].
Qed.

Local Lemma push_eq r s a b :
  eeq r s -> deq a b -> eeq (push r a) (push s b).
Proof. intros Hr H i; destruct i as [[|k]|x|x]; simpl; auto. Qed.

Definition directed {I : Type} (R : I -> env) :=
  (exists i : I, True) /\ forall i j, exists k, ele (R i) (R k) /\ ele (R j) (R k).
Definition sup {I : Type} (R : I -> env) : env := fun s o => exists i, R i s o.

Local Lemma directed_collect {I : Type} (R : I -> env) (HD : directed R)
    (F : env -> den) (HM : forall r s, ele r s -> dle (F r) (F s)) xs :
  (forall o, List.In o xs -> exists i, F (R i) o) ->
  exists i, dle (dlist xs) (F (R i)).
Proof.
  destruct HD as [[i _] HD]; induction xs as [|o xs IH]; intros H.
  - exists i; firstorder.
  - destruct (H o) as (j & Hj); [left; reflexivity|].
    destruct IH as (k & Hk); [intros; apply H; right; assumption|].
    destruct (HD j k) as (m & Hjm & Hkm).
    exists m; intros p [<-|Hp].
    + exact (HM _ _ Hjm _ Hj).
    + exact (HM _ _ Hkm _ (Hk _ Hp)).
Qed.

Definition continuous (F : env -> den) :=
  forall (I : Type) (R : I -> env), directed R ->
    forall o, F (sup R) o -> exists i, F (R i) o.
Definition monotone (F : env -> den) := forall r s, ele r s -> dle (F r) (F s).

Local Lemma cont_const d : continuous (fun _ => d).
Proof. intros I R [[i _] _] o H; now exists i. Qed.

Local Lemma cont_var v : continuous (fun r => r v).
Proof. intros I R HD o H; exact H. Qed.

Local Lemma cont_guard F G o :
  monotone F -> monotone G -> continuous F -> continuous G ->
  continuous (fun r => dguard (F r) o (G r)).
Proof.
  intros HF HG CF CG I R HD p [H1 H2].
  destruct (CF _ _ HD _ H1) as [i Hi], (CG _ _ HD _ H2) as [j Hj].
  destruct (proj2 HD i j) as (k & Hik & Hjk).
  exists k; split; [exact (HF _ _ Hik _ Hi) | exact (HG _ _ Hjk _ Hj)].
Qed.

Local Lemma cont_union F G : continuous F -> continuous G ->
  continuous (fun r => dunion (F r) (G r)).
Proof.
  intros CF CG I R HD o [H|H].
  - destruct (CF _ _ HD _ H) as [i Hi]; exists i; now left.
  - destruct (CG _ _ HD _ H) as [i Hi]; exists i; now right.
Qed.

Local Lemma cont_node n F G : continuous F -> continuous G ->
  continuous (fun r => dnode n (F r) (G r)).
Proof.
  intros CF CG I R HD [m|[] o|xs o|x] H; simpl in H.
  - destruct HD as [[i _] _]; now exists i.
  - exact (CF _ _ HD _ H).
  - exact (CG _ _ HD _ H).
  - contradiction.
  - contradiction.
Qed.

Local Lemma cont_field b F : continuous F -> continuous (fun r => dfield b (F r)).
Proof. intros CF I R HD o H; exact (CF _ _ HD _ H). Qed.

Local Lemma cont_app F G :
  monotone F -> monotone G -> continuous F -> continuous G ->
  continuous (fun r => dapp (F r) (G r)).
Proof.
  intros HF HG CF CG I R HD o (xs & H & Hxs).
  destruct (CF _ _ HD _ H) as [i Hi].
  destruct (directed_collect R HD G HG xs) as [j Hj].
  { intros p Hp; apply CG with (R := R); auto. }
  destruct (proj2 HD i j) as (k & Hik & Hjk).
  exists k, xs; split; [exact (HF _ _ Hik _ Hi) | eapply dle_trans; [exact Hj | exact (HG _ _ Hjk)]].
Qed.

Local Lemma cont_push F G :
  (forall r s, ele r s -> dle (meaning r F) (meaning s F)) ->
  continuous (fun r => meaning r F) ->
  monotone G -> continuous G ->
  continuous (fun r => meaning (push r (G r)) F).
Proof.
  intros MF CF MG CG I R HD o H.
  set (S := fun i => push (R i) (G (R i))).
  assert (DS : directed S).
  { destruct HD as [Hi Hd]; split; auto. intros i j.
    destruct (Hd i j) as (k & Hik & Hjk).
    exists k; split; apply push_le; auto. }
  assert (HS : ele (push (sup R) (G (sup R))) (sup S)).
  { intros [[|k]|x|x] p Hp; try exact Hp.
    exact (CG _ _ HD _ Hp). }
  exact (CF _ _ DS _ (MF _ _ HS _ H)).
Qed.

Local Lemma cont_lam F :
  (forall d, continuous (fun r => F r d)) ->
  continuous (fun r => dlam (F r)).
Proof. intros C I R HD [n|s o|xs o|x] H; try contradiction; exact (C _ _ _ HD _ H). Qed.

Local Lemma meaning_cont e : continuous (fun r => meaning r e).
Proof.
  induction e; cbn [meaning];
    unfold dcase, dprod, dsum, dpi, dinj, dpair, dite;
    repeat first [assumption | apply cont_const | apply cont_var
      | apply cont_node | apply cont_lam; intro | apply cont_app
      | apply cont_guard | apply cont_union | apply cont_field
      | apply cont_push | progress unfold monotone];
    intros; eauto 12 using meaning_le, push_le, field_le, dle_refl.
Qed.

Local Lemma meaning_beta r e a :
  deq (dapp (dlam (fun d => meaning (push r d) e)) a)
      (meaning (push r a) e).
Proof.
  apply eq_of_le.
  - intros o (xs & H & Hxs).
    exact (meaning_le e _ _ (push_le r r _ _ (fun i => dle_refl (r i)) Hxs) o H).
  - intros o H.
    set (J := sig (fun xs : list observation => dle (dlist xs) a)).
    set (R := fun i : J => push r (dlist (proj1_sig i))).
    assert (HD : directed R).
    { split.
      - assert (Hempty : dle (dlist []) a) by (intros p []).
        exists (exist _ [] Hempty); exact I.
      - intros [xs Hxs] [ys Hys].
        assert (Hboth : dle (dlist (xs ++ ys)) a).
        { intros p Hp; apply in_app_or in Hp; intuition. }
        exists (exist _ (xs ++ ys) Hboth); split; apply push_le;
          [intro; apply dle_refl | intros p Hp; apply in_or_app; now left
          | intro; apply dle_refl | intros p Hp; apply in_or_app; now right]. }
    assert (He : ele (push r a) (sup R)).
    { intros [[|k]|x|x] p Hp.
      - assert (Hone : dle (dlist [p]) a) by (intros q [<-|[]]; exact Hp).
        exists (exist _ [p] Hone); now left.
      - destruct HD as [[i _] _]; now exists i.
      - destruct HD as [[i _] _]; now exists i.
      - destruct HD as [[i _] _]; now exists i. }
    destruct (meaning_cont e _ _ HD _ (meaning_le e _ _ He _ H)) as [[xs Hxs] Hbody].
    now exists xs.
Qed.

Fixpoint scoped (k : nat) (e : expr) : Prop :=
  match e with
  | EBVar n => n < k
  | EPi _ a b | EAbs _ a b | ELet a b => scoped k a /\ scoped (S k) b
  | ECase _ c a b => scoped k c /\ scoped (S k) a /\ scoped (S k) b
  | EApp a b | EPair a b | EProd a b | ESum _ a b | EInj _ _ a b =>
      scoped k a /\ scoped k b
  | EBoxedInj _ a b => scoped 0 a /\ scoped 0 b
  | EIte _ c a b | EMux c a b => scoped k c /\ scoped k a /\ scoped k b
  | EProj _ a | EFold _ a | EUnfold _ a | ESec a | ETape a => scoped k a
  | _ => True
  end.

Fixpoint fvars (e : expr) : aset :=
  match e with
  | EFVar x => {[ x ]}
  | EPi _ a b | EAbs _ a b | ELet a b | EApp a b | EPair a b
  | EProd a b | ESum _ a b | EInj _ _ a b | EBoxedInj _ a b =>
      fvars a ∪ fvars b
  | ECase _ c a b | EIte _ c a b | EMux c a b =>
      fvars c ∪ fvars a ∪ fvars b
  | EProj _ a | EFold _ a | EUnfold _ a | ESec a | ETape a => fvars a
  | _ => ∅
  end.

Local Lemma scoped_mono e k n : scoped k e -> k <= n -> scoped n e.
Proof.
  revert k n; induction e; simpl; intuition eauto with arith.
Qed.

Local Lemma open_scoped e k s :
  scoped (S k) e -> scoped 0 s -> scoped k (open_ k s e).
Proof.
  revert k; induction e; intros n H Hs; simpl in *;
    try solve [intuition eauto].
  destruct (decide (n = k)); simpl; eauto using scoped_mono, Nat.le_0_l;
    lia.
Qed.

Local Lemma close_scoped e k x :
  scoped k (open_ k (EFVar x) e) -> scoped (S k) e.
Proof.
  revert k; induction e; intros n H; simpl in *; try solve [intuition eauto].
  destruct (decide (n = k)); simpl in *; lia.
Qed.

Local Lemma aset_mem_union (x : atom) (A B : aset) :
  x ∈ A ∪ B <-> x ∈ A \/ x ∈ B.
Proof. apply elem_of_union. Qed.

Local Lemma open_fvars e k s : fvars (open_ k s e) ⊆ fvars e ∪ fvars s.
Proof.
  revert k; induction e; intro n; simpl;
    try (destruct (decide (n = k)); simpl);
    intros y Hy; repeat rewrite aset_mem_union in Hy; repeat rewrite aset_mem_union;
    try apply elem_of_empty in Hy; try contradiction;
    try tauto;
    repeat match goal with
    | IH : forall i : nat, _ |- _ =>
        let H0 := fresh in let H1 := fresh in
        pose proof (IH n y) as H0; pose proof (IH (S n) y) as H1;
        clear IH; repeat rewrite aset_mem_union in H0; repeat rewrite aset_mem_union in H1
    end; tauto.
Qed.

Local Lemma close_fvars e k s : fvars e ⊆ fvars (open_ k s e).
Proof.
  revert k; induction e; intro n; simpl;
    try (destruct (decide (n = k)); simpl);
    intros y Hy; repeat rewrite aset_mem_union in Hy; repeat rewrite aset_mem_union;
    try apply elem_of_empty in Hy; try contradiction;
    try tauto;
    repeat match goal with
    | IH : forall i : nat, _ |- _ =>
        let H0 := fresh in let H1 := fresh in
        pose proof (IH n y) as H0; pose proof (IH (S n) y) as H1; clear IH
    end; tauto.
Qed.

Local Lemma otval_scope e : otval e -> scoped 0 e /\ fvars e ⊆ ∅.
Proof. induction 1; simpl in *; intuition; set_solver. Qed.

Local Lemma oval_scope e : oval e -> scoped 0 e /\ fvars e ⊆ ∅.
Proof.
  induction 1; simpl in *; try pose proof (otval_scope _ H) as ?;
    intuition; set_solver.
Qed.

Local Lemma ovalty_scope v t :
  ovalty v t -> oval v /\ otval t.
Proof.
  induction 1; intuition (subst; eauto using oval, otval);
    destruct b; simpl in *; eauto 8 using oval, otval.
Qed.

Local Lemma cofinite_scoped (L : aset) e :
  (forall x, x ∉ L -> scoped 0 (open (EFVar x) e)) -> scoped 1 e.
Proof.
  intro H; set (x := fresh L).
  exact (close_scoped e 0 x (H x (is_fresh L))).
Qed.

Local Lemma cofinite_fvars (L D : aset) e :
  (forall x, x ∉ L -> fvars (open (EFVar x) e) ⊆ {[ x ]} ∪ D) ->
  fvars e ⊆ D.
Proof.
  intro H; set (S := L ∪ fvars e).
  pose proof (is_fresh S) as Hx; set (x := fresh S) in *.
  pose proof (close_fvars e 0 (EFVar x)).
  specialize (H x ltac:(unfold S in Hx; set_solver)).
  unfold open in H; unfold S in Hx; set_solver.
Qed.

Local Lemma lc_scoped e : lc e -> scoped 0 e.
Proof.
  induction 1; simpl in *; intuition eauto using cofinite_scoped;
    try solve [apply otval_scope in H; tauto | apply oval_scope in H0; tauto].
Qed.

Local Lemma typing_scope Σ :
  (forall Γ e l t, typing Σ Γ e l t -> scoped 0 e /\ fvars e ⊆ dom Γ) /\
  (forall Γ t k, kinding Σ Γ t k -> scoped 0 t /\ fvars t ⊆ dom Γ).
Proof.
  apply typing_kinding_mutind; intros;
    repeat match goal with H : _ /\ _ |- _ => destruct H end;
    repeat match goal with
    | H : forall x, x ∉ ?L -> scoped _ _ /\ fvars _ ⊆ dom (<[x:=_]>_) |- _ =>
      let HS := fresh "HS" in let HF := fresh "HF" in
      pose proof (fun x Hx => proj1 (H x Hx)) as HS;
      pose proof (fun x Hx => proj2 (H x Hx)) as HF;
      clear H; setoid_rewrite fin_map_dom.dom_insert_L in HF;
      apply cofinite_scoped in HS; apply cofinite_fvars in HF
    | H : ovalty _ _ |- _ =>
      apply ovalty_scope in H as [H _]; apply oval_scope in H; simpl in H; destruct H
    end;
    cbn [scoped fvars] in *;
    repeat match goal with H : _ /\ _ |- _ => destruct H end;
    repeat split; try exact I; try assumption;
    try solve [match goal with H : _ !! _ = Some _ |- _ =>
      apply singleton_subseteq_l, elem_of_dom; eauto end];
    try solve [lazymatch goal with |- _ ⊆ _ => set_solver end].
Qed.

Local Lemma gdef_scope Σ x D :
  gctx_typing Σ -> Σ !! x = Some D ->
  match D with
  | DADT _ => True
  | DFun _ e => scoped 0 e /\ fvars e ⊆ ∅
  | DOADT _ e => scoped 1 e /\ fvars e ⊆ ∅
  end.
Proof.
  intros H HD; apply (map_Forall_lookup_1 _ _ _ _ H) in HD.
  destruct HD.
  - exact I.
  - split.
    + eapply cofinite_scoped. intros y Hy.
      eapply (proj2 (typing_scope Σ)); eauto.
    + eapply cofinite_fvars. intros y Hy.
      specialize (H1 y Hy).
      apply (proj2 (typing_scope Σ)) in H1 as [_ H1].
      rewrite fin_map_dom.dom_singleton_L in H1; rewrite union_empty_r_L; exact H1.
  - apply (proj1 (typing_scope Σ)) in H1 as [? H1].
    now rewrite fin_map_dom.dom_empty_L in H1.
Qed.

Local Lemma close_scoped_any e k s :
  scoped k (open_ k s e) -> scoped (S k) e.
Proof.
  revert k; induction e; intros n H; simpl in *; try solve [intuition eauto].
  destruct (decide (n = k)); simpl in *; lia.
Qed.

Local Lemma node_eq n a b a' b' :
  deq a a' -> deq b b' -> deq (dnode n a b) (dnode n a' b').
Proof. intros Ha Hb [m|[] p|xs p|x]; simpl; auto. Qed.

Local Lemma app_eq f a g b :
  deq f g -> deq a b -> deq (dapp f a) (dapp g b).
Proof. intros Hf Ha; apply eq_of_le; apply app_le; apply deq_le; auto; now symmetry. Qed.

Local Lemma lam_eq f g :
  (forall d, deq (f d) (g d)) -> deq (dlam f) (dlam g).
Proof. intros H [n|s o|xs o|x]; simpl; try tauto; apply H. Qed.

Local Lemma field_eq b a a' : deq a a' -> deq (dfield b a) (dfield b a').
Proof. firstorder. Qed.

Local Lemma ite_eq c a b c' a' b' :
  deq c c' -> deq a a' -> deq b b' -> deq (dite c a b) (dite c' a' b').
Proof. unfold dite, dunion, dguard, deq; firstorder. Qed.

Local Lemma ite_lit b a c : deq (dite (dlit b) a c) (if b then a else c).
Proof.
  destruct b; intros o; cbn [dite dunion dguard dlit dmark];
    split.
  - intros [[_ H]|[H _]]; [exact H|discriminate H].
  - intro H; left; split; [reflexivity|exact H].
  - intros [[H _]|[_ H]]; [discriminate H|exact H].
  - intro H; right; split; [reflexivity|exact H].
Qed.

Local Lemma ite_inj b p a c : deq (dite (dinj b p) a c) (if b then a else c).
Proof.
  destruct b; intros o; cbn [dite dunion dguard dinj dnode];
    split.
  - intros [[_ H]|[H _]]; [exact H|discriminate H].
  - intro H; left; split; [reflexivity|exact H].
  - intros [[H _]|[_ H]]; [discriminate H|exact H].
  - intro H; right; split; [reflexivity|exact H].
Qed.

Definition agrees k (S : aset) (r s : env) :=
  (forall i, i < k -> deq (r (Bound i)) (s (Bound i))) /\
  (forall x, x ∈ S -> deq (r (Free x)) (s (Free x))) /\
  (forall x, deq (r (Global x)) (s (Global x))).

Local Lemma agrees_shrink k k' S S' r s :
  agrees k S r s -> k' <= k -> S' ⊆ S -> agrees k' S' r s.
Proof. intros [HB [HF HG]] Hk HS; split; [intros i Hi; apply HB; lia|].
  split; [intros x Hx; apply HF, HS, Hx|exact HG]. Qed.

Local Lemma agrees_push k D r s a b :
  agrees k D r s -> deq a b -> agrees (S k) D (push r a) (push s b).
Proof.
  intros [HB [HF HG]] H; split; [intros [|i] Hi; simpl; auto with arith|auto].
Qed.

Local Lemma meaning_agree e k r s :
  scoped k e -> agrees k (fvars e) r s -> deq (meaning r e) (meaning s e).
Proof.
  revert k r s; induction e; intros n r s HS HE; cbn [meaning scoped fvars] in *;
    unfold dcase, dprod, dsum, dpi, dinj, dpair;
    try solve [reflexivity];
    try solve [destruct HE as [HB [HF HG]]; apply HB || (apply HF; set_solver) || apply HG; auto];
    decompose [and] HS;
    repeat first [apply node_eq | apply app_eq | apply lam_eq; intro
      | apply ite_eq | apply field_eq];
    try reflexivity;
    first [eapply IHe | eapply IHe1 | eapply IHe2 | eapply IHe3];
    try eassumption;
    try solve [eapply agrees_shrink; [exact HE | lia | set_solver]].
  all: apply agrees_push; [eapply agrees_shrink; [exact HE | lia | set_solver]|].
  all: try reflexivity.
  all: try solve [eapply (IHe1 n); [assumption|eapply agrees_shrink; [exact HE | lia | set_solver]]].
  all: apply field_eq; eapply (IHe1 n); [assumption | eapply agrees_shrink; [exact HE | lia | set_solver]].
Qed.

Local Lemma meaning_nonbound e n r s :
  scoped 0 e -> agrees n (fvars e) r s -> deq (meaning r e) (meaning s e).
Proof.
  intros; eapply meaning_agree; [eassumption|].
  eapply agrees_shrink; [eassumption|lia|reflexivity].
Qed.

Local Lemma meaning_open_gen e k u r s :
  scoped (S k) e -> scoped 0 u ->
  agrees k (fvars e) r s ->
  deq (meaning r u) (s (Bound k)) ->
  deq (meaning r (open_ k u e)) (meaning s e).
Proof.
  revert k r s; induction e; intros n r s HS HU HE HN;
    cbn [meaning scoped fvars open_] in *;
    try solve [reflexivity];
    try solve [
      destruct HE as [HB [HF HG]];
      first [destruct (decide (n = k)) as [->|?]; cbn [meaning];
               [exact HN | apply HB; lia]
            | apply HF; set_solver | apply HG]];
    unfold dcase, dprod, dsum, dpi, dinj, dpair;
    decompose [and] HS;
    repeat first [apply node_eq | apply app_eq | apply lam_eq; intro
      | apply ite_eq | apply field_eq];
    try reflexivity;
    try first [eapply IHe | eapply IHe1 | eapply IHe2 | eapply IHe3];
    try solve [eassumption];
    try solve [eapply agrees_shrink; [exact HE | lia | set_solver]].
  all: try match goal with
        | |- agrees (S _) _ (push _ _) (push _ _) =>
            apply agrees_push;
            [eapply agrees_shrink; [exact HE | lia | set_solver]|]
        | HArg : scoped 0 ?arg, HVal : deq (meaning ?r0 ?arg) _ |- deq (meaning (push ?r0 _) ?arg) _ =>
            etransitivity; [apply meaning_nonbound with (n := 0); [exact HArg|]
              | exact HVal]; split; [lia|]; split; intros; reflexivity
        end.
  all: try reflexivity.
  all: try solve [
    first [apply (IHe1 n) | apply field_eq; apply (IHe1 n)];
    try eassumption; eapply agrees_shrink; [exact HE | lia | set_solver]].

Qed.

Local Lemma meaning_open e u r :
  scoped 1 e -> scoped 0 u ->
  deq (meaning r (open u e)) (meaning (push r (meaning r u)) e).
Proof.
  intros HS HU; apply meaning_open_gen; [exact HS|exact HU| |reflexivity].
  split; [lia|]; split; intros; reflexivity.
Qed.

Local Lemma meaning_fresh_open e r x a :
  scoped 1 e -> x ∉ fvars e ->
  deq (meaning (put r x a) (open (EFVar x) e)) (meaning (push r a) e).
Proof.
  intros; apply meaning_open_gen; try exact I; try assumption.
  - split; [lia|]; split; [|reflexivity].
    intros y Hy; simpl; destruct (decide (x = y)); [subst; contradiction|reflexivity].
  - cbn [meaning put push]; destruct (decide (x = x)); [reflexivity|congruence].
Qed.

Local Lemma meaning_cofinite (L : aset) e e' r a :
  (forall x, x ∉ L -> scoped 0 (open (EFVar x) e)) ->
  (forall x, x ∉ L -> scoped 0 (open (EFVar x) e')) ->
  (forall x, x ∉ L -> forall r', (forall y, deq (r (Global y)) (r' (Global y))) ->
    deq (meaning r' (open (EFVar x) e)) (meaning r' (open (EFVar x) e'))) ->
  deq (meaning (push r a) e) (meaning (push r a) e').
Proof.
  intros Hs Hs' H; set (D := L ∪ fvars e ∪ fvars e').
  pose proof (is_fresh D) as Hx; set (x := fresh D) in *.
  unfold D in Hx.
  assert (HL : x ∉ L) by set_solver.
  etransitivity; [symmetry; apply meaning_fresh_open with (x := x)|].
  - eauto using cofinite_scoped.
  - set_solver.
  - etransitivity; [apply H; [exact HL| intros; reflexivity]|].
    apply meaning_fresh_open; eauto using cofinite_scoped; set_solver.
Qed.

(* Interpret recursive global definitions by the union of their finite
   approximations. Continuity makes this union a fixed point. *)
Definition global_operator (Σ : gctx) (r : env) : env :=
  fun i => match i with
           | Global x =>
               match Σ !! x with
               | Some (DFun _ e) => meaning r e
               | Some (DOADT _ e) => dlam (fun d => meaning (push r d) e)
               | Some (DADT _) => dnominal x
               | None => dzero
               end
           | _ => dzero
           end.

Fixpoint approximation Σ n : env :=
  match n with 0 => ezero | S k => global_operator Σ (approximation Σ k) end.
Definition global_meaning Σ := sup (approximation Σ).
Definition fixed_globals Σ r :=
  forall x, deq (r (Global x)) (global_meaning Σ (Global x)).

Local Lemma global_operator_le Σ r s :
  ele r s -> ele (global_operator Σ r) (global_operator Σ s).
Proof.
  intros H [k|x|x].
  - exact (dle_refl _).
  - exact (dle_refl _).
  - cbn [global_operator]; destruct (Σ !! x) as [[t|t e|t e]|].
    + exact (dle_refl _).
    + exact (meaning_le e r s H).
    + apply lam_le; intro d; apply meaning_le, push_le; [exact H|exact (dle_refl _)].
    + exact (dle_refl _).
Qed.

Local Lemma approximation_next Σ n :
  ele (approximation Σ n) (approximation Σ (S n)).
Proof. induction n; [intros i o [] | exact (global_operator_le _ _ _ IHn)]. Qed.

Local Lemma approximation_le Σ n m :
  n <= m -> ele (approximation Σ n) (approximation Σ m).
Proof.
  induction 1; [intro; apply dle_refl|].
  intro i; eapply dle_trans; [apply IHle | apply approximation_next].
Qed.

Local Lemma approximation_directed Σ : directed (approximation Σ).
Proof.
  split; [now exists 0 | intros n m; exists ((n + m)%nat); split; apply approximation_le; lia].
Qed.

Local Lemma global_operator_cont Σ i : continuous (fun r => global_operator Σ r i).
Proof.
  destruct i as [k|x|x].
  - exact (cont_const _).
  - exact (cont_const _).
  - unfold global_operator; destruct (Σ !! x) as [[t|t e|t e]|].
    + exact (cont_const _).
    + exact (meaning_cont e).
    + apply cont_lam; intro d; apply cont_push.
      * exact (meaning_le e).
      * exact (meaning_cont e).
      * intros r' s H; exact (dle_refl _).
      * exact (cont_const _).
    + exact (cont_const _).
Qed.

Local Lemma global_fixed Σ : eeq (global_meaning Σ) (global_operator Σ (global_meaning Σ)).
Proof.
  intro i; apply eq_of_le.
  - intros o ([|n] & H); [contradiction|].
    exact (global_operator_le Σ _ _ (fun j p Hp => ex_intro _ n Hp) i o H).
  - intros o H.
    destruct (global_operator_cont Σ i _ _ (approximation_directed Σ) _ H) as [n Hn].
    now exists (S n).
Qed.

Local Lemma global_fun Σ r x T e :
  gctx_typing Σ -> fixed_globals Σ r -> Σ !! x = Some (DFun T e) ->
  deq (meaning r (EGVar x)) (meaning r e).
Proof.
  intros HG Hr Hx; pose proof (gdef_scope _ _ _ HG Hx) as [Hs Hfv].
  cbn [meaning]; etransitivity; [apply Hr|].
  etransitivity; [apply global_fixed|].
  unfold global_operator; rewrite Hx.
  apply meaning_agree with (k := 0); [exact Hs|].
  split; [lia|]; split.
  - intros y Hy; apply Hfv, elem_of_empty in Hy; contradiction.
  - intro; symmetry; apply Hr.
Qed.

Local Lemma global_oadt Σ r X t e :
  gctx_typing Σ -> fixed_globals Σ r -> Σ !! X = Some (DOADT t e) ->
  deq (meaning r (EGVar X)) (dlam (fun d => meaning (push r d) e)).
Proof.
  intros HG Hr Hx; pose proof (gdef_scope _ _ _ HG Hx) as [Hs Hfv].
  cbn [meaning]; etransitivity; [apply Hr|].
  etransitivity; [apply global_fixed|].
  unfold global_operator; rewrite Hx.
  apply lam_eq; intro d; apply meaning_agree with (k := 1); [exact Hs|].
  apply agrees_push; [|reflexivity].
  split; [lia|]; split.
  - intros y Hy; apply Hfv, elem_of_empty in Hy; contradiction.
  - intro; symmetry; apply Hr.
Qed.

Local Lemma global_adt Σ r X t :
  fixed_globals Σ r -> Σ !! X = Some (DADT t) ->
  deq (meaning r (EGVar X)) (dnominal X).
Proof.
  intros Hr Hx; cbn [meaning]; etransitivity; [apply Hr|].
  etransitivity; [apply global_fixed|].
  unfold global_operator; now rewrite Hx.
Qed.

Local Lemma pared_scope Σ e e' :
  gctx_typing Σ -> pared Σ e e' -> scoped 0 e /\ scoped 0 e'.
Proof.
  intros HG H; induction H;
    repeat match goal with
    | H : scoped 0 _ /\ scoped 0 _ |- _ => destruct H
    | H : forall x, x ∉ ?L -> scoped 0 _ /\ scoped 0 _ |- _ =>
        let HL := fresh in let HR := fresh in
        pose proof (cofinite_scoped L _ (fun x Hx => proj1 (H x Hx))) as HL;
        pose proof (cofinite_scoped L _ (fun x Hx => proj2 (H x Hx))) as HR;
        clear H
    | H : lc _ |- _ => apply lc_scoped in H
    | H : otval _ |- _ => apply otval_scope in H as [H _]
    | H : oval _ |- _ => apply oval_scope in H as [H _]
    | H : ovalty _ _ |- _ => apply ovalty_scope in H as [?H ?H]
    | H : Σ !! _ = Some (DFun _ _) |- _ =>
        let HS := fresh in pose proof (gdef_scope _ _ _ HG H) as [HS _]; clear H
    | H : Σ !! _ = Some (DOADT _ _) |- _ =>
        let HS := fresh in pose proof (gdef_scope _ _ _ HG H) as [HS _]; clear H
    end;
    cbn [scoped]; unfold open in *;
    repeat split; try exact I; eauto 5 using open_scoped;
    destruct b; simpl in *; intuition eauto using open_scoped.
Qed.

Local Lemma dcase_eq c c' f f' g g' :
  deq c c' ->
  (forall a a', deq a a' -> deq (f a) (f' a')) ->
  (forall a a', deq a a' -> deq (g a) (g' a')) ->
  deq (dcase c f g) (dcase c' f' g').
Proof. unfold dcase; auto using ite_eq, field_eq. Qed.

Local Lemma dcase_inj b p f g :
  deq (dcase (dinj b p) f g) (if b then f p else g p).
Proof. unfold dcase; apply ite_inj. Qed.

Local Lemma box_payload_meaning v : oval v -> forall r s, deq (meaning r v) (meaning s v).
Proof.
  induction 1; intros; cbn [meaning]; unfold dpair, dinj;
    eauto using node_eq, deq_equiv; reflexivity.
Qed.

Local Instance dapp_proper : Proper (deq ==> deq ==> deq) dapp.
Proof. intros f g Hf a b Ha; now apply app_eq. Qed.
Local Instance dite_proper : Proper (deq ==> deq ==> deq ==> deq) dite.
Proof. intros c c' Hc a a' Ha b b' Hb; now apply ite_eq. Qed.
Local Instance dfield_proper b : Proper (deq ==> deq) (dfield b).
Proof. intros a a' H; now apply field_eq. Qed.

Local Lemma meaning_body_eq r e f p q :
  deq p q ->
  (forall d, deq (meaning (push r d) e) (meaning (push r d) f)) ->
  deq (meaning (push r p) e) (meaning (push r q) f).
Proof.
  intros Hp Hf; transitivity (meaning (push r q) e); [apply meaning_eq, push_eq; [reflexivity|exact Hp]|apply Hf].
Qed.

Local Lemma meaning_open_match r e f p u :
  scoped 1 f -> scoped 0 u ->
  deq p (meaning r u) ->
  (forall d, deq (meaning (push r d) e) (meaning (push r d) f)) ->
  deq (meaning (push r p) e) (meaning r (open u f)).
Proof.
  intros HF HU Hp He.
  transitivity (meaning (push r (meaning r u)) f);
    [now apply meaning_body_eq|symmetry; now apply meaning_open].
Qed.

Local Lemma meaning_case_eq r c c' e e' f f' :
  deq c c' ->
  (forall d, deq (meaning (push r d) e) (meaning (push r d) e')) ->
  (forall d, deq (meaning (push r d) f) (meaning (push r d) f')) ->
  deq (dcase c (fun d => meaning (push r d) e) (fun d => meaning (push r d) f))
      (dcase c' (fun d => meaning (push r d) e') (fun d => meaning (push r d) f')).
Proof. intros; apply dcase_eq; intros; eauto using meaning_body_eq. Qed.

Local Lemma pared_meaning Σ e e' :
  gctx_typing Σ -> pared Σ e e' ->
  forall r, fixed_globals Σ r -> deq (meaning r e) (meaning r e').
Proof.
  intros HG H; induction H; intros r Hr; cbn [meaning].
  all: try solve [reflexivity | eauto using global_fun, node_eq, app_eq, field_eq, ite_eq].
  all: repeat match goal with
  | H : pared ?sg ?a ?b |- _ =>
      let Ha := fresh in let Hb := fresh in
      pose proof (pared_scope sg _ _ HG H) as [Ha Hb]; clear H
  | H : forall x, x ∉ ?L -> pared ?sg (open (EFVar x) ?a) (open (EFVar x) ?b) |- _ =>
      let Ha := fresh in let Hb := fresh in let HC := fresh in
      pose proof (cofinite_scoped L a (fun x Hx => proj1 (pared_scope sg _ _ HG (H x Hx)))) as Ha;
      pose proof (cofinite_scoped L b (fun x Hx => proj2 (pared_scope sg _ _ HG (H x Hx)))) as Hb;
      assert (HC : forall s d, fixed_globals sg s ->
                      deq (meaning (push s d) a) (meaning (push s d) b));
      [intros s d Hs; eapply (meaning_cofinite L);
       [intros x Hx; exact (proj1 (pared_scope sg _ _ HG (H x Hx)))
       |intros x Hx; exact (proj2 (pared_scope sg _ _ HG (H x Hx)))
       |intros x Hx s' Hs';
        match goal with IH : forall x, x ∉ L -> forall r, fixed_globals sg r ->
          deq (meaning r (open (EFVar x) a)) (meaning r (open (EFVar x) b)) |- _ =>
          apply (IH x Hx); intro y; etransitivity; [symmetry; apply Hs'|apply Hs]
        end]
      | clear H]
  end.
  all: try solve [apply lam_eq; intro; auto].
  all: try solve [apply node_eq; [auto | apply lam_eq; intro; auto]].
  all: try solve [apply meaning_body_eq; eauto].
  all: try solve [
    match goal with |- deq (dapp (dlam (fun d => meaning (push ?r d) ?e)) ?p) _ =>
      transitivity (meaning (push r p) e); [apply meaning_beta|]
    end; apply meaning_open_match; eauto].
  all: try solve [
    etransitivity; [apply app_eq; [eapply global_oadt; eauto|eauto]|];
    etransitivity; [apply meaning_beta|]; symmetry; apply meaning_open; eauto;
    match goal with H : ?sg !! _ = Some (DOADT _ _) |- _ =>
      exact (proj1 (gdef_scope sg _ _ HG H))
    end ].
  all: try (destruct b; cbn [meaning]).
  all: try (destruct b'; cbn [meaning]).
  all: repeat first
    [ progress cbn [dfield dpair dnode]
    | progress setoid_rewrite ite_lit
    | progress setoid_rewrite dcase_inj ].
  all: try solve [eauto using app_eq, field_eq, ite_eq].
  all: try solve [apply meaning_open_match; eauto using box_payload_meaning;
    try (apply oval_scope in H; tauto)].
  all: try solve [unfold dinj; apply node_eq; eauto using box_payload_meaning; reflexivity].
  all: try solve [apply meaning_case_eq; eauto; setoid_rewrite ite_lit; eauto].
  all: try solve [symmetry; apply meaning_open; assumption].
  all: apply deq_sym; etransitivity; [apply ite_lit|].
  all: apply meaning_case_eq; eauto.
  all: symmetry.
  all: try solve [eauto].
  all: lazymatch goal with |- deq (dite (dlit ?b) ?a ?c) _ =>
    transitivity (if b then a else c); [exact (ite_lit b a c)|cbn; eauto]
  end.
Qed.

Local Lemma conversion_meaning Σ e e' r :
  gctx_typing Σ -> fixed_globals Σ r -> pared_equiv Σ e e' ->
  deq (meaning r e) (meaning r e').
Proof.
  intros HG Hr H; induction H; [reflexivity| |];
    etransitivity; eauto using pared_meaning;
    symmetry; eauto using pared_meaning.
Qed.

(* Oblivious kinds can observe only oblivious constructor tags and
   fields whose observations are themselves oblivious. *)
Inductive obl_observation : observation -> Prop :=
| OblUnit : obl_observation (Mark 0)
| OblBool : obl_observation (Mark 2)
| OblProd : obl_observation (Mark 3)
| OblSum : obl_observation (Mark 5)
| OblField b o : obl_observation o -> obl_observation (Field b o).
Definition obl_den (a : den) := forall o, a o -> obl_observation o.

Local Lemma obl_transport a b : deq a b -> obl_den a -> obl_den b.
Proof. firstorder. Qed.

Local Lemma obl_type_node n a b :
  obl_observation (Mark n) -> obl_den a -> obl_den b -> obl_den (dnode n a b).
Proof.
  intros Hn Ha Hb [m|[] p|xs p|x]; simpl;
    intros; try contradiction; subst; eauto using obl_observation.
Qed.

Local Lemma kinding_obl_aux Σ Γ e k :
  kinding Σ Γ e k ->
  forall r,
    (forall X t body d, Σ !! X = Some (DOADT t body) ->
       obl_den (dapp (r (Global X)) d)) ->
    (k = KAny \/ k = KObliv) -> obl_den (meaning r e).
Proof.
  induction 1; intros r HR HK; cbn [meaning];
    try solve [destruct HK; discriminate];
    try solve [unfold dbool; destruct l;
      [intros o ->; constructor | destruct HK; discriminate]];
    try solve [destruct κ; cbn in HK; destruct HK; discriminate];
    try solve [unfold dunit, dmark; intros o ->; constructor];
    try solve [apply obl_type_node; eauto using obl_observation];
    try solve [eapply HR; eauto].
  - unfold dite, dunion, dguard; intros o [[_ Ha]|[_ Hb]].
    + exact (IHkinding1 r HR (or_intror eq_refl) o Ha).
    + exact (IHkinding2 r HR (or_intror eq_refl) o Hb).
  - unfold dcase, dite, dunion, dguard; intros o [[_ Ha]|[_ Hb]].
    all: match goal with
    | IH : forall x, x ∉ ?L -> forall r, _ ->
        _ -> obl_den (meaning r (open (EFVar x) ?e)),
      HH : meaning (push _ ?d) ?e ?o |- _ =>
        let D := fresh in set (D := L ∪ fvars e);
        let Hfresh := fresh in pose proof (is_fresh D) as Hfresh;
        unfold D in Hfresh;
        let x := constr:(fresh D) in
        let Hx := fresh in assert (Hx : x ∉ L) by set_solver;
        let HS := fresh in assert (HS : scoped 1 e) by
          (eapply cofinite_scoped; intros y Hy;
           eapply (proj2 (typing_scope Σ)); eauto);
        eapply (IH x Hx (put r x d)); [exact HR|exact HK|];
        apply (meaning_fresh_open e r x d HS ltac:(set_solver)); exact HH
    end.
  - intros o Ho.
    match goal with
    | IH : forall x, x ∉ ?L -> forall r, _ ->
        _ -> obl_den (meaning r (open (EFVar x) ?e)),
      HH : meaning (push _ ?d) ?e ?p |- _ =>
        let D := fresh in set (D := L ∪ fvars e);
        let Hfresh := fresh in pose proof (is_fresh D) as Hfresh;
        unfold D in Hfresh;
        let x := constr:(fresh D) in
        let Hx := fresh in assert (Hx : x ∉ L) by set_solver;
        let HS := fresh in assert (HS : scoped 1 e) by
          (eapply cofinite_scoped; intros y Hy;
           eapply (proj2 (typing_scope Σ)); eauto);
        eapply (IH x Hx (put r x d)); [exact HR|now right|];
        apply (meaning_fresh_open e r x d HS ltac:(set_solver)); exact HH
    end.
  - eapply IHkinding; [exact HR|].
    destruct κ, κ'; cbn in *; intuition (try discriminate; reflexivity).
Qed.

Local Lemma approximation_obl Σ :
  gctx_typing Σ -> forall n X t body d, Σ !! X = Some (DOADT t body) ->
  obl_den (dapp (approximation Σ n (Global X)) d).
Proof.
  intros HG n; induction n as [|n IH].
  - intros X t body d HX o (xs & H & _); contradiction.
  - intros X t body d HX o (xs & H & _).
    cbn [approximation global_operator] in H; rewrite HX in H.
    apply (map_Forall_lookup_1 _ _ _ _ HG) in HX; inversion HX; subst.
    match goal with
    | HB : forall x, x ∉ ?L -> kinding _ _ (open (EFVar x) body) _ |- _ =>
        let D := fresh in set (D := L ∪ fvars body);
        let Hfresh := fresh in pose proof (is_fresh D) as Hfresh;
        unfold D in Hfresh;
        let x := constr:(fresh D) in
        let Hx := fresh in assert (Hx : x ∉ L) by set_solver;
        let HS := fresh in assert (HS : scoped 1 body) by
          (eapply cofinite_scoped; intros y Hy;
           eapply (proj2 (typing_scope Σ)); eauto);
        eapply (kinding_obl_aux _ _ _ _ (HB x Hx)
          (put (approximation Σ n) x (dlist xs))); [exact IH|now right|];
        apply (meaning_fresh_open body (approximation Σ n) x (dlist xs) HS ltac:(set_solver));
        exact H
    end.
Qed.

Local Lemma kinding_obl Σ r Γ e :
  gctx_typing Σ -> fixed_globals Σ r -> kinding Σ Γ e KObliv ->
  obl_den (meaning r e).
Proof.
  intros HG Hr Hk; eapply kinding_obl_aux; [exact Hk| |now right].
  intros X t body d HX o (xs & H & Hd).
  destruct (proj1 (Hr X (Arrow xs o)) H) as [n Hn].
  exact (approximation_obl Σ HG n X t body d HX o (ex_intro _ xs (conj Hn Hd))).
Qed.

Local Lemma open_inert e k u : scoped k e -> open_ k u e = e.
Proof.
  revert k; induction e; intros n H; simpl in *;
    try solve [f_equal; intuition eauto | reflexivity].
  destruct (decide (n = k)); [lia|reflexivity].
Qed.


Local Lemma subst_scope e k x u : scoped k e -> scoped 0 u -> scoped k (subst x u e).
Proof.
  revert k; induction e; intros n H Hu; simpl in *; try solve [intuition eauto].
  destruct (decide (x = x0)); simpl; eauto using scoped_mono, Nat.le_0_l.
Qed.

Local Lemma subst_open_fresh e k x y u :
  scoped 0 u -> x <> y ->
  subst x u (open_ k (EFVar y) e) = open_ k (EFVar y) (subst x u e).
Proof.
  intros Hu Hxy; revert k; induction e; intro n; simpl;
    try solve [f_equal; auto | reflexivity].
  - destruct (decide (n = k)); simpl; [|reflexivity].
    destruct (decide (x = y)); congruence.
  - destruct (decide (x = x0)); [symmetry; eapply open_inert, scoped_mono; eauto with arith|reflexivity].
Qed.

Local Lemma subst_open_same e k x u :
  x ∉ fvars e -> subst x u (open_ k (EFVar x) e) = open_ k u e.
Proof.
  revert k; induction e; intros n H; simpl in *; try reflexivity;
    try solve [f_equal; eauto; set_solver].
  - destruct (decide (n = k)); simpl; [|reflexivity].
    destruct (decide (x = x)); congruence.
  - destruct (decide (x = x0)); [subst; set_solver|reflexivity].
Qed.



(* The auxiliary typing uses denotations for types and dependent families.
   A context entry gives the effect, type and denotation of a free variable. *)
Notation rtctx := (amap (bool * den * den)).
Definition entry_den (v : option (bool * den * den)) : den :=
  match v with Some (_, _, d) => d | None => dzero end.

Local Lemma entry_den_eq (a b : option (bool * den * den)) :
  a = b -> deq (entry_den a) (entry_den b).
Proof. intros ->; reflexivity. Qed.

Definition rt_env Σ (Γ : rtctx) : env :=
  fun i => match i with
           | Bound _ => dzero
           | Global x => global_meaning Σ (Global x)
           | Free x => entry_den (Γ !! x)
           end.
Definition rm Σ Γ := meaning (rt_env Σ Γ).
Definition gtype Σ := rm Σ ∅.
Definition constant (a : den) := dlam (fun _ => a).
Definition leak (l l' : bool) := l = true -> l' = true.

Local Lemma constant_app a d : deq (dapp (constant a) d) a.
Proof.
  intros o; split; [intros (xs & H & _); exact H|].
  intro H; exists []; split; [exact H|intros p []].
Qed.

Local Lemma atom_lookup_insert_eq {A} (m : amap A) (x : atom) t :
  (<[x:=t]>m) !! x = Some t.
Proof. apply fin_maps.lookup_insert_eq. Qed.

Local Lemma atom_lookup_insert_ne {A} (m : amap A) (x y : atom) t :
  x <> y -> (<[x:=t]>m) !! y = m !! y.
Proof. apply fin_maps.lookup_insert_ne. Qed.

Local Lemma atom_insert_commute {A} (m : amap A) (x y : atom) t u :
  x <> y -> <[x:=t]>(<[y:=u]>m) = <[y:=u]>(<[x:=t]>m).
Proof. apply fin_maps.insert_insert_ne. Qed.

Local Lemma atom_dom_insert {A} (m : amap A) (x : atom) t :
  dom (<[x:=t]>m) = ({[x]} ∪ dom m : aset).
Proof. apply fin_map_dom.dom_insert_L. Qed.

Local Lemma rt_env_insert Σ Γ x l a d :
  eeq (rt_env Σ (<[x:=(l,a,d)]>Γ)) (put (rt_env Σ Γ) x d).
Proof.
  intros [k|y|y].
  - reflexivity.
  - change (deq (match (<[x:=(l,a,d)]>Γ) !! y with
                 | Some (_,_,p) => p | None => dzero end)
                (if decide (x = y) then d else rt_env Σ Γ (Free y))).
    destruct (decide (x = y)) as [->|H].
    + rewrite (atom_lookup_insert_eq Γ y (l,a,d)); reflexivity.
    + rewrite (atom_lookup_insert_ne Γ x y (l,a,d) H); reflexivity.
  - reflexivity.
Qed.

Local Lemma rt_env_fixes Σ Γ : fixed_globals Σ (rt_env Σ Γ).
Proof. intros x; reflexivity. Qed.

Local Lemma rm_global_closed Σ Γ e :
  scoped 0 e -> fvars e ⊆ ∅ -> deq (rm Σ Γ e) (gtype Σ e).
Proof.
  intros Hs Hf; apply meaning_agree with (k := 0); [exact Hs|].
  split; [lia|]; split; [|reflexivity].
  intros x Hx; apply Hf, elem_of_empty in Hx; contradiction.
Qed.

Reserved Notation "Γ '⊩' e ':{' l '}' A" (at level 40,
  e constr at level 0, l constr at level 99, A constr at level 0).

Section runtime_typing.
Context (Σ : gctx).
Local Notation "'M' Γ e" := (rm Σ Γ e) (at level 10, Γ constr at level 0, e constr at level 0).

Inductive runtime : rtctx -> expr -> bool -> den -> Prop :=
| RTVar Γ x q l a d A :
    Γ !! x = Some (q,a,d) -> leak q l -> deq a A ->
    Γ ⊩ (EFVar x) :{l} A
| RTFun Γ x q t e l A :
    Σ !! x = Some (DFun (q,t) e) -> leak q l -> deq (gtype Σ t) A ->
    Γ ⊩ (EGVar x) :{l} A
| RTOADT Γ x t body l A :
    Σ !! x = Some (DOADT t body) ->
    deq (dpi false (gtype Σ t) (constant dtype)) A ->
    Γ ⊩ (EGVar x) :{l} A
| RTADT Γ x t l A :
    Σ !! x = Some (DADT t) -> deq dtype A ->
    Γ ⊩ (EGVar x) :{l} A
| RTUnit Γ l A :
    deq dunit A -> Γ ⊩ EUnitV :{l} A
| RTLit Γ b l A :
    deq (dbool false) A -> Γ ⊩ (ELit b) :{l} A
| RTBox Γ b l A :
    deq (dbool true) A -> Γ ⊩ (EBoxedLit b) :{l} A
| RTBoxInj Γ b ω v l A :
    ovalty (EBoxedInj b ω v) ω -> deq (M Γ ω) A ->
    Γ ⊩ (EBoxedInj b ω v) :{l} A
| RTUnitT Γ l A :
    deq dtype A -> Γ ⊩ EUnitT :{l} A
| RTBoolT Γ b l A :
    deq dtype A -> Γ ⊩ (EBool b) :{l} A
| RTPiT Γ q t u l A :
    scoped 0 (EPi q t u) -> deq dtype A ->
    Γ ⊩ (EPi q t u) :{l} A
| RTProdT Γ t u l A :
    Γ ⊩ t :{l} dtype -> Γ ⊩ u :{l} dtype -> deq dtype A ->
    Γ ⊩ (EProd t u) :{l} A
| RTSumT Γ b t u l A :
    Γ ⊩ t :{l} dtype -> Γ ⊩ u :{l} dtype -> deq dtype A ->
    Γ ⊩ (ESum b t u) :{l} A
| RTAbs Γ q t e l a B A (L : aset) :
    scoped 0 t ->
    (forall x, x ∉ L -> forall d, (<[x:=(q,a,d)]>Γ) ⊩ (open (EFVar x) e) :{l} (dapp B d)) ->
    deq (dpi q a B) A ->
    Γ ⊩ (EAbs q t e) :{l} A
| RTApp Γ f u l q a B A :
    Γ ⊩ f :{l} (dpi q a B) -> Γ ⊩ u :{q} a ->
    deq (dapp B (M Γ u)) A ->
    Γ ⊩ (EApp f u) :{l} A
| RTLet Γ u e q l a B A (L : aset) :
    Γ ⊩ u :{q} a -> leak q l ->
    (forall x, x ∉ L -> forall d, (<[x:=(q,a,d)]>Γ) ⊩ (open (EFVar x) e) :{l} (dapp B d)) ->
    deq (dapp B (M Γ u)) A ->
    Γ ⊩ (ELet u e) :{l} A
| RTPair Γ e f l a b A :
    Γ ⊩ e :{l} a -> Γ ⊩ f :{l} b -> deq (dprod a b) A ->
    Γ ⊩ (EPair e f) :{l} A
| RTProj Γ (b : bool) e l a c A :
    Γ ⊩ e :{l} (dprod a c) -> deq (if b then a else c) A ->
    Γ ⊩ (EProj b e) :{l} A
| RTInj Γ (b : bool) t e l a c A :
    scoped 0 t -> Γ ⊩ e :{l} (if b then a else c) ->
    deq (dsum false a c) A ->
    Γ ⊩ (EInj false b t e) :{l} A
| RTOInj Γ (b : bool) t e l a c A :
    Γ ⊩ t :{false} dtype ->
    deq (M Γ t) (dsum true a c) ->
    Γ ⊩ e :{false} (if b then a else c) ->
    deq (dsum true a c) A ->
    Γ ⊩ (EInj true b t e) :{l} A
| RTIf Γ c e f l a A :
    Γ ⊩ c :{l} (dbool false) -> Γ ⊩ e :{l} a -> Γ ⊩ f :{l} a -> deq a A ->
    Γ ⊩ (EIte false c e f) :{l} A
| RTIfDep Γ c e f l B A :
    Γ ⊩ c :{false} (dbool false) ->
    Γ ⊩ e :{l} (dapp B (dlit true)) -> Γ ⊩ f :{l} (dapp B (dlit false)) ->
    deq (dapp B (M Γ c)) A ->
    Γ ⊩ (EIte false c e f) :{l} A
| RTOIf Γ c e f a A :
    Γ ⊩ c :{false} (dbool true) -> Γ ⊩ e :{true} a -> Γ ⊩ f :{true} a -> deq a A ->
    Γ ⊩ (EIte true c e f) :{true} A
| RTCase Γ c e f l q a b d A (L1 L2 : aset) :
    Γ ⊩ c :{q} (dsum false a b) -> leak q l ->
    (forall x, x ∉ L1 -> forall p, (<[x:=(q,a,p)]>Γ) ⊩ (open (EFVar x) e) :{l} d) ->
    (forall x, x ∉ L2 -> forall p, (<[x:=(q,b,p)]>Γ) ⊩ (open (EFVar x) f) :{l} d) ->
    deq d A ->
    Γ ⊩ (ECase false c e f) :{l} A
| RTCaseDep Γ c e f l a b B A (L1 L2 : aset) :
    Γ ⊩ c :{false} (dsum false a b) ->
    (forall x, x ∉ L1 -> forall p, (<[x:=(false,a,p)]>Γ) ⊩ (open (EFVar x) e) :{l} (dapp B (dinj true p))) ->
    (forall x, x ∉ L2 -> forall p, (<[x:=(false,b,p)]>Γ) ⊩ (open (EFVar x) f) :{l} (dapp B (dinj false p))) ->
    deq (dapp B (M Γ c)) A ->
    Γ ⊩ (ECase false c e f) :{l} A
| RTOCase Γ c e f a b d A (L1 L2 : aset) :
    Γ ⊩ c :{false} (dsum true a b) ->
    (forall x, x ∉ L1 -> forall p, (<[x:=(false,a,p)]>Γ) ⊩ (open (EFVar x) e) :{true} d) ->
    (forall x, x ∉ L2 -> forall p, (<[x:=(false,b,p)]>Γ) ⊩ (open (EFVar x) f) :{true} d) ->
    deq d A ->
    Γ ⊩ (ECase true c e f) :{true} A
| RTFold Γ X t e l A :
    Σ !! X = Some (DADT t) -> Γ ⊩ e :{l} (gtype Σ t) ->
    deq (dnominal X) A ->
    Γ ⊩ (EFold X e) :{l} A
| RTUnfold Γ X t e l A :
    Σ !! X = Some (DADT t) -> Γ ⊩ e :{l} (dnominal X) ->
    deq (gtype Σ t) A ->
    Γ ⊩ (EUnfold X e) :{l} A
| RTSec Γ e l A :
    Γ ⊩ e :{l} (dbool false) -> deq (dbool true) A ->
    Γ ⊩ (ESec e) :{l} A
| RTTape Γ e q l a A :
    Γ ⊩ e :{q} a -> obl_den a -> deq a A ->
    Γ ⊩ (ETape e) :{l} A
| RTMux Γ c e f l a A :
    Γ ⊩ c :{false} (dbool true) -> Γ ⊩ e :{false} a -> Γ ⊩ f :{false} a ->
    obl_den a -> deq a A ->
    Γ ⊩ (EMux c e f) :{l} A
where "Γ '⊩' e ':{' l '}' A" := (runtime Γ e l A).

End runtime_typing.

Local Hint Constructors runtime : rt.
Local Hint Unfold leak : rt.

Local Lemma rt_conv Σ Γ e l a b :
  runtime Σ Γ e l a -> deq a b -> runtime Σ Γ e l b.
Proof.
  intros H H'; destruct H; econstructor; try eassumption;
    etransitivity; eassumption.
Qed.

Local Lemma leak_refl l : leak l l.
Proof. firstorder. Qed.

Local Lemma leak_trans l q p : leak l q -> leak q p -> leak l p.
Proof. firstorder. Qed.

Local Lemma leak_top l : leak l true.
Proof. firstorder. Qed.

Local Lemma rt_effect Σ Γ e l a :
  runtime Σ Γ e l a -> forall q, leak l q -> runtime Σ Γ e q a.
Proof.
  induction 1; intros p Hp; try solve [econstructor; eauto using leak_trans].
  all: unfold leak in Hp; rewrite (Hp eq_refl); econstructor; eauto.
Qed.

Local Lemma rt_scope Σ Γ e l a :
  runtime Σ Γ e l a -> scoped 0 e.
Proof.
  induction 1; cbn [scoped] in *; repeat split; try exact I; try tauto.
  all: try solve [
    match goal with H : forall x, x ∉ ?L -> forall d : den, scoped 0 (open (EFVar x) ?e) |- scoped 1 ?e =>
      exact (cofinite_scoped L e (fun x Hx => H x Hx dzero))
    end].
  all: match goal with H : ovalty _ _ |- _ =>
    apply ovalty_scope in H as [H _]; apply oval_scope in H; simpl in H; tauto end.
Qed.

Definition matches_subst x u r s :=
  (forall k, deq (r (Bound k)) (s (Bound k))) /\
  (forall y, y <> x -> deq (r (Free y)) (s (Free y))) /\
  (forall y, deq (r (Global y)) (s (Global y))) /\
  deq (meaning r u) (s (Free x)).

Local Lemma matches_subst_push x u r s d d' :
  scoped 0 u -> matches_subst x u r s -> deq d d' ->
  matches_subst x u (push r d) (push s d').
Proof.
  intros Hu [HB [HF [HG Hx]]] Hd; split.
  - intros [|k]; [exact Hd|apply HB].
  - split; [exact HF|]; split; [exact HG|].
    etransitivity; [|exact Hx].
    apply meaning_nonbound with (n := 0); [exact Hu|].
    split; [lia|]; split; intros; reflexivity.
Qed.

Local Lemma meaning_subst_gen e x u r s :
  scoped 0 u -> matches_subst x u r s ->
  deq (meaning r (subst x u e)) (meaning s e).
Proof.
  revert r s; induction e; intros r s Hu HE; cbn [subst meaning];
    unfold dcase, dprod, dsum, dpi, dinj, dpair;
    try reflexivity;
    try solve [destruct HE as [HB [HF [HG Hx]]]; auto;
      destruct (decide (x = x0)) as [->|?]; cbn [meaning]; auto; apply HF; congruence];
    repeat first [apply node_eq | apply app_eq | apply lam_eq; intro
      | apply ite_eq | apply field_eq].
  all: try reflexivity.
  all: first [eapply IHe | eapply IHe1 | eapply IHe2 | eapply IHe3]; try eassumption.
  all: apply matches_subst_push; try assumption; try reflexivity.
  all: first [apply field_eq; eapply IHe1 | eapply IHe1]; eassumption.
Qed.

Definition rt_agree (Γ Γ' : rtctx) (D : aset) :=
  forall x, x ∈ D -> Γ !! x = Γ' !! x.

Local Lemma rt_agree_shrink Γ Γ' D D' :
  rt_agree Γ Γ' D -> D' ⊆ D -> rt_agree Γ Γ' D'.
Proof. firstorder. Qed.

Local Lemma rt_agree_binder Γ Γ' e x t :
  rt_agree Γ Γ' (fvars e) ->
  rt_agree (<[x:=t]>Γ) (<[x:=t]>Γ') (fvars (open (EFVar x) e)).
Proof.
  intros HE y Hy. destruct (decide (x = y)) as [->|H].
  - now rewrite !atom_lookup_insert_eq.
  - rewrite !atom_lookup_insert_ne by exact H.
    apply HE; apply (open_fvars e 0 (EFVar x)) in Hy; simpl in Hy; set_solver.
Qed.

Local Lemma rm_agree Σ Γ Γ' e :
  scoped 0 e -> rt_agree Γ Γ' (fvars e) ->
  deq (rm Σ Γ e) (rm Σ Γ' e).
Proof.
  intros HS HE; apply meaning_agree with (k := 0); [exact HS|].
  split; [lia|]; split; [|reflexivity].
  intros x Hx; exact (entry_den_eq _ _ (HE x Hx)).
Qed.

Local Lemma rm_subst Σ Γ e x u q a d :
  scoped 0 u -> deq (rm Σ Γ u) d ->
  deq (rm Σ Γ (subst x u e)) (rm Σ (<[x:=(q,a,d)]>Γ) e).
Proof.
  intros HS H; apply meaning_subst_gen; [exact HS|].
  split; [reflexivity|]; split; [|split; [reflexivity|]].
  - intros y Hy; apply entry_den_eq; symmetry; apply atom_lookup_insert_ne; congruence.
  - etransitivity; [exact H|]; symmetry.
    exact (entry_den_eq _ _ (atom_lookup_insert_eq Γ x (q,a,d))).
Qed.

Local Ltac transfer_runtime HE :=
  first [
    solve [eassumption]
  | solve [reflexivity]
  | solve [match goal with
      | IH : forall Δ, rt_agree _ Δ _ -> runtime _ Δ ?e _ _ |- runtime _ _ ?e _ _ =>
          eapply IH; intros z Hz; apply HE; set_solver
      end]
  | solve [intros x Hx p;
      match goal with
      | IH : forall y, y ∉ _ -> forall d Δ, rt_agree _ Δ _ ->
          runtime _ Δ (open (EFVar y) ?body) _ _
        |- runtime _ _ (open (EFVar x) ?body) _ _ =>
          eapply (IH x Hx p); apply rt_agree_binder; intros z Hz; apply HE; set_solver
      end] 
  | solve [etransitivity; [apply app_eq; [reflexivity|]|eassumption];
      symmetry; apply rm_agree; [eauto using rt_scope|];
      eapply rt_agree_shrink; [exact HE|set_solver]]
  | solve [etransitivity; [|eassumption]; symmetry; apply rm_agree;
      [eauto using rt_scope|]; eapply rt_agree_shrink; [exact HE|set_solver]]
  | solve [etransitivity; [|eassumption]; symmetry; apply rm_agree;
      [match goal with H : ovalty _ _ |- _ =>
        apply ovalty_scope in H as [_ H]; apply otval_scope in H; tauto end
      |eapply rt_agree_shrink; [exact HE|set_solver]]] ].

Local Lemma rt_irrel Σ Γ e l A :
  runtime Σ Γ e l A ->
  forall Γ', rt_agree Γ Γ' (fvars e) -> runtime Σ Γ' e l A.
Proof.
  induction 1; intros Δ HE; cbn [fvars] in *.
  all: try solve [econstructor; transfer_runtime HE].
  all: try solve [eapply RTIfDep; transfer_runtime HE].
  all: try solve [eapply RTCaseDep; transfer_runtime HE].
  all: try solve [
    eapply RTVar with (q := q) (a := a) (d := d);
    [etransitivity; [symmetry; apply HE; set_solver|exact H]|eassumption|eassumption]].
Qed.

Local Ltac substitute_binder :=
  intros x Hx p;
  lazymatch goal with
  | |- runtime ?sg (<[x:=?binding]>?G) (open (EFVar x) (subst ?y ?u ?e)) _ _ =>
      let Hneq := fresh in assert (Hneq : y <> x) by set_solver;
      let Hag := fresh in
      assert (Hag : rt_agree G (<[x:=binding]>G) (fvars u)) by
        (intros z Hz; rewrite atom_lookup_insert_ne; [reflexivity|set_solver]);
      unfold open; rewrite <- subst_open_fresh by assumption; fold (open (EFVar x) e);
      match goal with
      | IH : forall z, z ∉ ?L -> forall d G' y' u' q a d', _ ->
          runtime sg G' u' q a -> _ ->
          runtime sg G' (subst y' u' (open (EFVar z) e)) _ _ |- _ =>
          eapply (IH x ltac:(set_solver) p);
          [apply atom_insert_commute; congruence
          |eapply rt_irrel; eassumption
          |etransitivity; [symmetry; apply rm_agree; eassumption|eassumption]]
      end
  end.

Local Lemma rt_subst Σ Δ e l A :
  runtime Σ Δ e l A ->
  forall Γ x u q a d,
    Δ = <[x:=(q,a,d)]>Γ ->
    runtime Σ Γ u q a -> deq (rm Σ Γ u) d ->
    runtime Σ Γ (subst x u e) l A.
Proof.
  induction 1; intros Γ' y u0 q0 a0 d0 -> Hu Hd;
    pose proof (rt_scope _ _ _ _ _ Hu) as Hsu;
    cbn [subst] in *.
  1: {
    destruct (decide (y = x)) as [->|Hne].
    - rewrite atom_lookup_insert_eq in H; inversion H; subst.
      eauto using rt_conv, rt_effect.
    - rewrite atom_lookup_insert_ne in H by exact Hne.
      eauto with rt.
  }
  all: try solve [
    econstructor; try eassumption; eauto using subst_scope;
    try solve [etransitivity; [apply app_eq; [reflexivity|eapply rm_subst; eauto]|eassumption]];
    try solve [etransitivity; [eapply rm_subst; eauto|eassumption]];
    try solve [etransitivity; [|eassumption];
      apply rm_agree; [apply ovalty_scope in H as [_ H]; apply otval_scope in H; tauto|];
      intros x Hx; apply ovalty_scope in H as [_ H]; apply otval_scope in H as [_ HF];
      apply HF, elem_of_empty in Hx; contradiction ]].
  all: try solve [
    apply RTPiT;
    [change (scoped 0 (subst y u0 (EPi q t u))); apply subst_scope; assumption
    |assumption]].
  all: let finish :=
    (try eassumption; eauto using subst_scope;
     try solve [etransitivity; [apply app_eq; [reflexivity|eapply rm_subst; eauto]|eassumption]];
     substitute_binder) in
    first [
      solve [eapply RTAbs with (L := L ∪ {[y]} ∪ fvars u0); finish]
    | solve [eapply RTLet with (L := L ∪ {[y]} ∪ fvars u0); finish]
    | solve [eapply RTCase with (L1 := L1 ∪ {[y]} ∪ fvars u0) (L2 := L2 ∪ {[y]} ∪ fvars u0); finish]
    | solve [eapply RTCaseDep with (L1 := L1 ∪ {[y]} ∪ fvars u0) (L2 := L2 ∪ {[y]} ∪ fvars u0); finish]
    | solve [eapply RTOCase with (L1 := L1 ∪ {[y]} ∪ fvars u0) (L2 := L2 ∪ {[y]} ∪ fvars u0); finish]
    | idtac ].
Qed.

Local Lemma global_decl_types Σ x D :
  gctx_typing Σ -> Σ !! x = Some D ->
  match D with
  | DADT t | DFun (_,t) _ | DOADT t _ => scoped 0 t /\ fvars t ⊆ ∅
  end.
Proof.
  intros HG HD; apply (map_Forall_lookup_1 _ _ _ _ HG) in HD; destruct HD;
    match goal with H : kinding Σ ∅ _ _ |- _ =>
      apply (proj2 (typing_scope Σ)) in H; now rewrite fin_map_dom.dom_empty_L in H end.
Qed.

Local Lemma typing_result_scope Σ :
  gctx_typing Σ ->
  forall Γ e l t, typing Σ Γ e l t -> scoped 0 t /\ fvars t ⊆ dom Γ.
Proof.
  intros HG Γ e l t HT; induction HT;
    repeat match goal with
    | H : kinding Σ _ _ _ |- _ => apply (proj2 (typing_scope Σ)) in H
    | H : (Σ !! _ = Some _) |- _ =>
        let HH := fresh in pose proof (global_decl_types _ _ _ HG H) as HH;
        clear H
    | H : forall x, x ∉ ?L -> scoped _ (open (EFVar x) _) /\ fvars (open (EFVar x) _) ⊆ dom (<[x:=_]>_) |- _ =>
        let HS := fresh in let HF := fresh in
        pose proof (fun x Hx => proj1 (H x Hx)) as HS;
        pose proof (fun x Hx => proj2 (H x Hx)) as HF;
        clear H; setoid_rewrite atom_dom_insert in HF;
        apply cofinite_scoped in HS; apply cofinite_fvars in HF
    | H : ovalty _ _ |- _ =>
        apply ovalty_scope in H as [_ H]; apply otval_scope in H
    end;
    cbn [scoped fvars] in *;
    repeat match goal with H : _ /\ _ |- _ => destruct H end;
    repeat split; try exact I; try assumption;
    try solve [lazymatch goal with |- _ ⊆ _ => set_solver end].
  all: try match goal with
    | H : typing ?sg _ ?e _ _ |- context[open ?e _] =>
      apply (proj1 (typing_scope sg)) in H as [? ?]
    end.
  all: try solve [unfold open; eapply open_scoped; eassumption].
  all: try solve [
    unfold open; etransitivity; [apply open_fvars|]; set_solver].
  all: try destruct b; simpl; intuition eauto.
  all: set_solver.
Qed.

Definition related_ctx Σ (Γ : tctx) (Δ : rtctx) :=
  forall x q t, Γ !! x = Some (q,t) ->
    scoped 0 t /\ fvars t ⊆ dom Γ /\
    exists a d, Δ !! x = Some (q,a,d) /\ deq (rm Σ Δ t) a.

Local Lemma rm_insert_irrel Σ Γ x e q a d :
  scoped 0 e -> x ∉ fvars e ->
  deq (rm Σ (<[x:=(q,a,d)]>Γ) e) (rm Σ Γ e).
Proof.
  intros HS Hx; apply rm_agree; [exact HS|].
  intros y Hy; exact (atom_lookup_insert_ne Γ x y (q,a,d) ltac:(set_solver)).
Qed.

Local Lemma related_ctx_insert Σ Γ Δ x q t a d :
  related_ctx Σ Γ Δ -> x ∉ dom Γ ->
  scoped 0 t -> fvars t ⊆ dom Γ -> deq (rm Σ Δ t) a ->
  related_ctx Σ (<[x:=(q,t)]>Γ) (<[x:=(q,a,d)]>Δ).
Proof.
  intros HR Hx Hs Hf Ha y l u Hy.
  destruct (decide (x = y)) as [->|Hne].
  - rewrite atom_lookup_insert_eq in Hy; inversion Hy; subst.
    split; [exact Hs|]; split.
    + rewrite atom_dom_insert; set_solver.
    + exists a,d; split; [apply atom_lookup_insert_eq|].
      etransitivity; [apply rm_insert_irrel; [exact Hs|set_solver]|exact Ha].
  - rewrite atom_lookup_insert_ne in Hy by exact Hne.
    destruct (HR _ _ _ Hy) as (HS & HF & b & p & HB & HE).
    split; [exact HS|]; split.
    + rewrite atom_dom_insert; set_solver.
    + exists b,p; split; [etransitivity; [apply atom_lookup_insert_ne; congruence|exact HB]|].
      etransitivity; [apply rm_insert_irrel; [exact HS|set_solver]|exact HE].
Qed.

Local Lemma rm_open_binder Σ Δ x q a d e :
  scoped 1 e -> x ∉ fvars e ->
  deq (rm Σ (<[x:=(q,a,d)]>Δ) (open (EFVar x) e))
      (dapp (dlam (fun p => meaning (push (rt_env Σ Δ) p) e)) d).
Proof.
  intros HS HF; etransitivity; [apply meaning_eq, rt_env_insert|].
  etransitivity; [apply meaning_fresh_open; assumption|symmetry; apply meaning_beta].
Qed.

Local Lemma rm_open_app Σ Δ e u :
  scoped 1 e -> scoped 0 u ->
  deq (dapp (dlam (fun p => meaning (push (rt_env Σ Δ) p) e)) (rm Σ Δ u))
      (rm Σ Δ (open u e)).
Proof.
  intros HS HU; etransitivity; [apply meaning_beta|].
  symmetry; now apply meaning_open.
Qed.

Definition family (r : env) (t : expr) : den :=
  dlam (fun p => meaning (push r p) t).

Local Lemma family_open_ext Σ Δ x q a d t u :
  scoped 1 t -> scoped 0 u -> x ∉ fvars t ->
  deq (dapp (family (rt_env Σ Δ) t) (rm Σ (<[x:=(q,a,d)]>Δ) u))
      (rm Σ (<[x:=(q,a,d)]>Δ) (open u t)).
Proof.
  intros HS HU Hx.
  etransitivity; [|apply rm_open_app; assumption].
  apply app_eq; [apply lam_eq; intro p|reflexivity].
  apply meaning_agree with (k := 1); [exact HS|].
  apply agrees_push; [|reflexivity].
  split; [lia|]; split; [|reflexivity].
  intros y Hy; apply entry_den_eq; symmetry; apply atom_lookup_insert_ne; set_solver.
Qed.

Local Lemma rm_case_branch Σ Δ x q a d b t τ :
  scoped 1 τ -> scoped 0 t -> x ∉ fvars τ ->
  deq (rm Σ (<[x:=(q,a,d)]>Δ) (open (EInj false b t (EFVar x)) τ))
      (dapp (family (rt_env Σ Δ) τ) (dinj b d)).
Proof.
  intros HS HT HF; symmetry.
  transitivity (dapp (family (rt_env Σ Δ) τ)
      (rm Σ (<[x:=(q,a,d)]>Δ) (EInj false b t (EFVar x)))).
  - apply app_eq; [reflexivity|].
    cbn [rm meaning]; unfold dinj. apply node_eq; [|reflexivity].
    symmetry; exact (entry_den_eq _ _ (atom_lookup_insert_eq Δ x (q,a,d))).
  - apply family_open_ext; cbn [scoped]; auto.
Qed.

Local Lemma leak_join_l p q : leak p (p ⊔ q).
Proof. destruct p,q; firstorder. Qed.
Local Lemma leak_join_r p q : leak q (p ⊔ q).
Proof. destruct p,q; firstorder. Qed.
Local Lemma bool_sq_le p q : p ⊑ q -> leak p q.
Proof. destruct p,q; cbn; firstorder congruence. Qed.
Local Hint Resolve leak_join_l leak_join_r leak_trans leak_refl leak_top bool_sq_le : rt.

Local Ltac solve_leak :=
  solve [eauto 5 using leak_join_l, leak_join_r, leak_trans, leak_refl, leak_top, bool_sq_le].

Local Ltac source_binder :=
  intros x Hx d;
  match goal with
  | IH : forall y, y ∉ ?L -> forall D, related_ctx ?Σ (<[y:=(?q,?t)]>?G) D ->
      runtime ?Σ D (open (EFVar y) ?e) ?l _, HR : related_ctx ?Σ ?G ?Δ |-
      runtime ?Σ (<[x:=(?q,?a,d)]>?Δ) (open (EFVar x) ?e) _ _ =>
      let Hdom := fresh in assert (Hdom : x ∉ dom G) by set_solver;
      let HL := fresh in assert (HL : x ∉ L) by set_solver;
      eapply rt_effect; [eapply rt_conv;
        [apply (IH x HL); eapply related_ctx_insert;
          try solve [eassumption | reflexivity | set_solver | cbn [scoped] in *; tauto]|]
        | solve_leak];
      try reflexivity;
      try solve [symmetry; apply constant_app];
      try solve [apply rm_insert_irrel; [eassumption|set_solver]];
      try solve [apply rm_open_binder; [eassumption|set_solver]];
      try solve [apply rm_case_branch;
        [eassumption || (eapply close_scoped_any; eassumption)
        |eassumption || (cbn [scoped] in *; tauto)
        |set_solver]]
  end.

Local Lemma runtime_from_typing Σ :
  gctx_typing Σ ->
  (forall Γ e l t, typing Σ Γ e l t ->
      forall Δ, related_ctx Σ Γ Δ -> runtime Σ Δ e l (rm Σ Δ t)) /\
  (forall Γ e k, kinding Σ Γ e k ->
      forall Δ, related_ctx Σ Γ Δ -> runtime Σ Δ e false dtype).
Proof.
  intro HG; apply typing_kinding_mutind; intros.
  all: repeat match goal with
  | H : typing ?sg _ ?e _ ?t |- _ =>
      let HS := fresh in let HF := fresh in let HT := fresh in let HTF := fresh in
      pose proof (proj1 (typing_scope sg) _ _ _ _ H) as [HS HF];
      pose proof (typing_result_scope sg HG _ _ _ _ H) as [HT HTF]; clear H
  | H : forall x, x ∉ ?L -> typing ?sg _ (open (EFVar x) _) _ (open (EFVar x) ?t) |- _ =>
      let HS := fresh in
      assert (HS : scoped 1 t) by
        (eapply cofinite_scoped; intros y Hy;
         exact (proj1 (typing_result_scope sg HG _ _ _ _ (H y Hy))));
      clear H
  | H : forall x, x ∉ ?L -> kinding ?sg _ (open (EFVar x) ?t) _ |- _ =>
      let HS := fresh in
      assert (HS : scoped 1 t) by
        (eapply cofinite_scoped; intros y Hy;
         exact (proj1 (proj2 (typing_scope sg) _ _ _ (H y Hy))));
      clear H
  | H : kinding ?sg _ ?e _ |- _ =>
      let HS := fresh in let HF := fresh in
      pose proof (proj2 (typing_scope sg) _ _ _ H) as [HS HF];
      let O := fresh in
      try (lazymatch type of H with kinding ?sg _ _ KObliv =>
        pose proof (kinding_obl sg (rt_env sg Δ) _ _ HG (rt_env_fixes sg Δ) H) as O end);
      clear H
  end.
  all: try subst l.
  all: try solve [econstructor; try reflexivity; try eassumption; eauto 6 with rt].
  - match goal with
    | HR : related_ctx _ _ _, HU : _ !! _ = Some (_,_) |- _ =>
      destruct (HR _ _ _ HU) as (_ & _ & a & d & Hlookup & HE)
    end.
    eapply RTVar; [eassumption|apply leak_refl|symmetry; eassumption].
  - eapply RTFun; [eassumption|apply leak_refl|].
    symmetry; apply rm_global_closed; eapply (global_decl_types _ _ _ HG H).
  - eapply RTAbs with (a := rm Σ Δ τ2) (B := family (rt_env Σ Δ) τ1)
        (L := L ∪ dom Γ ∪ fvars τ1);
      try assumption; try reflexivity.
    source_binder.
  - eapply RTLet with (a := rm Σ Δ τ1) (B := family (rt_env Σ Δ) τ2)
        (L := L ∪ dom Γ ∪ fvars τ2).
    + eauto.
    + eauto with rt.
    + source_binder.
    + apply rm_open_app; assumption.
  - eapply RTApp with (a := rm Σ Δ τ2) (B := family (rt_env Σ Δ) τ1);
      try solve [eauto].
    apply rm_open_app; [match goal with H : scoped 0 (EPi _ _ _) |- _ => exact (proj2 H) end|assumption].
  - eapply RTPair with (a := rm Σ Δ τ1) (b := rm Σ Δ τ2);
      [eapply rt_effect | eapply rt_effect | reflexivity]; eauto with rt.
  - eapply RTProj with (a := rm Σ Δ τ1) (c := rm Σ Δ τ2); [eauto|destruct b; reflexivity].
  - eapply RTInj with (a := rm Σ Δ τ1) (c := rm Σ Δ τ2); [assumption| |reflexivity].
    destruct b; eauto.
  - eapply RTIfDep with (B := family (rt_env Σ Δ) τ).
    + eauto.
    + eapply rt_effect; [eapply rt_conv; [eauto|]|eauto with rt].
      symmetry; apply (rm_open_app Σ Δ τ (ELit true)); [eapply close_scoped_any; eassumption|exact I].
    + eapply rt_effect; [eapply rt_conv; [eauto|]|eauto with rt].
      symmetry; apply (rm_open_app Σ Δ τ (ELit false)); [eapply close_scoped_any; eassumption|exact I].
    + apply rm_open_app; [eapply close_scoped_any; eassumption|assumption].
  - eapply RTIf; [eapply rt_effect | eapply rt_effect | eapply rt_effect | reflexivity];
      (solve [eauto 3] || solve_leak).
  - eapply RTCaseDep with (B := family (rt_env Σ Δ) τ)
        (L1 := L1 ∪ dom Γ ∪ fvars τ) (L2 := L2 ∪ dom Γ ∪ fvars τ).
    + eauto.
    + source_binder.
    + source_binder.
    + apply rm_open_app; [eapply close_scoped_any; eassumption|assumption].
  - eapply RTCase with (L1 := L1 ∪ dom Γ ∪ fvars τ) (L2 := L2 ∪ dom Γ ∪ fvars τ).
    + eauto.
    + solve_leak.
    + source_binder.
    + source_binder.
    + reflexivity.
  - eapply RTFold; [eassumption| |].
    + eapply rt_conv; [eauto|].
      apply rm_global_closed; eapply (global_decl_types _ _ _ HG H).
    + symmetry; eapply global_adt; eauto using rt_env_fixes.
  - eapply RTUnfold; [eassumption| |].
    + eapply rt_conv; [eauto|].
      eapply global_adt; eauto using rt_env_fixes.
    + symmetry; apply rm_global_closed; eapply (global_decl_types _ _ _ HG H).
  - eapply RTOInj with (a := rm Σ Δ τ1) (c := rm Σ Δ τ2); [eauto|reflexivity| |reflexivity]. destruct b; eauto.
  - eapply RTOIf; [eauto|eapply rt_effect|eapply rt_effect|reflexivity]; eauto with rt.
  - eapply RTOCase with (L1 := L1 ∪ dom Γ ∪ fvars τ) (L2 := L2 ∪ dom Γ ∪ fvars τ).
    + eauto.
    + source_binder.
    + source_binder.
    + reflexivity.
  - eapply rt_conv; [eapply rt_effect; eauto with rt|].
    eapply conversion_meaning; eauto using rt_env_fixes.
  - eapply RTPiT; [ |reflexivity].
    simpl; tauto.
  - eapply RTApp with (B := constant dtype).
    + eapply RTOADT; [eassumption|reflexivity].
    + eapply rt_conv; [eauto|].
      apply rm_global_closed; eapply (global_decl_types _ _ _ HG H).
    + apply constant_app.
  - eapply RTCase with (a := rm Σ Δ τ1') (b := rm Σ Δ τ2')
        (L1 := L1 ∪ dom Γ) (L2 := L2 ∪ dom Γ).
    + eauto.
    + apply leak_refl.
    + source_binder.
    + source_binder.
    + reflexivity.
  - eapply RTLet with (B := constant dtype) (L := L ∪ dom Γ).
    + eauto.
    + apply leak_refl.
    + source_binder.
    + apply constant_app.
  - eauto.
Qed.

Local Lemma indist_refl e : e ≈ e.
Proof. induction e; constructor; assumption. Qed.

Local Lemma indist_sym e f : e ≈ f -> f ≈ e.
Proof. induction 1; constructor; assumption. Qed.

Local Lemma indist_trans e f g : e ≈ f -> f ≈ g -> e ≈ g.
Proof. intros H; revert g; induction H; intros g Hg; inversion Hg; subst; constructor; eauto. Qed.

Local Lemma indist_open_at e f u v k :
  e ≈ f -> u ≈ v -> open_ k u e ≈ open_ k v f.
Proof.
  intros He Hu; revert k; induction He; intro n; cbn [open_];
    try solve [constructor; eauto].
  destruct (decide (n = k)); eauto using indist_refl.
Qed.

Local Lemma indist_open e f u v : e ≈ f -> u ≈ v -> open u e ≈ open v f.
Proof. intros; now apply indist_open_at. Qed.

Local Lemma otval_indist e f : otval e -> e ≈ f -> e = f.
Proof.
  intros H; revert f; induction H; intros f HF; inversion HF; subst;
    repeat f_equal; eauto.
Qed.

Local Lemma ovalty_indist v w t : ovalty v t -> ovalty w t -> v ≈ w.
Proof.
  intros H; revert w; induction H; intros w Hw; inversion Hw; subst; constructor; eauto.
Qed.


Local Lemma named_inj x y : deq (dnominal x) (dnominal y) -> x = y.
Proof.
  intro H; pose proof (proj1 (H (Nominal x)) eq_refl) as He; injection He; auto.
Qed.

Local Lemma node_inj n m a b c d :
  deq (dnode n a b) (dnode m c d) -> n = m /\ deq a c /\ deq b d.
Proof.
  intro H; split; [exact (proj1 (H (Mark n)) eq_refl)|].
  split; intro o; [exact (H (Field true o))|exact (H (Field false o))].
Qed.

Local Lemma prod_inj a b c d :
  deq (dprod a b) (dprod c d) -> deq a c /\ deq b d.
Proof. intro H; exact (proj2 (node_inj _ _ _ _ _ _ H)). Qed.

Local Lemma sum_inj l a b c d :
  deq (dsum l a b) (dsum l c d) -> deq a c /\ deq b d.
Proof. intro H; exact (proj2 (node_inj _ _ _ _ _ _ H)). Qed.

Local Lemma pi_inj q q' a B a' B' :
  deq (dpi q a B) (dpi q' a' B') -> q = q' /\ deq a a' /\ deq B B'.
Proof.
  intro H; apply node_inj in H as (H & Ha & Hb); split; [destruct q, q'; congruence|auto].
Qed.

Local Ltac type_clash H :=
  let test tag := (
    let Bad := fresh in
    pose proof (proj1 (H (Mark tag)) eq_refl) as Bad;
    discriminate Bad) in
  first [solve [test 0] | solve [test 1] | solve [test 2] | solve [test 3]
    | solve [test 4] | solve [test 5] | solve [test 6] | solve [test 7]
    | solve [test 8]].

Local Lemma otval_type_unique Σ Γ a b :
  otval a -> otval b -> deq (rm Σ Γ a) (rm Σ Γ b) -> a = b.
Proof.
  intros H; revert b; induction H; intros b Hb Heq; inversion Hb; subst;
    cbn [rm meaning] in Heq;
    try reflexivity; try solve [type_clash Heq];
    apply node_inj in Heq as (_ & Ha & Hb');
    f_equal; eauto.
Qed.

Local Lemma otval_rm Σ Γ ω : otval ω -> obl_den (rm Σ Γ ω).
Proof.
  induction 1; cbn [rm meaning];
    try solve [intros o ->; constructor];
    apply obl_type_node; eauto using obl_observation.
Qed.

Local Lemma obl_prod_parts a b : obl_den (dprod a b) -> obl_den a /\ obl_den b.
Proof.
  intro H; split; intros o Ho.
  - specialize (H (Field true o) Ho); inversion H; assumption.
  - specialize (H (Field false o) Ho); inversion H; assumption.
Qed.

Local Ltac solve_obl_clash HO :=
  let test tag := (
    let Obs := fresh in
    pose proof (HO (Mark tag) eq_refl) as Obs; inversion Obs) in
  first [solve [test 1] | solve [test 4] | solve [test 6] | solve [test 7] | solve [test 8]
    | match type of HO with obl_den (dnominal ?x) =>
        let Obs := fresh in pose proof (HO (Nominal x) eq_refl) as Obs; inversion Obs end ].

Local Lemma runtime_oval Σ Γ v A :
  wval v -> runtime Σ Γ v false A -> obl_den A ->
  exists ω, ovalty v ω /\ deq (rm Σ Γ ω) A.
Proof.
  intros HV; revert A; induction HV; intros A HT HO; inversion HT; subst.
  all: try solve [
    exfalso;
    match goal with
    | H : deq ?d ?T, HObl : obl_den ?T |- _ =>
        let HH := fresh in
        assert (HH : obl_den d) by
          (eapply obl_transport; [symmetry; exact H|exact HObl]);
        try (match goal with q : bool |- _ => destruct q end);
        solve_obl_clash HH
    end ].
  all: try solve [eexists; split; [constructor|eassumption] ].
  - destruct (obl_prod_parts _ _ (obl_transport _ _ (deq_sym _ _ H6) HO)) as [OA OB].
    destruct (IHHV1 _ H1 OA) as (ω1 & Hv1 & E1).
    destruct (IHHV2 _ H3 OB) as (ω2 & Hv2 & E2).
    exists (EProd ω1 ω2); split; [now constructor|].
    transitivity (dprod a b); [apply node_eq; assumption|exact H6].
  - eexists; split; eassumption.
Qed.

Local Lemma runtime_exact_oval Σ Γ v ω :
  wval v -> runtime Σ Γ v false (rm Σ Γ ω) -> otval ω -> ovalty v ω.
Proof.
  intros HV HT HO.
  destruct (runtime_oval _ _ _ _ HV HT (otval_rm _ _ _ HO)) as (ω' & HV' & HE).
  destruct (ovalty_scope _ _ HV') as [_ HO'].
  pose proof (otval_type_unique _ _ _ _ HO' HO HE) as ->.
  exact HV'.
Qed.

Local Lemma runtime_of_ovalty Σ Γ v ω l :
  ovalty v ω -> runtime Σ Γ v l (rm Σ Γ ω).
Proof.
  induction 1; cbn [rm meaning]; eauto with rt; try (econstructor; reflexivity).
  - econstructor; try eassumption; reflexivity.
  - econstructor; [econstructor; eassumption|reflexivity].
Qed.

Local Lemma meaning_context r C e f :
  ectx C -> deq (meaning r e) (meaning r f) ->
  deq (meaning r (C e)) (meaning r (C f)).
Proof.
  intros HC H; destruct HC; cbn [meaning];
    unfold dcase, dprod, dsum, dpi, dinj, dpair;
    repeat first [reflexivity | assumption | apply app_eq | apply node_eq
      | apply field_eq | apply ite_eq | apply meaning_eq, push_eq].
  all: intro; reflexivity.
Qed.

Local Lemma lifting_context C : lectx C -> ectx C.
Proof. destruct 1; constructor; assumption. Qed.

Local Lemma context_scoped C e :
  ectx C -> scoped 0 (C e) -> scoped 0 e.
Proof. destruct 1; cbn [scoped]; tauto. Qed.

Local Lemma meaning_step Σ r e f :
  gctx_typing Σ -> fixed_globals Σ r -> step Σ e f -> scoped 0 e ->
  deq (meaning r e) (meaning r f).
Proof.
  intros HG Hr H; induction H; cbn [scoped meaning]; intros HS.
  all: try solve [reflexivity | apply ite_lit | eauto using global_fun].
  - destruct HS as [[Ht Hb] Hv]; etransitivity; [apply meaning_beta|].
    symmetry; apply meaning_open; assumption.
  - symmetry; apply meaning_open; tauto.
  - destruct b; apply ite_lit.
  - destruct b; (etransitivity; [apply dcase_inj|symmetry; apply meaning_open; tauto]).
  - destruct b; reflexivity.
  - etransitivity; [apply app_eq; [eapply global_oadt; eauto|reflexivity]|].
    etransitivity; [apply meaning_beta|].
    symmetry; apply meaning_open; [exact (proj1 (gdef_scope _ _ _ HG H0))|tauto].
  - unfold dinj; apply node_eq; [eauto using box_payload_meaning | reflexivity].
  - destruct b; apply ite_lit.
  - destruct b.
    + transitivity (meaning (push r (meaning ezero v)) e1).
      * apply dcase_inj.
      * symmetry; transitivity (meaning r (open v e1)); [apply ite_lit|].
        symmetry; apply meaning_open_match;
          [tauto|tauto|apply box_payload_meaning; assumption|intro; reflexivity].
    + transitivity (meaning (push r (meaning ezero v)) e2).
      * apply dcase_inj.
      * symmetry; transitivity (meaning r (open v e2)); [apply ite_lit|].
        symmetry; apply meaning_open_match;
          [tauto|tauto|apply box_payload_meaning; assumption|intro; reflexivity].
  - destruct b.
    + transitivity (meaning r (ℇ v1)).
      * eapply meaning_context; [apply lifting_context; eassumption|cbn [meaning]; apply ite_lit].
      * symmetry; apply ite_lit.
    + transitivity (meaning r (ℇ v2)).
      * eapply meaning_context; [apply lifting_context; eassumption|cbn [meaning]; apply ite_lit].
      * symmetry; apply ite_lit.
  - apply meaning_context; eauto using context_scoped.
Qed.

Local Lemma oval_wval v : oval v -> wval v.
Proof. induction 1; constructor; assumption. Qed.

Local Lemma woval_wval v : woval v -> wval v.
Proof. induction 1; constructor; assumption. Qed.

Local Lemma oval_woval v : oval v -> woval v.
Proof. induction 1; constructor; assumption. Qed.

Local Lemma wval_no_step Σ v e : step Σ v e -> wval v -> False.
Proof.
  induction 1; intros HV; try solve [inversion HV].
  - destruct H; inversion HV.
  - destruct H; inversion HV; subst; eauto.
    eapply IHstep; constructor.
Qed.

Local Lemma otval_no_step Σ v e : step Σ v e -> otval v -> False.
Proof.
  induction 1; intros HV; try solve [inversion HV].
  - destruct H; inversion HV.
  - destruct H; inversion HV; subst; eauto.
Qed.

Local Lemma runtime_wval_indist Σ Γ e f l A :
  wval e -> e ≈ f -> runtime Σ Γ f l A -> wval f.
Proof.
  intros HW; revert f l A; induction HW; intros f l0 A HI HT;
    inversion HI; subst.
  all: try solve [apply WUnitV | apply WLit | apply WAbs | apply WBoxedLit].
  all: try match goal with H : EBoxedLit _ ≈ _ |- _ => inversion H; subst end.
  all: inversion HT; subst.
  all: try solve [
    first [apply WPair | apply WInj | apply WFold | apply WIf]; eauto].
  all: match goal with H : ovalty (EBoxedInj _ _ _) _ |- _ =>
    exact (oval_wval _ (proj1 (ovalty_scope _ _ H))) end.
Qed.

Local Lemma runtime_oval_indist Σ Γ e f l A :
  oval e -> e ≈ f -> runtime Σ Γ f l A -> oval f.
Proof.
  intros HW; revert f l A; induction HW; intros f l0 A HI HT;
    inversion HI; subst.
  all: try solve [apply OVUnitV | apply OVBoxedLit].
  all: inversion HT; subst.
  all: try solve [apply OVPair; eauto].
  all: match goal with H : ovalty (EBoxedInj _ _ _) _ |- _ =>
    exact (proj1 (ovalty_scope _ _ H)) end.
Qed.

Local Lemma runtime_woval_indist Σ Γ e f l A :
  woval e -> e ≈ f -> runtime Σ Γ f l A -> woval f.
Proof.
  intros HW; revert f l A; induction HW; intros f l0 A HI HT;
    inversion HI; subst.
  all: try solve [apply OWUnitV | apply OWBoxedLit].
  all: try match goal with H : EBoxedLit _ ≈ _ |- _ => inversion H; subst end.
  all: inversion HT; subst.
  all: try solve [first [apply OWPair | apply OWIf]; eauto].
  all: match goal with H : ovalty (EBoxedInj _ _ _) _ |- _ =>
    exact (oval_woval _ (proj1 (ovalty_scope _ _ H))) end.
Qed.

Local Lemma ovalty_oval v t : ovalty v t -> oval v.
Proof. intro H; exact (proj1 (ovalty_scope _ _ H)). Qed.

Local Lemma ovalty_otval v t : ovalty v t -> otval t.
Proof. intro H; exact (proj2 (ovalty_scope _ _ H)). Qed.

Local Lemma otval_indist_rhs v w : otval v -> v ≈ w -> otval w.
Proof. intros H HE; now rewrite <- (otval_indist _ _ H HE). Qed.

Local Hint Resolve indist_refl indist_open ovalty_indist : trace.
Local Hint Constructors indistinguishable wval otval : trace.
Local Hint Resolve oval_wval woval_wval ovalty_oval ovalty_otval : trace.

Local Ltac invert_step_context :=
  repeat match goal with
  | H : ?C ?u = _ , HC : ectx ?C |- _ =>
      destruct HC; cbn in H; inversion H; clear H; subst
  | H : ?C ?u = _ , HC : lectx ?C |- _ =>
      destruct HC; cbn in H; inversion H; clear H; subst
  | H : _ = ?C ?u , HC : ectx ?C |- _ =>
      destruct HC; cbn in H; inversion H; clear H; subst
  | H : _ = ?C ?u , HC : lectx ?C |- _ =>
      destruct HC; cbn in H; inversion H; clear H; subst
  end.

(* Evaluation contexts select a unique redex. The dummy inhabitants in
   an oblivious case may vary, but inhabitants of the same type agree. *)
Local Lemma step_unique_observation Σ e f g :
  step Σ e f -> step Σ e g -> f ≈ g.
Proof.
  intros H; revert g; induction H; intros g' HS;
    try match goal with H : lectx _ |- _ => destruct H end;
    try match goal with H : ectx _ |- _ => destruct H end;
    cbn in *; inversion HS; subst; clear HS; invert_step_context;
    try solve [eauto 7 with trace];
    try solve [exfalso; eauto 9 using wval_no_step, otval_no_step with trace];
    try solve [match goal with
      | H1 : Σ !! ?x = Some ?D1, H2 : Σ !! ?x = Some ?D2 |- _ =>
          rewrite H1 in H2; inversion H2; subst; apply indist_refl
      end];
    try solve [
      destruct b; simpl; apply IIte; eauto using indist_open, ovalty_indist with trace].
  all: try solve [exfalso; eauto 10 using wval_no_step, otval_no_step with trace].
  all: match goal with H : step _ (EGVar _) _ |- _ =>
    inversion H; subst; try congruence; invert_step_context end.
Qed.

Local Lemma rt_open_binding Σ Γ e l q a (F : den -> den) (L : aset) u :
  (forall x, x ∉ L -> forall d,
    runtime Σ (<[x:=(q,a,d)]>Γ) (open (EFVar x) e) l (F d)) ->
  runtime Σ Γ u q a ->
  runtime Σ Γ (open u e) l (F (rm Σ Γ u)).
Proof.
  intros H Hu; set (D := L ∪ fvars e).
  pose proof (is_fresh D) as HD; set (x := fresh D) in *.
  unfold D in HD.
  assert (Hx : x ∉ L) by set_solver.
  specialize (H x Hx (rm Σ Γ u)).
  pose proof (rt_subst _ _ _ _ _ H Γ x u q a (rm Σ Γ u) eq_refl Hu
    (ltac:(reflexivity))) as HS.
  unfold open in *; rewrite subst_open_same in HS by set_solver; exact HS.
Qed.

Local Lemma rt_empty_related Σ Γ : related_ctx Σ ∅ Γ.
Proof. intros x q t H; rewrite fin_maps.lookup_empty in H; discriminate. Qed.

Local Lemma rt_global_fun Σ Γ x q τ e :
  gctx_typing Σ -> Σ !! x = Some (DFun (q,τ) e) ->
  runtime Σ Γ e q (gtype Σ τ).
Proof.
  intros HG HX.
  pose proof (global_decl_types _ _ _ HG HX) as [Hsc Hfree].
  apply (map_Forall_lookup_1 _ _ _ _ HG) in HX; inversion HX; subst.
  eapply rt_conv.
  - eapply (proj1 (runtime_from_typing Σ HG)); eauto using rt_empty_related.
  - now apply rm_global_closed.
Qed.

Local Lemma rt_global_oadt Σ Γ X τ body u :
  gctx_typing Σ -> Σ !! X = Some (DOADT τ body) ->
  runtime Σ Γ u false (gtype Σ τ) ->
  runtime Σ Γ (open u body) false dtype.
Proof.
  intros HG HX Hu.
  pose proof (global_decl_types _ _ _ HG HX) as [HS HF].
  apply (map_Forall_lookup_1 _ _ _ _ HG) in HX; inversion HX; subst.
  eapply rt_open_binding with (a := gtype Σ τ) (F := fun _ => dtype); [|exact Hu].
  intros x Hx d; eapply (proj2 (runtime_from_typing Σ HG)); eauto.
  intros y q t Hy; rewrite fin_maps.lookup_singleton_Some in Hy; destruct Hy as [-> Hy];
    inversion Hy; subst.
  split; [exact HS|]; split.
  - rewrite fin_map_dom.dom_singleton_L; set_solver.
  - exists (gtype Σ t),d; split; [apply atom_lookup_insert_eq|].
    now apply rm_global_closed.
Qed.

Local Lemma rt_context_replace Σ Γ C e f l A :
  ectx C ->
  (forall q a, runtime Σ Γ e q a -> runtime Σ Γ f q a) ->
  deq (rm Σ Γ e) (rm Σ Γ f) ->
  runtime Σ Γ (C e) l A ->
  runtime Σ Γ (C f) l A.
Proof.
  intros HC HI HE HT; destruct HC; inversion HT; subst.
  all: first [
    solve [eapply RTIfDep; eauto;
      etransitivity; [apply app_eq; [reflexivity|symmetry; exact HE]|eassumption]]
  | solve [eapply RTCaseDep; eauto;
      etransitivity; [apply app_eq; [reflexivity|symmetry; exact HE]|eassumption]]
  | econstructor ];
    try eassumption; try solve [eapply HI; eassumption].
  all: try solve [etransitivity; [|eassumption];
    first [symmetry; eassumption | apply app_eq; [reflexivity|symmetry; eassumption]]].
Qed.

Local Lemma rt_lift_if Σ Γ C b v w l A :
  lectx C ->
  runtime Σ Γ (C (EIte true (EBoxedLit b) v w)) l A ->
  runtime Σ Γ (EIte true (EBoxedLit b) (C v) (C w)) l A.
Proof.
  intros HC HT; destruct HC; inversion HT; subst;
    match goal with
    | H : runtime Σ Γ (EIte true (EBoxedLit b) v w) _ _ |- _ =>
      inversion H; subst; clear H
    end;
    try match goal with H : leak true ?q |- _ =>
      specialize (H eq_refl); subst q
    end;
    eapply RTOIf with (a := A); try reflexivity;
    try solve [apply RTBox; reflexivity];
    econstructor; try eassumption;
    eauto using rt_conv, leak_refl.
Qed.

Local Lemma runtime_injection Σ Γ b ω v l A :
  otval ω -> wval v ->
  runtime Σ Γ (EInj true b ω v) l A ->
  ovalty (EBoxedInj b ω v) ω.
Proof.
  intros HO HV HT; inversion HT; subst; inversion HO; subst;
    cbn [rm meaning] in *;
    repeat match goal with H : deq _ (dsum true _ _) |- _ =>
      try solve [type_clash H]
    end.
  match goal with H : deq (dsum true _ _) (dsum true _ _) |- _ =>
    apply sum_inj in H as [HL HR]
  end.
  constructor; destruct b; cbn in *;
    eauto using runtime_exact_oval, rt_conv, deq_sym.
Qed.

Local Ltac apply_case_binding :=
  lazymatch goal with |- runtime ?sg ?G (open ?v ?body) ?l ?R =>
    first [
      match goal with
      | HB : forall x, x ∉ ?L -> forall p,
          runtime sg (<[x:=(?q,?a,p)]>G) (open (EFVar x) body) l (dapp ?B (dinj ?b p)) |- _ =>
          eapply rt_conv;
          [eapply rt_open_binding with (F := fun p => dapp B (dinj b p));
           [exact HB|eapply rt_conv; eassumption]
          |eassumption]
      end
    | match goal with
      | HB : forall x, x ∉ ?L -> forall p,
          runtime sg (<[x:=(?q,?a,p)]>G) (open (EFVar x) body) l ?T |- _ =>
          eapply rt_conv;
          [eapply rt_open_binding with (F := fun _ => T);
           [exact HB|eapply rt_conv; eassumption]
          |eassumption]
      end ]
  end.

(* The auxiliary typing is preserved even when a weak value contains an
   oblivious conditional. A safe weak value of oblivious type has an exact
   ovalty witness, which is used for mux and boxed case analysis. *)
Local Lemma runtime_preservation Σ Γ e f :
  gctx_typing Σ -> step Σ e f ->
  forall l A, runtime Σ Γ e l A -> runtime Σ Γ f l A.
Proof.
  intros HG H; induction H; intros l0 A HT.
  - inversion HT; subst.
    match goal with HT' : runtime Σ Γ (EAbs _ _ _) _ _ |- _ =>
      inversion HT'; subst; clear HT' end.
    match goal with H : deq (dpi _ _ _) (dpi _ _ _) |- _ =>
      apply pi_inj in H as (-> & HE & HF)
    end.
    eapply rt_conv; [eapply rt_open_binding; [eassumption|eapply rt_conv; eauto using deq_sym]|].
    etransitivity; [apply app_eq; [eassumption|reflexivity]|eassumption].
  - inversion HT; subst.
    eapply rt_conv; [eapply rt_open_binding; eassumption|assumption].
  - inversion HT; subst; destruct b; cbn [rm meaning]; eauto using rt_conv.
  - inversion HT; subst;
      match goal with H : runtime Σ Γ (EInj false _ _ _) _ _ |- _ =>
        inversion H; subst; clear H end;
      match goal with H : deq (dsum false _ _) (dsum false _ _) |- _ =>
        apply sum_inj in H as [HE HF]
      end;
      destruct b; cbn [rm meaning] in *; apply_case_binding.
  - inversion HT; subst.
    match goal with H : runtime Σ Γ (EPair _ _) _ _ |- _ =>
      inversion H; subst; clear H end.
    match goal with H : deq (dprod _ _) (dprod _ _) |- _ =>
      apply prod_inj in H as [HE HF]
    end.
    destruct b; cbn in *; eauto using rt_conv.
  - inversion HT; subst.
    match goal with H : runtime Σ Γ (EFold _ _) _ _ |- _ =>
      inversion H; subst; clear H end.
    match goal with H : deq (dnominal _) (dnominal _) |- _ =>
      apply named_inj in H; subst end.
    match goal with
    | H1 : Σ !! ?X = Some ?D, H2 : Σ !! ?X = Some ?D' |- _ =>
        rewrite H1 in H2; inversion H2; subst
    end; eauto using rt_conv.
  - inversion HT; subst; try congruence.
    match goal with
    | H1 : Σ !! ?x = Some (DFun _ _), H2 : Σ !! ?x = Some (DFun _ _) |- _ =>
        rewrite H1 in H2; inversion H2; subst; clear H2
    end.
    eapply rt_conv; [eapply rt_effect; [eapply rt_global_fun; eassumption|eassumption]|eassumption].
  - inversion HT; subst.
    match goal with H : runtime Σ Γ (EGVar _) _ _ |- _ =>
      inversion H; subst; clear H end; try congruence.
    match goal with HA : Σ !! ?X = Some (DOADT _ _),
      HB : Σ !! ?X = Some (DOADT _ _) |- _ =>
        rewrite HA in HB; inversion HB; subst
    end.
    destruct (pi_inj _ _ _ _ _ _ H6) as (Hq & HE & HF); subst q.
    eapply rt_conv.
    + eapply rt_effect; [eapply rt_global_oadt; eauto using rt_conv, deq_sym|apply leak_top || (unfold leak; congruence)].
    + etransitivity; [symmetry; apply constant_app|].
      etransitivity; [apply app_eq; [eassumption|reflexivity]|eassumption].
  - inversion HT; subst; now apply RTBox.
  - inversion HT; subst.
    eapply RTBoxInj.
    + eapply runtime_injection; eauto using oval_wval.
    + etransitivity; eassumption.
  - inversion HT; subst; destruct b;
      (eapply rt_effect; [eapply rt_conv; eassumption|unfold leak; congruence]).
  - inversion HT; subst.
    match goal with H : runtime Σ Γ (EBoxedInj _ _ _) _ _ |- _ =>
      inversion H; subst; clear H end.
    match goal with H : ovalty (EBoxedInj _ _ _) _ |- _ =>
      inversion H; subst; clear H end.
    match goal with H : deq (rm _ _ (ESum true _ _)) (dsum true _ _) |- _ =>
      apply sum_inj in H as [HE HF]
    end.
    eapply RTOIf with (a := d); [apply RTBox; reflexivity| | |eassumption];
      destruct b; cbn [rm meaning] in *;
      (eapply rt_open_binding with (F := fun _ => d); [eassumption|]);
      (eapply rt_conv; [eapply runtime_of_ovalty; eassumption|eassumption]).
  - inversion HT; subst.
    match goal with H : runtime Σ Γ (EIte true _ _ _) _ _ |- _ =>
      inversion H; subst; clear H end.
    eapply RTMux with (a := a); [apply RTBox; reflexivity| | |eassumption|eassumption];
      (eapply RTTape with (q := true) (a := a);
        [eapply rt_conv; eassumption|assumption|reflexivity]).
  - inversion HT; subst.
    match goal with H : runtime Σ Γ (EPair _ _) _ _ |- _ =>
      inversion H; subst; clear H end.
    match goal with H : deq (dprod ?a ?b) ?d, HD : obl_den ?d |- _ =>
      destruct (obl_prod_parts _ _ (obl_transport _ _ (deq_sym _ _ H) HD)) as [OA OB]
    end.
    eapply RTPair; [eapply RTTape|eapply RTTape|etransitivity]; eauto; reflexivity.
  - inversion HT; subst; match goal with H : runtime Σ Γ EUnitV _ _ |- _ =>
      inversion H; subst end; apply RTUnit; etransitivity; eassumption.
  - inversion HT; subst; match goal with H : runtime Σ Γ (EBoxedLit _) _ _ |- _ =>
      inversion H; subst end; apply RTBox; etransitivity; eassumption.
  - inversion HT; subst; match goal with H : runtime Σ Γ (EBoxedInj _ _ _) _ _ |- _ =>
      inversion H; subst end; eapply RTBoxInj; [eassumption|etransitivity; eassumption].
  - eapply rt_lift_if; eassumption.
  - eapply rt_context_replace; [eassumption|eassumption| |exact HT].
    eapply meaning_step; eauto using rt_env_fixes.
    eapply context_scoped; eauto using rt_scope.
Qed.

Local Lemma indist_lift Σ Γ C e f b :
  lectx C -> wval e -> wval f ->
  forall u l' A', indistinguishable (C (EIte true (EBoxedLit b) e f)) u ->
  runtime Σ Γ u l' A' ->
  exists u', step Σ u u' /\
    indistinguishable (EIte true (EBoxedLit b) (C e) (C f)) u'.
Proof.
  intros HC HW HW' u l' A' HE HT; destruct HC; cbn in *; inversion HE; subst;
    repeat match goal with
    | H : indistinguishable (EIte true _ _ _) _ |- _ =>
        inversion H; subst; clear H
    | H : indistinguishable (EBoxedLit _) _ |- _ =>
        inversion H; subst; clear H
    end;
    inversion HT; subst;
    repeat match goal with
    | H : runtime Σ Γ (EIte true _ _ _) _ _ |- _ =>
        inversion H; subst; clear H
    end;
    try idtac.
  all: try solve [
    eexists; split;
    [ first [
        eapply (SOIf Σ _ _ _ _ (LCtxApp _) ) ||
          eapply (SOIf Σ _ _ _ _ (LCtxApp _ (ltac:(eauto using runtime_wval_indist))))
      | eapply (SOIf Σ _ _ _ _ LCtxSec)
      | eapply (SOIf Σ _ _ _ _ (LCtxIf _ _))
      | eapply (SOIf Σ _ _ _ _ (LCtxProj _))
      | eapply (SOIf Σ _ _ _ _ (LCtxCase _ _))
      | eapply (SOIf Σ _ _ _ _ (LCtxUnfold _)) ];
      eauto using runtime_wval_indist
    | eauto 8 with trace ]].
  assert (HW2 : wval e2') by (eauto using runtime_wval_indist).
  eexists; split.
  - eapply (SOIf Σ _ _ _ _ (LCtxApp _ HW2)); eauto using runtime_wval_indist.
  - eauto 8 with trace.
Qed.

Local Lemma indist_context_step Σ Γ C e f l A :
  ectx C ->
  (forall r B u q D, runtime Σ Γ e r B -> runtime Σ Γ u q D ->
    e ≈ u -> exists u', step Σ u u' /\ f ≈ u') ->
  runtime Σ Γ (C e) l A ->
  forall u q D, C e ≈ u -> runtime Σ Γ u q D ->
  exists u', step Σ u u' /\ C f ≈ u'.
Proof.
  intros HC IH HT u q D HE HU; destruct HC; cbn in *;
    inversion HE; subst; inversion HT; subst; inversion HU; subst;
    match goal with
    | H : e ≈ ?v, H1 : runtime Σ Γ e ?r ?B, H2 : runtime Σ Γ ?v ?s ?T |- _ =>
        destruct (IH r B v s T H1 H2 H) as (v' & HS & HV)
    end.
  all: repeat match goal with
    | Hw : wval ?v, HDiff : ?v ≈ ?v', HT' : runtime _ _ ?v' _ _ |- _ =>
        lazymatch goal with
        | _ : wval v' |- _ => fail
        | _ => let Hw' := fresh in pose proof (runtime_wval_indist _ _ _ _ _ _ Hw HDiff HT') as Hw'
        end
    | Hw : otval ?v, HDiff : ?v ≈ ?v' |- _ =>
        lazymatch goal with
        | _ : otval v' |- _ => fail
        | _ => let Hw' := fresh in pose proof (otval_indist_rhs _ _ Hw HDiff) as Hw'
        end
    end.
  all: eexists; split.
  all: try solve [
    first [
        eapply (SCtx Σ _ _ _ (CtxProd1 _) HS)
      | match goal with W : otval ?v |- _ => eapply (SCtx Σ _ _ _ (CtxProd2 v W) HS) end
      | eapply (SCtx Σ _ _ _ (CtxOSum1 _) HS)
      | match goal with W : otval ?v |- _ => eapply (SCtx Σ _ _ _ (CtxOSum2 v W) HS) end
      | match goal with W : wval ?v |- _ => eapply (SCtx Σ _ _ _ (CtxApp1 v W) HS) end
      | eapply (SCtx Σ _ _ _ (CtxApp2 _) HS)
      | eapply (SCtx Σ _ _ _ (CtxLet _) HS)
      | eapply (SCtx Σ _ _ _ CtxSec HS)
      | eapply (SCtx Σ _ _ _ (CtxIf _ _) HS)
      | eapply (SCtx Σ _ _ _ (CtxOIf1 _ _) HS)
      | match goal with W : wval ?v |- _ => eapply (SCtx Σ _ _ _ (CtxOIf2 v _ W) HS) end
      | match goal with W : wval ?v, W' : wval ?v' |- _ => eapply (SCtx Σ _ _ _ (CtxOIf3 v v' W W') HS) end
      | eapply (SCtx Σ _ _ _ (CtxPair1 _) HS)
      | match goal with W : wval ?v |- _ => eapply (SCtx Σ _ _ _ (CtxPair2 v W) HS) end
      | eapply (SCtx Σ _ _ _ (CtxProj _) HS)
      | eapply (SCtx Σ _ _ _ (CtxInj _ _) HS)
      | eapply (SCtx Σ _ _ _ (CtxOInj1 _ _) HS)
      | match goal with W : otval ?v |- _ => eapply (SCtx Σ _ _ _ (CtxOInj2 _ v W) HS) end
      | eapply (SCtx Σ _ _ _ (CtxCase _ _) HS)
      | eapply (SCtx Σ _ _ _ (CtxOCase _ _) HS)
      | eapply (SCtx Σ _ _ _ (CtxFold _) HS)
      | eapply (SCtx Σ _ _ _ (CtxUnfold _) HS)
      | eapply (SCtx Σ _ _ _ CtxTape HS)
      | eapply (SCtx Σ _ _ _ (CtxMux1 _ _) HS)
      | match goal with W : wval ?v |- _ => eapply (SCtx Σ _ _ _ (CtxMux2 v _ W) HS) end
      | match goal with W : wval ?v, W' : wval ?v' |- _ => eapply (SCtx Σ _ _ _ (CtxMux3 v v' W W') HS) end
    ]].
  all: eauto 8 with trace.
Qed.

Local Lemma same_oblivious_values Σ Γ v w a :
  wval v -> wval w ->
  runtime Σ Γ v false a -> runtime Σ Γ w false a ->
  obl_den a -> v ≈ w.
Proof.
  intros HV HW Tv Tw HO.
  destruct (runtime_oval _ _ _ _ HV Tv HO) as (ω & HT & HE).
  eapply ovalty_indist; [exact HT|].
  eapply runtime_exact_oval; [exact HW|eapply rt_conv; [exact Tw|symmetry; exact HE]|].
  exact (ovalty_otval _ _ HT).
Qed.

Local Lemma step_matches Σ Γ e f :
  step Σ e f ->
  forall l A u q D, runtime Σ Γ e l A -> runtime Σ Γ u q D -> e ≈ u ->
  exists u', step Σ u u' /\ f ≈ u'.
Proof.
  induction 1; intros l0 A u q D HE HU HI.
  all: try solve [eapply indist_lift; eauto].
  all: try solve [eapply indist_context_step; eauto].
  all: inversion HI; subst;
    repeat match goal with H : indistinguishable (EAbs _ _ _) _ |- _ =>
      inversion H; subst; clear H
    | H : indistinguishable (ELit _) _ |- _ => inversion H; subst; clear H
    | H : indistinguishable (EInj false _ _ _) _ |- _ => inversion H; subst; clear H
    | H : indistinguishable (EBoxedLit _) _ |- _ => inversion H; subst; clear H
    | H : indistinguishable (EBoxedInj _ _ _) _ |- _ => inversion H; subst; clear H
    | H : indistinguishable (EIte true _ _ _) _ |- _ => inversion H; subst; clear H
    | H : indistinguishable (EPair _ _) _ |- _ => inversion H; subst; clear H
    | H : indistinguishable (EFold _ _) _ |- _ => inversion H; subst; clear H
    | H : indistinguishable (EGVar _) _ |- _ => inversion H; subst; clear H
    | H : indistinguishable EUnitV _ |- _ => inversion H; subst; clear H
    end;
    inversion HU; subst; clear HU.
  - eexists; split; [eapply SApp; eauto using runtime_wval_indist|eauto with trace].
  - eexists; split; [eapply SLet; eauto using runtime_wval_indist|eauto with trace].
  - eexists; split; [apply SIf|destruct b; eauto].
  - eexists; split; [apply SIf|destruct b; eauto].
  - eexists; split;
      [eapply SCase; match goal with H : runtime _ _ (EInj false _ _ _) _ _ |- _ =>
        inversion H; subst; eauto using runtime_wval_indist end
      |destruct b; eauto with trace].
  - eexists; split;
      [eapply SCase; match goal with H : runtime _ _ (EInj false _ _ _) _ _ |- _ =>
        inversion H; subst; eauto using runtime_wval_indist end
      |destruct b; eauto with trace].
  - eexists; split;
      [eapply SProj; match goal with H : runtime _ _ (EPair _ _) _ _ |- _ =>
        inversion H; subst; eauto using runtime_wval_indist end
      |destruct b; eauto with trace].
  - eexists; split;
      [eapply SUnfold; match goal with H : runtime _ _ (EFold _ _) _ _ |- _ =>
        inversion H; subst; eauto using runtime_wval_indist end
      |assumption].
  - exists e; split; [eapply SFun; exact H|apply indist_refl].
  - exists e; split; [eapply SFun; exact H|apply indist_refl].
  - exists e; split; [eapply SFun; exact H|apply indist_refl].
  - eexists; split; [eapply SOADT; eauto using runtime_wval_indist|eauto with trace].
  - eexists; split; [apply SSec|constructor].
  - match goal with HO : otval ?t, HI' : ?t ≈ ?t' |- _ =>
      let EQ := fresh in pose proof (otval_indist _ _ HO HI') as EQ; subst t'
    end.
    eexists; split; [eapply SOInj; eauto using runtime_oval_indist|constructor].
  - inversion HE; subst; clear HE.
    assert (HVV : v1 ≈ v2) by (eapply same_oblivious_values; eassumption).
    eexists; split; [eapply SMux; eauto using runtime_wval_indist|].
    destruct b, b'; simpl; eauto using indist_trans, indist_sym.
  - inversion HE; subst; clear HE.
    repeat match goal with H : runtime _ _ (EBoxedInj _ _ _) _ _ |- _ =>
      inversion H; subst; clear H end.
    repeat match goal with H : ovalty (EBoxedInj _ _ _) _ |- _ =>
      inversion H; subst; clear H end.
    eexists; split; [eapply SOCase with (v1 := v1) (v2 := v2); eauto using ovalty_oval|].
    destruct b, b'; simpl; constructor; eauto using ovalty_indist with trace.
  - eexists; split;
      [eapply STapeOIf; match goal with H : runtime _ _ (EIte true _ _ _) _ _ |- _ =>
        inversion H; subst; eauto using runtime_woval_indist end
      |eauto 8 with trace].
  - eexists; split;
      [eapply STapePair; match goal with H : runtime _ _ (EPair _ _) _ _ |- _ =>
        inversion H; subst; eauto using runtime_woval_indist end
      |eauto 8 with trace].
  - eexists; split; [apply STapeUnitV|constructor].
  - eexists; split; [apply STapeBoxedLit|constructor].
  - eexists; split;
      [eapply STapeBoxedInj; eauto;
       match goal with H : runtime _ _ (EBoxedInj _ _ _) _ _ |- _ =>
         inversion H; subst; match goal with Hv : ovalty (EBoxedInj _ _ _) _ |- _ =>
           apply ovalty_oval in Hv; inversion Hv; assumption
         end
       end
      |constructor].
Qed.

Implicit Types (b : bool) (x X y Y : atom) (L : aset).

Definition trace_indistinguishable Σ e1 e2 : Prop :=
  forall n e1',
    Σ ⊨ e1 -->{n} e1' ->
    (exists e2', Σ ⊨ e2 -->{n} e2') /\
    (forall e2', Σ ⊨ e2 -->{n} e2' -> e1' ≈ e2').

Theorem obliviousness Σ e1 e2 τ1 τ2 :
  Σ; e1 ▷ τ1 ->
  Σ; e2 ▷ τ2 ->
  e1 ≈ e2 ->
  trace_indistinguishable Σ e1 e2.
Proof.
  intros [HG H1] [_ H2] Hobs.
  pose proof (proj1 (runtime_from_typing Σ HG) _ _ _ _ H1 ∅ (rt_empty_related Σ ∅)) as HT1.
  pose proof (proj1 (runtime_from_typing Σ HG) _ _ _ _ H2 ∅ (rt_empty_related Σ ∅)) as HT2.
  clear H1 H2.
  unfold trace_indistinguishable.
  intros n e1' Hsteps.
  revert e2 τ2 HT2 Hobs HT1.
  induction Hsteps as [e | n e f g Hstep Hsteps IH]; intros e2 τ2 HT2 Hobs HT1.
  - split; [exists e2; constructor|].
    intros u Hu; inversion Hu; subst; exact Hobs.
  - destruct (step_matches _ _ _ _ Hstep _ _ _ _ _ HT1 HT2 Hobs) as (u & Hsu & Hfu).
    pose proof (runtime_preservation _ _ _ _ HG Hstep _ _ HT1) as HTf.
    pose proof (runtime_preservation _ _ _ _ HG Hsu _ _ HT2) as HTu.
    destruct (IH _ _ HTu Hfu HTf) as [(v & Hv) _].
    split.
    + exists v; econstructor; eassumption.
    + intros v' Hv'; inversion Hv' as [|n' e' u' v'' Hsu' Htail]; subst.
      pose proof (step_unique_observation _ _ _ _ Hsu Hsu') as Huu.
      pose proof (runtime_preservation _ _ _ _ HG Hsu' _ _ HT2) as HTu'.
      destruct (IH _ _ HTu' (indist_trans _ _ _ Hfu Huu) HTf) as [_ Hout].
      eauto.
Qed.
