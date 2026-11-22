Require Import imports conv par geq typing.

Module consistency
  (Import lattice : Lattice)
  (Import syntax : syntax_sig lattice)
  (Import par : par_sig lattice syntax)
  (Import ieq : geq_sig lattice syntax)
  (Import conv : conv_sig lattice syntax par ieq)
  (Import typing : typing_sig lattice syntax par ieq conv).

Local Open Scope lattice_scope.

(* Level inclusion is transitive. *)
Lemma subset_trans : forall a b c : T, a ∩ b = a -> b ∩ c = b -> a ∩ c = a.
Proof.
  intros a b c Hab Hbc. transitivity ((a ∩ b) ∩ c).
  - rewrite Hab. reflexivity.
  - rewrite meet_associative. rewrite Hbc. rewrite Hab. reflexivity.
Qed.

(* A context lookup yields a corresponding level lookup in its econtext. *)
Lemma lookup_c2e : forall (i : fin) (G : context) (l : T) (A : tm),
  lookup i G l A -> elookup i (c2e G) l.
Proof.
  intros i G l A H. induction H.
  - simpl. reflexivity.
  - simpl. exact IHlookup.
Qed.

(* Generalized equality of a term with itself is decidable via level inclusion. *)
Lemma gieq_refl_of : forall (Xi : econtext) (l l0 : T) (b : tm),
  (l0 ⊆ l -> IEq Xi l b b) -> GIEq Xi l l0 b b.
Proof.
  intros Xi l l0 b H.
  destruct (T_eqdec (l0 ∩ l) l0) as [Hs | Hn].
  - apply GI_Dist; [exact Hs | apply H; exact Hs].
  - apply GI_InDist; exact Hn.
Qed.

(* Every well-typed term is IOk in the econtext of its typing context. *)
Lemma wt_iok : forall (G : context) (l : T) (a A : tm),
  Wt G l a A -> IOk (c2e G) l a.
Proof.
  intros G l a A H. induction H.
  - (* Var *) eapply IO_Var; [eapply lookup_c2e; eauto | eauto].
  - (* Pi *) simpl. eapply IO_Pi; eauto.
  - (* Abs *) simpl. eapply IO_Abs; eauto.
  - (* App *) simpl. eapply IO_App; eauto.
  - (* Conv *) exact IHWt1.
  - (* Zero *) eapply IO_Zero.
  - (* Suc *) simpl. eapply IO_Suc; eauto.
  - (* Ind *) simpl. eapply IO_Ind; eauto.
  - (* Nat *) eapply IO_Nat.
  - (* Univ *) eapply IO_Univ.
  - (* Void *) eapply IO_Void.
  - (* Absurd *) simpl. eapply IO_Absurd; eauto.
  - (* Refl *) eapply IO_Refl.
  - (* Eq *) simpl. eapply IO_Eq; eauto.
  - (* J *) simpl. eapply IO_J; eauto.
  - (* Sig *) simpl. eapply IO_Sig; eauto.
  - (* Pack *) simpl. eapply IO_Pack; eauto.
  - (* Let *) simpl. eapply IO_Let; eauto.
  - (* TT *) eapply IO_TT.
  - (* Unit *) eapply IO_Unit.
  - (* Seq *) simpl. eapply IO_Seq; eauto.
Qed.

(* Every well-typed term is IEq-equal to itself at any higher level. *)
Lemma wt_ieq_at : forall (G : context) (l : T) (a A : tm),
  Wt G l a A -> forall l', l ⊆ l' -> IEq (c2e G) l' a a.
Proof.
  intros G l a A H. induction H; intros l' Hle; simpl.
  - (* Var *) eapply I_Var; eauto 8 using lookup_c2e, subset_trans.
  - (* Pi *) eapply I_Pi; eauto 8 using subset_trans.
  - (* Abs *) eapply I_Abs; eauto 8 using subset_trans.
  - (* App *) eapply I_App.
    + eauto 8 using subset_trans.
    + eapply gieq_refl_of. intro Hsub. eauto 8 using subset_trans.
  - (* Conv *) eauto 8 using subset_trans.
  - (* Zero *) eapply I_Zero.
  - (* Suc *) eapply I_Suc; eauto 8 using subset_trans.
  - (* Ind *) eapply I_Ind; eauto 8 using subset_trans.
  - (* Nat *) eapply I_Nat.
  - (* Univ *) eapply I_Univ.
  - (* Void *) eapply I_Void.
  - (* Absurd *) eapply I_Absurd.
  - (* Refl *) eapply I_Refl.
  - (* Eq *) eapply I_Eq; eauto 8 using subset_trans.
  - (* J *) eapply I_J; eauto 8 using subset_trans.
  - (* Sig *) eapply I_Sig; eauto 8 using subset_trans.
  - (* Pack *) eapply I_Pack.
    + eapply gieq_refl_of. intro Hsub. eauto 8 using subset_trans.
    + eauto 8 using subset_trans.
  - (* Let *) eapply I_Let; eauto 8 using subset_trans.
  - (* TT *) eapply I_TT.
  - (* Unit *) eapply I_Unit.
  - (* Seq *) eapply I_Seq; eauto 8 using subset_trans.
Qed.

(* Typing is monotone in the level. *)
Lemma wt_mono : forall (G : context) (l : T) (a A : tm),
  Wt G l a A -> forall l', l ⊆ l' -> Wt G l' a A.
Proof.
  intros G l a A H. induction H; intros l' Hle.
  - (* Var *) eapply T_Var; eauto 8 using subset_trans.
  - (* Pi *) eapply T_Pi; eauto 8 using subset_trans.
  - (* Abs *) eapply T_Abs; eauto 8 using subset_trans.
  - (* App *) eapply T_App; eauto 8 using subset_trans.
  - (* Conv *) eapply T_Conv; eauto 8 using subset_trans.
  - (* Zero *) eapply T_Zero; eauto.
  - (* Suc *) eapply T_Suc; eauto 8 using subset_trans.
  - (* Ind *) eapply T_Ind; eauto 8 using subset_trans.
  - (* Nat *) eapply T_Nat; eauto.
  - (* Univ *) eapply T_Univ; eauto.
  - (* Void *) eapply T_Void; eauto.
  - (* Absurd *) eapply T_Absurd; eauto 8 using subset_trans.
  - (* Refl *) eapply T_Refl; eauto 8 using subset_trans.
  - (* Eq *) eapply T_Eq; eauto 8 using subset_trans.
  - (* J *) eapply (@T_J Γ t a b p A i j C l' ℓp ℓT ℓ0 ℓ1).
    + exact H.
    + eapply subset_trans; [exact H0 | exact Hle].
    + exact H1.
    + exact H2.
    + exact H3.
    + exact H4.
    + exact H5.
    + eapply IHWt6; exact Hle.
  - (* Sig *) eapply (@T_Sig Γ i j l' ℓ0 A B).
    + eapply IHWt1; exact Hle.
    + eapply IHWt2; exact Hle.
  - (* Pack *) eapply (@T_Pack Γ l' ℓ0 a A b B ℓT i).
    + exact H.
    + eapply IHWt2; exact Hle.
    + exact H1.
  - (* Let *) eapply (@T_Let Γ l' ℓp ℓ0 a b ℓT A B C i j k).
    + eapply subset_trans; [exact H | exact Hle].
    + exact H0.
    + exact H1.
    + exact H2.
    + eapply IHWt4; exact Hle.
    + exact H4.
  - (* TT *) eapply T_TT; eauto.
  - (* Unit *) eapply T_Unit; eauto.
  - (* Seq *) eapply (@T_Seq Γ l' ℓ0 ℓC a b C i).
    + eapply subset_trans; [exact H | exact Hle].
    + exact H0.
    + eapply IHWt2; exact Hle.
    + exact H2.
Qed.

Lemma subset_refl : forall a : T, a ⊆ a.
Proof. intro a. apply meet_idempotent. Qed.



(* IOk is monotone in its main level. *)
Lemma iok_mono : forall (Xi : econtext) (l : T) (a : tm),
  IOk Xi l a -> forall l', l ⊆ l' -> IOk Xi l' a.
Proof.
  intros Xi l a H. induction H; intros l' Hle.
  - eapply IO_Var; eauto 8 using subset_trans.
  - eapply IO_Univ.
  - eapply IO_Pi; eauto 8 using subset_trans.
  - eapply IO_Abs; eauto 8 using subset_trans.
  - eapply IO_App; eauto 8 using subset_trans.
  - eapply IO_Void.
  - eapply IO_Absurd; eauto.
  - eapply IO_Refl.
  - eapply IO_Eq; eauto 8 using subset_trans.
  - eapply IO_J; eauto 8 using subset_trans.
  - eapply IO_Sig; eauto 8 using subset_trans.
  - eapply IO_Pack; eauto 8 using subset_trans.
  - eapply IO_Let; eauto 8 using subset_trans.
  - eapply IO_Zero.
  - eapply IO_Suc; eauto 8 using subset_trans.
  - eapply IO_Ind; eauto 8 using subset_trans.
  - eapply IO_Nat.
  - eapply IO_Unit.
  - eapply IO_TT.
  - eapply IO_Seq; eauto 8 using subset_trans.
Qed.

(* Extending an econtext by a level on both sides preserves iok_ren_ok. *)
Lemma iok_ren_ok_extend : forall (rho : fin -> fin) (Xi D : econtext) (l : T),
  iok_ren_ok rho Xi D ->
  iok_ren_ok (up_ren rho) (l :: Xi) (l :: D).
Proof.
  intros rho Xi D l Hok i ℓ0 Hi.
  destruct i as [| k].
  - unfold elookup in Hi. simpl in Hi. assert (ℓ0 = l) as E by congruence. subst ℓ0. exists l. split.
    + simpl. reflexivity.
    + apply subset_refl.
  - unfold elookup in Hi. simpl in Hi. destruct (Hok k ℓ0 Hi) as [l' [Hlk Hsub]].
    exists l'. split.
    + simpl. exact Hlk.
    + exact Hsub.
Qed.

(* The shift renaming maps one econtext into a context extended by a level. *)
Lemma iok_ren_ok_shift : forall (Xi : econtext) (l : T),
  iok_ren_ok shift Xi (l :: Xi).
Proof.
  intros Xi l i ll Hi. exists ll. split.
  - simpl. exact Hi.
  - apply subset_refl.
Qed.

(* IOk is preserved by well-behaved renamings. *)
Lemma iok_ren : forall (Xi : econtext) (l : T) (a : tm),
  IOk Xi l a ->
  forall (D : econtext) (rho : fin -> fin),
    iok_ren_ok rho Xi D -> IOk D l (a⟨rho⟩).
Proof.
  intros Xi l a H. induction H; intros D rho Hok; simpl.
  - (* Var *) destruct (Hok i ℓ0 H) as [l' [Hlk Hsub]].
    eapply IO_Var.
    + exact Hlk.
    + eapply subset_trans; [exact Hsub | exact H0].
  - eapply IO_Univ.
  - eapply IO_Pi; eauto 10 using iok_ren_ok_extend, subset_trans.
  - eapply IO_Abs; eauto 10 using iok_ren_ok_extend, subset_trans.
  - eapply IO_App; eauto 10 using iok_ren_ok_extend, subset_trans.
  - eapply IO_Void.
  - eapply IO_Absurd; eauto 10 using iok_ren_ok_extend, subset_trans.
  - eapply IO_Refl.
  - eapply IO_Eq; eauto 10 using iok_ren_ok_extend, subset_trans.
  - eapply IO_J; eauto 10 using iok_ren_ok_extend, subset_trans.
  - eapply IO_Sig; eauto 10 using iok_ren_ok_extend, subset_trans.
  - eapply IO_Pack; eauto 10 using iok_ren_ok_extend, subset_trans.
  - eapply IO_Let; eauto 10 using iok_ren_ok_extend, subset_trans.
  - eapply IO_Zero.
  - eapply IO_Suc; eauto 10 using iok_ren_ok_extend, subset_trans.
  - eapply IO_Ind; eauto 10 using iok_ren_ok_extend, subset_trans.
  - eapply IO_Nat.
  - eapply IO_Unit.
  - eapply IO_TT.
  - eapply IO_Seq; eauto 10 using iok_ren_ok_extend, subset_trans.
Qed.

(* Extending an econtext preserves iok_subst_ok, using the shift renaming. *)
Lemma iok_subst_ok_extend : forall (rho : fin -> tm) (Xi D : econtext) (l : T),
  iok_subst_ok rho Xi D ->
  iok_subst_ok (up_tm_tm rho) (l :: Xi) (l :: D).
Proof.
  intros rho Xi D l Hok i ℓ0 Hi.
  destruct i as [| k].
  - unfold elookup in Hi. simpl in Hi. assert (ℓ0 = l) as E by congruence. subst ℓ0.
    simpl. eapply IO_Var.
    + simpl. reflexivity.
    + apply subset_refl.
  - unfold elookup in Hi. simpl in Hi. simpl.
    eapply iok_ren with (Xi := D) (D := l :: D) (rho := shift).
    + apply (Hok k ℓ0 Hi).
    + apply iok_ren_ok_shift.
Qed.

(* IOk is preserved by well-behaved substitutions. *)
Lemma iok_subst : forall (Xi : econtext) (l : T) (a : tm),
  IOk Xi l a ->
  forall (D : econtext) (rho : fin -> tm),
    iok_subst_ok rho Xi D -> IOk D l (a[rho]).
Proof.
  intros Xi l a H. induction H; intros D rho Hok; simpl.
  - (* Var *) eapply iok_mono.
    + apply (Hok i ℓ0 H).
    + exact H0.
  - eapply IO_Univ.
  - eapply IO_Pi; eauto 10 using iok_subst_ok_extend, iok_mono, subset_trans.
  - eapply IO_Abs; eauto 10 using iok_subst_ok_extend, iok_mono, subset_trans.
  - eapply IO_App; eauto 10 using iok_subst_ok_extend, iok_mono, subset_trans.
  - eapply IO_Void.
  - eapply IO_Absurd; eauto 10 using iok_subst_ok_extend, iok_mono, subset_trans.
  - eapply IO_Refl.
  - eapply IO_Eq; eauto 10 using iok_subst_ok_extend, iok_mono, subset_trans.
  - eapply IO_J; eauto 10 using iok_subst_ok_extend, iok_mono, subset_trans.
  - eapply IO_Sig; eauto 10 using iok_subst_ok_extend, iok_mono, subset_trans.
  - eapply IO_Pack; eauto 10 using iok_subst_ok_extend, iok_mono, subset_trans.
  - eapply IO_Let; eauto 10 using iok_subst_ok_extend, iok_mono, subset_trans.
  - eapply IO_Zero.
  - eapply IO_Suc; eauto 10 using iok_subst_ok_extend, iok_mono, subset_trans.
  - eapply IO_Ind; eauto 10 using iok_subst_ok_extend, iok_mono, subset_trans.
  - eapply IO_Nat.
  - eapply IO_Unit.
  - eapply IO_TT.
  - eapply IO_Seq; eauto 10 using iok_subst_ok_extend, iok_mono, subset_trans.
Qed.

(* Extensionality of renaming. *)
Lemma tm_ren_ext : forall (a : tm) (rho sigma : fin -> fin),
  (forall k, rho k = sigma k) -> ren_tm rho a = ren_tm sigma a.
Proof.
  induction a; simpl; intros; try reflexivity.
  - rewrite H. reflexivity.
  - (* tAbs *) f_equal. apply IHa. intro k; destruct k; simpl; [reflexivity|repeat (unfold funcomp; simpl); rewrite H; reflexivity].
  - (* tApp *) f_equal; [apply IHa1; exact H | apply IHa2; exact H].
  - (* tPi *) f_equal; [apply IHa1; exact H | apply IHa2; intro k; destruct k; simpl; [reflexivity|repeat (unfold funcomp; simpl); rewrite H; reflexivity]].
  - (* tAbsurd *) f_equal; apply IHa; exact H.
  - (* tEq *) f_equal; [apply IHa1; exact H | apply IHa2; exact H].
  - (* tJ *) f_equal; [apply IHa1; exact H | apply IHa2; exact H].
  - (* tSig *) f_equal; [apply IHa1; exact H | apply IHa2; intro k; destruct k; simpl; [reflexivity|repeat (unfold funcomp; simpl); rewrite H; reflexivity]].
  - (* tPack *) f_equal; [apply IHa1; exact H | apply IHa2; exact H].
  - (* tLet *) f_equal; [apply IHa1; exact H | apply IHa2; intro k; destruct k as [|[|j]]; simpl; try reflexivity; repeat (unfold funcomp; simpl); rewrite H; reflexivity].
  - (* tSuc *) f_equal; apply IHa; exact H.
  - (* tInd *) f_equal; [apply IHa1; exact H | apply IHa2; intro k; destruct k as [|[|j]]; simpl; try reflexivity; repeat (unfold funcomp; simpl); rewrite H; reflexivity | apply IHa3; exact H].
  - (* tSeq *) f_equal; [apply IHa1; exact H | apply IHa2; exact H].
Qed.

(* Extensionality of substitution. *)
Lemma tm_subst_ext : forall (a : tm) (sigma tau : fin -> tm),
  (forall k, sigma k = tau k) -> subst_tm sigma a = subst_tm tau a.
Proof.
  induction a; simpl; intros; try reflexivity.
  - rewrite H. reflexivity.
  - (* tAbs *) f_equal. apply IHa. intro k; destruct k; simpl; [reflexivity|repeat (unfold funcomp; simpl); rewrite H; reflexivity].
  - (* tApp *) f_equal; [apply IHa1; exact H | apply IHa2; exact H].
  - (* tPi *) f_equal; [apply IHa1; exact H | apply IHa2; intro k; destruct k; simpl; [reflexivity|repeat (unfold funcomp; simpl); rewrite H; reflexivity]].
  - (* tAbsurd *) f_equal; apply IHa; exact H.
  - (* tEq *) f_equal; [apply IHa1; exact H | apply IHa2; exact H].
  - (* tJ *) f_equal; [apply IHa1; exact H | apply IHa2; exact H].
  - (* tSig *) f_equal; [apply IHa1; exact H | apply IHa2; intro k; destruct k; simpl; [reflexivity|repeat (unfold funcomp; simpl); rewrite H; reflexivity]].
  - (* tPack *) f_equal; [apply IHa1; exact H | apply IHa2; exact H].
  - (* tLet *) f_equal; [apply IHa1; exact H | apply IHa2; intro k; destruct k as [|[|j]]; simpl; try reflexivity; repeat (unfold funcomp; simpl); rewrite H; reflexivity].
  - (* tSuc *) f_equal; apply IHa; exact H.
  - (* tInd *) f_equal; [apply IHa1; exact H | apply IHa2; intro k; destruct k as [|[|j]]; simpl; try reflexivity; repeat (unfold funcomp; simpl); rewrite H; reflexivity | apply IHa3; exact H].
  - (* tSeq *) f_equal; [apply IHa1; exact H | apply IHa2; exact H].
Qed.

(* Composition of renamings. *)
Lemma tm_ren_ren : forall (a : tm) (rho sigma : fin -> fin),
  ren_tm rho (ren_tm sigma a) = ren_tm (sigma >> rho) a.
Proof.
  induction a; simpl; intros; try reflexivity.
  - (* tAbs *) f_equal. rewrite (IHa (up_ren rho) (up_ren sigma)).
    apply tm_ren_ext. intro k; destruct k; simpl; reflexivity.
  - (* tApp *) f_equal; [exact (IHa1 rho sigma) | exact (IHa2 rho sigma)].
  - (* tPi *) f_equal.
    + exact (IHa1 rho sigma).
    + rewrite (IHa2 (up_ren rho) (up_ren sigma)). apply tm_ren_ext.
      intro k; destruct k; simpl; reflexivity.
  - (* tAbsurd *) f_equal; exact (IHa rho sigma).
  - (* tEq *) f_equal; [exact (IHa1 rho sigma) | exact (IHa2 rho sigma)].
  - (* tJ *) f_equal; [exact (IHa1 rho sigma) | exact (IHa2 rho sigma)].
  - (* tSig *) f_equal.
    + exact (IHa1 rho sigma).
    + rewrite (IHa2 (up_ren rho) (up_ren sigma)). apply tm_ren_ext.
      intro k; destruct k; simpl; reflexivity.
  - (* tPack *) f_equal; [exact (IHa1 rho sigma) | exact (IHa2 rho sigma)].
  - (* tLet *) f_equal.
    + exact (IHa1 rho sigma).
    + rewrite (IHa2 (up_ren (up_ren rho)) (up_ren (up_ren sigma))). apply tm_ren_ext.
      intro k; destruct k as [|[|j]]; simpl; reflexivity.
  - (* tSuc *) f_equal; exact (IHa rho sigma).
  - (* tInd *) f_equal.
    + exact (IHa1 rho sigma).
    + rewrite (IHa2 (up_ren (up_ren rho)) (up_ren (up_ren sigma))). apply tm_ren_ext.
      intro k; destruct k as [|[|j]]; simpl; reflexivity.
    + exact (IHa3 rho sigma).
  - (* tSeq *) f_equal; [exact (IHa1 rho sigma) | exact (IHa2 rho sigma)].
Qed.


Definition IEqSymP (Xi : econtext) (l : T) (a b : tm) (H : IEq Xi l a b) : Prop :=
  IEq Xi l b a.
Definition GIEqSymP (Xi : econtext) (l l0 : T) (a b : tm) (H : GIEq Xi l l0 a b) : Prop :=
  GIEq Xi l l0 b a.

Lemma ieq_gieq_sym : forall (Xi : econtext) (l : T),
  (forall (a b : tm) (H : IEq Xi l a b), IEq Xi l b a) /\
  (forall (l0 : T) (a b : tm) (H : GIEq Xi l l0 a b), GIEq Xi l l0 b a).
Proof.
  intros Xi l. apply (IEq_mutual IEqSymP GIEqSymP).
  - intros; eapply I_Var; eauto.
  - intros; eapply I_Univ.
  - intros; eapply I_Pi; eauto.
  - intros; eapply I_Abs; eauto.
  - intros; eapply I_App; eauto.
  - intros; eapply I_Void.
  - intros; eapply I_Absurd.
  - intros; eapply I_Refl.
  - intros; eapply I_Eq; eauto.
  - intros; eapply I_J; eauto.
  - intros; eapply I_Sig; eauto.
  - intros; eapply I_Pack; eauto.
  - intros; eapply I_Let; eauto.
  - intros; eapply I_Zero.
  - intros; eapply I_Suc; eauto.
  - intros; eapply I_Ind; eauto.
  - intros; eapply I_Nat.
  - intros; eapply I_Unit.
  - intros; eapply I_TT.
  - intros; eapply I_Seq; eauto.
  - intros; eapply GI_Dist; eauto.
  - intros; eapply GI_InDist; eauto.
Qed.

Definition IEqTransP (Xi : econtext) (l : T) (a b : tm) (H : IEq Xi l a b) : Prop :=
  forall c : tm, IEq Xi l b c -> IEq Xi l a c.
Definition GIEqTransP (Xi : econtext) (l l0 : T) (a b : tm) (H : GIEq Xi l l0 a b) : Prop :=
  forall c : tm, GIEq Xi l l0 b c -> GIEq Xi l l0 a c.

Lemma ieq_gieq_trans : forall (Xi : econtext) (l : T),
  (forall (a b : tm) (H : IEq Xi l a b), forall c : tm, IEq Xi l b c -> IEq Xi l a c) /\
  (forall (l0 : T) (a b : tm) (H : GIEq Xi l l0 a b),
      forall c : tm, GIEq Xi l l0 b c -> GIEq Xi l l0 a c).
Proof.
  intros Xi l. apply (IEq_mutual IEqTransP GIEqTransP).
  all: try (intros; unfold IEqTransP in *; intros c H2;
    match goal with
    | H : IEq ?X ?L ?B ?C |- IEq ?X ?L ?A ?C =>
        inversion H; subst; econstructor; eauto 8
    end).
  - (* GI_Dist *) intros Xi' l' l0' A B e i IH.
    unfold GIEqTransP, IEqTransP in *. intros c H2.
    destruct H2.
    + eapply GI_Dist; [exact e | apply IH; eassumption].
    + eapply GI_InDist; eassumption.
  - (* GI_InDist *) intros Xi' l' l0' A B n.
    unfold GIEqTransP in *. intros c H2.
    eapply GI_InDist; eassumption.
Qed.

Lemma ieq_sym : forall (Xi : econtext) (l : T) (a b : tm),
  IEq Xi l a b -> IEq Xi l b a.
Proof.
  intros Xi l a b H. exact (proj1 (ieq_gieq_sym Xi l) a b H).
Qed.

Lemma gieq_sym : forall (Xi : econtext) (l l0 : T) (a b : tm),
  GIEq Xi l l0 a b -> GIEq Xi l l0 b a.
Proof.
  intros Xi l l0 a b H. exact (proj2 (ieq_gieq_sym Xi l) l0 a b H).
Qed.

Lemma ieq_trans : forall (Xi : econtext) (l : T) (a b c : tm),
  IEq Xi l a b -> IEq Xi l b c -> IEq Xi l a c.
Proof.
  intros Xi l a b c H1 H2. exact (proj1 (ieq_gieq_trans Xi l) a b H1 c H2).
Qed.

Lemma gieq_trans : forall (Xi : econtext) (l l0 : T) (a b c : tm),
  GIEq Xi l l0 a b -> GIEq Xi l l0 b c -> GIEq Xi l l0 a c.
Proof.
  intros Xi l l0 a b c H1 H2. exact (proj2 (ieq_gieq_trans Xi l) l0 a b H1 c H2).
Qed.

Lemma conv_sym : forall (Xi : econtext) (A B : tm), conv Xi A B -> conv Xi B A.
Proof.
  intros Xi A B [l [c0 [c1 [H0 [H1 H2]]]]].
  exists l, c1, c0. split; [exact H1 | split; [exact H0 | apply ieq_sym; exact H2]].
Qed.

Lemma conv_refl_ieq : forall (Xi : econtext) (l : T) (A : tm),
  IEq Xi l A A -> conv Xi A A.
Proof.
  intros Xi l A H. exists l, A, A.
  split; [apply rtc_refl | split; [apply rtc_refl | exact H]].
Qed.

Lemma conv_refl_typed : forall (G : context) (l : T) (a A : tm),
  Wt G l a A -> conv (c2e G) a a.
Proof.
  intros G l a A H. apply (conv_refl_ieq (c2e G) l a).
  apply (wt_ieq_at G l a A H l). apply subset_refl.
Qed.

(* IOk is closed under parallel reduction. *)
Lemma iok_par : forall a b : tm, Par a b -> forall (Xi : econtext) (l : T),
  IOk Xi l a -> IOk Xi l b.
Proof.
  intros a b H. induction H; intros Xi l Hiok.
  - (* P_Var *) inversion Hiok; subst. eapply IO_Var; eauto.
  - (* P_Univ *) inversion Hiok; subst. eapply IO_Univ.
  - (* P_Pi *) inversion Hiok; subst. eapply IO_Pi; [eapply IHPar1; eauto | eapply IHPar2; eauto].
  - (* P_Abs *) inversion Hiok; subst. eapply IO_Abs; eapply IHPar; eauto.
  - (* P_App *) inversion Hiok; subst. eapply IO_App; [eapply IHPar1; eauto | eapply IHPar2; eauto].
  - (* P_AppAbs *) inversion Hiok; subst.
    match goal with
    | Hf : IOk _ _ (tAbs _ _) |- _ => inversion Hf; subst
    end.
    assert (Hbody : IOk (ℓ0 :: Xi) l a0) by (eapply IHPar1; eauto).
    assert (Harg : IOk Xi ℓ0 b1) by (eapply IHPar2; eauto).
    assert (Hok : iok_subst_ok (b1 ..) (ℓ0 :: Xi) Xi).
    { intros i ll Hil. destruct i as [| k].
      - unfold elookup in Hil; simpl in Hil. assert (ll = ℓ0) as E by congruence. subst ll. simpl. exact Harg.
      - unfold elookup in Hil; simpl in Hil. simpl. eapply IO_Var; [exact Hil | apply subset_refl]. }
    exact (iok_subst (ℓ0 :: Xi) l a0 Hbody Xi (b1 ..) Hok).
  - (* P_Void *) inversion Hiok; subst. eapply IO_Void.
  - (* P_Absurd *) inversion Hiok; subst. eapply IO_Absurd; eapply IHPar; eauto.
  - (* P_Refl *) inversion Hiok; subst. eapply IO_Refl.
  - (* P_Eq *) inversion Hiok; subst. eapply IO_Eq; [eassumption | eapply IHPar1; eauto | eapply IHPar2; eauto].
  - (* P_J *) inversion Hiok; subst. eapply IO_J; [eassumption | eapply IHPar1; eauto | eapply IHPar2; eauto].
  - (* P_JRefl *) inversion Hiok; subst. eapply IHPar; eauto.
  - (* P_Sig *) inversion Hiok; subst. eapply IO_Sig; [eapply IHPar1; eauto | eapply IHPar2; eauto].
  - (* P_Pack *) inversion Hiok; subst. eapply IO_Pack; [eapply IHPar1; eauto | eapply IHPar2; eauto].
  - (* P_Let *) inversion Hiok; subst. eapply IO_Let; [eassumption | eapply IHPar1; eauto | eapply IHPar2; eauto].
  - (* P_LetPack *) inversion Hiok; subst.
    match goal with
    | Hp : IOk _ _ (tPack _ _ _) |- _ => inversion Hp; subst
    end.
    assert (Ha1 : IOk Xi ℓ0 a1) by (eapply IHPar1; eauto).
    assert (Hb1 : IOk Xi ℓ1 b1) by (eapply IHPar2; eauto).
    assert (Hc1 : IOk (ℓ1 :: ℓ0 :: Xi) l c1) by (eapply IHPar3; eauto).
    assert (Hok : iok_subst_ok (b1 .: a1 ..) (ℓ1 :: ℓ0 :: Xi) Xi).
    { intros i ll Hil. destruct i as [| [| k]].
      - unfold elookup in Hil; simpl in Hil. assert (ll = ℓ1) as E by congruence. subst ll. simpl. exact Hb1.
      - unfold elookup in Hil; simpl in Hil. assert (ll = ℓ0) as E by congruence. subst ll. simpl. exact Ha1.
      - unfold elookup in Hil; simpl in Hil. simpl. eapply IO_Var; [exact Hil | apply subset_refl]. }
    exact (iok_subst (ℓ1 :: ℓ0 :: Xi) l c1 Hc1 Xi (b1 .: a1 ..) Hok).
  - (* P_Zero *) inversion Hiok; subst. eapply IO_Zero.
  - (* P_Suc *) inversion Hiok; subst. eapply IO_Suc; eapply IHPar; eauto.
  - (* P_Ind *) inversion Hiok; subst. eapply IO_Ind; [eassumption | eapply IHPar1; eauto | eapply IHPar2; eauto | eapply IHPar3; eauto].
  - (* P_IndZero *) inversion Hiok; subst. eapply iok_mono; [eapply IHPar; eauto | eassumption].
  - (* P_IndSuc *) inversion Hiok; subst.
    match goal with
    | Hc : IOk _ _ (tSuc _) |- _ => inversion Hc; subst
    end.
    assert (Ha1 : IOk Xi ℓ a1) by (eapply IHPar1; eauto).
    assert (Hb1 : IOk (ℓ :: ℓ :: Xi) ℓ b1) by (eapply IHPar2; eauto).
    assert (Hc1 : IOk Xi ℓ c1) by (eapply IHPar3; eauto).
    assert (Hind : IOk Xi ℓ (tInd ℓ a1 b1 c1)).
    { eapply IO_Ind; [apply subset_refl | exact Ha1 | exact Hb1 | exact Hc1]. }
    assert (Hok : iok_subst_ok ((tInd ℓ a1 b1 c1) .: c1 ..) (ℓ :: ℓ :: Xi) Xi).
    { intros i ll Hil. destruct i as [| [| k]].
      - unfold elookup in Hil; simpl in Hil. assert (ll = ℓ) as E by congruence. subst ll. simpl. exact Hind.
      - unfold elookup in Hil; simpl in Hil. assert (ll = ℓ) as E by congruence. subst ll. simpl. exact Hc1.
      - unfold elookup in Hil; simpl in Hil. simpl. eapply IO_Var; [exact Hil | apply subset_refl]. }
    eapply iok_mono.
    + exact (iok_subst (ℓ :: ℓ :: Xi) ℓ b1 Hb1 Xi ((tInd ℓ a1 b1 c1) .: c1 ..) Hok).
    + eassumption.
  - (* P_Nat *) inversion Hiok; subst. eapply IO_Nat.
  - (* P_TT *) inversion Hiok; subst. eapply IO_TT.
  - (* P_Seq *) inversion Hiok; subst. eapply IO_Seq; [eassumption | eapply IHPar1; eauto | eapply IHPar2; eauto].
  - (* P_SeqTT *) inversion Hiok; subst. eapply IHPar; eauto.
  - (* P_Unit *) inversion Hiok; subst. eapply IO_Unit.
Qed.

Definition IEqRenP (Xi : econtext) (l : T) (a b : tm) (H : IEq Xi l a b) : Prop :=
  forall (D : econtext) (rho : fin -> fin),
    iok_ren_ok rho Xi D -> IEq D l (a⟨rho⟩) (b⟨rho⟩).
Definition GIEqRenP (Xi : econtext) (l l0 : T) (a b : tm) (H : GIEq Xi l l0 a b) : Prop :=
  forall (D : econtext) (rho : fin -> fin),
    iok_ren_ok rho Xi D -> GIEq D l l0 (a⟨rho⟩) (b⟨rho⟩).

Lemma ieq_gieq_ren : forall (Xi : econtext) (l : T),
  (forall (a b : tm) (H : IEq Xi l a b), IEqRenP Xi l a b H) /\
  (forall (l0 : T) (a b : tm) (H : GIEq Xi l l0 a b), GIEqRenP Xi l l0 a b H).
Proof.
  intros Xi l. apply (IEq_mutual IEqRenP GIEqRenP).
  - (* I_Var *) intros Xi' l' i l0 e e0.
    unfold IEqRenP, GIEqRenP in *. intros D rho Hok.
    destruct (Hok i l0 e) as [l'' [Hlk Hsub]].
    eapply I_Var; [exact Hlk | eapply subset_trans; [exact Hsub | exact e0]].
  - (* I_Univ *) intros; unfold IEqRenP, GIEqRenP in *; intros D rho Hok; eapply I_Univ.
  - (* I_Pi *) intros; unfold IEqRenP, GIEqRenP in *; intros D rho Hok; eapply I_Pi; eauto 10 using iok_ren_ok_extend, subset_trans.
  - (* I_Abs *) intros; unfold IEqRenP, GIEqRenP in *; intros D rho Hok; eapply I_Abs; eauto 10 using iok_ren_ok_extend, subset_trans.
  - (* I_App *) intros; unfold IEqRenP, GIEqRenP in *; intros D rho Hok; eapply I_App; eauto 10 using iok_ren_ok_extend, subset_trans.
  - (* I_Void *) intros; unfold IEqRenP, GIEqRenP in *; intros D rho Hok; eapply I_Void.
  - (* I_Absurd *) intros; unfold IEqRenP, GIEqRenP in *; intros D rho Hok; eapply I_Absurd.
  - (* I_Refl *) intros; unfold IEqRenP, GIEqRenP in *; intros D rho Hok; eapply I_Refl.
  - (* I_Eq *) intros; unfold IEqRenP, GIEqRenP in *; intros D rho Hok; eapply I_Eq; eauto 10 using iok_ren_ok_extend, subset_trans.
  - (* I_J *) intros; unfold IEqRenP, GIEqRenP in *; intros D rho Hok; eapply I_J; eauto 10 using iok_ren_ok_extend, subset_trans.
  - (* I_Sig *) intros; unfold IEqRenP, GIEqRenP in *; intros D rho Hok; eapply I_Sig; eauto 10 using iok_ren_ok_extend, subset_trans.
  - (* I_Pack *) intros; unfold IEqRenP, GIEqRenP in *; intros D rho Hok; eapply I_Pack; eauto 10 using iok_ren_ok_extend, subset_trans.
  - (* I_Let *) intros; unfold IEqRenP, GIEqRenP in *; intros D rho Hok; eapply I_Let; eauto 10 using iok_ren_ok_extend, subset_trans.
  - (* I_Zero *) intros; unfold IEqRenP, GIEqRenP in *; intros D rho Hok; eapply I_Zero.
  - (* I_Suc *) intros; unfold IEqRenP, GIEqRenP in *; intros D rho Hok; eapply I_Suc; eauto 10 using iok_ren_ok_extend, subset_trans.
  - (* I_Ind *) intros; unfold IEqRenP, GIEqRenP in *; intros D rho Hok; eapply I_Ind; eauto 10 using iok_ren_ok_extend, subset_trans.
  - (* I_Nat *) intros; unfold IEqRenP, GIEqRenP in *; intros D rho Hok; eapply I_Nat.
  - (* I_Unit *) intros; unfold IEqRenP, GIEqRenP in *; intros D rho Hok; eapply I_Unit.
  - (* I_TT *) intros; unfold IEqRenP, GIEqRenP in *; intros D rho Hok; eapply I_TT.
  - (* I_Seq *) intros; unfold IEqRenP, GIEqRenP in *; intros D rho Hok; eapply I_Seq; eauto 10 using iok_ren_ok_extend, subset_trans.
  - (* GI_Dist *) intros; unfold IEqRenP, GIEqRenP in *; intros D rho Hok; eapply GI_Dist; eauto 10 using iok_ren_ok_extend, subset_trans.
  - (* GI_InDist *) intros; unfold IEqRenP, GIEqRenP in *; intros D rho Hok; eapply GI_InDist; eauto.
Qed.

Lemma ieq_ren : forall (Xi : econtext) (l : T) (a b : tm),
  IEq Xi l a b -> forall (D : econtext) (rho : fin -> fin),
    iok_ren_ok rho Xi D -> IEq D l (a⟨rho⟩) (b⟨rho⟩).
Proof.
  intros Xi l a b H D rho Hok.
  exact (proj1 (ieq_gieq_ren Xi l) a b H D rho Hok).
Qed.

Lemma gieq_ren : forall (Xi : econtext) (l l0 : T) (a b : tm),
  GIEq Xi l l0 a b -> forall (D : econtext) (rho : fin -> fin),
    iok_ren_ok rho Xi D -> GIEq D l l0 (a⟨rho⟩) (b⟨rho⟩).
Proof.
  intros Xi l l0 a b H D rho Hok.
  exact (proj2 (ieq_gieq_ren Xi l) l0 a b H D rho Hok).
Qed.

Definition ieq_subst_ok (rho : fin -> tm) (Xi D : econtext) : Prop :=
  forall i l0, elookup i Xi l0 -> forall l, l0 ⊆ l -> IEq D l (rho i) (rho i).

Lemma ieq_subst_ok_extend : forall (rho : fin -> tm) (Xi D : econtext) (l : T),
  ieq_subst_ok rho Xi D -> ieq_subst_ok (up_tm_tm rho) (l :: Xi) (l :: D).
Proof.
  intros rho Xi D l Hok i ll Hi m Hsub.
  destruct i as [| k].
  - unfold elookup in Hi; simpl in Hi. assert (ll = l) as E by congruence. subst ll. simpl.
    eapply I_Var; [simpl; reflexivity | exact Hsub].
  - unfold elookup in Hi; simpl in Hi. simpl.
    eapply ieq_ren with (Xi := D) (D := l :: D) (rho := shift).
    + apply (Hok k ll Hi m Hsub).
    + apply iok_ren_ok_shift.
Qed.

Definition IEqSubP (Xi : econtext) (l : T) (a b : tm) (H : IEq Xi l a b) : Prop :=
  forall (D : econtext) (rho : fin -> tm),
    ieq_subst_ok rho Xi D -> IEq D l (a[rho]) (b[rho]).
Definition GIEqSubP (Xi : econtext) (l l0 : T) (a b : tm) (H : GIEq Xi l l0 a b) : Prop :=
  forall (D : econtext) (rho : fin -> tm),
    ieq_subst_ok rho Xi D -> GIEq D l l0 (a[rho]) (b[rho]).

Lemma ieq_gieq_subst : forall (Xi : econtext) (l : T),
  (forall (a b : tm) (H : IEq Xi l a b), IEqSubP Xi l a b H) /\
  (forall (l0 : T) (a b : tm) (H : GIEq Xi l l0 a b), GIEqSubP Xi l l0 a b H).
Proof.
  intros Xi l. apply (IEq_mutual IEqSubP GIEqSubP).
  - (* I_Var *) intros Xi' l' i l0 e e0. unfold IEqSubP, GIEqSubP in *. intros D rho Hok.
    exact (Hok i l0 e l' e0).
  - (* I_Univ *) intros; unfold IEqSubP, GIEqSubP in *; intros D rho Hok; eapply I_Univ.
  - (* I_Pi *) intros; unfold IEqSubP, GIEqSubP in *; intros D rho Hok; eapply I_Pi; eauto 10 using ieq_subst_ok_extend.
  - (* I_Abs *) intros; unfold IEqSubP, GIEqSubP in *; intros D rho Hok; eapply I_Abs; eauto 10 using ieq_subst_ok_extend.
  - (* I_App *) intros; unfold IEqSubP, GIEqSubP in *; intros D rho Hok; eapply I_App; eauto 10 using ieq_subst_ok_extend.
  - (* I_Void *) intros; unfold IEqSubP, GIEqSubP in *; intros D rho Hok; eapply I_Void.
  - (* I_Absurd *) intros; unfold IEqSubP, GIEqSubP in *; intros D rho Hok; eapply I_Absurd.
  - (* I_Refl *) intros; unfold IEqSubP, GIEqSubP in *; intros D rho Hok; eapply I_Refl.
  - (* I_Eq *) intros; unfold IEqSubP, GIEqSubP in *; intros D rho Hok; eapply I_Eq; eauto 10 using ieq_subst_ok_extend.
  - (* I_J *) intros; unfold IEqSubP, GIEqSubP in *; intros D rho Hok; eapply I_J; eauto 10 using ieq_subst_ok_extend.
  - (* I_Sig *) intros; unfold IEqSubP, GIEqSubP in *; intros D rho Hok; eapply I_Sig; eauto 10 using ieq_subst_ok_extend.
  - (* I_Pack *) intros; unfold IEqSubP, GIEqSubP in *; intros D rho Hok; eapply I_Pack; eauto 10 using ieq_subst_ok_extend.
  - (* I_Let *) intros; unfold IEqSubP, GIEqSubP in *; intros D rho Hok; eapply I_Let; eauto 10 using ieq_subst_ok_extend.
  - (* I_Zero *) intros; unfold IEqSubP, GIEqSubP in *; intros D rho Hok; eapply I_Zero.
  - (* I_Suc *) intros; unfold IEqSubP, GIEqSubP in *; intros D rho Hok; eapply I_Suc; eauto 10 using ieq_subst_ok_extend.
  - (* I_Ind *) intros; unfold IEqSubP, GIEqSubP in *; intros D rho Hok; eapply I_Ind; eauto 10 using ieq_subst_ok_extend.
  - (* I_Nat *) intros; unfold IEqSubP, GIEqSubP in *; intros D rho Hok; eapply I_Nat.
  - (* I_Unit *) intros; unfold IEqSubP, GIEqSubP in *; intros D rho Hok; eapply I_Unit.
  - (* I_TT *) intros; unfold IEqSubP, GIEqSubP in *; intros D rho Hok; eapply I_TT.
  - (* I_Seq *) intros; unfold IEqSubP, GIEqSubP in *; intros D rho Hok; eapply I_Seq; eauto 10 using ieq_subst_ok_extend.
  - (* GI_Dist *) intros; unfold IEqSubP, GIEqSubP in *; intros D rho Hok; eapply GI_Dist; eauto 10 using ieq_subst_ok_extend.
  - (* GI_InDist *) intros; unfold IEqSubP, GIEqSubP in *; intros D rho Hok; eapply GI_InDist; eauto.
Qed.

Lemma ieq_subst : forall (Xi : econtext) (l : T) (a b : tm),
  IEq Xi l a b -> forall (D : econtext) (rho : fin -> tm),
    ieq_subst_ok rho Xi D -> IEq D l (a[rho]) (b[rho]).
Proof.
  intros Xi l a b H D rho Hok.
  exact (proj1 (ieq_gieq_subst Xi l) a b H D rho Hok).
Qed.

Lemma gieq_subst : forall (Xi : econtext) (l l0 : T) (a b : tm),
  GIEq Xi l l0 a b -> forall (D : econtext) (rho : fin -> tm),
    ieq_subst_ok rho Xi D -> GIEq D l l0 (a[rho]) (b[rho]).
Proof.
  intros Xi l l0 a b H D rho Hok.
  exact (proj2 (ieq_gieq_subst Xi l) l0 a b H D rho Hok).
Qed.


Lemma tm_ren_shift_up : forall (rho : fin -> fin) (t : tm),
  ren_tm (up_ren rho) (ren_tm shift t) = ren_tm shift (ren_tm rho t).
Proof.
  intros rho t. rewrite tm_ren_ren. rewrite tm_ren_ren.
  apply tm_ren_ext. intro x. destruct x; repeat (unfold funcomp; simpl); reflexivity.
Qed.

Lemma tm_ren_shift_up2 : forall (rho : fin -> fin) (t : tm),
  ren_tm (up_ren (up_ren rho)) (ren_tm shift (ren_tm shift t)) =
  ren_tm shift (ren_tm shift (ren_tm rho t)).
Proof.
  intros rho t.
  rewrite (tm_ren_shift_up (up_ren rho) (ren_tm shift t)).
  rewrite (tm_ren_shift_up rho t). reflexivity.
Qed.

Lemma tm_ren_subst : forall (a : tm) (rho : fin -> fin) (sigma : fin -> tm),
  ren_tm rho (subst_tm sigma a) =
  subst_tm (fun k => ren_tm rho (sigma k)) a.
Proof.
  induction a; simpl; intros; try reflexivity.
  - (* tAbs *) f_equal. rewrite (IHa (up_ren rho) (up_tm_tm sigma)).
    apply tm_subst_ext. intro k; destruct k as [|j]; simpl.
    + reflexivity.
    + apply tm_ren_shift_up.
  - (* tApp *) f_equal; [exact (IHa1 rho sigma) | exact (IHa2 rho sigma)].
  - (* tPi *) f_equal.
    + exact (IHa1 rho sigma).
    + rewrite (IHa2 (up_ren rho) (up_tm_tm sigma)). apply tm_subst_ext.
      intro k; destruct k as [|j]; simpl.
      * reflexivity.
      * apply tm_ren_shift_up.
  - (* tAbsurd *) f_equal; exact (IHa rho sigma).
  - (* tEq *) f_equal; [exact (IHa1 rho sigma) | exact (IHa2 rho sigma)].
  - (* tJ *) f_equal; [exact (IHa1 rho sigma) | exact (IHa2 rho sigma)].
  - (* tSig *) f_equal.
    + exact (IHa1 rho sigma).
    + rewrite (IHa2 (up_ren rho) (up_tm_tm sigma)). apply tm_subst_ext.
      intro k; destruct k as [|j]; simpl.
      * reflexivity.
      * apply tm_ren_shift_up.
  - (* tPack *) f_equal; [exact (IHa1 rho sigma) | exact (IHa2 rho sigma)].
  - (* tLet *) f_equal.
    + exact (IHa1 rho sigma).
    + rewrite (IHa2 (up_ren (up_ren rho)) (up_tm_tm (up_tm_tm sigma))).
      apply tm_subst_ext. intro k; destruct k as [|[|j]]; simpl.
      * reflexivity.
      * reflexivity.
      * apply tm_ren_shift_up2.
  - (* tSuc *) f_equal; exact (IHa rho sigma).
  - (* tInd *) f_equal.
    + exact (IHa1 rho sigma).
    + rewrite (IHa2 (up_ren (up_ren rho)) (up_tm_tm (up_tm_tm sigma))).
      apply tm_subst_ext. intro k; destruct k as [|[|j]]; simpl.
      * reflexivity.
      * reflexivity.
      * apply tm_ren_shift_up2.
    + exact (IHa3 rho sigma).
  - (* tSeq *) f_equal; [exact (IHa1 rho sigma) | exact (IHa2 rho sigma)].
Qed.

Lemma tm_subst_ren : forall (a : tm) (rho : fin -> fin) (sigma : fin -> tm),
  subst_tm sigma (ren_tm rho a) =
  subst_tm (fun k => sigma (rho k)) a.
Proof.
  induction a; simpl; intros; try reflexivity.
  - (* tAbs *) f_equal. rewrite (IHa (up_ren rho) (up_tm_tm sigma)).
    apply tm_subst_ext. intro k; destruct k as [|j]; simpl.
    + reflexivity.
    + repeat (unfold funcomp; simpl); reflexivity.
  - (* tApp *) f_equal; [exact (IHa1 rho sigma) | exact (IHa2 rho sigma)].
  - (* tPi *) f_equal.
    + exact (IHa1 rho sigma).
    + rewrite (IHa2 (up_ren rho) (up_tm_tm sigma)). apply tm_subst_ext.
      intro k; destruct k as [|j]; simpl.
      * reflexivity.
      * repeat (unfold funcomp; simpl); reflexivity.
  - (* tAbsurd *) f_equal; exact (IHa rho sigma).
  - (* tEq *) f_equal; [exact (IHa1 rho sigma) | exact (IHa2 rho sigma)].
  - (* tJ *) f_equal; [exact (IHa1 rho sigma) | exact (IHa2 rho sigma)].
  - (* tSig *) f_equal.
    + exact (IHa1 rho sigma).
    + rewrite (IHa2 (up_ren rho) (up_tm_tm sigma)). apply tm_subst_ext.
      intro k; destruct k as [|j]; simpl.
      * reflexivity.
      * repeat (unfold funcomp; simpl); reflexivity.
  - (* tPack *) f_equal; [exact (IHa1 rho sigma) | exact (IHa2 rho sigma)].
  - (* tLet *) f_equal.
    + exact (IHa1 rho sigma).
    + rewrite (IHa2 (up_ren (up_ren rho)) (up_tm_tm (up_tm_tm sigma))).
      apply tm_subst_ext. intro k; destruct k as [|[|j]]; simpl.
      * reflexivity.
      * reflexivity.
      * repeat (unfold funcomp; simpl); reflexivity.
  - (* tSuc *) f_equal; exact (IHa rho sigma).
  - (* tInd *) f_equal.
    + exact (IHa1 rho sigma).
    + rewrite (IHa2 (up_ren (up_ren rho)) (up_tm_tm (up_tm_tm sigma))).
      apply tm_subst_ext. intro k; destruct k as [|[|j]]; simpl.
      * reflexivity.
      * reflexivity.
      * repeat (unfold funcomp; simpl); reflexivity.
    + exact (IHa3 rho sigma).
  - (* tSeq *) f_equal; [exact (IHa1 rho sigma) | exact (IHa2 rho sigma)].
Qed.

(* Extension of a good renaming to one more context entry. *)
Lemma lgr_extend : forall (rho : fin -> fin) (G D : context) (l0 : T) (A : tm),
  lookup_good_renaming rho G D ->
  lookup_good_renaming (up_ren rho) ((l0, A) :: G) ((l0, A⟨rho⟩) :: D).
Proof.
  intros rho G D l0 A Hok i ll B Hlk. inversion Hlk; subst.
  - exists ll. split.
    + simpl. rewrite tm_ren_shift_up. apply here.
    + apply subset_refl.
  - destruct (Hok n ll A0 H4) as [l' [Hlk' Hsub]].
    exists l'. split.
    + simpl. rewrite tm_ren_shift_up. eapply there. exact Hlk'.
    + exact Hsub.
Qed.

(* Renaming of the App/Pack/Ind/Let/Seq conclusion types. *)
Lemma type_ren_cons : forall (B b : tm) (rho : fin -> fin),
  ren_tm rho (subst_tm (scons b ids) B) =
  subst_tm (scons (ren_tm rho b) ids) (ren_tm (up_ren rho) B).
Proof.
  intros B b rho. rewrite tm_ren_subst. rewrite tm_subst_ren.
  apply tm_subst_ext. intro k; destruct k as [|j];
    repeat (unfold funcomp; simpl); reflexivity.
Qed.

(* Renaming of the J conclusion type (two binders). *)
Lemma type_ren_j : forall (C p b : tm) (rho : fin -> fin),
  ren_tm rho (subst_tm (scons p (scons b ids)) C) =
  subst_tm (scons (ren_tm rho p) (scons (ren_tm rho b) ids))
    (ren_tm (up_ren (up_ren rho)) C).
Proof.
  intros C p b rho. rewrite tm_ren_subst. rewrite tm_subst_ren.
  apply tm_subst_ext. intro k; destruct k as [|[|j]];
    repeat (unfold funcomp; simpl); reflexivity.
Qed.

(* Renaming of the Ind branch type. *)
Definition s_ind : fin -> tm :=
  scons (tSuc (var_tm 0)) (fun k => var_tm (S k)).

Lemma ind_branch_ren : forall (A : tm) (rho : fin -> fin),
  ren_tm (up_ren (up_ren rho)) (ren_tm shift (A [s_ind])) =
  ren_tm shift ((ren_tm (up_ren rho) A) [s_ind]).
Proof.
  intros A rho.
  rewrite (tm_ren_shift_up (up_ren rho) (A [s_ind])).
  rewrite tm_ren_subst. rewrite tm_ren_subst.
  rewrite tm_subst_ren. rewrite tm_ren_subst.
  apply tm_subst_ext. intro k; destruct k as [|j]; unfold s_ind;
    repeat (unfold funcomp; simpl); reflexivity.
Qed.

(* Renaming of the Let branch type. *)
Definition s_let (l0 : T) : fin -> tm :=
  scons (tPack l0 (var_tm 1) (var_tm 0)) (fun k => var_tm (S (S k))).

Lemma let_branch_ren : forall (C : tm) (rho : fin -> fin) (l0 : T),
  ren_tm (up_ren (up_ren rho)) (C [s_let l0]) =
  (ren_tm (up_ren rho) C) [s_let l0].
Proof.
  intros C rho l0. rewrite tm_ren_subst. rewrite tm_subst_ren.
  apply tm_subst_ext. intro k; destruct k as [|j]; unfold s_let;
    repeat (unfold funcomp; simpl); reflexivity.
Qed.


(* Parallel reduction is preserved by renamings. *)
Lemma Par_ren : forall a b : tm, Par a b -> forall rho : fin -> fin,
  Par (a⟨rho⟩) (b⟨rho⟩).
Proof.
  intros a b H. induction H; intros rho.
  - (* P_Var *) eapply P_Var.
  - (* P_Univ *) eapply P_Univ.
  - (* P_Pi *) simpl. eapply P_Pi; [eapply IHPar1 | eapply IHPar2].
  - (* P_Abs *) simpl. eapply P_Abs. eapply IHPar.
  - (* P_App *) simpl. eapply P_App; [eapply IHPar1 | eapply IHPar2].
  - (* P_AppAbs *) simpl. rewrite type_ren_cons.
    eapply P_AppAbs; [eapply IHPar1 | eapply IHPar2].
  - (* P_Void *) eapply P_Void.
  - (* P_Absurd *) simpl. eapply P_Absurd. eapply IHPar.
  - (* P_Refl *) eapply P_Refl.
  - (* P_Eq *) simpl. eapply P_Eq; [eapply IHPar1 | eapply IHPar2].
  - (* P_J *) simpl. eapply P_J; [eapply IHPar1 | eapply IHPar2].
  - (* P_JRefl *) simpl. eapply P_JRefl. eapply IHPar.
  - (* P_Sig *) simpl. eapply P_Sig; [eapply IHPar1 | eapply IHPar2].
  - (* P_Pack *) simpl. eapply P_Pack; [eapply IHPar1 | eapply IHPar2].
  - (* P_Let *) simpl. eapply P_Let; [eapply IHPar1 | eapply IHPar2].
  - (* P_LetPack *) simpl. rewrite type_ren_j.
    eapply P_LetPack; [eapply IHPar1 | eapply IHPar2 | eapply IHPar3].
  - (* P_Zero *) eapply P_Zero.
  - (* P_Suc *) simpl. eapply P_Suc. eapply IHPar.
  - (* P_Ind *) simpl. eapply P_Ind; [eapply IHPar1 | eapply IHPar2 | eapply IHPar3].
  - (* P_IndZero *) simpl. eapply P_IndZero. eapply IHPar.
  - (* P_IndSuc *) simpl. rewrite type_ren_j. simpl.
    eapply P_IndSuc; [eapply IHPar1 | eapply IHPar2 | eapply IHPar3].
  - (* P_Nat *) eapply P_Nat.
  - (* P_TT *) eapply P_TT.
  - (* P_Seq *) simpl. eapply P_Seq; [eapply IHPar1 | eapply IHPar2].
  - (* P_SeqTT *) simpl. eapply P_SeqTT. eapply IHPar.
  - (* P_Unit *) eapply P_Unit.
Qed.


Lemma elookup_lookup : forall (i : fin) (G : context) (l : T),
  elookup i (c2e G) l -> exists A, lookup i G l A.
Proof.
  intros i. induction i as [|k IH]; intros G l Hi.
  - destruct G as [| [l0 A0] G'].
    + unfold elookup in Hi; simpl in Hi; discriminate Hi.
    + unfold elookup in Hi; simpl in Hi.
      assert (l = l0) as E by congruence. subst l.
      exists (A0⟨↑⟩). apply here.
  - destruct G as [| [l0 A0] G'].
    + unfold elookup in Hi; simpl in Hi; discriminate Hi.
    + unfold elookup in Hi; simpl in Hi.
      destruct (IH G' l Hi) as [A Hlk]. exists (A⟨↑⟩). eapply there. exact Hlk.
Qed.

Lemma iok_ren_ok_c2e : forall (rho : fin -> fin) (G D : context),
  lookup_good_renaming rho G D -> iok_ren_ok rho (c2e G) (c2e D).
Proof.
  intros rho G D Hok i l Hi.
  destruct (elookup_lookup i G l Hi) as [A Hlk].
  destruct (Hok i l A Hlk) as [l' [Hlk' Hsub]].
  exists l'. split; [eapply lookup_c2e; exact Hlk' | exact Hsub].
Qed.

Lemma rtc_Par_ren : forall a b : tm, rtc Par a b -> forall rho : fin -> fin,
  rtc Par (a⟨rho⟩) (b⟨rho⟩).
Proof.
  intros a b H. induction H; intros rho.
  - apply rtc_refl.
  - eapply rtc_l.
    + apply Par_ren. exact H.
    + apply IHrtc.
Qed.

Lemma conv_ren : forall (G D : context) (rho : fin -> fin),
  lookup_good_renaming rho G D ->
  forall A B : tm, conv (c2e G) A B -> conv (c2e D) (A⟨rho⟩) (B⟨rho⟩).
Proof.
  intros G D rho Hok A B [l [c0 [c1 [H0 [H1 H2]]]]].
  exists l, (c0⟨rho⟩), (c1⟨rho⟩). split.
  - apply rtc_Par_ren. exact H0.
  - split.
    + apply rtc_Par_ren. exact H1.
    + apply (ieq_ren (c2e G) l c0 c1 H2 (c2e D) rho).
      apply iok_ren_ok_c2e. exact Hok.
Qed.



Lemma rtc_tVoid_eq : forall c : tm, rtc Par tVoid c -> c = tVoid.
Proof.
  intros c H. remember tVoid as t eqn:E. revert E.
  induction H; intros E; subst.
  - reflexivity.
  - inversion H. subst. apply IHrtc. reflexivity.
Qed.

Lemma conv_void : forall (Xi : econtext) (A : tm),
  conv Xi A tVoid -> rtc Par A tVoid.
Proof.
  intros Xi A [l [c0 [c1 [H0 [H1 H2]]]]].
  assert (c1 = tVoid) as E1 by (apply rtc_tVoid_eq; exact H1).
  subst c1.
  assert (c0 = tVoid) as E0 by (inversion H2; reflexivity).
  subst c0. exact H0.
Qed.

Lemma conv_void_sym : forall (Xi : econtext) (A : tm),
  conv Xi tVoid A -> rtc Par A tVoid.
Proof.
  intros Xi A [l [c0 [c1 [H0 [H1 H2]]]]].
  assert (c0 = tVoid) as E0 by (apply rtc_tVoid_eq; exact H0).
  subst c0.
  assert (c1 = tVoid) as E1 by (inversion H2; reflexivity).
  subst c1. exact H1.
Qed.

(* Head inversion for IEq. *)
Lemma IEq_void_inv : forall (Xi : econtext) (l : T) (A : tm),
  IEq Xi l tVoid A -> A = tVoid.
Proof. intros Xi l A H. inversion H. reflexivity. Qed.
Lemma IEq_univ_inv : forall (Xi : econtext) (l : T) (n : fin) (A : tm),
  IEq Xi l (tUniv n) A -> A = tUniv n.
Proof. intros Xi l n A H. inversion H. reflexivity. Qed.
Lemma IEq_nat_inv : forall (Xi : econtext) (l : T) (A : tm),
  IEq Xi l tNat A -> A = tNat.
Proof. intros Xi l A H. inversion H. reflexivity. Qed.
Lemma IEq_unit_inv : forall (Xi : econtext) (l : T) (A : tm),
  IEq Xi l tUnit A -> A = tUnit.
Proof. intros Xi l A H. inversion H. reflexivity. Qed.
Lemma IEq_pi_inv : forall (Xi : econtext) (l l0 : T) (C D A : tm),
  IEq Xi l (tPi l0 C D) A -> exists C' D', A = tPi l0 C' D'.
Proof. intros Xi l l0 C D A H. inversion H. eauto. Qed.
Lemma IEq_sig_inv : forall (Xi : econtext) (l l0 : T) (C D A : tm),
  IEq Xi l (tSig l0 C D) A -> exists C' D', A = tSig l0 C' D'.
Proof. intros Xi l l0 C D A H. inversion H. eauto. Qed.
Lemma IEq_eq_inv : forall (Xi : econtext) (l l0 : T) (a b A : tm),
  IEq Xi l (tEq l0 a b) A -> exists a' b', A = tEq l0 a' b'.
Proof. intros Xi l l0 a b A H. inversion H. eauto. Qed.

(* Head preservation for Par (single step and reflexive-transitive closure). *)
Definition hpi t := exists l A B, t = tPi l A B.
Definition huniv t := exists n, t = tUniv n.
Definition hnat t := t = tNat.
Definition hunit t := t = tUnit.
Definition hsig t := exists l A B, t = tSig l A B.
Definition heq t := exists l a b, t = tEq l a b.

Lemma Par_hpi a b : Par a b -> hpi a -> hpi b.
Proof. intros H [l [A [B E]]]; rewrite E in H; inversion H; repeat eexists; reflexivity. Qed.
Lemma Par_huniv a b : Par a b -> huniv a -> huniv b.
Proof. intros H [n E]; rewrite E in H; inversion H; repeat eexists; reflexivity. Qed.
Lemma Par_hnat a b : Par a b -> hnat a -> hnat b.
Proof. intros H E; rewrite E in H; inversion H; reflexivity. Qed.
Lemma Par_hunit a b : Par a b -> hunit a -> hunit b.
Proof. intros H E; rewrite E in H; inversion H; reflexivity. Qed.
Lemma Par_hsig a b : Par a b -> hsig a -> hsig b.
Proof. intros H [l [A [B E]]]; rewrite E in H; inversion H; repeat eexists; reflexivity. Qed.
Lemma Par_heq a b : Par a b -> heq a -> heq b.
Proof. intros H [l [x [y E]]]; rewrite E in H; inversion H; repeat eexists; reflexivity. Qed.

Lemma rtc_hpi a b : rtc Par a b -> hpi a -> hpi b.
Proof. intros H. induction H; intros Hp; [exact Hp | apply IHrtc, (Par_hpi _ _ H Hp)]. Qed.
Lemma rtc_huniv a b : rtc Par a b -> huniv a -> huniv b.
Proof. intros H. induction H; intros Hp; [exact Hp | apply IHrtc, (Par_huniv _ _ H Hp)]. Qed.
Lemma rtc_hnat a b : rtc Par a b -> hnat a -> hnat b.
Proof. intros H. induction H; intros Hp; [exact Hp | apply IHrtc, (Par_hnat _ _ H Hp)]. Qed.
Lemma rtc_hunit a b : rtc Par a b -> hunit a -> hunit b.
Proof. intros H. induction H; intros Hp; [exact Hp | apply IHrtc, (Par_hunit _ _ H Hp)]. Qed.
Lemma rtc_hsig a b : rtc Par a b -> hsig a -> hsig b.
Proof. intros H. induction H; intros Hp; [exact Hp | apply IHrtc, (Par_hsig _ _ H Hp)]. Qed.
Lemma rtc_heq a b : rtc Par a b -> heq a -> heq b.
Proof. intros H. induction H; intros Hp; [exact Hp | apply IHrtc, (Par_heq _ _ H Hp)]. Qed.

(* Conversion rigidity for rigid-head types. *)
Lemma rtc_tUniv_eq : forall (i : fin) (c : tm), rtc Par (tUniv i) c -> c = tUniv i.
Proof.
  intros i c H. remember (tUniv i) as t eqn:E. revert E.
  induction H; intros E; subst.
  - reflexivity.
  - inversion H. subst. apply IHrtc. reflexivity.
Qed.

Lemma conv_univ_rtc : forall (Xi : econtext) (i : fin) (A : tm),
  conv Xi (tUniv i) A -> rtc Par A (tUniv i).
Proof.
  intros Xi i A [l [c0 [c1 [H0 [H1 H2]]]]].
  assert (c0 = tUniv i) as E by (apply rtc_tUniv_eq; exact H0).
  subst c0.
  assert (c1 = tUniv i) as E by (exact (IEq_univ_inv Xi l i c1 H2)).
  subst c1. exact H1.
Qed.

Lemma rtc_tNat_eq : forall (c : tm), rtc Par tNat c -> c = tNat.
Proof.
  intros c H. remember tNat as t eqn:E. revert E.
  induction H; intros E; subst.
  - reflexivity.
  - inversion H. subst. apply IHrtc. reflexivity.
Qed.

Lemma conv_nat_rtc : forall (Xi : econtext) (A : tm),
  conv Xi tNat A -> rtc Par A tNat.
Proof.
  intros Xi A [l [c0 [c1 [H0 [H1 H2]]]]].
  assert (c0 = tNat) as E by (apply rtc_tNat_eq; exact H0).
  subst c0.
  assert (c1 = tNat) as E by (exact (IEq_nat_inv Xi l c1 H2)).
  subst c1. exact H1.
Qed.

Lemma rtc_tUnit_eq : forall (c : tm), rtc Par tUnit c -> c = tUnit.
Proof.
  intros c H. remember tUnit as t eqn:E. revert E.
  induction H; intros E; subst.
  - reflexivity.
  - inversion H. subst. apply IHrtc. reflexivity.
Qed.

Lemma conv_unit_rtc : forall (Xi : econtext) (A : tm),
  conv Xi tUnit A -> rtc Par A tUnit.
Proof.
  intros Xi A [l [c0 [c1 [H0 [H1 H2]]]]].
  assert (c0 = tUnit) as E by (apply rtc_tUnit_eq; exact H0).
  subst c0.
  assert (c1 = tUnit) as E by (exact (IEq_unit_inv Xi l c1 H2)).
  subst c1. exact H1.
Qed.



Definition hpi_at (l : T) (t : tm) : Prop := exists A B, t = tPi l A B.
Definition hsig_at (l : T) (t : tm) : Prop := exists A B, t = tSig l A B.
Definition heq_at (l : T) (t : tm) : Prop := exists a b, t = tEq l a b.

Lemma Par_hpi_at : forall (l : T) a b, Par a b -> hpi_at l a -> hpi_at l b.
Proof. intros l a b H [A [B E]]; rewrite E in H; inversion H; repeat eexists; reflexivity. Qed.
Lemma Par_hsig_at : forall (l : T) a b, Par a b -> hsig_at l a -> hsig_at l b.
Proof. intros l a b H [A [B E]]; rewrite E in H; inversion H; repeat eexists; reflexivity. Qed.
Lemma Par_heq_at : forall (l : T) a b, Par a b -> heq_at l a -> heq_at l b.
Proof. intros l a b H [x [y E]]; rewrite E in H; inversion H; repeat eexists; reflexivity. Qed.

Lemma rtc_hpi_at : forall (l : T) a b, rtc Par a b -> hpi_at l a -> hpi_at l b.
Proof. intros l a b H. induction H; intros Hp; [exact Hp | apply IHrtc, (Par_hpi_at _ _ _ H Hp)]. Qed.
Lemma rtc_hsig_at : forall (l : T) a b, rtc Par a b -> hsig_at l a -> hsig_at l b.
Proof. intros l a b H. induction H; intros Hp; [exact Hp | apply IHrtc, (Par_hsig_at _ _ _ H Hp)]. Qed.
Lemma rtc_heq_at : forall (l : T) a b, rtc Par a b -> heq_at l a -> heq_at l b.
Proof. intros l a b H. induction H; intros Hp; [exact Hp | apply IHrtc, (Par_heq_at _ _ _ H Hp)]. Qed.

Lemma conv_pi_rtc : forall (Xi : econtext) (l : T) (C D A : tm),
  conv Xi (tPi l C D) A -> exists C' D', rtc Par A (tPi l C' D').
Proof.
  intros Xi l C D A [m [c0 [c1 [H0 [H1 H2]]]]].
  assert (hpi_at l c0).
  { apply (rtc_hpi_at l (tPi l C D)); [exact H0 | repeat eexists; reflexivity]. }
  destruct H as [C0 [D0 E0]]. subst c0.
  destruct (IEq_pi_inv Xi m l C0 D0 c1 H2) as [C1 [D1 E1]]. subst c1.
  exists C1, D1. exact H1.
Qed.
Lemma conv_sig_rtc : forall (Xi : econtext) (l : T) (C D A : tm),
  conv Xi (tSig l C D) A -> exists C' D', rtc Par A (tSig l C' D').
Proof.
  intros Xi l C D A [m [c0 [c1 [H0 [H1 H2]]]]].
  assert (hsig_at l c0).
  { apply (rtc_hsig_at l (tSig l C D)); [exact H0 | repeat eexists; reflexivity]. }
  destruct H as [C0 [D0 E0]]. subst c0.
  destruct (IEq_sig_inv Xi m l C0 D0 c1 H2) as [C1 [D1 E1]]. subst c1.
  exists C1, D1. exact H1.
Qed.
Lemma conv_eq_rtc : forall (Xi : econtext) (l : T) (a b A : tm),
  conv Xi (tEq l a b) A -> exists a' b', rtc Par A (tEq l a' b').
Proof.
  intros Xi l a b A [m [c0 [c1 [H0 [H1 H2]]]]].
  assert (heq_at l c0).
  { apply (rtc_heq_at l (tEq l a b)); [exact H0 | repeat eexists; reflexivity]. }
  destruct H as [x [y E0]]. subst c0.
  destruct (IEq_eq_inv Xi m l x y c1 H2) as [x' [y' E1]]. subst c1.
  exists x', y'. exact H1.
Qed.

(* Transitivity of conversion through a rigid endpoint. *)
Lemma conv_trans_univ : forall (Xi : econtext) (i : fin) (A B : tm),
  conv Xi A (tUniv i) -> conv Xi (tUniv i) B -> conv Xi A B.
Proof.
  intros Xi i A B H1 H2.
  destruct H1 as [l [c0 [c1 H1]]].
  assert (HA : rtc Par A (tUniv i)) by
    (apply (conv_univ_rtc Xi i A); apply conv_sym; exists l, c0, c1; exact H1).
  assert (HB : rtc Par B (tUniv i)) by (apply (conv_univ_rtc Xi i B); exact H2).
  exists l, (tUniv i), (tUniv i). split; [exact HA | split; [exact HB | eapply I_Univ]].
Qed.
Lemma conv_trans_nat : forall (Xi : econtext) (A B : tm),
  conv Xi A tNat -> conv Xi tNat B -> conv Xi A B.
Proof.
  intros Xi A B H1 H2.
  destruct H1 as [l [c0 [c1 H1]]].
  assert (HA : rtc Par A tNat) by (apply (conv_nat_rtc Xi A); apply conv_sym; exists l, c0, c1; exact H1).
  assert (HB : rtc Par B tNat) by (apply (conv_nat_rtc Xi B); exact H2).
  exists l, tNat, tNat. split; [exact HA | split; [exact HB | eapply I_Nat]].
Qed.
Lemma conv_trans_unit : forall (Xi : econtext) (A B : tm),
  conv Xi A tUnit -> conv Xi tUnit B -> conv Xi A B.
Proof.
  intros Xi A B H1 H2.
  destruct H1 as [l [c0 [c1 H1]]].
  assert (HA : rtc Par A tUnit) by (apply (conv_unit_rtc Xi A); apply conv_sym; exists l, c0, c1; exact H1).
  assert (HB : rtc Par B tUnit) by (apply (conv_unit_rtc Xi B); exact H2).
  exists l, tUnit, tUnit. split; [exact HA | split; [exact HB | eapply I_Unit]].
Qed.
Lemma conv_trans_void : forall (Xi : econtext) (A B : tm),
  conv Xi A tVoid -> conv Xi tVoid B -> conv Xi A B.
Proof.
  intros Xi A B H1 H2.
  destruct H1 as [l [c0 [c1 H1]]].
  assert (HA : rtc Par A tVoid) by (apply (conv_void Xi A); exists l, c0, c1; exact H1).
  assert (HB : rtc Par B tVoid) by (apply (conv_void_sym Xi B); exact H2).
  exists l, tVoid, tVoid. split; [exact HA | split; [exact HB | eapply I_Void]].
Qed.



Lemma subst_up_shift : forall (t : tm) (tau : fin -> tm),
  subst_tm (up_tm_tm tau) (ren_tm shift t) = ren_tm shift (subst_tm tau t).
Proof.
  intros t tau. rewrite tm_subst_ren. rewrite tm_ren_subst.
  apply tm_subst_ext. intro k. simpl. repeat (unfold funcomp; simpl). reflexivity.
Qed.

Lemma subst_up2_shift2 : forall (t : tm) (tau : fin -> tm),
  subst_tm (up_tm_tm (up_tm_tm tau)) (ren_tm shift (ren_tm shift t)) =
  ren_tm shift (ren_tm shift (subst_tm tau t)).
Proof.
  intros t tau.
  rewrite (subst_up_shift (ren_tm shift t) (up_tm_tm tau)).
  rewrite (subst_up_shift t tau). reflexivity.
Qed.

Lemma tm_subst_subst : forall (a : tm) (sigma tau : fin -> tm),
  subst_tm tau (subst_tm sigma a) =
  subst_tm (fun k => subst_tm tau (sigma k)) a.
Proof.
  induction a; simpl; intros; try reflexivity.
  - (* tAbs *) f_equal. rewrite (IHa (up_tm_tm sigma) (up_tm_tm tau)).
    apply tm_subst_ext. intro k; destruct k as [|j]; simpl.
    + reflexivity.
    + apply subst_up_shift.
  - (* tApp *) f_equal; [exact (IHa1 sigma tau) | exact (IHa2 sigma tau)].
  - (* tPi *) f_equal.
    + exact (IHa1 sigma tau).
    + rewrite (IHa2 (up_tm_tm sigma) (up_tm_tm tau)). apply tm_subst_ext.
      intro k; destruct k as [|j]; simpl.
      * reflexivity.
      * apply subst_up_shift.
  - (* tAbsurd *) f_equal; exact (IHa sigma tau).
  - (* tEq *) f_equal; [exact (IHa1 sigma tau) | exact (IHa2 sigma tau)].
  - (* tJ *) f_equal; [exact (IHa1 sigma tau) | exact (IHa2 sigma tau)].
  - (* tSig *) f_equal.
    + exact (IHa1 sigma tau).
    + rewrite (IHa2 (up_tm_tm sigma) (up_tm_tm tau)). apply tm_subst_ext.
      intro k; destruct k as [|j]; simpl.
      * reflexivity.
      * apply subst_up_shift.
  - (* tPack *) f_equal; [exact (IHa1 sigma tau) | exact (IHa2 sigma tau)].
  - (* tLet *) f_equal.
    + exact (IHa1 sigma tau).
    + rewrite (IHa2 (up_tm_tm (up_tm_tm sigma)) (up_tm_tm (up_tm_tm tau))).
      apply tm_subst_ext. intro k; destruct k as [|[|j]]; simpl.
      * reflexivity.
      * reflexivity.
      * apply subst_up2_shift2.
  - (* tSuc *) f_equal; exact (IHa sigma tau).
  - (* tInd *) f_equal.
    + exact (IHa1 sigma tau).
    + rewrite (IHa2 (up_tm_tm (up_tm_tm sigma)) (up_tm_tm (up_tm_tm tau))).
      apply tm_subst_ext. intro k; destruct k as [|[|j]]; simpl.
      * reflexivity.
      * reflexivity.
      * apply subst_up2_shift2.
    + exact (IHa3 sigma tau).
  - (* tSeq *) f_equal; [exact (IHa1 sigma tau) | exact (IHa2 sigma tau)].
Qed.


(* Characterisations of conversion to rigid base types. *)
Lemma conv_void_iff : forall (Xi : econtext) (l : T) (A : tm),
  conv Xi A tVoid <-> rtc Par A tVoid.
Proof.
  intros Xi l A. split.
  - apply (conv_void Xi A).
  - intro H. exists l, tVoid, tVoid. split; [exact H | split; [apply rtc_refl | eapply I_Void]].
Qed.
Lemma conv_void_iff_sym : forall (Xi : econtext) (l : T) (A : tm),
  conv Xi tVoid A <-> rtc Par A tVoid.
Proof.
  intros Xi l A. split.
  - apply (conv_void_sym Xi A).
  - intro H. exists l, tVoid, tVoid. split; [apply rtc_refl | split; [exact H | eapply I_Void]].
Qed.
Lemma conv_nat_iff : forall (Xi : econtext) (l : T) (A : tm),
  conv Xi tNat A <-> rtc Par A tNat.
Proof.
  intros Xi l A. split.
  - apply (conv_nat_rtc Xi A).
  - intro H. exists l, tNat, tNat. split; [apply rtc_refl | split; [exact H | eapply I_Nat]].
Qed.
Lemma conv_nat_iff_sym : forall (Xi : econtext) (l : T) (A : tm),
  conv Xi A tNat <-> rtc Par A tNat.
Proof.
  intros Xi l A. split.
  - intro H. apply (conv_nat_rtc Xi A). apply conv_sym. exact H.
  - intro H. exists l, tNat, tNat. split; [exact H | split; [apply rtc_refl | eapply I_Nat]].
Qed.
Lemma conv_univ_iff : forall (Xi : econtext) (l : T) (i : fin) (A : tm),
  conv Xi (tUniv i) A <-> rtc Par A (tUniv i).
Proof.
  intros Xi l i A. split.
  - apply (conv_univ_rtc Xi i A).
  - intro H. exists l, (tUniv i), (tUniv i).
    split; [apply rtc_refl | split; [exact H | eapply I_Univ]].
Qed.
Lemma conv_univ_iff_sym : forall (Xi : econtext) (l : T) (i : fin) (A : tm),
  conv Xi A (tUniv i) <-> rtc Par A (tUniv i).
Proof.
  intros Xi l i A. split.
  - intro H. apply (conv_univ_rtc Xi i A). apply conv_sym. exact H.
  - intro H. exists l, (tUniv i), (tUniv i).
    split; [exact H | split; [apply rtc_refl | eapply I_Univ]].
Qed.
Lemma conv_unit_iff : forall (Xi : econtext) (l : T) (A : tm),
  conv Xi tUnit A <-> rtc Par A tUnit.
Proof.
  intros Xi l A. split.
  - apply (conv_unit_rtc Xi A).
  - intro H. exists l, tUnit, tUnit. split; [apply rtc_refl | split; [exact H | eapply I_Unit]].
Qed.
Lemma conv_unit_iff_sym : forall (Xi : econtext) (l : T) (A : tm),
  conv Xi A tUnit <-> rtc Par A tUnit.
Proof.
  intros Xi l A. split.
  - intro H. apply (conv_unit_rtc Xi A). apply conv_sym. exact H.
  - intro H. exists l, tUnit, tUnit. split; [exact H | split; [apply rtc_refl | eapply I_Unit]].
Qed.

(* Basic reduction/equality compatibility of conversion. *)
Lemma rtc_trans' : forall (a b c : tm),
  rtc Par a b -> rtc Par b c -> rtc Par a c.
Proof.
  intros a b c H1 H2. revert c H2. induction H1; intros c H2.
  - exact H2.
  - eapply rtc_l; [exact H | eauto].
Qed.

Lemma conv_of_ieq : forall (Xi : econtext) (l : T) (A B : tm),
  IEq Xi l A B -> conv Xi A B.
Proof.
  intros Xi l A B H. exists l, A, B. split; [apply rtc_refl | split; [apply rtc_refl | exact H]].
Qed.

Lemma conv_rtc_l : forall (Xi : econtext) (A C B : tm),
  rtc Par A C -> conv Xi C B -> conv Xi A B.
Proof.
  intros Xi A C B H1 H2. destruct H2 as [l [c0 [c1 [H0 [H1' H2']]]]].
  exists l, c0, c1. split; [| split; [exact H1' | exact H2']].
  eapply rtc_trans'; [exact H1 | exact H0].
Qed.

Lemma conv_rtc_r : forall (Xi : econtext) (A B C : tm),
  rtc Par B C -> conv Xi A C -> conv Xi A B.
Proof.
  intros Xi A B C H1 H2. destruct H2 as [l [c0 [c1 [H0 [H1' H2']]]]].
  exists l, c0, c1. split; [exact H0 | split; [| exact H2']].
  eapply rtc_trans'; [exact H1 | exact H1'].
Qed.



Lemma conv_intro : forall (Xi : econtext) (l : T) (A B c0 c1 : tm),
  rtc Par A c0 -> rtc Par B c1 -> IEq Xi l c0 c1 -> conv Xi A B.
Proof.
  intros Xi l A B c0 c1 H0 H1 H2. exists l, c0, c1. split; [exact H0 | split; [exact H1 | exact H2]].
Qed.

Lemma conv_par_both : forall (Xi : econtext) (A A' B B' : tm),
  rtc Par A A' -> rtc Par B B' -> conv Xi A' B' -> conv Xi A B.
Proof.
  intros Xi A A' B B' HA HB H.
  apply (conv_rtc_r Xi A B B' HB). apply (conv_rtc_l Xi A A' B' HA). exact H.
Qed.

Lemma conv_par_l : forall (Xi : econtext) (A A' B : tm),
  Par A A' -> conv Xi A' B -> conv Xi A B.
Proof.
  intros Xi A A' B H1 H2. apply (conv_rtc_l Xi A A' B).
  - eapply rtc_l; [exact H1 | apply rtc_refl].
  - exact H2.
Qed.

Lemma conv_par_r : forall (Xi : econtext) (A B B' : tm),
  Par B B' -> conv Xi A B' -> conv Xi A B.
Proof.
  intros Xi A B B' H1 H2. apply (conv_rtc_r Xi A B B').
  - eapply rtc_l; [exact H1 | apply rtc_refl].
  - exact H2.
Qed.

Lemma up_ids_pt : forall k : fin,
  (up_tm_tm (fun k => var_tm k)) k = var_tm k.
Proof.
  intro k; destruct k as [|j]; simpl; try reflexivity;
    repeat (unfold funcomp); simpl; reflexivity.
Qed.

Lemma up2_ids_pt : forall k : fin,
  (up_tm_tm (up_tm_tm (fun k => var_tm k))) k = var_tm k.
Proof.
  intro k; destruct k as [|[|j]]; simpl; try reflexivity;
    repeat (unfold funcomp); simpl; reflexivity.
Qed.

Lemma tm_subst_ids : forall t : tm, subst_tm (fun k => var_tm k) t = t.
Proof.
  apply tm_ind.
  - intros i. simpl. reflexivity.
  - intros l a IH. simpl. f_equal.
    rewrite (tm_subst_ext a (up_tm_tm (fun k => var_tm k)) (fun k => var_tm k) up_ids_pt).
    exact IH.
  - intros a1 IH1 l a2 IH2. simpl. f_equal; assumption.
  - intros l a1 IH1 a2 IH2. simpl. f_equal.
    + assumption.
    + rewrite (tm_subst_ext a2 (up_tm_tm (fun k => var_tm k)) (fun k => var_tm k) up_ids_pt). assumption.
  - intros n. simpl. reflexivity.
  - simpl. reflexivity.
  - intros a IH. simpl. f_equal; assumption.
  - intros l a1 a2 IH1 IH2. simpl. f_equal; assumption.
  - intros l a1 a2 IH1 IH2. simpl. f_equal; assumption.
  - simpl. reflexivity.
  - intros l a1 IH1 a2 IH2. simpl. f_equal.
    + assumption.
    + rewrite (tm_subst_ext a2 (up_tm_tm (fun k => var_tm k)) (fun k => var_tm k) up_ids_pt). assumption.
  - intros l a1 a2 IH1 IH2. simpl. f_equal; assumption.
  - intros l0 l1 a1 IH1 a2 IH2. simpl. f_equal.
    + assumption.
    + rewrite (tm_subst_ext a2 (up_tm_tm (up_tm_tm (fun k => var_tm k))) (fun k => var_tm k) up2_ids_pt). assumption.
  - simpl. reflexivity.
  - intros a IH. simpl. f_equal; assumption.
  - intros l a1 IH1 a2 IH2 a3 IH3. simpl. f_equal.
    + assumption.
    + rewrite (tm_subst_ext a2 (up_tm_tm (up_tm_tm (fun k => var_tm k))) (fun k => var_tm k) up2_ids_pt). assumption.
    + assumption.
  - simpl. reflexivity.
  - simpl. reflexivity.
  - intros l a1 a2 IH1 IH2. simpl. f_equal; assumption.
  - simpl. reflexivity.
Qed.

Lemma subst_cons_up : forall (t : tm) (sigma : fin -> tm) (b : tm),
  subst_tm (scons b ids) (subst_tm (up_tm_tm sigma) t) =
  subst_tm (scons b sigma) t.
Proof.
  intros t sigma b. rewrite tm_subst_subst.
  apply tm_subst_ext. intro k; destruct k as [|j]; simpl.
  - reflexivity.
  - rewrite tm_subst_ren.
    assert (He : forall x, (shift >> (scons b ids)) x = var_tm x).
    { intro x; repeat (unfold funcomp; simpl); reflexivity. }
    rewrite (tm_subst_ext (sigma j) (shift >> (scons b ids)) (fun k => var_tm k) He).
    apply tm_subst_ids.
Qed.

Lemma subst_cons_cons_up2 : forall (t : tm) (sigma : fin -> tm) (b a : tm),
  subst_tm (scons b (scons a ids)) (subst_tm (up_tm_tm (up_tm_tm sigma)) t) =
  subst_tm (scons b (scons a sigma)) t.
Proof.
  intros t sigma b a. rewrite tm_subst_subst.
  apply tm_subst_ext. intro k; destruct k as [|[|j]]; simpl.
  - reflexivity.
  - reflexivity.
  - rewrite tm_subst_ren. rewrite tm_subst_ren.
    assert (He : forall x, (shift >> (shift >> (scons b (scons a ids)))) x = var_tm x).
    { intro x; repeat (unfold funcomp; simpl); reflexivity. }
    rewrite (tm_subst_ext (sigma j) (shift >> (shift >> (scons b (scons a ids))))
                          (fun k => var_tm k) He).
    apply tm_subst_ids.
Qed.


Lemma up_par : forall (sigma sigma' : fin -> tm),
  (forall i, Par (sigma i) (sigma' i)) ->
  forall i, Par ((up_tm_tm sigma) i) ((up_tm_tm sigma') i).
Proof.
  intros sigma sigma' H i. destruct i as [|k]; simpl.
  - eapply P_Var.
  - apply (Par_ren (sigma k) (sigma' k) (H k) shift).
Qed.

Lemma up2_par : forall (sigma sigma' : fin -> tm),
  (forall i, Par (sigma i) (sigma' i)) ->
  forall i, Par ((up_tm_tm (up_tm_tm sigma)) i) ((up_tm_tm (up_tm_tm sigma')) i).
Proof.
  intros sigma sigma' H i. destruct i as [|[|k]]; simpl.
  - eapply P_Var.
  - eapply P_Var.
  - apply (Par_ren _ _ (Par_ren _ _ (H k) shift) shift).
Qed.

Lemma Par_subst : forall a a' : tm, Par a a' ->
  forall sigma sigma' : fin -> tm,
    (forall i, Par (sigma i) (sigma' i)) ->
    Par (a[sigma]) (a'[sigma']).
Proof.
  intros a a' H. induction H; intros sigma sigma' Hsig; simpl.
  - (* P_Var *) apply Hsig.
  - (* P_Univ *) eapply P_Univ.
  - (* P_Pi *) eapply P_Pi; [eapply IHPar1; exact Hsig | eapply IHPar2; apply up_par; exact Hsig].
  - (* P_Abs *) eapply P_Abs; eapply IHPar; apply up_par; exact Hsig.
  - (* P_App *) eapply P_App; [eapply IHPar1; exact Hsig | eapply IHPar2; exact Hsig].
  - (* P_AppAbs *) simpl. rewrite tm_subst_subst.
    assert (Hsub : subst_tm (fun k => subst_tm sigma' (scons b1 ids k)) a0 =
                  subst_tm (scons (subst_tm sigma' b1) sigma') a0).
    { apply tm_subst_ext. intro k; destruct k as [|j]; simpl; reflexivity. }
    rewrite Hsub. rewrite <- (subst_cons_up a0 sigma' (subst_tm sigma' b1)).
    eapply P_AppAbs.
    + eapply IHPar1. apply up_par. exact Hsig.
    + eapply IHPar2. exact Hsig.
  - (* P_Void *) eapply P_Void.
  - (* P_Absurd *) eapply P_Absurd; eapply IHPar; exact Hsig.
  - (* P_Refl *) eapply P_Refl.
  - (* P_Eq *) eapply P_Eq; [eapply IHPar1; exact Hsig | eapply IHPar2; exact Hsig].
  - (* P_J *) eapply P_J; [eapply IHPar1; exact Hsig | eapply IHPar2; exact Hsig].
  - (* P_JRefl *) eapply P_JRefl; eapply IHPar; exact Hsig.
  - (* P_Sig *) eapply P_Sig; [eapply IHPar1; exact Hsig | eapply IHPar2; apply up_par; exact Hsig].
  - (* P_Pack *) eapply P_Pack; [eapply IHPar1; exact Hsig | eapply IHPar2; exact Hsig].
  - (* P_Let *) eapply P_Let; [eapply IHPar1; exact Hsig | eapply IHPar2; apply up2_par; exact Hsig].
  - (* P_LetPack *) simpl. rewrite tm_subst_subst.
    assert (Hsub : subst_tm (fun k => subst_tm sigma' (scons b1 (scons a1 ids) k)) c1 =
                  subst_tm (scons (subst_tm sigma' b1) (scons (subst_tm sigma' a1) sigma')) c1).
    { apply tm_subst_ext. intro k; destruct k as [|[|j]]; simpl; reflexivity. }
    rewrite Hsub.
    rewrite <- (subst_cons_cons_up2 c1 sigma' (subst_tm sigma' b1) (subst_tm sigma' a1)).
    eapply P_LetPack.
    + eapply IHPar1. exact Hsig.
    + eapply IHPar2. exact Hsig.
    + eapply IHPar3. apply up2_par. exact Hsig.
  - (* P_Zero *) eapply P_Zero.
  - (* P_Suc *) eapply P_Suc; eapply IHPar; exact Hsig.
  - (* P_Ind *) eapply P_Ind;
      [eapply IHPar1; exact Hsig | eapply IHPar2; apply up2_par; exact Hsig | eapply IHPar3; exact Hsig].
  - (* P_IndZero *) eapply P_IndZero; eapply IHPar; exact Hsig.
  - (* P_IndSuc *) simpl. rewrite tm_subst_subst.
    assert (Hsub : subst_tm (fun k => subst_tm sigma' (scons (tInd ℓ a1 b1 c1) (scons c1 ids) k)) b1 =
                  subst_tm (scons (subst_tm sigma' (tInd ℓ a1 b1 c1)) (scons (subst_tm sigma' c1) sigma')) b1).
    { apply tm_subst_ext. intro k; destruct k as [|[|j]]; simpl; reflexivity. }
    rewrite Hsub.
    rewrite <- (subst_cons_cons_up2 b1 sigma' (subst_tm sigma' (tInd ℓ a1 b1 c1)) (subst_tm sigma' c1)).
    eapply P_IndSuc.
    + eapply IHPar1. exact Hsig.
    + eapply IHPar2. apply up2_par. exact Hsig.
    + eapply IHPar3. exact Hsig.
  - (* P_Nat *) eapply P_Nat.
  - (* P_TT *) eapply P_TT.
  - (* P_Seq *) eapply P_Seq; [eapply IHPar1; exact Hsig | eapply IHPar2; exact Hsig].
  - (* P_SeqTT *) eapply P_SeqTT; eapply IHPar; exact Hsig.
  - (* P_Unit *) eapply P_Unit.
Qed.


Fixpoint dev (a : tm) : tm :=
  match a with
  | var_tm i => var_tm i
  | tAbs l body => tAbs l (dev body)
  | tApp u l v =>
      match u with
      | tAbs l0 body =>
          if T_eqb l0 l then subst_tm (scons (dev v) ids) (dev body)
          else tApp (dev u) l (dev v)
      | _ => tApp (dev u) l (dev v)
      end
  | tPi l A B => tPi l (dev A) (dev B)
  | tUniv n => tUniv n
  | tVoid => tVoid
  | tAbsurd x => tAbsurd (dev x)
  | tEq l x y => tEq l (dev x) (dev y)
  | tJ lp t p =>
      match p with
      | tRefl => dev t
      | _ => tJ lp (dev t) (dev p)
      end
  | tRefl => tRefl
  | tSig l A B => tSig l (dev A) (dev B)
  | tPack l x y => tPack l (dev x) (dev y)
  | tLet l0 l1 x body =>
      match x with
      | tPack l0' a b =>
          if T_eqb l0' l0 then subst_tm (scons (dev b) (scons (dev a) ids)) (dev body)
          else tLet l0 l1 (dev x) (dev body)
      | _ => tLet l0 l1 (dev x) (dev body)
      end
  | tZero => tZero
  | tSuc x => tSuc (dev x)
  | tInd l a b c =>
      match c with
      | tZero => dev a
      | tSuc c0 => subst_tm (scons (tInd l (dev a) (dev b) (dev c0)) (scons (dev c0) ids)) (dev b)
      | _ => tInd l (dev a) (dev b) (dev c)
      end
  | tNat => tNat
  | tTT => tTT
  | tSeq l a b =>
      match a with
      | tTT => dev b
      | _ => tSeq l (dev a) (dev b)
      end
  | tUnit => tUnit
  end.

Lemma Par_dev : forall a : tm, Par a (dev a).
Proof.
  apply tm_ind.
  - intros i. simpl. eapply P_Var.
  - intros l a IH. simpl. eapply P_Abs. exact IH.
  - intros u IH1 l v IH2. simpl. destruct u; simpl in *;
      try (lazymatch goal with
           | |- Par (tApp (tAbs _ _) _ _) _ => fail
           | _ => eapply P_App; [exact IH1 | exact IH2]
           end).
    destruct (T_eqb t l) eqn:E.
    + destruct (T_eqdec t l) as [Heq|Hneq]; [| congruence].
      subst t. inversion IH1; subst. eapply P_AppAbs; [assumption | exact IH2].
    + eapply P_App; [exact IH1 | exact IH2].
  - intros l A IH1 B IH2. simpl. eapply P_Pi; [exact IH1 | exact IH2].
  - intros n. simpl. eapply P_Univ.
  - simpl. eapply P_Void.
  - intros x IH. simpl. eapply P_Absurd. exact IH.
  - intros l x IH1 y IH2. simpl. eapply P_Eq; [exact IH1 | exact IH2].
  - intros lp t IH1 p IH2. simpl. destruct p; simpl in *;
      first [ lazymatch goal with
              | |- Par (tJ _ _ tRefl) _ => eapply P_JRefl; exact IH1
              end
            | eapply P_J; [exact IH1 | exact IH2] ].
  - simpl. eapply P_Refl.
  - intros l A IH1 B IH2. simpl. eapply P_Sig; [exact IH1 | exact IH2].
  - intros l x IH1 y IH2. simpl. eapply P_Pack; [exact IH1 | exact IH2].
  - intros l0 l1 x IH1 body IH2. simpl. destruct x; simpl in *;
      try (lazymatch goal with
           | |- Par (tLet _ _ (tPack _ _ _) _) _ => fail
           | _ => eapply P_Let; [exact IH1 | exact IH2]
           end).
    destruct (T_eqb t l0) eqn:E.
    + destruct (T_eqdec t l0) as [Heq|Hneq]; [| congruence].
      subst t. inversion IH1; subst. eapply P_LetPack; [assumption | assumption | exact IH2].
    + eapply P_Let; [exact IH1 | exact IH2].
  - simpl. eapply P_Zero.
  - intros x IH. simpl. eapply P_Suc. exact IH.
  - intros l a IH1 b IH2 c IH3. simpl. destruct c; simpl in *;
      first [ lazymatch goal with
              | |- Par (tInd _ _ _ tZero) _ => eapply P_IndZero; exact IH1
              | |- Par (tInd _ _ _ (tSuc _)) _ =>
                  inversion IH3; subst; eapply P_IndSuc; [exact IH1 | exact IH2 | assumption]
              end
            | eapply P_Ind; [exact IH1 | exact IH2 | exact IH3] ].
  - simpl. eapply P_Nat.
  - simpl. eapply P_TT.
  - intros l a IH1 b IH2. simpl. destruct a; simpl in *;
      first [ lazymatch goal with
              | |- Par (tSeq _ tTT _) _ => eapply P_SeqTT; exact IH2
              end
            | eapply P_Seq; [exact IH1 | exact IH2] ].
  - simpl. eapply P_Unit.
Qed.


Lemma T_eqb_refl : forall a : T, T_eqb a a = true.
Proof.
  intro a. destruct (T_eqdec a a) as [H|H].
  - reflexivity.
  - exfalso. apply H. reflexivity.
Qed.

Lemma dev_app_abs : forall (l0 : T) (body : tm) (l : T) (v : tm),
  dev (tApp (tAbs l0 body) l v) =
  if T_eqb l0 l then subst_tm (scons (dev v) ids) (dev body)
  else tApp (tAbs l0 (dev body)) l (dev v).
Proof. intros; simpl; reflexivity. Qed.

Lemma dev_let_pack : forall (l0 l1 l0' : T) (a b body : tm),
  dev (tLet l0 l1 (tPack l0' a b) body) =
  if T_eqb l0' l0 then subst_tm (scons (dev b) (scons (dev a) ids)) (dev body)
  else tLet l0 l1 (tPack l0' (dev a) (dev b)) (dev body).
Proof. intros; simpl; reflexivity. Qed.

Lemma dev_ind_zero : forall (l : T) (a b : tm),
  dev (tInd l a b tZero) = dev a.
Proof. intros; simpl; reflexivity. Qed.

Lemma dev_ind_suc : forall (l : T) (a b c : tm),
  dev (tInd l a b (tSuc c)) =
  subst_tm (scons (tInd l (dev a) (dev b) (dev c)) (scons (dev c) ids)) (dev b).
Proof. intros; simpl; reflexivity. Qed.

Lemma dev_j_refl : forall (lp : T) (t : tm),
  dev (tJ lp t tRefl) = dev t.
Proof. intros; simpl; reflexivity. Qed.

Lemma dev_seq_tt : forall (l : T) (b : tm),
  dev (tSeq l tTT b) = dev b.
Proof. intros; simpl; reflexivity. Qed.

Lemma Par_dev_red : forall a b : tm, Par a b -> Par b (dev a).
Proof.
  intros a b H. induction H.
  - (* P_Var *) simpl. eapply P_Var.
  - (* P_Univ *) simpl. eapply P_Univ.
  - (* P_Pi *) simpl. eapply P_Pi; [eassumption | eassumption].
  - (* P_Abs *) simpl. eapply P_Abs; eassumption.
  - (* P_App *) simpl. inversion H; subst; simpl in *;
      try (eapply P_App; [eassumption | eassumption]).
    match type of IHPar1 with
    | Par (tAbs ?L _) _ =>
        destruct (T_eqb L ℓ0) eqn:E;
        [ destruct (T_eqdec L ℓ0) as [Heq|Hneq]; [| congruence];
          rewrite Heq in IHPar1; rewrite Heq; inversion IHPar1; subst;
          eapply P_AppAbs; [eassumption | eassumption]
        | eapply P_App; [eassumption | eassumption] ]
    end.
  - (* P_AppAbs *) simpl. rewrite T_eqb_refl. simpl.
    eapply Par_subst.
    + eassumption.
    + intro i; destruct i as [|k]; simpl.
      * eassumption.
      * eapply P_Var.
  - (* P_Void *) simpl. eapply P_Void.
  - (* P_Absurd *) simpl. eapply P_Absurd; eassumption.
  - (* P_Refl *) simpl. eapply P_Refl.
  - (* P_Eq *) simpl. eapply P_Eq; [eassumption | eassumption].
  - (* P_J *) simpl. inversion H0; subst; simpl in *;
      try (eapply P_J; [eassumption | eassumption]).
    eapply P_JRefl; eassumption.
  - (* P_JRefl *) simpl. eassumption.
  - (* P_Sig *) simpl. eapply P_Sig; [eassumption | eassumption].
  - (* P_Pack *) simpl. eapply P_Pack; [eassumption | eassumption].
  - (* P_Let *) simpl. inversion H; subst; simpl in *;
      try (eapply P_Let; [eassumption | eassumption]).
    match type of IHPar1 with
    | Par (tPack ?L _ _) _ =>
        destruct (T_eqb L ℓ0) eqn:E;
        [ destruct (T_eqdec L ℓ0) as [Heq|Hneq]; [| congruence];
          rewrite Heq in IHPar1; rewrite Heq; inversion IHPar1; subst;
          eapply P_LetPack; [eassumption | eassumption | eassumption]
        | eapply P_Let; [eassumption | eassumption] ]
    end.
  - (* P_LetPack *) simpl. rewrite T_eqb_refl. simpl.
    eapply Par_subst.
    + eassumption.
    + intro i; destruct i as [|[|k]]; simpl.
      * eassumption.
      * eassumption.
      * eapply P_Var.
  - (* P_Zero *) simpl. eapply P_Zero.
  - (* P_Suc *) simpl. eapply P_Suc; eassumption.
  - (* P_Ind *) simpl. inversion H1; subst; simpl in *;
      try (eapply P_Ind; [eassumption | eassumption | eassumption]).
    + eapply P_IndZero; eassumption.
    + inversion IHPar3; subst.
      eapply P_IndSuc; [eassumption | eassumption | eassumption].
  - (* P_IndZero *) simpl. eassumption.
  - (* P_IndSuc *) simpl.
    eapply Par_subst.
    + eassumption.
    + intro i; destruct i as [|[|k]]; simpl.
      * eapply P_Ind; [eassumption | eassumption | eassumption].
      * eassumption.
      * eapply P_Var.
  - (* P_Nat *) simpl. eapply P_Nat.
  - (* P_TT *) simpl. eapply P_TT.
  - (* P_Seq *) simpl. inversion H; subst; simpl in *;
      try (eapply P_Seq; [eassumption | eassumption]).
    eapply P_SeqTT; eassumption.
  - (* P_SeqTT *) simpl. eassumption.
  - (* P_Unit *) simpl. eapply P_Unit.
Qed.


Lemma Par_confluent : forall (a b c : tm),
  Par a b -> Par a c -> exists d, Par b d /\ Par c d.
Proof.
  intros a b c Hb Hc. exists (dev a). split;
    eapply Par_dev_red; eassumption.
Qed.

Lemma Par_strip : forall (a c : tm), rtc Par a c ->
  forall b, Par a b -> exists d, rtc Par b d /\ rtc Par c d.
Proof.
  intros a c H. induction H as [x | x y z Hxy Hrest IH]; intros b Hb.
  - exists b. split; [apply rtc_refl |].
    eapply rtc_l; [exact Hb | apply rtc_refl].
  - destruct (Par_confluent x y b Hxy Hb) as [e [Hye Hbe]].
    destruct (IH e Hye) as [d [Hed Hzd]].
    exists d. split; [| exact Hzd].
    eapply rtc_l; [exact Hbe | exact Hed].
Qed.

Lemma Par_rtc_confluent : forall (a b c : tm),
  rtc Par a b -> rtc Par a c -> exists d, rtc Par b d /\ rtc Par c d.
Proof.
  intros a b c Hb. revert c.
  induction Hb as [a | a y b Hxy Hrest IH]; intros c Hc.
  - exists c. split; [exact Hc | apply rtc_refl].
  - destruct (Par_strip a c Hc y Hxy) as [e [Hye Hce]].
    destruct (IH e Hye) as [d [Hbd Hed]].
    exists d. split; [exact Hbd |].
    eapply rtc_trans'; [exact Hce | exact Hed].
Qed.


Lemma gieq_to_ieq : forall (Xi : econtext) (l l0 : T) (A B : tm),
  GIEq Xi l l0 A B -> l0 ⊆ l -> IEq Xi l A B.
Proof.
  intros Xi l l0 A B H Hs. inversion H; subst.
  - assumption.
  - match goal with Hn : ~ (_ ⊆ _) |- _ => exfalso; apply Hn; exact Hs end.
Qed.

Lemma gieq_var_refl0 : forall (D : econtext) (l l0 : T),
  GIEq (l0 :: D) l l0 (var_tm 0) (var_tm 0).
Proof.
  intros D l l0. destruct (T_eqdec (l0 ∩ l) l0) as [Hs|Hn].
  - apply GI_Dist; [exact Hs | eapply I_Var; [simpl; reflexivity | exact Hs]].
  - apply GI_InDist; exact Hn.
Qed.

Lemma pt_extend1 : forall (Xi D : econtext) (l0 l : T) (sigma tau : fin -> tm),
  (forall i lk, elookup i Xi lk -> GIEq D l lk (sigma i) (tau i)) ->
  forall i lk, elookup i (l0 :: Xi) lk ->
    GIEq (l0 :: D) l lk ((up_tm_tm sigma) i) ((up_tm_tm tau) i).
Proof.
  intros Xi D l0 l sigma tau Hpt i lk Hlk.
  destruct i as [|k].
  - unfold elookup in Hlk; simpl in Hlk. injection Hlk as ?; subst lk.
    unfold up_tm_tm; simpl. apply gieq_var_refl0.
  - unfold elookup in Hlk; simpl in Hlk.
    unfold up_tm_tm; simpl.
    eapply gieq_ren; [apply Hpt; exact Hlk | apply iok_ren_ok_shift].
Qed.

Lemma pt_extend2 : forall (Xi D : econtext) (l1 l0 l : T) (sigma tau : fin -> tm),
  (forall i lk, elookup i Xi lk -> GIEq D l lk (sigma i) (tau i)) ->
  forall i lk, elookup i (l1 :: l0 :: Xi) lk ->
    GIEq (l1 :: l0 :: D) l lk
      ((up_tm_tm (up_tm_tm sigma)) i) ((up_tm_tm (up_tm_tm tau)) i).
Proof.
  intros Xi D l1 l0 l sigma tau Hpt i lk Hlk.
  destruct i as [| [|k]].
  - unfold elookup in Hlk; simpl in Hlk. injection Hlk as ?; subst lk.
    unfold up_tm_tm; simpl. apply gieq_var_refl0.
  - unfold elookup in Hlk; simpl in Hlk. injection Hlk as ?; subst lk.
    unfold up_tm_tm; simpl.
    eapply gieq_ren; [apply gieq_var_refl0 | apply iok_ren_ok_shift].
  - unfold elookup in Hlk; simpl in Hlk.
    unfold up_tm_tm; simpl.
    eapply gieq_ren.
    + eapply gieq_ren; [apply Hpt; exact Hlk | apply iok_ren_ok_shift].
    + apply iok_ren_ok_shift.
Qed.

Definition IEq2P (Xi : econtext) (l : T) (a b : tm) (H : IEq Xi l a b) : Prop :=
  forall (D : econtext) (sigma tau : fin -> tm),
    (forall i lk, elookup i Xi lk -> GIEq D l lk (sigma i) (tau i)) ->
    IEq D l (a[sigma]) (b[tau]).
Definition GIEq2P (Xi : econtext) (l l0 : T) (a b : tm) (H : GIEq Xi l l0 a b) : Prop :=
  forall (D : econtext) (sigma tau : fin -> tm),
    (forall i lk, elookup i Xi lk -> GIEq D l lk (sigma i) (tau i)) ->
    GIEq D l l0 (a[sigma]) (b[tau]).

Lemma ieq_gieq_subst2 : forall (Xi : econtext) (l : T),
  (forall (a b : tm) (H : IEq Xi l a b), IEq2P Xi l a b H) /\
  (forall (l0 : T) (a b : tm) (H : GIEq Xi l l0 a b), GIEq2P Xi l l0 a b H).
Proof.
  intros Xi l. apply (IEq_mutual IEq2P GIEq2P).
  - (* I_Var *) intros Xi' l' i l0 e e0.
    unfold IEq2P, GIEq2P in *. intros D sigma tau Hpt.
    eapply gieq_to_ieq; [apply Hpt; exact e | exact e0].
  - (* I_Univ *) intros; unfold IEq2P, GIEq2P in *; intros D sigma tau Hpt; eapply I_Univ.
  - (* I_Pi *) intros; unfold IEq2P, GIEq2P in *; intros D sigma tau Hpt;
      eapply I_Pi; eauto 10 using pt_extend1.
  - (* I_Abs *) intros; unfold IEq2P, GIEq2P in *; intros D sigma tau Hpt;
      eapply I_Abs; eauto 10 using pt_extend1.
  - (* I_App *) intros; unfold IEq2P, GIEq2P in *; intros D sigma tau Hpt;
      eapply I_App; eauto 10.
  - (* I_Void *) intros; unfold IEq2P, GIEq2P in *; intros D sigma tau Hpt; eapply I_Void.
  - (* I_Absurd *) intros; unfold IEq2P, GIEq2P in *; intros D sigma tau Hpt; eapply I_Absurd.
  - (* I_Refl *) intros; unfold IEq2P, GIEq2P in *; intros D sigma tau Hpt; eapply I_Refl.
  - (* I_Eq *) intros; unfold IEq2P, GIEq2P in *; intros D sigma tau Hpt;
      eapply I_Eq; eauto 10.
  - (* I_J *) intros; unfold IEq2P, GIEq2P in *; intros D sigma tau Hpt;
      eapply I_J; eauto 10.
  - (* I_Sig *) intros; unfold IEq2P, GIEq2P in *; intros D sigma tau Hpt;
      eapply I_Sig; eauto 10 using pt_extend1.
  - (* I_Pack *) intros; unfold IEq2P, GIEq2P in *; intros D sigma tau Hpt;
      eapply I_Pack; eauto 10.
  - (* I_Let *) intros; unfold IEq2P, GIEq2P in *; intros D sigma tau Hpt;
      eapply I_Let; eauto 10 using pt_extend2.
  - (* I_Zero *) intros; unfold IEq2P, GIEq2P in *; intros D sigma tau Hpt; eapply I_Zero.
  - (* I_Suc *) intros; unfold IEq2P, GIEq2P in *; intros D sigma tau Hpt;
      eapply I_Suc; eauto 10.
  - (* I_Ind *) intros; unfold IEq2P, GIEq2P in *; intros D sigma tau Hpt;
      eapply I_Ind; eauto 10 using pt_extend2.
  - (* I_Nat *) intros; unfold IEq2P, GIEq2P in *; intros D sigma tau Hpt; eapply I_Nat.
  - (* I_Unit *) intros; unfold IEq2P, GIEq2P in *; intros D sigma tau Hpt; eapply I_Unit.
  - (* I_TT *) intros; unfold IEq2P, GIEq2P in *; intros D sigma tau Hpt; eapply I_TT.
  - (* I_Seq *) intros; unfold IEq2P, GIEq2P in *; intros D sigma tau Hpt;
      eapply I_Seq; eauto 10.
  - (* GI_Dist *) intros; unfold IEq2P, GIEq2P in *; intros D sigma tau Hpt;
      eapply GI_Dist; eauto 10.
  - (* GI_InDist *) intros; unfold IEq2P, GIEq2P in *; intros D sigma tau Hpt;
      eapply GI_InDist; eauto.
Qed.


Lemma Par_refl : forall a : tm, Par a a.
Proof.
  apply tm_ind.
  - intros i. eapply P_Var.
  - intros l a IH. eapply P_Abs. exact IH.
  - intros a1 IH1 l a2 IH2. eapply P_App; eassumption.
  - intros l a1 IH1 a2 IH2. eapply P_Pi; eassumption.
  - intros n. eapply P_Univ.
  - eapply P_Void.
  - intros a IH. eapply P_Absurd. exact IH.
  - intros l a1 IH1 a2 IH2. eapply P_Eq; eassumption.
  - intros l a1 IH1 a2 IH2. eapply P_J; eassumption.
  - eapply P_Refl.
  - intros l a1 IH1 a2 IH2. eapply P_Sig; eassumption.
  - intros l a1 IH1 a2 IH2. eapply P_Pack; eassumption.
  - intros l0 l1 a1 IH1 a2 IH2. eapply P_Let; eassumption.
  - eapply P_Zero.
  - intros a IH. eapply P_Suc. exact IH.
  - intros l a1 IH1 a2 IH2 a3 IH3. eapply P_Ind; eassumption.
  - eapply P_Nat.
  - eapply P_TT.
  - intros l a1 IH1 a2 IH2. eapply P_Seq; eassumption.
  - eapply P_Unit.
Qed.

Lemma rtc_Par1 : forall (f : tm -> tm),
  (forall a a', Par a a' -> Par (f a) (f a')) ->
  forall a a', rtc Par a a' -> rtc Par (f a) (f a').
Proof.
  intros f step a a' H. induction H as [x | x y z Hxy Hrest IH].
  - apply rtc_refl.
  - eapply rtc_l; [apply step; exact Hxy | exact IH].
Qed.

Lemma rtc_Par2 : forall (f : tm -> tm -> tm),
  (forall a a' b b', Par a a' -> Par b b' -> Par (f a b) (f a' b')) ->
  forall a a' b b', rtc Par a a' -> rtc Par b b' ->
    rtc Par (f a b) (f a' b').
Proof.
  intros f step a a' b b' Ha Hb. revert b b' Hb.
  induction Ha as [x | x y z Hxy Hrest IH]; intros b b' Hb.
  - induction Hb as [u | u v w Huv Hvw IHb].
    + apply rtc_refl.
    + eapply rtc_l.
      * apply step; [apply Par_refl | exact Huv].
      * apply IHb.
  - eapply rtc_l.
    + apply step; [exact Hxy | apply Par_refl].
    + apply IH. exact Hb.
Qed.

Lemma rtc_Par3 : forall (f : tm -> tm -> tm -> tm),
  (forall a a' b b' c c',
      Par a a' -> Par b b' -> Par c c' -> Par (f a b c) (f a' b' c')) ->
  forall a a' b b' c c',
    rtc Par a a' -> rtc Par b b' -> rtc Par c c' ->
    rtc Par (f a b c) (f a' b' c').
Proof.
  intros f step a a' b b' c c' Ha Hb Hc. revert b b' c c' Hb Hc.
  induction Ha as [x | x y z Hxy Hrest IH]; intros b b' c c' Hb Hc.
  - revert c c' Hc.
    induction Hb as [u | u v w Huv Hvw IHb]; intros c c' Hc.
    + induction Hc as [p | p q r Hpq Hqr IHc].
      * apply rtc_refl.
      * eapply rtc_l.
        -- apply step; [apply Par_refl | apply Par_refl | exact Hpq].
        -- apply IHc.
    + eapply rtc_l.
      * apply step; [apply Par_refl | exact Huv | apply Par_refl].
      * apply IHb. exact Hc.
  - eapply rtc_l.
    + apply step; [exact Hxy | apply Par_refl | apply Par_refl].
    + apply IH; [exact Hb | exact Hc].
Qed.

Lemma gieq_var_self : forall (Xi : econtext) (l lk : T) (i : fin),
  elookup i Xi lk -> GIEq Xi l lk (var_tm i) (var_tm i).
Proof.
  intros Xi l lk i Hlk.
  destruct (T_eqdec (lk ∩ l) lk) as [Hs|Hn].
  - apply GI_Dist; [exact Hs | eapply I_Var; [exact Hlk | exact Hs]].
  - apply GI_InDist; exact Hn.
Qed.

Lemma rtc_up : forall (sigma sigma' : fin -> tm),
  (forall i, rtc Par (sigma i) (sigma' i)) ->
  forall i, rtc Par ((up_tm_tm sigma) i) ((up_tm_tm sigma') i).
Proof.
  intros sigma sigma' H i. destruct i as [|k]; simpl.
  - apply rtc_refl.
  - eapply rtc_Par_ren. apply H.
Qed.

Lemma rtc_up2 : forall (sigma sigma' : fin -> tm),
  (forall i, rtc Par (sigma i) (sigma' i)) ->
  forall i, rtc Par ((up_tm_tm (up_tm_tm sigma)) i)
                  ((up_tm_tm (up_tm_tm sigma')) i).
Proof.
  intros sigma sigma' H i. destruct i as [|[|k]]; simpl.
  - apply rtc_refl.
  - apply rtc_refl.
  - eapply rtc_Par_ren. eapply rtc_Par_ren. apply H.
Qed.

Lemma rtc_subst_same : forall (a a' : tm), rtc Par a a' ->
  forall sigma : fin -> tm, rtc Par (a[sigma]) (a'[sigma]).
Proof.
  intros a a' H. induction H as [x | x y z Hxy Hrest IH]; intro sigma.
  - apply rtc_refl.
  - eapply rtc_l.
    + eapply Par_subst; [exact Hxy | intro i; apply Par_refl].
    + apply IH.
Qed.

Lemma rtc_subst_pointwise : forall (a : tm) (sigma sigma' : fin -> tm),
  (forall i, rtc Par (sigma i) (sigma' i)) ->
  rtc Par (a[sigma]) (a[sigma']).
Proof.
  apply (tm_ind (fun a => forall (sigma sigma' : fin -> tm),
    (forall i, rtc Par (sigma i) (sigma' i)) ->
    rtc Par (a[sigma]) (a[sigma']))).
  - intros i sigma sigma' H. simpl. apply H.
  - intros l a IH sigma sigma' H. simpl.
    eapply (rtc_Par1 (fun x => tAbs l x)).
    + intros x y Hxy. eapply P_Abs. exact Hxy.
    + apply IH. apply rtc_up. exact H.
  - intros a1 IH1 l a2 IH2 sigma sigma' H. simpl.
    eapply (rtc_Par2 (fun x y => tApp x l y)).
    + intros x x' y y' Hx Hy. eapply P_App; eassumption.
    + apply IH1. exact H.
    + apply IH2. exact H.
  - intros l a1 IH1 a2 IH2 sigma sigma' H. simpl.
    eapply (rtc_Par2 (fun x y => tPi l x y)).
    + intros x x' y y' Hx Hy. eapply P_Pi; eassumption.
    + apply IH1. exact H.
    + apply IH2. apply rtc_up. exact H.
  - intros n sigma sigma' H. simpl. apply rtc_refl.
  - intros sigma sigma' H. simpl. apply rtc_refl.
  - intros a IH sigma sigma' H. simpl.
    eapply (rtc_Par1 (fun x => tAbsurd x)).
    + intros x y Hxy. eapply P_Absurd. exact Hxy.
    + apply IH. exact H.
  - intros l a1 IH1 a2 IH2 sigma sigma' H. simpl.
    eapply (rtc_Par2 (fun x y => tEq l x y)).
    + intros x x' y y' Hx Hy. eapply P_Eq; eassumption.
    + apply IH1. exact H.
    + apply IH2. exact H.
  - intros l a1 IH1 a2 IH2 sigma sigma' H. simpl.
    eapply (rtc_Par2 (fun x y => tJ l x y)).
    + intros x x' y y' Hx Hy. eapply P_J; eassumption.
    + apply IH1. exact H.
    + apply IH2. exact H.
  - intros sigma sigma' H. simpl. apply rtc_refl.
  - intros l a1 IH1 a2 IH2 sigma sigma' H. simpl.
    eapply (rtc_Par2 (fun x y => tSig l x y)).
    + intros x x' y y' Hx Hy. eapply P_Sig; eassumption.
    + apply IH1. exact H.
    + apply IH2. apply rtc_up. exact H.
  - intros l a1 IH1 a2 IH2 sigma sigma' H. simpl.
    eapply (rtc_Par2 (fun x y => tPack l x y)).
    + intros x x' y y' Hx Hy. eapply P_Pack; eassumption.
    + apply IH1. exact H.
    + apply IH2. exact H.
  - intros l0 l1 a1 IH1 a2 IH2 sigma sigma' H. simpl.
    eapply (rtc_Par2 (fun x y => tLet l0 l1 x y)).
    + intros x x' y y' Hx Hy. eapply P_Let; eassumption.
    + apply IH1. exact H.
    + apply IH2. apply rtc_up2. exact H.
  - intros sigma sigma' H. simpl. apply rtc_refl.
  - intros a IH sigma sigma' H. simpl.
    eapply (rtc_Par1 (fun x => tSuc x)).
    + intros x y Hxy. eapply P_Suc. exact Hxy.
    + apply IH. exact H.
  - intros l a1 IH1 a2 IH2 a3 IH3 sigma sigma' H. simpl.
    eapply (rtc_Par3 (fun x y z => tInd l x y z)).
    + intros x x' y y' z z' Hx Hy Hz. eapply P_Ind; eassumption.
    + apply IH1. exact H.
    + apply IH2. apply rtc_up2. exact H.
    + apply IH3. exact H.
  - intros sigma sigma' H. simpl. apply rtc_refl.
  - intros sigma sigma' H. simpl. apply rtc_refl.
  - intros l a1 IH1 a2 IH2 sigma sigma' H. simpl.
    eapply (rtc_Par2 (fun x y => tSeq l x y)).
    + intros x x' y y' Hx Hy. eapply P_Seq; eassumption.
    + apply IH1. exact H.
    + apply IH2. exact H.
  - intros sigma sigma' H. simpl. apply rtc_refl.
Qed.

Lemma rtc_subst : forall (a a' : tm), rtc Par a a' ->
  forall (sigma sigma' : fin -> tm),
    (forall i, rtc Par (sigma i) (sigma' i)) ->
    rtc Par (a[sigma]) (a'[sigma']).
Proof.
  intros a a' H. induction H as [x | x y z Hxy Hrest IH]; intros sigma sigma' Hpt.
  - apply rtc_subst_pointwise. exact Hpt.
  - eapply rtc_trans'.
    + eapply rtc_subst_same. eapply rtc_l; [exact Hxy | apply rtc_refl].
    + apply IH. exact Hpt.
Qed.


Lemma IEq_void_inv_r : forall (Xi : econtext) (l : T) (A : tm),
  IEq Xi l A tVoid -> A = tVoid.
Proof. intros Xi l A H. inversion H. reflexivity. Qed.


(* A parallel step out of an equation exposes parallel steps of the endpoints. *)
Lemma Par_eq_inv : forall (l : T) (x y c : tm),
  Par (tEq l x y) c -> exists x' y', c = tEq l x' y' /\ Par x x' /\ Par y y'.
Proof.
  intros l x y c H. inversion H; subst; repeat eexists; try split; eauto.
Qed.

Lemma rtc_Par_eq_inv : forall (l : T) (x y c : tm),
  rtc Par (tEq l x y) c ->
  exists x' y', c = tEq l x' y' /\ rtc Par x x' /\ rtc Par y y'.
Proof.
  intros l x y c H. remember (tEq l x y) as t eqn:E. revert x y E.
  induction H as [t | t u c Htu Huc IH]; intros x y E; subst.
  - exists x, y. split; [reflexivity | split; apply rtc_refl].
  - destruct (Par_eq_inv _ _ _ _ Htu) as [x1 [y1 [Ex [Hx Hy]]]]; subst u.
    destruct (IH x1 y1 eq_refl) as [x2 [y2 [Ec [Hx2 Hy2]]]]; subst c.
    exists x2, y2. split; [reflexivity | split].
    + eapply rtc_trans'; [eapply rtc_l; [exact Hx | apply rtc_refl] | exact Hx2].
    + eapply rtc_trans'; [eapply rtc_l; [exact Hy | apply rtc_refl] | exact Hy2].
Qed.

(* Conversion between reflexive equation types projects to conversion of the
   common endpoint with either endpoint of the other equation type. *)
Lemma conv_eq_equal_l : forall (Xi : econtext) (l l' : T) (x a b : tm),
  conv Xi (tEq l x x) (tEq l' a b) -> conv Xi x a.
Proof.
  intros Xi l l' x a b [m [c0 [c1 [H0 [H1 H2]]]]].
  destruct (rtc_Par_eq_inv _ _ _ _ H0) as [x1 [x2 [E0 [Hx1 Hx2]]]]; subst c0.
  destruct (rtc_Par_eq_inv _ _ _ _ H1) as [a1 [b1 [E1 [Ha Hb]]]]; subst c1.
  inversion H2; subst.
  exists m, x1, a1. split; [exact Hx1 | split; [exact Ha | assumption]].
Qed.

(* rtc Par to tVoid is *not* the same as syntactic equality with tVoid:
   beta-redexes whose body is tVoid reduce to tVoid.  This is the key fact
   that prevents the T_Conv case from being reduced to a syntactic tVoid
   premise. *)
Lemma Par_void_redex2 : forall (l : T) (b : tm),
  Par (tApp (tAbs l tVoid) l b) tVoid.
Proof.
  intros l b. eapply (P_AppAbs tVoid tVoid b b l);
    [eapply P_Void | apply Par_refl].
Qed.

Lemma rtc_void_nonunique : forall l : T, exists A : tm, rtc Par A tVoid /\ A <> tVoid.
Proof.
  intros l. exists (tApp (tAbs l tVoid) l tTT). split.
  - eapply rtc_l; [apply Par_void_redex2 | apply rtc_refl].
  - discriminate.
Qed.


(* ---------- concrete open-context Void inhabitants (obstruction facts) ---------- *)

(* A closed function Void -> Void exists.  Hence "no closed inhabitant of a
   Pi type whose codomain reduces to Void" is false in general; the argument
   of such a function is the only thing that can keep it from producing a
   closed Void inhabitant. *)
Lemma wt_void_to_void : forall (G : context) (l lvl : T),
  Wff G -> l ⊆ lvl ->
  Wt G lvl (tAbs l (var_tm 0)) (tPi l tVoid tVoid).
Proof.
  intros G l lvl HG Hsub.
  eapply (@T_Abs G lvl l lvl tVoid (var_tm 0) tVoid 0).
  - eapply (@T_Pi G 0 0 lvl l tVoid tVoid).
    + eapply (@T_Void G lvl 0); exact HG.
    + eapply (@T_Void ((l, tVoid) :: G) lvl 0).
      eapply Wff_cons; [exact HG | eapply (@T_Void G lvl 0); exact HG].
  - eapply (@T_Var ((l, tVoid) :: G) l lvl 0 tVoid).
    + eapply Wff_cons; [exact HG | eapply (@T_Void G lvl 0); exact HG].
    + exact (here l tVoid G).
    + exact Hsub.
Qed.

(* A variable whose type is [Pi Unit Void] inhabits Void in an open context,
   even though there need not be any closed Void inhabitant.  This is why a
   nil-only induction on typing derivations cannot be closed under the
   extended contexts used by T_Abs/T_Let/T_Ind/T_J/T_Seq. *)
Lemma wt_open_void_var_pi_unit : forall (G : context) (lp l lvl : T),
  Wff G -> lp ⊆ lvl ->
  Wt ((lp, tPi l tUnit tVoid) :: G) lvl
     (tApp (var_tm 0) l tTT) tVoid.
Proof.
  intros G lp l lvl HG Hsub.
  eapply (@T_App ((lp, tPi l tUnit tVoid) :: G) lvl l (var_tm 0) tUnit tVoid tTT).
  - eapply (@T_Var ((lp, tPi l tUnit tVoid) :: G) lp lvl 0 (tPi l tUnit tVoid)).
    + eapply Wff_cons.
      * exact HG.
      * eapply (@T_Pi G 0 0 lvl l tUnit tVoid).
        -- eapply (@T_Unit G lvl 0); exact HG.
        -- eapply (@T_Void ((l, tUnit) :: G) lvl 0).
           eapply Wff_cons; [exact HG | eapply (@T_Unit G lvl 0); exact HG].
    + exact (here lp (tPi l tUnit tVoid) G).
    + exact Hsub.
  - eapply (@T_TT ((lp, tPi l tUnit tVoid) :: G) l).
    eapply Wff_cons.
    + exact HG.
    + eapply (@T_Pi G 0 0 lvl l tUnit tVoid).
      * eapply (@T_Unit G lvl 0); exact HG.
      * eapply (@T_Void ((l, tUnit) :: G) lvl 0).
        eapply Wff_cons; [exact HG | eapply (@T_Unit G lvl 0); exact HG].
Qed.



Lemma Par_Var_inv : forall i c, Par (var_tm i) c -> c = var_tm i.
Proof. intros i c H. inversion H. reflexivity. Qed.
Lemma Par_Univ_inv : forall n c, Par (tUniv n) c -> c = tUniv n.
Proof. intros n c H. inversion H. reflexivity. Qed.
Lemma Par_Void_inv : forall c, Par tVoid c -> c = tVoid.
Proof. intros c H. inversion H. reflexivity. Qed.
Lemma Par_Refl_inv : forall c, Par tRefl c -> c = tRefl.
Proof. intros c H. inversion H. reflexivity. Qed.
Lemma Par_Zero_inv : forall c, Par tZero c -> c = tZero.
Proof. intros c H. inversion H. reflexivity. Qed.
Lemma Par_Nat_inv : forall c, Par tNat c -> c = tNat.
Proof. intros c H. inversion H. reflexivity. Qed.
Lemma Par_TT_inv : forall c, Par tTT c -> c = tTT.
Proof. intros c H. inversion H. reflexivity. Qed.
Lemma Par_Unit_inv : forall c, Par tUnit c -> c = tUnit.
Proof. intros c H. inversion H. reflexivity. Qed.

Lemma Par_Pi_inv : forall l A B c,
  Par (tPi l A B) c -> exists A' B', c = tPi l A' B' /\ Par A A' /\ Par B B'.
Proof. intros l A B c H. inversion H; subst. eauto 6. Qed.

Lemma Par_Abs_inv : forall l a c,
  Par (tAbs l a) c -> exists a', c = tAbs l a' /\ Par a a'.
Proof. intros l a c H. inversion H; subst. eauto 6. Qed.

Lemma Par_Suc_inv : forall a c,
  Par (tSuc a) c -> exists a', c = tSuc a' /\ Par a a'.
Proof. intros a c H. inversion H; subst. eauto 6. Qed.

Lemma Par_Absurd_inv : forall a c,
  Par (tAbsurd a) c -> exists a', c = tAbsurd a' /\ Par a a'.
Proof. intros a c H. inversion H; subst. eauto 6. Qed.

Lemma Par_Eq_inv : forall l a b c,
  Par (tEq l a b) c -> exists a' b', c = tEq l a' b' /\ Par a a' /\ Par b b'.
Proof. intros l a b c H. inversion H; subst. eauto 6. Qed.

Lemma Par_Sig_inv : forall l A B c,
  Par (tSig l A B) c -> exists A' B', c = tSig l A' B' /\ Par A A' /\ Par B B'.
Proof. intros l A B c H. inversion H; subst. eauto 6. Qed.

Lemma Par_Pack_inv : forall l a b c,
  Par (tPack l a b) c -> exists a' b', c = tPack l a' b' /\ Par a a' /\ Par b b'.
Proof. intros l a b c H. inversion H; subst. eauto 6. Qed.

Lemma Par_App_inv : forall a l b c,
  Par (tApp a l b) c ->
  (exists a' b', c = tApp a' l b' /\ Par a a' /\ Par b b') \/
  (exists body a' b', a = tAbs l body /\ c = a'[b'..] /\ Par body a' /\ Par b b').
Proof. intros a l b c H. inversion H; subst.
  - left. eauto 6.
  - right. eauto 8.
Qed.

Lemma Par_J_inv : forall l a b c,
  Par (tJ l a b) c ->
  (exists a' b', c = tJ l a' b' /\ Par a a' /\ Par b b') \/
  (exists a', b = tRefl /\ c = a' /\ Par a a').
Proof. intros l a b c H. inversion H; subst.
  - left. eauto 6.
  - right. eauto 6.
Qed.

Lemma Par_Let_inv : forall l0 l1 a b c,
  Par (tLet l0 l1 a b) c ->
  (exists a' b', c = tLet l0 l1 a' b' /\ Par a a' /\ Par b b') \/
  (exists a0 b0 c0 a1 b1 c1,
      a = tPack l0 a0 b0 /\ b = c0 /\
      c = c1[b1 .: a1 ..] /\ Par a0 a1 /\ Par b0 b1 /\ Par c0 c1).
Proof. intros l0 l1 a b c H. inversion H; subst.
  - left. eauto 6.
  - right. eauto 12.
Qed.

Lemma Par_Ind_inv : forall l a b c d,
  Par (tInd l a b c) d ->
  (exists a' b' c', d = tInd l a' b' c' /\ Par a a' /\ Par b b' /\ Par c c') \/
  (exists a', c = tZero /\ d = a' /\ Par a a') \/
  (exists a1 b1 c0 c1,
      c = tSuc c0 /\ d = b1[(tInd l a1 b1 c1) .: c1 ..] /\
      Par a a1 /\ Par b b1 /\ Par c0 c1).
Proof. intros l a b c d H. inversion H; subst.
  - left. eauto 8.
  - right; left. eauto 6.
  - right; right. eauto 10.
Qed.

Lemma Par_Seq_inv : forall l a b c,
  Par (tSeq l a b) c ->
  (exists a' b', c = tSeq l a' b' /\ Par a a' /\ Par b b') \/
  (exists b', a = tTT /\ c = b' /\ Par b b').
Proof. intros l a b c H. inversion H; subst.
  - left. eauto 6.
  - right. eauto 6.
Qed.


Lemma ieq_subst2 : forall (Xi : econtext) (l : T) (a b : tm),
  IEq Xi l a b -> forall (D : econtext) (sigma tau : fin -> tm),
    (forall i lk, elookup i Xi lk -> GIEq D l lk (sigma i) (tau i)) ->
    IEq D l (a[sigma]) (b[tau]).
Proof.
  intros Xi l a b H D sigma tau Hpt.
  exact (proj1 (ieq_gieq_subst2 Xi l) a b H D sigma tau Hpt).
Qed.

Lemma gieq_subst2 : forall (Xi : econtext) (l l0 : T) (a b : tm),
  GIEq Xi l l0 a b -> forall (D : econtext) (sigma tau : fin -> tm),
    (forall i lk, elookup i Xi lk -> GIEq D l lk (sigma i) (tau i)) ->
    GIEq D l l0 (a[sigma]) (b[tau]).
Proof.
  intros Xi l l0 a b H D sigma tau Hpt.
  exact (proj2 (ieq_gieq_subst2 Xi l) l0 a b H D sigma tau Hpt).
Qed.


Lemma IEq_abs_inv : forall (Xi : econtext) (l l0 : T) (a A : tm),
  IEq Xi l (tAbs l0 a) A ->
  exists a', A = tAbs l0 a' /\ IEq (l0 :: Xi) l a a'.
Proof. intros Xi l l0 a A H. inversion H; subst; eauto 6. Qed.

Lemma IEq_absurd_inv : forall (Xi : econtext) (l : T) (a A : tm),
  IEq Xi l (tAbsurd a) A -> exists b, A = tAbsurd b.
Proof. intros Xi l a A H. inversion H; subst; eauto 6. Qed.

Lemma IEq_suc_inv : forall (Xi : econtext) (l : T) (a A : tm),
  IEq Xi l (tSuc a) A -> exists a', A = tSuc a' /\ IEq Xi l a a'.
Proof. intros Xi l a A H. inversion H; subst; eauto 6. Qed.

Lemma IEq_zero_inv : forall (Xi : econtext) (l : T) (A : tm),
  IEq Xi l tZero A -> A = tZero.
Proof. intros Xi l A H. inversion H. reflexivity. Qed.

Lemma IEq_refl_inv : forall (Xi : econtext) (l : T) (A : tm),
  IEq Xi l tRefl A -> A = tRefl.
Proof. intros Xi l A H. inversion H. reflexivity. Qed.

Lemma IEq_pack_inv : forall (Xi : econtext) (l l0 : T) (a b A : tm),
  IEq Xi l (tPack l0 a b) A ->
  exists a' b', A = tPack l0 a' b' /\ GIEq Xi l l0 a a' /\ IEq Xi l b b'.
Proof. intros Xi l l0 a b A H. inversion H; subst; eauto 8. Qed.

Lemma IEq_pi_inv2 : forall (Xi : econtext) (l l0 : T) (C D A : tm),
  IEq Xi l (tPi l0 C D) A ->
  exists C' D', A = tPi l0 C' D' /\ IEq Xi l C C' /\ IEq (l0 :: Xi) l D D'.
Proof. intros Xi l l0 C D A H. inversion H; subst; eauto 8. Qed.

Lemma IEq_abs_inv_r : forall (Xi : econtext) (l l0 : T) (A a : tm),
  IEq Xi l A (tAbs l0 a) ->
  exists a', A = tAbs l0 a' /\ IEq (l0 :: Xi) l a' a.
Proof. intros Xi l l0 A a H. inversion H; subst; eauto 6. Qed.

Lemma IEq_TT_inv : forall (Xi : econtext) (l : T) (A : tm),
  IEq Xi l tTT A -> A = tTT.
Proof. intros Xi l A H. inversion H. reflexivity. Qed.
Lemma IEq_TT_inv_r : forall (Xi : econtext) (l : T) (A : tm),
  IEq Xi l A tTT -> A = tTT.
Proof. intros Xi l A H. inversion H. reflexivity. Qed.

Lemma IEq_refl_inv_r : forall (Xi : econtext) (l : T) (A : tm),
  IEq Xi l A tRefl -> A = tRefl.
Proof. intros Xi l A H. inversion H. reflexivity. Qed.

Lemma IEq_pack_inv_r : forall (Xi : econtext) (l l0 : T) (A a b : tm),
  IEq Xi l A (tPack l0 a b) ->
  exists a' b', A = tPack l0 a' b' /\ GIEq Xi l l0 a' a /\ IEq Xi l b' b.
Proof. intros Xi l l0 A a b H. inversion H; subst; eauto 8. Qed.

Lemma gieq_of_ieq : forall (Xi : econtext) (l l0 : T) (A B : tm),
  IEq Xi l A B -> GIEq Xi l l0 A B.
Proof.
  intros Xi l l0 A B H.
  destruct (T_eqdec (l0 ∩ l) l0) as [Hs|Hn].
  - apply GI_Dist; [exact Hs | exact H].
  - apply GI_InDist; exact Hn.
Qed.

Lemma IEq_suc_inv_r : forall (Xi : econtext) (l : T) (A a : tm),
  IEq Xi l A (tSuc a) -> exists a', A = tSuc a' /\ IEq Xi l a' a.
Proof. intros Xi l A a H. inversion H; subst; eauto 6. Qed.

Lemma IEq_zero_inv_r : forall (Xi : econtext) (l : T) (A : tm),
  IEq Xi l A tZero -> A = tZero.
Proof. intros Xi l A H. inversion H. reflexivity. Qed.

Definition IEqParP (Xi : econtext) (l : T) (a b : tm) (H : IEq Xi l a b) : Prop :=
  forall b', Par b b' -> exists a', rtc Par a a' /\ IEq Xi l a' b'.
Definition GIEqParP (Xi : econtext) (l l0 : T) (a b : tm) (H : GIEq Xi l l0 a b) : Prop :=
  forall b', Par b b' -> exists a', rtc Par a a' /\ GIEq Xi l l0 a' b'.

Lemma ieq_gieq_par : forall (Xi : econtext) (l : T),
  (forall (a b : tm) (H : IEq Xi l a b), IEqParP Xi l a b H) /\
  (forall (l0 : T) (a b : tm) (H : GIEq Xi l l0 a b), GIEqParP Xi l l0 a b H).
Proof.
  intros Xi l. apply (IEq_mutual IEqParP GIEqParP).
  - (* I_Var *) intros Xi' l' i l0 e e0. unfold IEqParP in *.
    intros b' Hpar. apply Par_Var_inv in Hpar. subst b'.
    exists (var_tm i). split; [apply rtc_refl | eapply I_Var; eassumption].
  - (* I_Univ *) intros Xi' l' n. unfold IEqParP in *.
    intros b' Hpar. apply Par_Univ_inv in Hpar. subst b'.
    exists (tUniv n). split; [apply rtc_refl | eapply I_Univ].
  - (* I_Pi *) intros Xi' l' l0 A0 A1 B0 B1 H1 IH1 H2 IH2.
    unfold IEqParP in *. intros b' Hpar.
    destruct (Par_Pi_inv l0 A1 B1 b' Hpar) as [A1' [B1' [E [HA HB]]]]. subst b'.
    destruct (IH1 A1' HA) as [A0' [HA0 HIA]].
    destruct (IH2 B1' HB) as [B0' [HB0 HIB]].
    exists (tPi l0 A0' B0'). split.
    + eapply (rtc_Par2 (fun x y => tPi l0 x y)).
      * intros x x' y y' Hx Hy. eapply P_Pi; eassumption.
      * exact HA0.
      * exact HB0.
    + eapply I_Pi; eassumption.
  - (* I_Abs *) intros Xi' l' l0 a0 a1 H1 IH1. unfold IEqParP in *.
    intros b' Hpar.
    destruct (Par_Abs_inv l0 a1 b' Hpar) as [a1' [E Hp]]. subst b'.
    destruct (IH1 a1' Hp) as [a0' [HA HI]].
    exists (tAbs l0 a0'). split.
    + eapply rtc_Par1; [intros x y Hxy; eapply P_Abs; exact Hxy | exact HA].
    + eapply I_Abs; exact HI.
  - (* I_App *) intros Xi' l' a0 a1 l0 b0 b1 H1 IH1 H2 IH2.
    unfold IEqParP in *. intros b' Hpar.
    destruct (Par_App_inv a1 l0 b1 b' Hpar) as
      [[a1' [b1' [E [HA HB]]]] |
       [body1 [a1' [b1' [Ea [Ec [Hbody Hb]]]]]]].
    + subst b'.
      destruct (IH1 a1' HA) as [a0' [HA0 HIA]].
      destruct (IH2 b1' HB) as [b0' [HB0 HIB]].
      exists (tApp a0' l0 b0'). split.
      * eapply (rtc_Par2 (fun x y => tApp x l0 y)).
        -- intros x x' y y' Hx Hy. eapply P_App; eassumption.
        -- exact HA0.
        -- exact HB0.
      * eapply I_App; eassumption.
    + subst b'. subst a1.
      destruct (IH1 (tAbs l0 a1') (P_Abs l0 body1 a1' Hbody))
        as [f0 [Hf0 HIf]].
      destruct (IEq_abs_inv_r _ _ _ _ _ HIf) as [body0' [Efa HIbody]].
      subst f0.
      destruct (IH2 b1' Hb) as [b0' [HB0 HIB]].
      assert (Hstep : rtc Par (tApp a0 l0 b0) (body0'[b0'..])).
      { eapply rtc_trans'.
        - eapply rtc_Par2 with (f := fun x y => tApp x l0 y).
          + intros x x' y y' Hx Hy. eapply P_App; eassumption.
          + exact Hf0.
          + exact HB0.
        - eapply rtc_l.
          + eapply P_AppAbs; [apply Par_refl | apply Par_refl].
          + apply rtc_refl. }
      assert (HI : IEq Xi' l' (body0'[b0'..]) (a1'[b1'..])).
      { eapply ieq_subst2 with (Xi := l0 :: Xi').
        - exact HIbody.
        - intros i lk Hlk. destruct i as [|k].
          + unfold elookup in Hlk; simpl in Hlk. injection Hlk as ?; subst lk.
            simpl. exact HIB.
          + simpl. eapply gieq_var_self.
            unfold elookup in Hlk; simpl in Hlk. exact Hlk. }
      exists (body0'[b0'..]). split; [exact Hstep | exact HI].
  - (* I_Void *) intros Xi' l'. unfold IEqParP in *.
    intros b' Hpar. apply Par_Void_inv in Hpar. subst b'.
    exists tVoid. split; [apply rtc_refl | eapply I_Void].
  - (* I_Absurd *) intros Xi' l' a b. unfold IEqParP in *.
    intros b' Hpar. destruct (Par_Absurd_inv b b' Hpar) as [b'' [E Hp]].
    subst b'. exists (tAbsurd a). split; [apply rtc_refl | eapply I_Absurd].
  - (* I_Refl *) intros Xi' l'. unfold IEqParP in *.
    intros b' Hpar. apply Par_Refl_inv in Hpar. subst b'.
    exists tRefl. split; [apply rtc_refl | eapply I_Refl].
  - (* I_Eq *) intros Xi' l' l0 a0 a1 b0 b1 e H1 IH1 H2 IH2.
    unfold IEqParP in *. intros b' Hpar.
    destruct (Par_Eq_inv l0 a1 b1 b' Hpar) as [a1' [b1' [E [HA HB]]]]. subst b'.
    destruct (IH1 a1' HA) as [a0' [HA0 HIA]].
    destruct (IH2 b1' HB) as [b0' [HB0 HIB]].
    exists (tEq l0 a0' b0'). split.
    + eapply (rtc_Par2 (fun x y => tEq l0 x y)).
      * intros x x' y y' Hx Hy. eapply P_Eq; eassumption.
      * exact HA0.
      * exact HB0.
    + eapply I_Eq; eassumption.
  - (* I_J *) intros Xi' l' lp t0 t1 p0 p1 e H1 IH1 H2 IH2.
    unfold IEqParP in *. intros b' Hpar.
    destruct (Par_J_inv lp t1 p1 b' Hpar) as
      [[a1' [b1' [E [HA HB]]]] | [a1' [Ep [Eb Hp]]]].
    + subst b'.
      destruct (IH1 a1' HA) as [t0' [Ht0 HIt]].
      destruct (IH2 b1' HB) as [p0' [Hp0 HIp]].
      exists (tJ lp t0' p0'). split.
      * eapply (rtc_Par2 (fun x y => tJ lp x y)).
        -- intros x x' y y' Hx Hy. eapply P_J; eassumption.
        -- exact Ht0.
        -- exact Hp0.
      * eapply I_J; eassumption.
    + subst b'. subst p1.
      destruct (IH2 tRefl (Par_refl tRefl)) as [p0' [Hp0 HIp]].
      assert (p0' = tRefl) as Ep0 by (eapply IEq_refl_inv_r; exact HIp).
      subst p0'.
      destruct (IH1 a1' Hp) as [t0' [Ht0 HIt]].
      exists t0'. split.
      * eapply rtc_trans'.
        -- eapply (rtc_Par2 (fun x y => tJ lp x y)).
           ++ intros x x' y y' Hx Hy. eapply P_J; eassumption.
           ++ apply rtc_refl.
           ++ exact Hp0.
        -- eapply rtc_trans'.
           ++ eapply rtc_l; [eapply P_JRefl; apply Par_refl | apply rtc_refl].
           ++ exact Ht0.
      * exact HIt.
  - (* I_Sig *) intros Xi' l' l0 A0 B0 A1 B1 H1 IH1 H2 IH2.
    unfold IEqParP in *. intros b' Hpar.
    destruct (Par_Sig_inv l0 A1 B1 b' Hpar) as [A1' [B1' [E [HA HB]]]]. subst b'.
    destruct (IH1 A1' HA) as [A0' [HA0 HIA]].
    destruct (IH2 B1' HB) as [B0' [HB0 HIB]].
    exists (tSig l0 A0' B0'). split.
    + eapply (rtc_Par2 (fun x y => tSig l0 x y)).
      * intros x x' y y' Hx Hy. eapply P_Sig; eassumption.
      * exact HA0.
      * exact HB0.
    + eapply I_Sig; eassumption.
  - (* I_Pack *) intros Xi' l' l0 a0 b0 a1 b1 H1 IH1 H2 IH2.
    unfold IEqParP, GIEqParP in *. intros b' Hpar.
    destruct (Par_Pack_inv l0 a1 b1 b' Hpar) as [a1' [b1' [E [HA HB]]]]. subst b'.
    destruct (IH1 a1' HA) as [a0' [HA0 HIA]].
    destruct (IH2 b1' HB) as [b0' [HB0 HIB]].
    exists (tPack l0 a0' b0'). split.
    + eapply (rtc_Par2 (fun x y => tPack l0 x y)).
      * intros x x' y y' Hx Hy. eapply P_Pack; eassumption.
      * exact HA0.
      * exact HB0.
    + eapply I_Pack; eassumption.
  - (* I_Let *) intros Xi' l' l0 l1 a0 b0 a1 b1 e H1 IH1 H2 IH2.
    unfold IEqParP in *. intros b' Hpar.
    destruct (Par_Let_inv l0 l1 a1 b1 b' Hpar) as
      [[a1' [b1' [E [HA HB]]]] |
       [a0p [b0p [c0 [a1p [b1p [c1 [Ea [Eb [Ec [HA [HB Hc]]]]]]]]]]]].
    + subst b'.
      destruct (IH1 a1' HA) as [a0' [HA0 HIA]].
      destruct (IH2 b1' HB) as [b0' [HB0 HIB]].
      exists (tLet l0 l1 a0' b0'). split.
      * eapply (rtc_Par2 (fun x y => tLet l0 l1 x y)).
        -- intros x x' y y' Hx Hy. eapply P_Let; eassumption.
        -- exact HA0.
        -- exact HB0.
      * eapply I_Let; eassumption.
    + subst a1. subst b1. subst b'.
      destruct (IH1 (tPack l0 a1p b1p) (P_Pack l0 a0p a1p b0p b1p HA HB))
        as [f0 [Hf0 HIf]].
      destruct (IEq_pack_inv_r _ _ _ _ _ _ HIf)
        as [A0' [B0' [Ef [HIA HIB]]]].
      subst f0.
      destruct (IH2 c1 Hc) as [body0' [Hbody0 HIbody]].
      assert (Hstep : rtc Par (tLet l0 l1 a0 b0)
                             (body0'[B0' .: A0' ..])).
      { eapply rtc_trans'.
        - eapply (rtc_Par2 (fun x y => tLet l0 l1 x y)).
          + intros x x' y y' Hx Hy. eapply P_Let; eassumption.
          + exact Hf0.
          + exact Hbody0.
        - eapply rtc_l.
          + eapply P_LetPack; [apply Par_refl | apply Par_refl | apply Par_refl].
          + apply rtc_refl. }
      assert (HI : IEq Xi' l' (body0'[B0' .: A0' ..])
                            (c1[b1p .: a1p ..])).
      { eapply ieq_subst2 with (Xi := l1 :: l0 :: Xi').
        - exact HIbody.
        - intros i lk Hlk. destruct i as [|[|k]].
          + unfold elookup in Hlk; simpl in Hlk. injection Hlk as ?; subst lk.
            simpl. eapply gieq_of_ieq. exact HIB.
          + unfold elookup in Hlk; simpl in Hlk. injection Hlk as ?; subst lk.
            simpl. exact HIA.
          + simpl. eapply gieq_var_self.
            unfold elookup in Hlk; simpl in Hlk. exact Hlk. }
      exists (body0'[B0' .: A0' ..]). split; [exact Hstep | exact HI].
  - (* I_Zero *) intros Xi' l'. unfold IEqParP in *.
    intros b' Hpar. apply Par_Zero_inv in Hpar. subst b'.
    exists tZero. split; [apply rtc_refl | eapply I_Zero].
  - (* I_Suc *) intros Xi' l' a0 a1 H1 IH1. unfold IEqParP in *.
    intros b' Hpar. destruct (Par_Suc_inv a1 b' Hpar) as [a1' [E Hp]].
    subst b'. destruct (IH1 a1' Hp) as [a0' [HA HI]].
    exists (tSuc a0'). split.
    + eapply rtc_Par1; [intros x y Hxy; eapply P_Suc; exact Hxy | exact HA].
    + eapply I_Suc; exact HI.
  - (* I_Ind *) intros Xi' l' l0 a0 b0 c0 a1 b1 c1 e H1 IH1 H2 IH2 H3 IH3.
    unfold IEqParP in *. intros b' Hpar.
    destruct (Par_Ind_inv l0 a1 b1 c1 b' Hpar) as
      [ (a1' & b1' & c1' & E & HA & HB & HC) |
        [ (a1' & Ez & Eb & Ha) |
          (a1' & b1' & c0' & c1' & Es & Eb & HA & HB & Hc) ] ].
    + subst b'.
      destruct (IH1 a1' HA) as [a0' [HA0 HIA]].
      destruct (IH2 b1' HB) as [b0' [HB0 HIB]].
      destruct (IH3 c1' HC) as [c0' [HC0 HIC]].
      exists (tInd l0 a0' b0' c0'). split.
      * eapply (rtc_Par3 (fun x y z => tInd l0 x y z)).
        -- intros x x' y y' z z' Hx Hy Hz. eapply P_Ind; eassumption.
        -- exact HA0.
        -- exact HB0.
        -- exact HC0.
      * eapply I_Ind; eassumption.
    + subst c1. subst b'.
      destruct (IH3 tZero (Par_refl tZero)) as [c0' [HC0 HIC]].
      assert (c0' = tZero) as Ec by (eapply IEq_zero_inv_r; exact HIC).
      subst c0'.
      destruct (IH1 a1' Ha) as [a0' [HA0 HIA]].
      exists a0'. split.
      * eapply rtc_trans'.
        -- eapply (rtc_Par3 (fun x y z => tInd l0 x y z)).
           ++ intros x x' y y' z z' Hx Hy Hz. eapply P_Ind; eassumption.
           ++ apply rtc_refl.
           ++ apply rtc_refl.
           ++ exact HC0.
        -- eapply rtc_trans'.
           ++ eapply rtc_l; [eapply P_IndZero; apply Par_refl | apply rtc_refl].
           ++ exact HA0.
      * exact HIA.
    + subst c1. subst b'.
      destruct (IH3 (tSuc c1') (P_Suc c0' c1' Hc)) as [c0'' [HC0 HIC]].
      destruct (IEq_suc_inv_r _ _ _ _ HIC) as [cL [Ec HIL]].
      subst c0''.
      destruct (IH1 a1' HA) as [a0' [HA0 HIA]].
      destruct (IH2 b1' HB) as [b0' [HB0 HIB]].
      assert (Hstep : rtc Par (tInd l0 a0 b0 c0)
                             (b0'[(tInd l0 a0' b0' cL) .: cL ..])).
      { eapply rtc_trans'.
        - eapply (rtc_Par3 (fun x y z => tInd l0 x y z)).
          + intros x x' y y' z z' Hx Hy Hz. eapply P_Ind; eassumption.
          + apply rtc_refl.
          + apply rtc_refl.
          + exact HC0.
        - eapply rtc_trans'.
          + eapply (rtc_Par3 (fun x y z => tInd l0 x y z)).
            * intros x x' y y' z z' Hx Hy Hz. eapply P_Ind; eassumption.
            * exact HA0.
            * exact HB0.
            * apply rtc_refl.
          + eapply rtc_l.
            * eapply P_IndSuc; [apply Par_refl | apply Par_refl | apply Par_refl].
            * apply rtc_refl. }
      assert (HI : IEq Xi' l' (b0'[(tInd l0 a0' b0' cL) .: cL ..])
                            (b1'[(tInd l0 a1' b1' c1') .: c1' ..])).
      { eapply ieq_subst2 with (Xi := l0 :: l0 :: Xi').
        - exact HIB.
        - intros i lk Hlk. destruct i as [|[|k]].
          + unfold elookup in Hlk; simpl in Hlk. injection Hlk as ?; subst lk.
            simpl. eapply gieq_of_ieq.
            exact (@I_Ind Xi' l' l0 a0' b0' cL a1' b1' c1' e HIA HIB HIL).
          + unfold elookup in Hlk; simpl in Hlk. injection Hlk as ?; subst lk.
            simpl. eapply gieq_of_ieq. exact HIL.
          + simpl. eapply gieq_var_self.
            unfold elookup in Hlk; simpl in Hlk. exact Hlk. }
      exists (b0'[(tInd l0 a0' b0' cL) .: cL ..]). split; [exact Hstep | exact HI].
  - (* I_Nat *) intros Xi' l'. unfold IEqParP in *.
    intros b' Hpar. apply Par_Nat_inv in Hpar. subst b'.
    exists tNat. split; [apply rtc_refl | eapply I_Nat].
  - (* I_Unit *) intros Xi' l'. unfold IEqParP in *.
    intros b' Hpar. apply Par_Unit_inv in Hpar. subst b'.
    exists tUnit. split; [apply rtc_refl | eapply I_Unit].
  - (* I_TT *) intros Xi' l'. unfold IEqParP in *.
    intros b' Hpar. apply Par_TT_inv in Hpar. subst b'.
    exists tTT. split; [apply rtc_refl | eapply I_TT].
  - (* I_Seq *) intros Xi' l' l0 a0 a1 b0 b1 e H1 IH1 H2 IH2.
    unfold IEqParP in *. intros b' Hpar.
    destruct (Par_Seq_inv l0 a1 b1 b' Hpar) as
      [[a1' [b1' [E [HA HB]]]] | [b1' [Ea [Eb Hp]]]].
    + subst b'.
      destruct (IH1 a1' HA) as [a0' [HA0 HIA]].
      destruct (IH2 b1' HB) as [b0' [HB0 HIB]].
      exists (tSeq l0 a0' b0'). split.
      * eapply (rtc_Par2 (fun x y => tSeq l0 x y)).
        -- intros x x' y y' Hx Hy. eapply P_Seq; eassumption.
        -- exact HA0.
        -- exact HB0.
      * eapply I_Seq; eassumption.
    + subst b'. subst a1.
      destruct (IH1 tTT (Par_refl tTT)) as [a0' [HA0 HIA0]].
      assert (a0' = tTT) as Et by (eapply IEq_TT_inv_r; exact HIA0). subst a0'.
      destruct (IH2 b1' Hp) as [b0' [HB0 HIB]].
      exists b0'. split.
      * eapply rtc_trans'.
        -- eapply (rtc_Par2 (fun x y => tSeq l0 x y)).
           ++ intros x x' y y' Hx Hy. eapply P_Seq; eassumption.
           ++ exact HA0.
           ++ exact HB0.
        -- eapply rtc_l; [eapply P_SeqTT; apply Par_refl | apply rtc_refl].
      * exact HIB.
  - (* GI_Dist *) intros Xi' l' l0 A B e H1 IH1. unfold GIEqParP in *.
    intros b' Hpar. destruct (IH1 b' Hpar) as [A' [HA HI]].
    exists A'. split; [exact HA | eapply GI_Dist; eassumption].
  - (* GI_InDist *) intros Xi' l' l0 A B n. unfold GIEqParP in *.
    intros b' Hpar. exists A. split; [apply rtc_refl | eapply GI_InDist; exact n].
Qed.
Lemma ieq_par_r : forall (Xi : econtext) (l : T) (a b : tm),
  IEq Xi l a b -> forall b', Par b b' ->
  exists a', rtc Par a a' /\ IEq Xi l a' b'.
Proof.
  intros Xi l a b H b' Hpar.
  exact (proj1 (ieq_gieq_par Xi l) a b H b' Hpar).
Qed.

Lemma gieq_par_r : forall (Xi : econtext) (l l0 : T) (a b : tm),
  GIEq Xi l l0 a b -> forall b', Par b b' ->
  exists a', rtc Par a a' /\ GIEq Xi l l0 a' b'.
Proof.
  intros Xi l l0 a b H b' Hpar.
  exact (proj2 (ieq_gieq_par Xi l) l0 a b H b' Hpar).
Qed.

Lemma ieq_rtc_r : forall (Xi : econtext) (l : T) (a b : tm),
  IEq Xi l a b -> forall b', rtc Par b b' ->
  exists a', rtc Par a a' /\ IEq Xi l a' b'.
Proof.
  intros Xi l a b H b' HR. revert a H.
  induction HR as [x | x y z Hxy Hrest IH]; intros a H.
  - exists a. split; [apply rtc_refl | exact H].
  - destruct (ieq_par_r _ _ _ _ H y Hxy) as [a1 [Ha1 HI1]].
    destruct (IH a1 HI1) as [a2 [Ha2 HI2]].
    exists a2. split; [| exact HI2].
    eapply rtc_trans'; [exact Ha1 | exact Ha2].
Qed.

Lemma conv_trans_void_r : forall (Xi : econtext) (A B : tm),
  conv Xi A B -> conv Xi B tVoid -> conv Xi A tVoid.
Proof.
  intros Xi A B [l [c0 [c1 [HA [HB HIEq]]]]] HBv.
  assert (HBvoid : rtc Par B tVoid) by (apply (conv_void Xi B); exact HBv).
  destruct (Par_rtc_confluent B c1 tVoid HB HBvoid) as [e [Hc1 He]].
  assert (Hev : e = tVoid) by (apply (rtc_tVoid_eq e); exact He).
  subst e.
  destruct (ieq_rtc_r Xi l c0 c1 HIEq tVoid Hc1) as [c0' [Hc0' HI]].
  assert (Ec : c0' = tVoid) by (apply (IEq_void_inv_r Xi l c0'); exact HI).
  subst c0'.
  apply (proj2 (conv_void_iff Xi l A)).
  eapply rtc_trans'; [exact HA | exact Hc0'].
Qed.


Lemma ieq_rtc_l : forall (Xi : econtext) (l : T) (a b : tm),
  IEq Xi l a b -> forall a', rtc Par a a' ->
  exists b', rtc Par b b' /\ IEq Xi l a' b'.
Proof.
  intros Xi l a b H a' Ha.
  destruct (ieq_rtc_r Xi l b a (ieq_sym _ _ _ _ H) a' Ha)
    as [b' [Hb' HI]].
  exists b'. split; [exact Hb' | apply ieq_sym; exact HI].
Qed.

Lemma conv_trans_void_l : forall (Xi : econtext) (A B : tm),
  conv Xi A B -> conv Xi tVoid A -> conv Xi tVoid B.
Proof.
  intros Xi A B HAB HVA.
  apply conv_sym.
  eapply conv_trans_void_r; [apply conv_sym; exact HAB | apply conv_sym; exact HVA].
Qed.

Lemma conv_void_congr : forall (Xi : econtext) (A B : tm),
  conv Xi A B -> conv Xi A tVoid -> conv Xi B tVoid.
Proof.
  intros Xi A B HAB HAV.
  eapply conv_trans_void_r; [apply conv_sym; exact HAB | exact HAV].
Qed.


Lemma conv_eq_equal_r : forall (Xi : econtext) (l l' : T) (x a b : tm),
  conv Xi (tEq l x x) (tEq l' a b) -> conv Xi x b.
Proof.
  intros Xi l l' x a b [m [c0 [c1 [H0 [H1 H2]]]]].
  destruct (rtc_Par_eq_inv l x x c0 H0) as [x1 [x2 [E0 [Hx1 Hx2]]]]; subst c0.
  destruct (rtc_Par_eq_inv l' a b c1 H1) as [a1 [b1 [E1 [Ha Hb]]]]; subst c1.
  inversion H2; subst.
  exists m, x2, b1. split; [exact Hx2 | split; [exact Hb | assumption]].
Qed.

Lemma conv_eq_void_endpoint : forall (Xi : econtext) (l l' : T) (x a b : tm),
  conv Xi (tEq l x x) (tEq l' a b) -> rtc Par b tVoid -> rtc Par a tVoid.
Proof.
  intros Xi l l' x a b H Hb.
  assert (Hxa : conv Xi x a) by (apply (conv_eq_equal_l Xi l l' x a b); exact H).
  assert (Hxb : conv Xi x b) by (apply (conv_eq_equal_r Xi l l' x a b); exact H).
  assert (Hbv : conv Xi b tVoid) by (apply (proj2 (conv_void_iff Xi l b)); exact Hb).
  assert (Hxv : conv Xi x tVoid) by (eapply conv_trans_void_r; [exact Hxb | exact Hbv]).
  assert (Hav : conv Xi a tVoid)
    by (eapply conv_trans_void_r; [apply conv_sym; exact Hxa | exact Hxv]).
  apply (proj1 (conv_void_iff Xi l a)); exact Hav.
Qed.


Definition VoidFree (A : tm) : Prop := ~ rtc Par A tVoid.

Lemma voidfree_conv_iff : forall (Xi : econtext) (A B : tm),
  conv Xi A B -> (VoidFree A <-> VoidFree B).
Proof.
  intros Xi A B H. destruct H as [m [c0 [c1 [HA [HB HIEq]]]]].
  split; intros HV.
  - intro HBv. apply HV.
    assert (HvA : conv Xi A tVoid).
    { eapply conv_trans_void_r.
      - exists m, c0, c1. split; [exact HA | split; [exact HB | exact HIEq]].
      - apply (proj2 (conv_void_iff Xi m B)); exact HBv. }
    apply (proj1 (conv_void_iff Xi m A)); exact HvA.
  - intro HAv. apply HV.
    assert (HvB : conv Xi B tVoid).
    { eapply conv_trans_void_r.
      - apply conv_sym. exists m, c0, c1.
        split; [exact HA | split; [exact HB | exact HIEq]].
      - apply (proj2 (conv_void_iff Xi m A)); exact HAv. }
    apply (proj1 (conv_void_iff Xi m B)); exact HvB.
Qed.

Lemma VoidFree_pi : forall (l0 : T) (A B : tm), VoidFree (tPi l0 A B).
Proof.
  intros l0 A B H.
  assert (hpi tVoid) as [l [X [Y E]]].
  { apply (rtc_hpi (tPi l0 A B) tVoid H). exists l0, A, B; reflexivity. }
  discriminate E.
Qed.

Lemma VoidFree_void : ~ VoidFree tVoid.
Proof. intro H. apply H. apply rtc_refl. Qed.


Definition SPred := tm -> Prop.

(* A type expression is "Void-free" if it has no parallel reduction path to
   tVoid.  This predicate is invariant under conversion (proved below) and is
   the uniform soundness guard for all type constructors. *)

(* A semantic type family, used to interpret a variable that is itself a
   type-level function (so that [tApp] as a type has a meaning). *)
Definition SFam := tm -> SPred.

(* Semantic environment entry: the term value, the level of the context entry,
   the semantic type when the value is used as a code, and the semantic type
   family when the value is used as a type-level function. *)
Record SV := {
  sv_tm  : tm;
  sv_lvl : T;
  sv_ty  : option SPred;
  sv_fam : option SFam
}.
Definition Env := list SV.

Definition env_lookup (E : Env) (i : fin) : option SV := nth_error E i.

Definition mkSV (l : T) (v : tm) (P : option SPred) (F : option SFam) : SV :=
  {| sv_tm := v; sv_lvl := l; sv_ty := P; sv_fam := F |}.

(* Level-indexed semantic predicate.  Every clause is conjoined with
   [VoidFree A]: any type with a reduction path to tVoid is empty, uniformly
   for all constructors (this is what makes T_Conv to tVoid sound).
   The Pi clause is negative; the Sig clause is the Church/negative encoding
   of dependent pairs; variables used as types/families are read from the
   environment.  The remaining type constructors are over-approximated by
   [True] under the VoidFree guard; this is sound for the consistency
   argument because the only informative case left is the Pi/Sig structure,
   and every Void-reducing type is excluded by the guard. *)
Fixpoint csem (l : T) (A : tm) (E : Env) {struct A} : SPred :=
  fun u =>
    VoidFree A /\
    match A with
    | tVoid => False
    | tUnit => True
    | tNat => True
    | tUniv _ => True
    | tPi l0 A0 B =>
        (forall (sv : SV), sv_lvl sv = l0 ->
           csem l0 A0 E (sv_tm sv) ->
           csem l B (sv :: E) (tApp u l0 (sv_tm sv)))
        /\
        (if T_eqb (l0 ∩ l) l0 then True
         else forall (sv1 sv2 : SV) (x : tm),
             csem l0 A0 E (sv_tm sv1) -> csem l0 A0 E (sv_tm sv2) ->
             (csem l B (sv1 :: E) x <-> csem l B (sv2 :: E) x))
    | tSig l0 A0 B =>
        (forall (R : SPred),
           (forall (a b : tm), csem l0 A0 E a ->
              csem l B (mkSV l0 a None None :: E) b -> R (tPack l0 a b))
           -> R u)
    | tEq _ _ _ => True
    | tAbsurd _ => True
    | tSuc _ => True
    | tZero => True
    | tRefl => True
    | tTT => True
    | var_tm k =>
        match env_lookup E k with
        | Some sv => match sv_ty sv with Some P => P u | None => True end
        | None => True
        end
    | tApp f l0 b =>
        match f with
        | var_tm k =>
            match env_lookup E k with
            | Some sv => match sv_fam sv with Some F => F b u | None => True end
            | None => True
            end
        | _ => True
        end
    | tAbs _ _ => True
    | tJ _ _ _ => True
    | tPack _ _ _ => True
    | tLet _ _ _ _ => True
    | tInd _ _ _ _ => True
    | tSeq _ _ _ => True
    end.

(* Well-formed semantic environments.  The [sv_ty]/[sv_fam] components are
   unconstrained here: the fundamental lemma will be proved for all of them,
   which is exactly what lets the Pi clause quantify over arbitrary semantic
   arguments. *)
Fixpoint EnvOk (G : context) (E : Env) {struct G} : Prop :=
  match G, E with
  | nil, nil => True
  | (l0, A) :: G', sv :: E' =>
      EnvOk G' E' /\ sv_lvl sv = l0 /\ csem l0 A E' (sv_tm sv)
  | _, _ => False
  end.

(* ---------- verified semantic rigidity lemmas ---------- *)

Lemma csem_voidfree : forall (l : T) (A : tm) (E : Env) (u : tm),
  csem l A E u -> VoidFree A.
Proof.
  intros l A E u. destruct A; cbn [csem]; intro H; exact (proj1 H).
Qed.

Lemma csem_void_elim : forall (l : T) (E : Env) (u : tm),
  csem l tVoid E u -> False.
Proof. intros l E u H. cbn [csem] in H. exact (proj2 H). Qed.

Lemma csem_conv_void_absurd :
  forall (Xi : econtext) (l : T) (A : tm) (E : Env) (u : tm),
    csem l A E u -> conv Xi A tVoid -> False.
Proof.
  intros Xi l A E u Hsem Hconv.
  apply (csem_voidfree l A E u Hsem).
  apply (conv_void Xi A Hconv).
Qed.

(* Verified eliminators for the negative Pi and Church Sig clauses. *)
Lemma csem_pi_elim : forall (l l0 : T) (A B : tm) (E : Env) (f : tm) (sv : SV),
  csem l (tPi l0 A B) E f ->
  sv_lvl sv = l0 ->
  csem l0 A E (sv_tm sv) ->
  csem l B (sv :: E) (tApp f l0 (sv_tm sv)).
Proof.
  intros l l0 A B E f sv H Hl HA.
  cbn [csem] in H.
  exact (proj1 (proj2 H) sv Hl HA).
Qed.

Lemma csem_sig_elim : forall (l l0 : T) (A B : tm) (E : Env) (u : tm) (R : SPred),
  csem l (tSig l0 A B) E u ->
  (forall (a b : tm), csem l0 A E a ->
     csem l B (mkSV l0 a None None :: E) b -> R (tPack l0 a b)) ->
  R u.
Proof.
  intros l l0 A B E u R H HR.
  cbn [csem] in H.
  exact (proj2 H R HR).
Qed.

(* ---------- semantic obligations for the fundamental lemma ---------- *)

(* Conversion invariance of the semantic clauses (the T_Conv case). *)
Definition ConvInvariantSem : Prop :=
  forall (Xi : econtext) (l : T) (A B : tm) (E : Env) (u : tm),
    conv Xi A B -> csem l A E u -> csem l B E u.

(* Type-level substitution: evaluating [B] in the environment extended by [v]
   agrees with evaluating [B[v..]] in the original environment.  The extended
   entry carries the syntactic meanings of [v] as a code and as a family. *)
Definition SubstSem : Prop :=
  forall (l l0 : T) (B : tm) (E : Env) (v u : tm),
    csem l B
      (mkSV l0 v (Some (csem l0 v E))
                  (Some (fun x => csem l0 (tApp v l0 x) E)) :: E) u
    <-> csem l (B[v..]) E u.

(* The Pi clause of a lambda: the predicate at the codomain, in the extended
   environment, is closed under forming the lambda-application.  This packages
   beta-expansion together with the term substitution of the environment's
   value. *)
Definition AbsSem : Prop :=
  forall (l l0 : T) (B : tm) (E : Env) (sv : SV) (body : tm),
    csem l B (sv :: E) body ->
    csem l B (sv :: E) (tApp (tAbs l0 body) l0 (sv_tm sv)).

(* Erasure/irrelevance for the Pi clause: when the annotation level is not
   below the ambient level, the codomain predicate is independent of the
   argument (this is the semantic counterpart of GI_InDist). *)
Definition IrrelSem : Prop :=
  forall (l l0 : T) (A B : tm) (E : Env),
    ~ (l0 ⊆ l) ->
    forall (sv1 sv2 : SV) (x : tm),
      csem l0 A E (sv_tm sv1) -> csem l0 A E (sv_tm sv2) ->
      (csem l B (sv1 :: E) x <-> csem l B (sv2 :: E) x).

(* The remaining obligation for T_Let: from the semantics of the open body in
   every valid environment for [(lp,B)::(l0,A)::G], derive the semantics of the
   let-of-pack term at the type obtained by substituting the two semantic
   components.  This is the beta/LetPack rule combined with the two-variable
   type substitution lemma. *)
Definition LetBodySem : Prop :=
  forall (G : context) (l lp l0 : T) (A B C : tm) (E : Env) (b : tm),
    EnvOk G E ->
    (forall (E' : Env), EnvOk ((lp, B) :: (l0, A) :: G) E' ->
       csem l (C[(tPack l0 (var_tm 1) (var_tm 0))
                   .: (shift >> shift >> var_tm)]) E' b) ->
    forall (a0 b0 : tm),
      csem l0 A E a0 ->
      csem lp B (mkSV l0 a0 None None :: E) b0 ->
      csem l (C[(tPack l0 a0 b0) ..]) E (tLet l0 lp (tPack l0 a0 b0) b).

(* ---------- fundamental lemma statement and conditional cases ---------- *)

Definition FundamentalLemma : Prop :=
  forall (G : context) (l : T) (a A : tm),
    Wt G l a A -> forall E : Env, EnvOk G E -> csem l A E a.

(* T_App case, conditionally on the substitution lemma for semantic types. *)
Lemma fundamental_T_App_case :
  SubstSem ->
  forall (G : context) (l l0 : T) (f : tm) (A B b : tm),
    (forall E : Env, EnvOk G E -> csem l (tPi l0 A B) E f) ->
    (forall E : Env, EnvOk G E -> csem l0 A E b) ->
    forall E : Env, EnvOk G E -> csem l (B[b..]) E (tApp f l0 b).
Proof.
  intros SUB G l l0 f A B b IHf IHb E HE.
  destruct (IHf E HE) as [HVF [HP _]].
  set (sv := mkSV l0 b (Some (csem l0 b E))
                       (Some (fun x => csem l0 (tApp b l0 x) E))).
  assert (Hl : sv_lvl sv = l0) by reflexivity.
  assert (HA : csem l0 A E (sv_tm sv)) by (unfold sv; exact (IHb E HE)).
  pose proof (HP sv Hl HA) as Happ.
  unfold sv in Happ.
  apply (proj1 (SUB l l0 B E b (tApp f l0 b))).
  exact Happ.
Qed.

(* T_Abs case, conditionally on AbsSem and IrrelSem. *)
Lemma fundamental_T_Abs_case :
  AbsSem -> IrrelSem ->
  forall (G : context) (l l0 : T) (body : tm) (A B : tm),
    (forall E : Env, EnvOk ((l0, A) :: G) E -> csem l B E body) ->
    forall E : Env, EnvOk G E -> csem l (tPi l0 A B) E (tAbs l0 body).
Proof.
  intros ABS IRR G l l0 body A B IHbody E HE.
  cbn [csem].
  split.
  - apply VoidFree_pi.
  - split.
    + intros sv Hlvl HA.
      apply (ABS l l0 B E sv body).
      apply IHbody. split; [exact HE | split; [exact Hlvl | exact HA]].
    + destruct (T_eqb (l0 ∩ l) l0) eqn:Eb.
      * exact I.
      * assert (Hn : ~ (l0 ∩ l = l0)).
        { intro He. rewrite He in Eb. rewrite T_eqb_refl in Eb. discriminate Eb. }
        apply (IRR l l0 A B E Hn).
Qed.

(* T_Let case, conditionally on the body/pack obligation, using the Church
   elimination of the package's semantic value. *)
Lemma fundamental_T_Let_case :
  LetBodySem ->
  forall (G : context) (l lp l0 : T) (A B C : tm) (a b : tm),
    (forall E : Env, EnvOk G E -> csem lp (tSig l0 A B) E a) ->
    (forall E : Env, EnvOk ((lp, B) :: (l0, A) :: G) E ->
       csem l (C[(tPack l0 (var_tm 1) (var_tm 0))
                   .: (shift >> shift >> var_tm)]) E b) ->
    forall E : Env, EnvOk G E -> csem l (C[a..]) E (tLet l0 lp a b).
Proof.
  intros LBS G l lp l0 A B C a b IHa IHb E HE.
  set (R := fun p : tm => csem l (C[p..]) E (tLet l0 lp p b)).
  change (R a).
  apply (csem_sig_elim lp l0 A B E a R).
  - apply IHa; exact HE.
  - intros a0 b0 HA HB.
    apply (LBS G l lp l0 A B C E b HE IHb a0 b0 HA HB).
Qed.

(* The obligations that remain for the full fundamental lemma. *)
Definition RemainingSemObligations : Prop :=
  ConvInvariantSem /\ SubstSem /\ AbsSem /\ IrrelSem /\ LetBodySem.

Definition FundamentalLemma_of_obligations : Prop :=
  RemainingSemObligations -> FundamentalLemma.

(* Exact remaining work for a complete proof.
   (1) The obligations ConvInvariantSem, SubstSem, AbsSem, IrrelSem and
       LetBodySem above are stated but not proved.  SubstSem is the semantic
       type-substitution lemma; AbsSem packages beta-expansion for the Pi
       clause; IrrelSem is the semantic form of GI_InDist; LetBodySem is the
       beta/LetPack rule together with the two-variable type substitution.
   (2) The full induction on Wt has not been carried out.  Its T_Var case
       exposes a design point that must still be settled: with the current
       "predicate on raw open terms" reading, [csem A E (var i)] tests the
       variable term itself rather than the value stored in the environment.
       A complete model should either (a) interpret terms under the syntactic
       substitution given by [sv_tm], or (b) strengthen EnvOk so that the
       entry's code semantics and the shifted type's semantics agree and add
       a level-monotonicity lemma (needed because T_Var changes the level via
       the inclusion [lk ⊆ l]).  The base cases (T_Zero/T_Suc/T_Nat/T_Unit/
       T_TT/T_Refl/T_Univ/T_Void) are guarded by [VoidFree]; the remaining
       eliminator cases need semantic obligations analogous to
       LetBodySem (for T_Ind, T_J and T_Seq). *)

(* The fundamental lemma implies the target consistency statement. *)
Lemma consistency_from_fundamental :
  FundamentalLemma -> forall (a : tm) (l : T), ~ (nil ⊢ a ; l ∈ tVoid).
Proof.
  intros FL a l H.
  apply (csem_void_elim l nil a).
  exact (FL nil l a tVoid H nil I).
Qed.



(* A tInd whose scrutinee is a variable cannot reduce to tVoid. *)
Lemma rtc_ind_var_head : forall (l : T) (a b d : tm),
  rtc Par (tInd l a b (var_tm 0)) d ->
  exists a' b' c', d = tInd l a' b' c'.
Proof.
  intros l a b d H.
  remember (tInd l a b (var_tm 0)) as t eqn:E.
  revert a b E.
  induction H as [t | t u d Htu Hud IH]; intros a b E; subst.
  - exists a, b, (var_tm 0); reflexivity.
  - destruct (Par_Ind_inv l a b (var_tm 0) u Htu) as
      [ [a' [b' [c' [Eu [Ha [Hb Hc]]]]]]
      | [ [a' [Ez _]] | [a1 [b1 [c0 [c1 [Es _]]]]] ] ].
    + subst u.
      apply (IH a' b').
      apply Par_Var_inv in Hc. subst c'. reflexivity.
    + discriminate Ez.
    + discriminate Es.
Qed.

Lemma VoidFree_ind_var : forall (l : T) (a b : tm),
  VoidFree (tInd l a b (var_tm 0)).
Proof.
  intros l a b H.
  destruct (rtc_ind_var_head l a b tVoid H) as [a' [b' [c' E]]].
  discriminate E.
Qed.

(* Formal counterexample to the current [SubstSem] obligation: the stub
   interpretation of tInd is unable to see that substituting [tSuc tZero] for
   the scrutinee variable produces a type reducing to tVoid. *)
Lemma SubstSem_counterexample :
  forall (l l0 : T) (u : tm),
    csem l (tInd l tNat tVoid (var_tm 0))
      (mkSV l0 (tSuc tZero) (Some (csem l0 (tSuc tZero) nil))
             (Some (fun x => csem l0 (tApp (tSuc tZero) l0 x) nil)) :: nil) u
    /\
    ~ csem l (tInd l tNat tVoid (tSuc tZero)) nil u.
Proof.
  intros l l0 u. split.
  - cbn [csem]. split; [apply VoidFree_ind_var | exact I].
  - intro H. cbn [csem] in H. destruct H as [HVF _].
    apply HVF.
    assert (Hred : rtc Par (tInd l tNat tVoid (tSuc tZero)) tVoid).
    { eapply rtc_l.
      - eapply (P_IndSuc l tNat tNat tVoid tVoid tZero tZero);
          apply Par_refl.
      - apply rtc_refl. }
    exact Hred.
Qed.


(* ================= relational NBE model (replaces the syntactic csem) ================= *)

Inductive Val : Type :=
| VVar (i : fin)
| VUniv (n : nat)
| VVoid | VUnit | VTT | VNat | VZero | VRefl
| VSuc (v : Val)
| VAbsurd (v : Val)
| VPi (l : T) (A : Val) (body : tm) (env : list Val)
| VAbs (l : T) (body : tm) (env : list Val)
| VApp (f : Val) (l : T) (x : Val)
| VSig (l : T) (A : Val) (body : tm) (env : list Val)
| VPack (l : T) (a b : Val)
| VEq (l : T) (a b : Val)
| VJ (l : T) (t p : Val)
| VLet (l0 l1 : T) (a : Val) (body : tm) (env : list Val)
| VInd (l : T) (a : Val) (body : tm) (env : list Val) (c : Val)
| VSeq (l : T) (a b : Val).

Inductive NeutralV : Val -> Prop :=
| NV_var (i : fin) : NeutralV (VVar i)
| NV_app (f : Val) (l : T) (x : Val) : NeutralV f -> NeutralV (VApp f l x)
| NV_ind (l : T) (a : Val) (body : tm) (env : list Val) (c : Val) :
    NeutralV c -> NeutralV (VInd l a body env c)
| NV_j (l : T) (t p : Val) : NeutralV p -> NeutralV (VJ l t p)
| NV_let (l0 l1 : T) (a : Val) (body : tm) (env : list Val) :
    NeutralV a -> NeutralV (VLet l0 l1 a body env)
| NV_seq (l : T) (a b : Val) : NeutralV a -> NeutralV (VSeq l a b).

Definition StuckCode (v : Val) : Prop :=
  NeutralV v /\ (forall i : fin, v <> VVar i).

Lemma StuckCode_neq_void : forall n : Val, StuckCode n -> n <> VVoid.
Proof. intros n [Hn _] E. subst n. inversion Hn. Qed.

Record NEnvEntry := {
  ee_val : Val;
  ee_code : Val -> Prop;
  ee_fam : Val -> Val -> Prop
}.
Definition empty_entry : NEnvEntry :=
  {| ee_val := VVoid; ee_code := fun _ => True; ee_fam := fun _ _ => True |}.
Definition NEnv := list NEnvEntry.

Definition eval_env (E : NEnv) : list Val := map ee_val E.

Lemma eval_env_cons : forall (e : NEnvEntry) (E : NEnv),
  eval_env (e :: E) = ee_val e :: eval_env E.
Proof. intros. reflexivity. Qed.

(* Relational evaluation and application: no Fixpoint, no fuel, closures are
   syntactic.  Beta/iota rules are relational premises, so termination is not
   needed. *)
Inductive Apply : T -> Val -> Val -> Val -> Prop :=
| Apply_abs : forall (l : T) (body : tm) (env : list Val) (x r : Val),
    Eval body (x :: env) r -> Apply l (VAbs l body env) x r
| Apply_abs_ne : forall (l l' : T) (body : tm) (env : list Val) (x : Val),
    l <> l' -> Apply l (VAbs l' body env) x (VApp (VAbs l' body env) l x)
| Apply_stuck : forall (l : T) (f x : Val),
    NeutralV f -> Apply l f x (VApp f l x)
with Eval : tm -> list Val -> Val -> Prop :=
| Eval_var : forall (i : fin) (env : list Val) (v : Val),
    nth_error env i = Some v -> Eval (var_tm i) env v
| Eval_univ : forall (n : nat) (env : list Val), Eval (tUniv n) env (VUniv n)
| Eval_void : forall env, Eval tVoid env VVoid
| Eval_unit : forall env, Eval tUnit env VUnit
| Eval_nat : forall env, Eval tNat env VNat
| Eval_tt : forall env, Eval tTT env VTT
| Eval_zero : forall env, Eval tZero env VZero
| Eval_suc : forall (a : tm) (env : list Val) (v : Val),
    Eval a env v -> Eval (tSuc a) env (VSuc v)
| Eval_refl : forall env, Eval tRefl env VRefl
| Eval_absurd : forall (a : tm) (env : list Val) (v : Val),
    Eval a env v -> Eval (tAbsurd a) env (VAbsurd v)
| Eval_pi : forall (l : T) (A B : tm) (env : list Val) (av : Val),
    Eval A env av -> Eval (tPi l A B) env (VPi l av B env)
| Eval_abs : forall (l : T) (a : tm) (env : list Val),
    Eval (tAbs l a) env (VAbs l a env)
| Eval_app : forall (f : tm) (l : T) (b : tm) (env : list Val)
    (fv bv r : Val),
    Eval f env fv -> Eval b env bv -> Apply l fv bv r ->
    Eval (tApp f l b) env r
| Eval_sig : forall (l : T) (A B : tm) (env : list Val) (av : Val),
    Eval A env av -> Eval (tSig l A B) env (VSig l av B env)
| Eval_pack : forall (l : T) (a b : tm) (env : list Val) (av bv : Val),
    Eval a env av -> Eval b env bv -> Eval (tPack l a b) env (VPack l av bv)
| Eval_eq : forall (l : T) (a b : tm) (env : list Val) (av bv : Val),
    Eval a env av -> Eval b env bv -> Eval (tEq l a b) env (VEq l av bv)
| Eval_j : forall (l : T) (t p : tm) (env : list Val) (tv pv r : Val),
    Eval t env tv -> Eval p env pv -> JEval l tv pv r ->
    Eval (tJ l t p) env r
| Eval_let : forall (l0 l1 : T) (a b : tm) (env : list Val) (av r : Val),
    Eval a env av -> LetEval l0 l1 av b env r ->
    Eval (tLet l0 l1 a b) env r
| Eval_tind : forall (l : T) (a b c : tm) (env : list Val) (av cv r : Val),
    Eval a env av -> Eval c env cv -> IndEval l av b env cv r ->
    Eval (tInd l a b c) env r
| Eval_seq : forall (l : T) (a b : tm) (env : list Val) (av bv r : Val),
    Eval a env av -> Eval b env bv -> SeqEval l av bv r ->
    Eval (tSeq l a b) env r
with IndEval : T -> Val -> tm -> list Val -> Val -> Val -> Prop :=
| Ind_zero : forall (l : T) (av : Val) (b : tm) (env : list Val),
    IndEval l av b env VZero av
| Ind_suc : forall (l : T) (av : Val) (b : tm) (env : list Val)
    (cv rrec r : Val),
    IndEval l av b env cv rrec ->
    Eval b (rrec :: cv :: env) r ->
    IndEval l av b env (VSuc cv) r
| Ind_stuck : forall (l : T) (av : Val) (b : tm) (env : list Val) (cv : Val),
    StuckCode cv -> IndEval l av b env cv (VInd l av b env cv)
with JEval : T -> Val -> Val -> Val -> Prop :=
| J_refl : forall (l : T) (tv : Val), JEval l tv VRefl tv
| J_stuck : forall (l : T) (tv pv : Val),
    StuckCode pv -> JEval l tv pv (VJ l tv pv)
with LetEval : T -> T -> Val -> tm -> list Val -> Val -> Prop :=
| Let_pack : forall (l0 l1 : T) (av bv : Val) (body : tm) (env : list Val)
    (r : Val),
    Eval body (bv :: av :: env) r ->
    LetEval l0 l1 (VPack l0 av bv) body env r
| Let_pack_ne : forall (l0 l1 l0' : T) (av bv : Val) (body : tm)
    (env : list Val),
    l0 <> l0' ->
    LetEval l0 l1 (VPack l0' av bv) body env
      (VLet l0 l1 (VPack l0' av bv) body env)
| Let_stuck : forall (l0 l1 : T) (av : Val) (body : tm) (env : list Val),
    StuckCode av -> LetEval l0 l1 av body env (VLet l0 l1 av body env)
with SeqEval : T -> Val -> Val -> Val -> Prop :=
| Seq_tt : forall (l : T) (bv : Val), SeqEval l VTT bv bv
| Seq_stuck : forall (l : T) (av bv : Val),
    StuckCode av -> SeqEval l av bv (VSeq l av bv).

(* NOTE: Rocq 9.1.0's [Combined Scheme] hits an anomaly
   ("decompose_prod_n: not enough products") when the non-recursive J/Seq
   relations are included in the combination.  The four recursive relations
   combine correctly; J and Seq determinacy are proved separately below. *)
Scheme Apply_ind2 := Induction for Apply Sort Prop
  with Eval_ind2 := Induction for Eval Sort Prop
  with IndEval_ind2 := Induction for IndEval Sort Prop
  with LetEval_ind2 := Induction for LetEval Sort Prop.

Combined Scheme Eval_mutual4 from
  Apply_ind2, Eval_ind2, IndEval_ind2, LetEval_ind2.

(* J and Seq have no recursive premises; their determinacy is independent of
   the four-way mutual induction. *)
Lemma JEval_det : forall (l : T) (tv pv r : Val),
  JEval l tv pv r -> forall r', JEval l tv pv r' -> r = r'.
Proof.
  intros l tv pv r H. induction H as [l tv | l tv pv Hs]; intros r' H'.
  - inversion H'; subst; try reflexivity.
    exfalso. match goal with Hn : StuckCode ?x |- _ =>
      destruct Hn as [Hnv _]; inversion Hnv end.
  - inversion H'; subst; try reflexivity.
    exfalso. match goal with Hn : StuckCode ?x |- _ =>
      destruct Hn as [Hnv _]; inversion Hnv end.
Qed.

Lemma SeqEval_det : forall (l : T) (av bv r : Val),
  SeqEval l av bv r -> forall r', SeqEval l av bv r' -> r = r'.
Proof.
  intros l av bv r H. induction H as [l bv | l av bv Hs]; intros r' H'.
  - inversion H'; subst; try reflexivity.
    exfalso. match goal with Hn : StuckCode ?x |- _ =>
      destruct Hn as [Hnv _]; inversion Hnv end.
  - inversion H'; subst; try reflexivity.
    exfalso. match goal with Hn : StuckCode ?x |- _ =>
      destruct Hn as [Hnv _]; inversion Hnv end.
Qed.

(* Impredicative Prop-valued type semantics: the least relation closed under
   the negative/realizability clauses.  Pi and Sig are negative (no data
   extraction); Void has no introduction rule.  The [if] in the Pi clause is
   the semantic GI_InDist irrelevance condition. *)
Definition TySemClosure (R : T -> NEnv -> Val -> Val -> Prop) : Prop :=
  (forall (l : T) (E : NEnv) (i : fin) (v : Val),
      ee_code (nth i E empty_entry) v -> R l E (VVar i) v) /\
  (forall (l : T) (E : NEnv) (n : nat) (v : Val),
      R l E (VUniv n) v) /\
  (forall (l : T) (E : NEnv) (v : Val),
      v <> VVoid -> R l E VUnit v) /\
  (forall (l : T) (E : NEnv) (v : Val),
      v <> VVoid -> R l E VNat v) /\
  (forall (l : T) (E : NEnv) (l0 : T) (a b : Val) (v : Val),
      v <> VVoid -> R l E (VEq l0 a b) v) /\
  (forall (l : T) (E : NEnv) (l0 : T) (A : Val) (body : tm) (env : list Val)
      (f : Val),
      f <> VVoid ->
      (forall (x : Val) (e : NEnvEntry),
          ee_val e = x ->
          R l0 E A x ->
          exists (r Bv : Val),
            Apply l0 f x r /\
            Eval body (x :: env) Bv /\
            (forall (Bv' : Val),
                Eval body (x :: env) Bv' -> R l (e :: E) Bv' r)) ->
      (if T_eqb (l0 ∩ l) l0 then True
       else forall (x1 x2 : Val) (e1 e2 : NEnvEntry) (B1 B2 : Val),
           ee_val e1 = x1 -> ee_val e2 = x2 ->
           R l0 E A x1 -> R l0 E A x2 ->
           Eval body (x1 :: env) B1 -> Eval body (x2 :: env) B2 ->
           forall u : Val, R l (e1 :: E) B1 u <-> R l (e2 :: E) B2 u) ->
      R l E (VPi l0 A body env) f) /\
  (forall (l : T) (E : NEnv) (l0 : T) (A : Val) (body : tm) (env : list Val)
      (p : Val),
      (forall P : Val -> Prop,
          (forall (x y : Val) (ex ey : NEnvEntry),
              ee_val ex = x -> ee_val ey = y ->
              R l0 E A x ->
              forall (Bv : Val),
                Eval body (x :: env) Bv -> R l (ex :: E) Bv y ->
                P (VPack l0 x y)) ->
          P p) ->
      R l E (VSig l0 A body env) p) /\
  (forall (l : T) (E : NEnv) (n v : Val),
      StuckCode n -> R l E n v).

Definition TySem (l : T) (E : NEnv) (A v : Val) : Prop :=
  forall R : T -> NEnv -> Val -> Val -> Prop,
    TySemClosure R -> R l E A v.

Definition R0 : T -> NEnv -> Val -> Val -> Prop :=
  fun _ _ A _ => A <> VVoid.

Lemma TySemClosure_R0 : TySemClosure R0.
Proof.
  unfold TySemClosure, R0.
  repeat split; intros; try discriminate.
  apply StuckCode_neq_void. exact H.
Qed.

Lemma TySem_void_absurd : forall (l : T) (E : NEnv) (v : Val),
  TySem l E VVoid v -> False.
Proof.
  intros l E v H. exact (H R0 TySemClosure_R0 eq_refl).
Qed.

Lemma Eval_void_inv : forall (env : list Val) (v : Val),
  Eval tVoid env v -> v = VVoid.
Proof. intros env v H. inversion H. reflexivity. Qed.

Fixpoint NEnvOk (G : context) (E : NEnv) {struct G} : Prop :=
  match G, E with
  | nil, nil => True
  | (l0, A) :: G', e :: E' =>
      NEnvOk G' E' /\
      (exists av, Eval A (eval_env E') av /\ TySem l0 E' av (ee_val e))
  | _, _ => False
  end.

Definition NBEFundamentalLemma : Prop :=
  forall (G : context) (l : T) (a A : tm) (H : Wt G l a A) (E : NEnv),
    NEnvOk G E ->
    exists av v, Eval A (eval_env E) av /\ Eval a (eval_env E) v
                 /\ TySem l E av v.

(* Verified semantic helpers for the base type formers. *)
Lemma TySem_univ : forall (l : T) (E : NEnv) (n : nat) (v : Val),
  TySem l E (VUniv n) v.
Proof.
  intros l E n v. unfold TySem. intros R HR.
  destruct HR as [Hvar [Huniv [Hunit [Hnat [Heq [Hpi [Hsig Hstuck]]]]]]].
  apply Huniv.
Qed.

Lemma TySem_unit : forall (l : T) (E : NEnv) (v : Val),
  v <> VVoid -> TySem l E VUnit v.
Proof.
  intros l E v Hv. unfold TySem. intros R HR.
  destruct HR as [Hvar [Huniv [Hunit [Hnat [Heq [Hpi [Hsig Hstuck]]]]]]].
  apply Hunit. exact Hv.
Qed.

Lemma TySem_nat : forall (l : T) (E : NEnv) (v : Val),
  v <> VVoid -> TySem l E VNat v.
Proof.
  intros l E v Hv. unfold TySem. intros R HR.
  destruct HR as [Hvar [Huniv [Hunit [Hnat [Heq [Hpi [Hsig Hstuck]]]]]]].
  apply Hnat. exact Hv.
Qed.

Lemma TySem_eq : forall (l : T) (E : NEnv) (l0 : T) (a b v : Val),
  v <> VVoid -> TySem l E (VEq l0 a b) v.
Proof.
  intros l E l0 a b v Hv. unfold TySem. intros R HR.
  destruct HR as [Hvar [Huniv [Hunit [Hnat [Heq [Hpi [Hsig Hstuck]]]]]]].
  apply Heq. exact Hv.
Qed.

Lemma Eval_nat_inv : forall (env : list Val) (v : Val),
  Eval tNat env v -> v = VNat.
Proof. intros env v H. inversion H. reflexivity. Qed.

Lemma Eval_unit_inv : forall (env : list Val) (v : Val),
  Eval tUnit env v -> v = VUnit.
Proof. intros env v H. inversion H. reflexivity. Qed.

Lemma Eval_univ_inv : forall (i : nat) (env : list Val) (v : Val),
  Eval (tUniv i) env v -> v = VUniv i.
Proof. intros i env v H. inversion H. reflexivity. Qed.

Lemma Eval_pi_inv : forall (l : T) (A B : tm) (env : list Val) (v : Val),
  Eval (tPi l A B) env v ->
  exists av, v = VPi l av B env /\ Eval A env av.
Proof. intros l A B env v H. inversion H. eauto. Qed.

(* Easy cases of the NBE fundamental lemma.  These are the rules whose
   conclusion is a base type or a type constructor at a universe; no
   environment weakening or hereditary substitution is needed. *)

Lemma nbe_T_Void : forall (G : context) (l : T) (i : nat) (E : NEnv),
  NEnvOk G E ->
  exists av v, Eval (tUniv i) (eval_env E) av /\
              Eval tVoid (eval_env E) v /\ TySem l E av v.
Proof.
  intros G l i E _. exists (VUniv i), VVoid.
  split; [apply Eval_univ | split; [apply Eval_void | apply TySem_univ]].
Qed.

Lemma nbe_T_Univ : forall (G : context) (l : T) (i : nat) (E : NEnv),
  NEnvOk G E ->
  exists av v, Eval (tUniv (S i)) (eval_env E) av /\
              Eval (tUniv i) (eval_env E) v /\ TySem l E av v.
Proof.
  intros G l i E _. exists (VUniv (S i)), (VUniv i).
  split; [apply Eval_univ | split; [apply Eval_univ | apply TySem_univ]].
Qed.

Lemma nbe_T_Nat : forall (G : context) (l : T) (i : nat) (E : NEnv),
  NEnvOk G E ->
  exists av v, Eval (tUniv i) (eval_env E) av /\
              Eval tNat (eval_env E) v /\ TySem l E av v.
Proof.
  intros G l i E _. exists (VUniv i), VNat.
  split; [apply Eval_univ | split; [apply Eval_nat | apply TySem_univ]].
Qed.

Lemma nbe_T_Unit : forall (G : context) (l : T) (i : nat) (E : NEnv),
  NEnvOk G E ->
  exists av v, Eval (tUniv i) (eval_env E) av /\
              Eval tUnit (eval_env E) v /\ TySem l E av v.
Proof.
  intros G l i E _. exists (VUniv i), VUnit.
  split; [apply Eval_univ | split; [apply Eval_unit | apply TySem_univ]].
Qed.

Lemma nbe_T_TT : forall (G : context) (l : T) (E : NEnv),
  NEnvOk G E ->
  exists av v, Eval tUnit (eval_env E) av /\
              Eval tTT (eval_env E) v /\ TySem l E av v.
Proof.
  intros G l E _. exists VUnit, VTT.
  split; [apply Eval_unit | split; [apply Eval_tt | apply TySem_unit; discriminate]].
Qed.

Lemma nbe_T_Zero : forall (G : context) (l : T) (E : NEnv),
  NEnvOk G E ->
  exists av v, Eval tNat (eval_env E) av /\
              Eval tZero (eval_env E) v /\ TySem l E av v.
Proof.
  intros G l E _. exists VNat, VZero.
  split; [apply Eval_nat | split; [apply Eval_zero | apply TySem_nat; discriminate]].
Qed.

Lemma nbe_T_Suc : forall (G : context) (l : T) (a : tm),
  (forall E : NEnv, NEnvOk G E ->
     exists av v, Eval tNat (eval_env E) av /\
                 Eval a (eval_env E) v /\ TySem l E av v) ->
  forall E : NEnv, NEnvOk G E ->
     exists av v, Eval tNat (eval_env E) av /\
                 Eval (tSuc a) (eval_env E) v /\ TySem l E av v.
Proof.
  intros G l a IH E HE.
  destruct (IH E HE) as [av [v [HA [Ha _]]]].
  assert (av = VNat) by (apply (Eval_nat_inv (eval_env E) av); exact HA).
  subst av. exists VNat, (VSuc v).
  split; [apply Eval_nat | split; [apply Eval_suc; exact Ha | apply TySem_nat; discriminate]].
Qed.

Lemma nbe_T_Absurd : forall (G : context) (l l0 : T) (a A : tm),
  (forall E : NEnv, NEnvOk G E ->
     exists av v, Eval tVoid (eval_env E) av /\
                 Eval a (eval_env E) v /\ TySem l0 E av v) ->
  forall E : NEnv, NEnvOk G E ->
     exists av v, Eval A (eval_env E) av /\
                 Eval (tAbsurd a) (eval_env E) v /\ TySem l E av v.
Proof.
  intros G l l0 a A IH E HE.
  destruct (IH E HE) as [av [v [HA [Ha HT]]]].
  assert (av = VVoid) by (apply (Eval_void_inv (eval_env E) av); exact HA).
  subst av. exfalso.
  exact (TySem_void_absurd l0 E v HT).
Qed.

Lemma nbe_T_Pi : forall (G : context) (l : T) (i j : nat) (l0 : T) (A B : tm),
  (forall E : NEnv, NEnvOk G E ->
     exists av v, Eval (tUniv i) (eval_env E) av /\
                 Eval A (eval_env E) v /\ TySem l E av v) ->
  (forall E : NEnv, NEnvOk ((l0, A) :: G) E ->
     exists av v, Eval (tUniv j) (eval_env E) av /\
                 Eval B (eval_env E) v /\ TySem l E av v) ->
  forall E : NEnv, NEnvOk G E ->
     exists av v, Eval (tUniv (max i j)) (eval_env E) av /\
                 Eval (tPi l0 A B) (eval_env E) v /\ TySem l E av v.
Proof.
  intros G l i j l0 A B IHA IHB E HE.
  destruct (IHA E HE) as [avA [vA [EA [HA HT]]]].
  exists (VUniv (max i j)), (VPi l0 vA B (eval_env E)).
  split; [apply Eval_univ | split].
  - apply (Eval_pi l0 A B (eval_env E) vA). exact HA.
  - apply TySem_univ.
Qed.

Lemma nbe_T_Sig : forall (G : context) (l : T) (i j : nat) (l0 : T) (A B : tm),
  (forall E : NEnv, NEnvOk G E ->
     exists av v, Eval (tUniv i) (eval_env E) av /\
                 Eval A (eval_env E) v /\ TySem l E av v) ->
  (forall E : NEnv, NEnvOk ((l0, A) :: G) E ->
     exists av v, Eval (tUniv j) (eval_env E) av /\
                 Eval B (eval_env E) v /\ TySem l E av v) ->
  forall E : NEnv, NEnvOk G E ->
     exists av v, Eval (tUniv (max i j)) (eval_env E) av /\
                 Eval (tSig l0 A B) (eval_env E) v /\ TySem l E av v.
Proof.
  intros G l i j l0 A B IHA IHB E HE.
  destruct (IHA E HE) as [avA [vA [EA [HA HT]]]].
  exists (VUniv (max i j)), (VSig l0 vA B (eval_env E)).
  split; [apply Eval_univ | split].
  - apply (Eval_sig l0 A B (eval_env E) vA). exact HA.
  - apply TySem_univ.
Qed.

(* ---------- explicit NBE obligations ---------- *)

(* Determinacy of the relational evaluator on the value domain. *)
Definition EvalDetObligation : Prop :=
  forall (a : tm) (env : list Val) (v v' : Val),
    Eval a env v -> Eval a env v' -> v = v'.

Definition Det4Obligation : Prop :=
  (forall (l : T) (f x r : Val),
     Apply l f x r -> forall r', Apply l f x r' -> r = r') /\
  (forall (a : tm) (env : list Val) (v : Val),
     Eval a env v -> forall v', Eval a env v' -> v = v') /\
  (forall (l : T) (av : Val) (b : tm) (env : list Val) (cv r : Val),
     IndEval l av b env cv r -> forall r',
       IndEval l av b env cv r' -> r = r') /\
  (forall (l0 l1 : T) (av : Val) (body : tm) (env : list Val) (r : Val),
     LetEval l0 l1 av body env r -> forall r',
       LetEval l0 l1 av body env r' -> r = r').

Lemma EvalDet_of_Det4 : Det4Obligation -> EvalDetObligation.
Proof.
  intros H4. destruct H4 as [HA [HE HC]].
  intros a env v v' He He'. exact (HE a env v He v' He').
Qed.

(* NBE Pi introduction (the closure of TySem at Pi codes). *)
Definition PiIntroObligation : Prop :=
  forall (l : T) (E : NEnv) (l0 : T) (A : Val) (body : tm) (env : list Val)
    (f : Val),
    f <> VVoid ->
    (forall (x : Val) (e : NEnvEntry),
        ee_val e = x ->
        TySem l0 E A x ->
        exists (r Bv : Val),
          Apply l0 f x r /\
          Eval body (x :: env) Bv /\
          (forall (Bv' : Val),
              Eval body (x :: env) Bv' -> TySem l (e :: E) Bv' r)) ->
    (if T_eqb (l0 ∩ l) l0 then True
     else forall (x1 x2 : Val) (e1 e2 : NEnvEntry) (B1 B2 : Val),
         ee_val e1 = x1 -> ee_val e2 = x2 ->
         TySem l0 E A x1 -> TySem l0 E A x2 ->
         Eval body (x1 :: env) B1 -> Eval body (x2 :: env) B2 ->
         forall u : Val,
           TySem l (e1 :: E) B1 u <-> TySem l (e2 :: E) B2 u) ->
    TySem l E (VPi l0 A body env) f.

(* NBE Pi elimination (totality of application and of the type family). *)
Definition PiElimObligation : Prop :=
  forall (l : T) (E : NEnv) (l0 : T) (A : Val) (body : tm) (env : list Val)
    (f x : Val) (e : NEnvEntry),
    TySem l E (VPi l0 A body env) f ->
    ee_val e = x ->
    TySem l0 E A x ->
    exists (r Bv : Val),
      Apply l0 f x r /\
      Eval body (x :: env) Bv /\
      (forall (Bv' : Val),
          Eval body (x :: env) Bv' -> TySem l (e :: E) Bv' r).

(* Hereditary substitution / value PER for type codes: the value of a type
   family at an environment extension agrees with the value of its
   substitution instance at the base environment. *)
Definition TySubstObligation : Prop :=
  forall (l l0 : T) (E : NEnv) (A : Val) (b : tm) (bv : Val)
         (B : tm) (Bv r : Val) (e : NEnvEntry),
    ee_val e = bv ->
    TySem l0 E A bv ->
    Eval b (eval_env E) bv ->
    Eval B (bv :: eval_env E) Bv ->
    TySem l (e :: E) Bv r ->
    exists B', Eval (B[b..]) (eval_env E) B' /\ TySem l E B' r.

(* Semantic GI_InDist irrelevance for the Pi codomain. *)
Definition TySemIrrelObligation : Prop :=
  forall (l l0 : T) (E : NEnv) (A : Val) (B : tm) (env : list Val),
    ~ (l0 ⊆ l) ->
    forall (x1 x2 : Val) (e1 e2 : NEnvEntry) (B1 B2 : Val),
      ee_val e1 = x1 -> ee_val e2 = x2 ->
      TySem l0 E A x1 -> TySem l0 E A x2 ->
      Eval B (x1 :: env) B1 -> Eval B (x2 :: env) B2 ->
      forall u : Val,
        TySem l (e1 :: E) B1 u <-> TySem l (e2 :: E) B2 u.

Lemma nth_error_map_gen : forall (A B : Type) (f : A -> B) (l : list A) (i : nat),
  nth_error (map f l) i =
  match nth_error l i with Some x => Some (f x) | None => None end.
Proof.
  intros A B f l. induction l as [|x xs IH]; intro i; destruct i; simpl; auto.
Qed.

Lemma nth_error_map_ee : forall (E : NEnv) (i : fin) (e : NEnvEntry),
  nth_error E i = Some e -> nth_error (eval_env E) i = Some (ee_val e).
Proof.
  intros E i e H. unfold eval_env. rewrite nth_error_map_gen. rewrite H. reflexivity.
Qed.

(* Environment lookup obligation for T_Var. *)
Definition NEnvOk_lookup_obligation : Prop :=
  forall (G : context) (E : NEnv) (i : fin) (l0 : T) (A : tm),
    lookup i G l0 A -> NEnvOk G E ->
    exists (e : NEnvEntry) (av : Val),
      nth_error E i = Some e /\ Eval A (eval_env E) av /\ TySem l0 E av (ee_val e).

(* Level monotonicity of the semantics. *)
Definition TySem_mono_obligation : Prop :=
  forall (l l' : T) (E : NEnv) (A v : Val),
    l ⊆ l' -> TySem l E A v -> TySem l' E A v.

(* Conditional T_Var case. *)
Lemma nbe_T_Var_case :
  NEnvOk_lookup_obligation -> TySem_mono_obligation ->
  forall (G : context) (l0 l : T) (i : fin) (A : tm) (E : NEnv),
    lookup i G l0 A -> l0 ⊆ l -> NEnvOk G E ->
    exists av v, Eval A (eval_env E) av /\
                Eval (var_tm i) (eval_env E) v /\ TySem l E av v.
Proof.
  intros LK MONO G l0 l i A E Hlk Hsub HE.
  destruct (LK G E i l0 A Hlk HE) as [e [av [Hnth [HA HT]]]].
  exists av, (ee_val e). split; [exact HA | split].
  - eapply Eval_var. apply nth_error_map_ee. exact Hnth.
  - eapply MONO; [exact Hsub | exact HT].
Qed.

(* Conditional T_Abs case.  The body hypothesis is the "functional" semantic
   form: a value of the body together with its membership in *every* value of
   the codomain type that the type family can evaluate to.  This is what a
   complete fundamental-lemma induction establishes for the body premise. *)
Lemma nbe_T_Abs_case :
  TySemIrrelObligation -> PiIntroObligation ->
  forall (G : context) (l l1 : T) (l0 : T) (i : nat) (a : tm) (A B : tm),
    (forall E : NEnv, NEnvOk G E ->
       exists av v, Eval (tUniv i) (eval_env E) av /\
                   Eval (tPi l0 A B) (eval_env E) v /\ TySem l1 E av v) ->
    (forall E : NEnv, NEnvOk ((l0, A) :: G) E ->
       exists vB avB, Eval B (eval_env E) avB /\
                     Eval a (eval_env E) vB /\
                     (forall Bv', Eval B (eval_env E) Bv' ->
                                  TySem l E Bv' vB)) ->
    forall E : NEnv, NEnvOk G E ->
       exists av v, Eval (tPi l0 A B) (eval_env E) av /\
                   Eval (tAbs l0 a) (eval_env E) v /\ TySem l E av v.
Proof.
  intros IRR INTRO G l l1 l0 i a A B IHpi IHbody E HE.
  destruct (IHpi E HE) as [avpi [vpi [Euniv [Epi HTpi]]]].
  assert (Hex : exists avA, vpi = VPi l0 avA B (eval_env E) /\
                            Eval A (eval_env E) avA)
    by (apply (Eval_pi_inv l0 A B (eval_env E) vpi); exact Epi).
  destruct Hex as [avA [Evpi EA]]. subst vpi.
  exists (VPi l0 avA B (eval_env E)), (VAbs l0 a (eval_env E)).
  split; [exact Epi | split; [apply Eval_abs |]].
  apply INTRO.
  - discriminate.
  - intros x e Hexe HA.
    assert (HNE : NEnvOk ((l0, A) :: G) (e :: E)).
    { split; [exact HE | exists avA; split; [exact EA | rewrite Hexe; exact HA]]. }
    destruct (IHbody (e :: E) HNE) as [vB [avB [EB [Ea Hcod]]]].
    assert (EBx : Eval B (x :: eval_env E) avB).
    { rewrite <- Hexe. rewrite <- eval_env_cons. exact EB. }
    exists vB, avB. split.
    + apply (Apply_abs l0 a (eval_env E) x vB).
      rewrite <- Hexe. exact Ea.
    + split; [exact EBx |].
      intros Bv' EBv'.
      apply (Hcod Bv').
      rewrite eval_env_cons. rewrite Hexe. exact EBv'.
  - destruct (T_eqb (l0 ∩ l) l0) eqn:Eb.
    + exact I.
    + assert (Hn : ~ (l0 ∩ l = l0))
        by (intro He; rewrite He in Eb; rewrite T_eqb_refl in Eb; discriminate Eb).
      exact (IRR l l0 E avA B (eval_env E) Hn).
Qed.

(* Conditional T_App case. *)
Lemma nbe_T_App_case :
  EvalDetObligation -> PiElimObligation -> TySubstObligation ->
  forall (G : context) (l l0 : T) (f : tm) (A B b : tm),
    (forall E : NEnv, NEnvOk G E ->
       exists av v, Eval (tPi l0 A B) (eval_env E) av /\
                   Eval f (eval_env E) v /\ TySem l E av v) ->
    (forall E : NEnv, NEnvOk G E ->
       exists av v, Eval A (eval_env E) av /\
                   Eval b (eval_env E) v /\ TySem l0 E av v) ->
    forall E : NEnv, NEnvOk G E ->
       exists av v, Eval (B[b..]) (eval_env E) av /\
                   Eval (tApp f l0 b) (eval_env E) v /\ TySem l E av v.
Proof.
  intros DET PIEL SUB G l l0 f A B b IHf IHb E HE.
  destruct (IHf E HE) as [avF [vF [EF [Ef HTf]]]].
  assert (Hex : exists avA, avF = VPi l0 avA B (eval_env E) /\
                            Eval A (eval_env E) avA)
    by (apply (Eval_pi_inv l0 A B (eval_env E) avF); exact EF).
  destruct Hex as [avA [EvF EA]]. subst avF.
  destruct (IHb E HE) as [avb [vb [EAb [Eb HTb]]]].
  assert (avA = avb)
    by (apply (DET A (eval_env E) avA avb); [exact EA | exact EAb]).
  subst avb.
  set (e := {| ee_val := vb; ee_code := fun _ => True; ee_fam := fun _ _ => True |}).
  destruct (PIEL l E l0 avA B (eval_env E) vF vb e HTf eq_refl HTb)
    as [r [Bv [HApp [EBv Hcod]]]].
  destruct (SUB l l0 E avA b vb B Bv r e eq_refl HTb Eb EBv (Hcod Bv EBv))
    as [B' [EB' HT']].
  exists B', r. split; [exact EB' | split].
  - eapply Eval_app; [exact Ef | exact Eb | exact HApp].
  - exact HT'.
Qed.

(* The obligations remaining for a full NBE fundamental lemma. *)
Definition NBERemainingObligations : Prop :=
  EvalDetObligation /\ PiIntroObligation /\ PiElimObligation /\
  TySubstObligation /\ TySemIrrelObligation /\
  NEnvOk_lookup_obligation /\ TySem_mono_obligation.

Lemma NEnvOk_nil_nil : NEnvOk nil nil.
Proof. simpl. exact I. Qed.

Lemma nbe_consistency_from_fundamental :
  NBEFundamentalLemma -> forall (a : tm) (l : T), ~ (nil ⊢ a ; l ∈ tVoid).
Proof.
  intros FL a l H.
  destruct (FL nil l a tVoid H nil NEnvOk_nil_nil)
    as [av [v [HA [Ha HT]]]].
  assert (av = VVoid) by (apply (Eval_void_inv (eval_env nil) av); exact HA).
  subst av.
  exact (TySem_void_absurd l nil v HT).
Qed.


(* ================= step-indexed value semantics ================= *)

(* [TySemN n l E code x] is the step-indexed type semantics: recursion is on
   the step index [n] only.  At index 0 every code except VVoid is universal;
   at [S k] the Pi/Sig clauses refer to [k].  This avoids both the impredicative
   closure and the Prop/Type-elimination restrictions. *)
Fixpoint TySemN (n : nat) (l : T) (E : NEnv) (code x : Val) {struct n} : Prop :=
  match n with
  | 0 => code <> VVoid
  | S k =>
      match code with
      | VVoid => False
      | VUnit => x <> VVoid
      | VNat => x <> VVoid
      | VEq _ _ _ => x <> VVoid
      | VUniv _ => True
      | VVar i => ee_code (nth i E empty_entry) x
      | VPi l0 A body envT =>
          (forall (arg : Val) (e : NEnvEntry),
              ee_val e = arg ->
              TySemN k l0 E A arg ->
              exists (r Bv : Val),
                Apply l0 code arg r /\
                Eval body (arg :: envT) Bv /\
                (forall (Bv' : Val),
                    Eval body (arg :: envT) Bv' -> TySemN k l (e :: E) Bv' r))
          /\
          (if T_eqb (l0 ∩ l) l0 then True
           else forall (arg1 arg2 : Val) (e1 e2 : NEnvEntry) (B1 B2 : Val),
               ee_val e1 = arg1 -> ee_val e2 = arg2 ->
               TySemN k l0 E A arg1 -> TySemN k l0 E A arg2 ->
               Eval body (arg1 :: envT) B1 -> Eval body (arg2 :: envT) B2 ->
               forall u : Val,
                 TySemN k l (e1 :: E) B1 u <-> TySemN k l (e2 :: E) B2 u)
      | VSig l0 A body envT =>
          (forall P : Val -> Prop,
              (forall (a b : Val) (ea eb : NEnvEntry),
                  ee_val ea = a -> ee_val eb = b ->
                  TySemN k l0 E A a ->
                  forall Bv : Val,
                    Eval body (a :: envT) Bv -> TySemN k l (ea :: E) Bv b ->
                    P (VPack l0 a b)) ->
              P code)
      | _ => x <> VVoid
      end
  end.

Fixpoint EnvOkN (n : nat) (G : context) (E : NEnv) {struct G} : Prop :=
  match G, E with
  | nil, nil => True
  | (l0, A) :: G', e :: E' =>
      EnvOkN n G' E' /\
      (exists Av, Eval A (eval_env E') Av /\ TySemN n l0 E' Av (ee_val e))
  | _, _ => False
  end.

Lemma TySemN_univ : forall (n : nat) (l : T) (E : NEnv) (m : nat) (x : Val),
  TySemN n l E (VUniv m) x.
Proof. intros n l E m x. destruct n; simpl; [discriminate | exact I]. Qed.

Lemma TySemN_unit : forall (n : nat) (l : T) (E : NEnv) (v : Val),
  v <> VVoid -> TySemN n l E VUnit v.
Proof. intros n l E v Hv. destruct n; simpl; [discriminate | exact Hv]. Qed.

Lemma TySemN_nat : forall (n : nat) (l : T) (E : NEnv) (v : Val),
  v <> VVoid -> TySemN n l E VNat v.
Proof. intros n l E v Hv. destruct n; simpl; [discriminate | exact Hv]. Qed.

Lemma TySemN_eq : forall (n : nat) (l : T) (E : NEnv) (l0 : T) (a b v : Val),
  v <> VVoid -> TySemN n l E (VEq l0 a b) v.
Proof. intros n l E l0 a b v Hv. destruct n; simpl; [discriminate | exact Hv]. Qed.

Lemma TySemN_void_absurd : forall (n : nat) (l : T) (E : NEnv) (x : Val),
  TySemN n l E VVoid x -> False.
Proof.
  intros n l E x H. destruct n; simpl in H.
  - apply H; reflexivity.
  - exact H.
Qed.

(* Easy cases of the step-indexed fundamental lemma, valid at every index. *)

Lemma nbeN_T_Void : forall (n : nat) (G : context) (l : T) (i : nat) (E : NEnv),
  EnvOkN n G E ->
  exists Av v, Eval (tUniv i) (eval_env E) Av /\
              Eval tVoid (eval_env E) v /\ TySemN n l E Av v.
Proof.
  intros n G l i E _. exists (VUniv i), VVoid.
  split; [apply Eval_univ | split; [apply Eval_void | apply TySemN_univ]].
Qed.

Lemma nbeN_T_Univ : forall (n : nat) (G : context) (l : T) (i : nat) (E : NEnv),
  EnvOkN n G E ->
  exists Av v, Eval (tUniv (S i)) (eval_env E) Av /\
              Eval (tUniv i) (eval_env E) v /\ TySemN n l E Av v.
Proof.
  intros n G l i E _. exists (VUniv (S i)), (VUniv i).
  split; [apply Eval_univ | split; [apply Eval_univ | apply TySemN_univ]].
Qed.

Lemma nbeN_T_Nat : forall (n : nat) (G : context) (l : T) (i : nat) (E : NEnv),
  EnvOkN n G E ->
  exists Av v, Eval (tUniv i) (eval_env E) Av /\
              Eval tNat (eval_env E) v /\ TySemN n l E Av v.
Proof.
  intros n G l i E _. exists (VUniv i), VNat.
  split; [apply Eval_univ | split; [apply Eval_nat | apply TySemN_univ]].
Qed.

Lemma nbeN_T_Unit : forall (n : nat) (G : context) (l : T) (i : nat) (E : NEnv),
  EnvOkN n G E ->
  exists Av v, Eval (tUniv i) (eval_env E) Av /\
              Eval tUnit (eval_env E) v /\ TySemN n l E Av v.
Proof.
  intros n G l i E _. exists (VUniv i), VUnit.
  split; [apply Eval_univ | split; [apply Eval_unit | apply TySemN_univ]].
Qed.

Lemma nbeN_T_TT : forall (n : nat) (G : context) (l : T) (E : NEnv),
  EnvOkN n G E ->
  exists Av v, Eval tUnit (eval_env E) Av /\
              Eval tTT (eval_env E) v /\ TySemN n l E Av v.
Proof.
  intros n G l E _. exists VUnit, VTT.
  split; [apply Eval_unit | split; [apply Eval_tt | apply TySemN_unit; discriminate]].
Qed.

Lemma nbeN_T_Zero : forall (n : nat) (G : context) (l : T) (E : NEnv),
  EnvOkN n G E ->
  exists Av v, Eval tNat (eval_env E) Av /\
              Eval tZero (eval_env E) v /\ TySemN n l E Av v.
Proof.
  intros n G l E _. exists VNat, VZero.
  split; [apply Eval_nat | split; [apply Eval_zero | apply TySemN_nat; discriminate]].
Qed.

Lemma nbeN_T_Suc : forall (n : nat) (G : context) (l : T) (a : tm),
  (forall E : NEnv, EnvOkN n G E ->
     exists Av v, Eval tNat (eval_env E) Av /\
                 Eval a (eval_env E) v /\ TySemN n l E Av v) ->
  forall E : NEnv, EnvOkN n G E ->
     exists Av v, Eval tNat (eval_env E) Av /\
                 Eval (tSuc a) (eval_env E) v /\ TySemN n l E Av v.
Proof.
  intros n G l a IH E HE.
  destruct (IH E HE) as [Av [v [HA [Ha _]]]].
  assert (Av = VNat) by (apply (Eval_nat_inv (eval_env E) Av); exact HA).
  subst Av. exists VNat, (VSuc v).
  split; [apply Eval_nat | split; [apply Eval_suc; exact Ha | apply TySemN_nat; discriminate]].
Qed.

Lemma nbeN_T_Absurd : forall (n : nat) (G : context) (l l0 : T) (a A : tm),
  (forall E : NEnv, EnvOkN n G E ->
     exists Av v, Eval tVoid (eval_env E) Av /\
                 Eval a (eval_env E) v /\ TySemN n l0 E Av v) ->
  forall E : NEnv, EnvOkN n G E ->
     exists Av v, Eval A (eval_env E) Av /\
                 Eval (tAbsurd a) (eval_env E) v /\ TySemN n l E Av v.
Proof.
  intros n G l l0 a A IH E HE.
  destruct (IH E HE) as [Av [v [HA [Ha HT]]]].
  assert (Av = VVoid) by (apply (Eval_void_inv (eval_env E) Av); exact HA).
  subst Av. exfalso. exact (TySemN_void_absurd n l0 E v HT).
Qed.

Lemma nbeN_T_Pi : forall (n : nat) (G : context) (l : T) (i j : nat)
  (l0 : T) (A B : tm),
  (forall E : NEnv, EnvOkN n G E ->
     exists Av v, Eval (tUniv i) (eval_env E) Av /\
                 Eval A (eval_env E) v /\ TySemN n l E Av v) ->
  forall E : NEnv, EnvOkN n G E ->
     exists Av v, Eval (tUniv (max i j)) (eval_env E) Av /\
                 Eval (tPi l0 A B) (eval_env E) v /\ TySemN n l E Av v.
Proof.
  intros n G l i j l0 A B IHA E HE.
  destruct (IHA E HE) as [AvA [vA [EA [HA HT]]]].
  exists (VUniv (max i j)), (VPi l0 vA B (eval_env E)).
  split; [apply Eval_univ | split].
  - apply (Eval_pi l0 A B (eval_env E) vA). exact HA.
  - apply TySemN_univ.
Qed.

Lemma nbeN_T_Sig : forall (n : nat) (G : context) (l : T) (i j : nat)
  (l0 : T) (A B : tm),
  (forall E : NEnv, EnvOkN n G E ->
     exists Av v, Eval (tUniv i) (eval_env E) Av /\
                 Eval A (eval_env E) v /\ TySemN n l E Av v) ->
  forall E : NEnv, EnvOkN n G E ->
     exists Av v, Eval (tUniv (max i j)) (eval_env E) Av /\
                 Eval (tSig l0 A B) (eval_env E) v /\ TySemN n l E Av v.
Proof.
  intros n G l i j l0 A B IHA E HE.
  destruct (IHA E HE) as [AvA [vA [EA [HA HT]]]].
  exists (VUniv (max i j)), (VSig l0 vA B (eval_env E)).
  split; [apply Eval_univ | split].
  - apply (Eval_sig l0 A B (eval_env E) vA). exact HA.
  - apply TySemN_univ.
Qed.

(* Explicit remaining obligations for the step-indexed fundamental lemma. *)

Definition NEnvOk_lookupN : Prop :=
  forall (n : nat) (G : context) (E : NEnv) (i : fin) (l0 : T) (A : tm),
    lookup i G l0 A -> EnvOkN n G E ->
    exists (e : NEnvEntry) (Av : Val),
      nth_error E i = Some e /\ Eval A (eval_env E) Av /\
      TySemN n l0 E Av (ee_val e).

Definition TySemN_level_mono : Prop :=
  forall (n : nat) (l l' : T) (E : NEnv) (A v : Val),
    l ⊆ l' -> TySemN n l E A v -> TySemN n l' E A v.

(* NBE compositionality for result types: the value of a type family at an
   environment extension relates to the value of its substitution instance. *)
Definition EvalSubstN : Prop :=
  forall (n : nat) (l l0 : T) (E : NEnv) (A : Val) (b : tm) (bv : Val)
         (B : tm) (Bv r : Val) (e : NEnvEntry),
    ee_val e = bv ->
    TySemN n l0 E A bv ->
    Eval b (eval_env E) bv ->
    Eval B (bv :: eval_env E) Bv ->
    TySemN n l (e :: E) Bv r ->
    exists B', Eval (B[b..]) (eval_env E) B' /\ TySemN n l E B' r.

(* Conversion invariance of the step-indexed semantics (T_Conv). *)
Definition ConvInvariantN : Prop :=
  forall (n : nat) (l : T) (E : NEnv) (Xi : econtext) (A B : tm)
         (Av Bv v : Val),
    conv Xi A B ->
    Eval A (eval_env E) Av -> Eval B (eval_env E) Bv ->
    TySemN n l E Av v -> TySemN n l E Bv v.

Definition TySemN_irrel : Prop :=
  forall (n : nat) (l l0 : T) (E : NEnv) (A : Val) (body : tm) (envT : list Val),
    ~ (l0 ⊆ l) ->
    forall (arg1 arg2 : Val) (e1 e2 : NEnvEntry) (B1 B2 : Val),
      ee_val e1 = arg1 -> ee_val e2 = arg2 ->
      TySemN n l0 E A arg1 -> TySemN n l0 E A arg2 ->
      Eval body (arg1 :: envT) B1 -> Eval body (arg2 :: envT) B2 ->
      forall u : Val,
        TySemN n l (e1 :: E) B1 u <-> TySemN n l (e2 :: E) B2 u.

(* STEP-INDEX OBSTRUCTION (recorded here for the next iteration).
   The naive step-indexed definition above consumes a step in the Pi clause:
   [TySemN (S n) (VPi ...)] uses [TySemN n] for the domain and codomain.  The
   fundamental lemma's T_Abs case therefore needs the body environment to be
   valid at step [n], while the hypothesis only gives validity at [S n].
   Cumulative environments do not fix this: the newly bound argument's entry
   would be required at all steps [m <= n], but the Pi clause provides its
   semantics only at step [n].  Making the environment cumulative at all lower
   steps would require the Pi clause itself to quantify cumulatively over all
   [m <= n] (a monotone/limited step-indexed relation), or an upward
   monotonicity principle [TySemN n -> TySemN (S n)] which is false at step 0
   (where the semantics is universal except VVoid).  Thus a plain decreasing
   step index is not sufficient; a bounded/cumulative (modal) step index is
   required.  The definitions and all base cases above compile. *)

(* The bounded/shifted formulation suggested for the step index.  A term is
   interpreted at step [n-1] from an environment valid at step [n].  The
   arithmetic works for the T_App head (use the function hypothesis at
   parameter [n+1] and the argument at [n]), but T_Abs still has an entry-step
   mismatch: the Pi clause at step [n-1] provides the argument semantics at
   step [n-2] (application consumes the step), while the body environment at
   parameter [n-1] requires the newly bound entry at step [n-1].  Closing that
   gap needs either a separate step for terms and types, or a modal "later"
   (a bounded/cumulative index where the Pi clause passes the same step to its
   domain and a later step only to the codomain). *)
Definition FunLemmaShift : Prop :=
  forall (G : context) (l : T) (a A : tm),
    Wt G l a A ->
    exists B : nat,
      forall n : nat, 0 < n -> n <= B ->
        forall E : NEnv, EnvOkN n G E ->
        forall Av : Val, Eval A (eval_env E) Av ->
          exists v : Val, Eval a (eval_env E) v /\ TySemN (n - 1) l E Av v.

Definition FunLemmaN : Prop :=
  forall (n : nat) (G : context) (l : T) (a A : tm),
    Wt G l a A ->
    forall E : NEnv, EnvOkN n G E ->
    forall Av : Val, Eval A (eval_env E) Av ->
    exists v : Val, Eval a (eval_env E) v /\ TySemN n l E Av v.


Lemma rtc_Par_pi_inv : forall (l : T) (A B c : tm),
  rtc Par (tPi l A B) c ->
  exists A' B', c = tPi l A' B' /\ rtc Par A A' /\ rtc Par B B'.
Proof.
  intros l A B c H. remember (tPi l A B) as t eqn:E. revert A B E.
  induction H as [t | t u c Htu Huc IH]; intros A B E; subst.
  - exists A, B. split; [reflexivity | split; apply rtc_refl].
  - destruct (Par_Pi_inv l A B u Htu) as [A1 [B1 [Eu [HA HB]]]]; subst u.
    destruct (IH A1 B1 eq_refl) as [A2 [B2 [Ec [HA2 HB2]]]]; subst c.
    exists A2, B2. split; [reflexivity | split].
    + eapply rtc_trans'; [eapply rtc_l; [exact HA | apply rtc_refl] | exact HA2].
    + eapply rtc_trans'; [eapply rtc_l; [exact HB | apply rtc_refl] | exact HB2].
Qed.

Lemma rtc_Par_sig_inv : forall (l : T) (A B c : tm),
  rtc Par (tSig l A B) c ->
  exists A' B', c = tSig l A' B' /\ rtc Par A A' /\ rtc Par B B'.
Proof.
  intros l A B c H. remember (tSig l A B) as t eqn:E. revert A B E.
  induction H as [t | t u c Htu Huc IH]; intros A B E; subst.
  - exists A, B. split; [reflexivity | split; apply rtc_refl].
  - destruct (Par_Sig_inv l A B u Htu) as [A1 [B1 [Eu [HA HB]]]]; subst u.
    destruct (IH A1 B1 eq_refl) as [A2 [B2 [Ec [HA2 HB2]]]]; subst c.
    exists A2, B2. split; [reflexivity | split].
    + eapply rtc_trans'; [eapply rtc_l; [exact HA | apply rtc_refl] | exact HA2].
    + eapply rtc_trans'; [eapply rtc_l; [exact HB | apply rtc_refl] | exact HB2].
Qed.


Lemma rtc_Par_abs_inv : forall (l : T) (a c : tm),
  rtc Par (tAbs l a) c -> exists a', c = tAbs l a' /\ rtc Par a a'.
Proof.
  intros l a c H. remember (tAbs l a) as t eqn:E. revert a E.
  induction H as [t | t u c Htu Huc IH]; intros a E; subst.
  - exists a. split; [reflexivity | apply rtc_refl].
  - destruct (Par_Abs_inv l a u Htu) as [a1 [Eu Ha]]; subst u.
    destruct (IH a1 eq_refl) as [a2 [Ec Ha2]]; subst c.
    exists a2. split; [reflexivity |].
    eapply rtc_trans'; [eapply rtc_l; [exact Ha | apply rtc_refl] | exact Ha2].
Qed.

Lemma rtc_Par_suc_inv : forall (a c : tm),
  rtc Par (tSuc a) c -> exists a', c = tSuc a' /\ rtc Par a a'.
Proof.
  intros a c H. remember (tSuc a) as t eqn:E. revert a E.
  induction H as [t | t u c Htu Huc IH]; intros a E; subst.
  - exists a. split; [reflexivity | apply rtc_refl].
  - destruct (Par_Suc_inv a u Htu) as [a1 [Eu Ha]]; subst u.
    destruct (IH a1 eq_refl) as [a2 [Ec Ha2]]; subst c.
    exists a2. split; [reflexivity |].
    eapply rtc_trans'; [eapply rtc_l; [exact Ha | apply rtc_refl] | exact Ha2].
Qed.

Lemma rtc_Par_absurd_inv : forall (a c : tm),
  rtc Par (tAbsurd a) c -> exists a', c = tAbsurd a' /\ rtc Par a a'.
Proof.
  intros a c H. remember (tAbsurd a) as t eqn:E. revert a E.
  induction H as [t | t u c Htu Huc IH]; intros a E; subst.
  - exists a. split; [reflexivity | apply rtc_refl].
  - destruct (Par_Absurd_inv a u Htu) as [a1 [Eu Ha]]; subst u.
    destruct (IH a1 eq_refl) as [a2 [Ec Ha2]]; subst c.
    exists a2. split; [reflexivity |].
    eapply rtc_trans'; [eapply rtc_l; [exact Ha | apply rtc_refl] | exact Ha2].
Qed.

Lemma rtc_Par_pack_inv : forall (l : T) (a b c : tm),
  rtc Par (tPack l a b) c ->
  exists a' b', c = tPack l a' b' /\ rtc Par a a' /\ rtc Par b b'.
Proof.
  intros l a b c H. remember (tPack l a b) as t eqn:E. revert a b E.
  induction H as [t | t u c Htu Huc IH]; intros a b E; subst.
  - exists a, b. split; [reflexivity | split; apply rtc_refl].
  - destruct (Par_Pack_inv l a b u Htu) as [a1 [b1 [Eu [Ha Hb]]]]; subst u.
    destruct (IH a1 b1 eq_refl) as [a2 [b2 [Ec [Ha2 Hb2]]]]; subst c.
    exists a2, b2. split; [reflexivity | split].
    + eapply rtc_trans'; [eapply rtc_l; [exact Ha | apply rtc_refl] | exact Ha2].
    + eapply rtc_trans'; [eapply rtc_l; [exact Hb | apply rtc_refl] | exact Hb2].
Qed.


Lemma subst_void_eq : forall (A c : tm),
  subst_tm (scons c ids) A = tVoid ->
  A = tVoid \/ (A = var_tm 0 /\ c = tVoid).
Proof.
  intros A c H. destruct A; simpl in H; try discriminate.
  - match goal with
    | |- var_tm ?i = tVoid \/ _ =>
        destruct i as [|k]; simpl in H;
        [ right; split; [reflexivity | exact H] | discriminate H ]
    end.
  - left. reflexivity.
Qed.

Lemma subst2_void_eq : forall (C p b : tm),
  subst_tm (scons p (scons b ids)) C = tVoid ->
  C = tVoid \/ (C = var_tm 0 /\ p = tVoid) \/ (C = var_tm 1 /\ b = tVoid).
Proof.
  intros C p b H. destruct C; simpl in H; try discriminate.
  - match goal with
    | |- var_tm ?i = tVoid \/ _ =>
        destruct i as [|[|k]]; simpl in H;
        [ right; left; split; [reflexivity | exact H]
        | right; right; split; [reflexivity | exact H]
        | discriminate H ]
    end.
  - left. reflexivity.
Qed.


Lemma IEq_eq_inv2 : forall (Xi : econtext) (l l0 : T) (a b A : tm),
  IEq Xi l (tEq l0 a b) A ->
  exists a' b', A = tEq l0 a' b' /\ IEq Xi l a a' /\ IEq Xi l b b'.
Proof. intros Xi l l0 a b A H. inversion H; subst; eauto 8. Qed.

Lemma IEq_sig_inv2 : forall (Xi : econtext) (l l0 : T) (C D A : tm),
  IEq Xi l (tSig l0 C D) A ->
  exists C' D', A = tSig l0 C' D' /\
    IEq Xi l C C' /\ IEq (l0 :: Xi) l D D'.
Proof. intros Xi l l0 C D A H. inversion H; subst; eauto 8. Qed.

Lemma IEq_app_inv2 : forall (Xi : econtext) (l : T) (a0 a1 : tm) (l0 : T) (b0 b1 A : tm),
  IEq Xi l (tApp a0 l0 b0) (tApp a1 l0 b1) ->
  IEq Xi l a0 a1 /\ GIEq Xi l l0 b0 b1.
Proof. intros Xi l a0 a1 l0 b0 b1 A H. inversion H; subst; eauto. Qed.

Lemma IEq_j_inv2 : forall (Xi : econtext) (l lp : T) (t0 p0 A : tm),
  IEq Xi l (tJ lp t0 p0) A ->
  exists t1 p1, A = tJ lp t1 p1 /\ IEq Xi l t0 t1 /\ IEq Xi l p0 p1.
Proof. intros Xi l lp t0 p0 A H. inversion H; subst; eauto 8. Qed.

Lemma IEq_ind_inv2 : forall (Xi : econtext) (l l0 : T) (a0 b0 c0 A : tm),
  IEq Xi l (tInd l0 a0 b0 c0) A ->
  exists a1 b1 c1, A = tInd l0 a1 b1 c1 /\
    IEq Xi l a0 a1 /\ IEq (l0 :: l0 :: Xi) l b0 b1 /\ IEq Xi l c0 c1.
Proof. intros Xi l l0 a0 b0 c0 A H. inversion H; subst; eauto 10. Qed.

Lemma IEq_seq_inv2 : forall (Xi : econtext) (l l0 : T) (a0 b0 A : tm),
  IEq Xi l (tSeq l0 a0 b0) A ->
  exists a1 b1, A = tSeq l0 a1 b1 /\ IEq Xi l a0 a1 /\ IEq Xi l b0 b1.
Proof. intros Xi l l0 a0 b0 A H. inversion H; subst; eauto 8. Qed.


Lemma lookup_nil : forall (i : fin) (l : T) (A : tm), lookup i nil l A -> False.
Proof. intros i l A H. inversion H. Qed.

Lemma nil_no_lookup : forall (i : fin) (l : T) (A : tm), ~ lookup i nil l A.
Proof. intros i l A H. apply (lookup_nil i l A); exact H. Qed.


Definition ConsistencyStatement : Prop :=
  forall (a : tm) (l : T), Wt nil l a tVoid -> False.

Definition AStatement : Prop :=
  forall (A b f : tm) (l l0 : T),
    Wt nil l0 b A -> Wt nil l f (tPi l0 A tVoid) -> False.

Definition BStatement : Prop :=
  forall (a t p : tm) (l lp l0 : T),
    Wt nil lp p (tEq l0 a tVoid) -> Wt nil l t a -> False.

(* Any closed term whose type is convertible to Void can be re-typed at the
   syntactic empty type, by a final T_Conv with target [tVoid]. *)
Lemma wt_to_void : forall (l : T) (a A : tm),
  Wt nil l a A -> conv nil A tVoid -> Wt nil l a tVoid.
Proof.
  intros l a A HA Hc.
  eapply (@T_Conv nil l l a A tVoid 0).
  - exact HA.
  - apply (T_Void nil l 0 Wff_nil).
  - exact Hc.
Qed.

Lemma consistency_conv_iff :
  ConsistencyStatement <->
  (forall (a : tm) (l : T) (A : tm),
     Wt nil l a A -> conv nil A tVoid -> False).
Proof.
  split.
  - intros C a l A HA Hc. apply (C a l). apply (wt_to_void l a A HA Hc).
  - intros H a l Ha. apply (H a l tVoid Ha).
    exists l, tVoid, tVoid. split; [apply rtc_refl | split; [apply rtc_refl | apply I_Void]].
Qed.

(* (A) follows from closed consistency: the application itself is a closed
   Void-typed term (note [tVoid[b..]] is definitionally [tVoid]). *)
Lemma A_of_consistency : ConsistencyStatement -> AStatement.
Proof.
  intros C A b f l l0 Hb Hf.
  apply (C (tApp f l0 b) l).
  change (Wt nil l (tApp f l0 b) (tVoid [b..])).
  apply (T_App nil l l0 f A tVoid b Hf Hb).
Qed.

(* Conversely, closed consistency is an instance of (A), using the closed
   function [fun _ : Void => x] which has type [Void -> Void]. *)
Lemma consistency_of_A : AStatement -> ConsistencyStatement.
Proof.
  intros HA a l Ha.
  apply (HA tVoid a (tAbs l (var_tm 0)) l l Ha).
  apply (wt_void_to_void nil l l Wff_nil).
  apply meet_idempotent.
Qed.

(* Hence the requested lemma (A) is *exactly* the target theorem. *)
Lemma A_iff_consistency : AStatement <-> ConsistencyStatement.
Proof.
  split; [apply consistency_of_A | apply A_of_consistency].
Qed.

(* (B) also immediately entails the target: [tRefl] is a closed proof of
   [Eq l Void Void] and the hypothetical [t] is the closed Void term itself. *)
Lemma consistency_of_B : BStatement -> ConsistencyStatement.
Proof.
  intros HB a l Ha.
  apply (HB tVoid a tRefl l l l).
  - apply (T_Refl nil l tVoid l (tUniv 0)).
    apply (T_Void nil l 0 Wff_nil).
  - exact Ha.
Qed.

(* The [tAbs] case of (A): a closed argument [b] for a bound variable, and an
   open body typing the empty type. *)
Definition OpenLambdaCanon : Prop :=
  forall (A b body : tm) (l l0 : T),
    Wt nil l0 b A -> Wt ((l0, A) :: nil) l body tVoid -> False.

(* This lambda case already entails the target: take [A = Void] and the body
   to be the bound variable itself.  So it is not a weaker subproblem. *)
Lemma consistency_of_open_lambda_canon :
  OpenLambdaCanon -> ConsistencyStatement.
Proof.
  intros H a l Ha.
  apply (H tVoid a (var_tm 0) l l Ha).
  eapply T_Var.
  - eapply Wff_cons.
    + exact Wff_nil.
    + apply (T_Void nil l 0 Wff_nil).
  - eapply here.
  - apply meet_idempotent.
Qed.

(* The dependent-application case that the T_App rule actually produces.  A
   bare codomain [B] with [B[b..] = tVoid] is more general than (A): the
   substitution can hit a variable ([B = var 0]), which is not covered by the
   statement of (A).  For nil contexts this case is equivalent to the target
   (it follows from consistency by applying T_App and rewriting). *)
Definition DepAppNilCase : Prop :=
  forall (l l0 : T) (f : tm) (A B b : tm),
    Wt nil l f (tPi l0 A B) -> Wt nil l0 b A -> B[b..] = tVoid -> False.

Lemma DepAppNil_of_consistency :
  ConsistencyStatement -> DepAppNilCase.
Proof.
  intros C l l0 f A B b Hf Hb HE.
  apply (C (tApp f l0 b) l).
  rewrite <- HE.
  apply (T_App nil l l0 f A B b Hf Hb).
Qed.

Lemma A_of_dep_app_nil : DepAppNilCase -> AStatement.
Proof.
  intros D A b f l l0 Hb Hf.
  apply (D l l0 f A tVoid b Hf Hb).
  reflexivity.
Qed.

Lemma DepAppNil_iff_consistency :
  DepAppNilCase <-> ConsistencyStatement.
Proof.
  split.
  - intro D. apply consistency_of_A. apply A_of_dep_app_nil. exact D.
  - apply DepAppNil_of_consistency.
Qed.

(* No variable is bound in the empty context. *)
Lemma wt_pi_univ_var : forall (l0 l : T) (i : nat),
  l0 ⊆ l ->
  Wt nil l (tPi l0 (tUniv i) (var_tm 0)) (tUniv (max (S i) i)).
Proof.
  intros l0 l i Hsub.
  eapply (@T_Pi nil (S i) i l l0 (tUniv i) (var_tm 0)).
  - apply (T_Univ nil l i Wff_nil).
  - eapply (@T_Var ((l0, tUniv i) :: nil) l0 l 0 (tUniv i)).
    + eapply Wff_cons; [exact Wff_nil | apply (T_Univ nil l i Wff_nil)].
    + eapply here.
    + exact Hsub.
Qed.

(* ---- Rigid-head conversion helpers ---- *)

(* Transitivity of conversion when the right-hand common type is a rigid
   closed constructor [P] (one with no non-trivial parallel reducts). *)
Lemma conv_of_conv_rigid :
  forall (P : tm) (Xi : econtext),
    (forall c : tm, rtc Par P c -> c = P) ->
    (forall (l : T) (c : tm), IEq Xi l c P -> c = P) ->
    (forall l : T, IEq Xi l P P) ->
    forall (A B : tm), conv Xi A B -> conv Xi A P -> conv Xi B P.
Proof.
  intros P Xi Hrtc Hieq HieqP A B HAB HAP.
  destruct HAP as [l1 [c0 [c1 [HAc0 [HPc1 HIE1]]]]].
  (* c1 is P, and so is c0 *)
  assert (Ec1 : c1 = P) by (apply Hrtc; exact HPc1). subst c1.
  assert (Ec0 : c0 = P) by (apply (Hieq l1 c0); exact HIE1). subst c0.
  destruct HAB as [l2 [d0 [d1 [HAd0 [HBd1 HIE2]]]]].
  destruct (Par_rtc_confluent A P d0 HAc0 HAd0) as [e [HPe Hd0e]].
  assert (Ee : e = P) by (apply Hrtc; exact HPe). subst e.
  destruct (ieq_rtc_l Xi l2 d0 d1 HIE2 P Hd0e) as [d1' [Hd1' HIE2']].
  assert (Ed1' : d1' = P) by (apply (Hieq l2 d1'); apply ieq_sym; exact HIE2'). subst d1'.
  exists l2, P, P. split.
  - eapply rtc_trans'; [exact HBd1 | exact Hd1'].
  - split; [apply rtc_refl | apply HieqP].
Qed.

Lemma conv_of_conv_univ : forall (Xi : econtext) (i : fin) (A B : tm),
  conv Xi A B -> conv Xi A (tUniv i) -> conv Xi B (tUniv i).
Proof.
  intros Xi i A B HAB HA.
  apply (conv_of_conv_rigid (tUniv i) Xi
           (fun c H => rtc_tUniv_eq i c H)
           (fun l c H => IEq_univ_inv Xi l i c (ieq_sym Xi l c (tUniv i) H))
           (fun l => @I_Univ Xi l i) A B HAB HA).
Qed.

(* Any well-typed closed [tVoid] term has a universe type. *)
Lemma Wt_tVoid_inv : forall (G : context) (l : T) (A : tm),
  Wt G l tVoid A -> exists i : fin, conv (c2e G) A (tUniv i).
Proof.
  intros G l A H.
  remember tVoid as v eqn:Ev.
  revert Ev.
  induction H; intros Ev; try discriminate Ev.
  - (* T_Conv *)
    destruct (IHWt1 Ev) as [k Hk].
    exists k.
    exact (conv_of_conv_univ (c2e Γ) k A B H1 Hk).
  - (* T_Void *)
    exists i, ℓ, (tUniv i), (tUniv i).
    split; [apply rtc_refl | split; [apply rtc_refl | apply (@I_Univ (c2e Γ) ℓ i)]].
Qed.

(* The incompatible rigid heads produced by the [var 0] inversion branches. *)
Lemma not_conv_nat_univ : forall (i : fin),
  ~ conv nil tNat (tUniv i).
Proof.
  intros i H. apply conv_nat_rtc in H.
  pose proof (rtc_tUniv_eq i tNat H) as E. discriminate E.
Qed.

Lemma not_conv_unit_univ : forall (i : fin),
  ~ conv nil tUnit (tUniv i).
Proof.
  intros i H. apply conv_unit_rtc in H.
  pose proof (rtc_tUniv_eq i tUnit H) as E. discriminate E.
Qed.

Lemma not_conv_sig_univ : forall (l : T) (A B : tm) (i : fin),
  ~ conv nil (tSig l A B) (tUniv i).
Proof.
  intros l A B i H.
  destruct (conv_sig_rtc nil l A B (tUniv i) H) as [C' [D' Hsig]].
  pose proof (rtc_tUniv_eq i (tSig l C' D') Hsig) as E. discriminate E.
Qed.



Lemma lookup_zero_inv : forall (G : context) (l0 : T) (A0 : tm) (l : T) (A : tm),
  lookup 0 ((l0, A0) :: G) l A -> l = l0 /\ A = A0⟨shift⟩.
Proof. intros G l0 A0 l A H. inversion H. auto. Qed.

Lemma lookup_succ_inv : forall (n : nat) (G : context) (l0 : T) (A0 : tm) (l : T) (A : tm),
  lookup (S n) ((l0, A0) :: G) l A ->
  exists l' A', lookup n G l' A' /\ l = l' /\ A = A'⟨shift⟩.
Proof. intros n G l0 A0 l A H. inversion H. eauto. Qed.


(* ================= cumulative (modal) NBE with per-entry steps ================= *)

Record HEnvEntry := {
  he_val  : Val;
  he_step : nat;
  he_code : Val -> Prop;
  he_fam  : Val -> Val -> Prop
}.
Definition empty_hentry : HEnvEntry :=
  {| he_val := VVoid; he_step := 0; he_code := fun _ => True;
     he_fam := fun _ _ => True |}.
Definition HEnv := list HEnvEntry.
Definition heval_env (E : HEnv) : list Val := map he_val E.

(* Cumulative semantics: [Sem (S k)] contains the core clause at step [S k]
   (whose Pi/Sig subclauses use [Sem k]) and, conjunctively, [Sem k].  Thus
   [Sem (S k) -> Sem k] holds by construction. *)
Fixpoint Sem (k : nat) (l : T) (E : HEnv) (code x : Val) {struct k} : Prop :=
  match k with
  | 0 => code <> VVoid
  | S k0 =>
      (match code with
       | VVoid => False
       | VUnit => x <> VVoid
       | VNat => x <> VVoid
       | VEq _ _ _ => x <> VVoid
       | VUniv _ => True
       | VVar i => he_code (nth i E empty_hentry) x
       | VPi l0 A body envT =>
           (forall (arg : Val) (e : HEnvEntry),
               he_val e = arg ->
               Sem k0 l0 E A arg ->
               exists (r Bv : Val),
                 Apply l0 code arg r /\
                 Eval body (arg :: envT) Bv /\
                 (forall (Bv' : Val),
                     Eval body (arg :: envT) Bv' -> Sem k0 l (e :: E) Bv' r))
           /\ (if T_eqb (l0 ∩ l) l0 then True
               else forall (arg1 arg2 : Val) (e1 e2 : HEnvEntry) (B1 B2 : Val),
                   he_val e1 = arg1 -> he_val e2 = arg2 ->
                   Sem k0 l0 E A arg1 -> Sem k0 l0 E A arg2 ->
                   Eval body (arg1 :: envT) B1 -> Eval body (arg2 :: envT) B2 ->
                   forall u : Val,
                     Sem k0 l (e1 :: E) B1 u <-> Sem k0 l (e2 :: E) B2 u)
       | VSig l0 A body envT =>
           (forall P : Val -> Prop,
               (forall (a b : Val) (ea eb : HEnvEntry),
                   he_val ea = a -> he_val eb = b ->
                   Sem k0 l0 E A a ->
                   forall Bv : Val,
                     Eval body (a :: envT) Bv -> Sem k0 l (ea :: E) Bv b ->
                     P (VPack l0 a b)) ->
               P code)
       | _ => x <> VVoid
       end)
      /\ Sem k0 l E code x
  end.

Lemma Sem_down : forall (k : nat) (l : T) (E : HEnv) (code x : Val),
  Sem (S k) l E code x -> Sem k l E code x.
Proof. intros k l E code x H. simpl in H. exact (proj2 H). Qed.

Lemma Sem_univ : forall (k : nat) (l : T) (E : HEnv) (m : nat) (x : Val),
  Sem k l E (VUniv m) x.
Proof.
  intros k. induction k as [|k IH]; intros l E m x; simpl.
  - discriminate.
  - split; [exact I | apply IH].
Qed.

Lemma Sem_unit : forall (k : nat) (l : T) (E : HEnv) (v : Val),
  v <> VVoid -> Sem k l E VUnit v.
Proof.
  intros k. induction k as [|k IH]; intros l E v Hv; simpl.
  - discriminate.
  - split; [exact Hv | apply IH; exact Hv].
Qed.

Lemma Sem_nat : forall (k : nat) (l : T) (E : HEnv) (v : Val),
  v <> VVoid -> Sem k l E VNat v.
Proof.
  intros k. induction k as [|k IH]; intros l E v Hv; simpl.
  - discriminate.
  - split; [exact Hv | apply IH; exact Hv].
Qed.

Lemma Sem_eq : forall (k : nat) (l : T) (E : HEnv) (l0 : T) (a b v : Val),
  v <> VVoid -> Sem k l E (VEq l0 a b) v.
Proof.
  intros k. induction k as [|k IH]; intros l E l0 a b v Hv; simpl.
  - discriminate.
  - split; [exact Hv | apply IH; exact Hv].
Qed.

Lemma Sem_void_absurd : forall (k : nat) (l : T) (E : HEnv) (x : Val),
  Sem k l E VVoid x -> False.
Proof.
  intros k. induction k as [|k IH]; intros l E x H; simpl in H.
  - apply H; reflexivity.
  - exact (proj1 H).
Qed.

(* Per-entry environment validity: every entry is valid at its own step, and
   every entry step is at least the uniform bound [A]. *)
Fixpoint EnvOkS (A : nat) (G : context) (E : HEnv) {struct G} : Prop :=
  match G, E with
  | nil, nil => True
  | (l0, Ty) :: G', e :: E' =>
      EnvOkS A G' E' /\ A <= he_step e /\
      (exists Av, Eval Ty (heval_env E') Av /\
                  Sem (he_step e) l0 E' Av (he_val e))
  | _, _ => False
  end.

Lemma nat_le_trans' : forall n m p : nat, n <= m -> m <= p -> n <= p.
Proof. intros n m p H1 H2. induction H2; [exact H1 | apply le_S; assumption]. Qed.

Lemma EnvOkS_down : forall (A A' : nat) (G : context) (E : HEnv),
  A' <= A -> EnvOkS A G E -> EnvOkS A' G E.
Proof.
  intros A A' G. induction G as [| [l0 Ty] G' IH]; intros E Hle HE.
  - destruct E; simpl in *; [exact I | exact HE].
  - destruct E as [|e E']; simpl in *.
    + exact HE.
    + destruct HE as [HE [Hstep Hval]]. split; [| split].
      * apply IH; [exact Hle | exact HE].
      * eapply nat_le_trans'; [exact Hle | exact Hstep].
      * exact Hval.
Qed.

Lemma EnvOkS_cons : forall (A' : nat) (l0 : T) (Ty : tm) (G : context)
  (E : HEnv) (e : HEnvEntry),
  EnvOkS A' G E -> A' <= he_step e ->
  (exists Av, Eval Ty (heval_env E) Av /\ Sem (he_step e) l0 E Av (he_val e)) ->
  EnvOkS A' ((l0, Ty) :: G) (e :: E).
Proof.
  intros A' l0 Ty G E e HE Hle Hval. simpl.
  split; [exact HE | split; [exact Hle | exact Hval]].
Qed.

(* Fundamental-lemma statement with a uniform environment bound [A0] and
   conclusion step [B0], using only [B0 <= A0]. *)
Definition FunLemmaCum : Prop :=
  forall (G : context) (l : T) (a A : tm),
    Wt G l a A ->
    forall (A0 B0 : nat), B0 <= A0 ->
    forall E : HEnv, EnvOkS A0 G E ->
    exists Av v, Eval A (heval_env E) Av /\
                Eval a (heval_env E) v /\ Sem B0 l E Av v.

(* Verified base cases at arbitrary bounds. *)

Lemma nbeC_T_Void : forall (A0 B0 : nat) (G : context) (l : T) (i : nat)
  (E : HEnv), B0 <= A0 -> EnvOkS A0 G E ->
  exists Av v, Eval (tUniv i) (heval_env E) Av /\
              Eval tVoid (heval_env E) v /\ Sem B0 l E Av v.
Proof.
  intros. exists (VUniv i), VVoid.
  split; [apply Eval_univ | split; [apply Eval_void | apply Sem_univ]].
Qed.

Lemma nbeC_T_Univ : forall (A0 B0 : nat) (G : context) (l : T) (i : nat)
  (E : HEnv), B0 <= A0 -> EnvOkS A0 G E ->
  exists Av v, Eval (tUniv (S i)) (heval_env E) Av /\
              Eval (tUniv i) (heval_env E) v /\ Sem B0 l E Av v.
Proof.
  intros. exists (VUniv (S i)), (VUniv i).
  split; [apply Eval_univ | split; [apply Eval_univ | apply Sem_univ]].
Qed.

Lemma nbeC_T_Nat : forall (A0 B0 : nat) (G : context) (l : T) (i : nat)
  (E : HEnv), B0 <= A0 -> EnvOkS A0 G E ->
  exists Av v, Eval (tUniv i) (heval_env E) Av /\
              Eval tNat (heval_env E) v /\ Sem B0 l E Av v.
Proof.
  intros. exists (VUniv i), VNat.
  split; [apply Eval_univ | split; [apply Eval_nat | apply Sem_univ]].
Qed.

Lemma nbeC_T_Unit : forall (A0 B0 : nat) (G : context) (l : T) (i : nat)
  (E : HEnv), B0 <= A0 -> EnvOkS A0 G E ->
  exists Av v, Eval (tUniv i) (heval_env E) Av /\
              Eval tUnit (heval_env E) v /\ Sem B0 l E Av v.
Proof.
  intros. exists (VUniv i), VUnit.
  split; [apply Eval_univ | split; [apply Eval_unit | apply Sem_univ]].
Qed.

Lemma nbeC_T_TT : forall (A0 B0 : nat) (G : context) (l : T) (E : HEnv),
  B0 <= A0 -> EnvOkS A0 G E ->
  exists Av v, Eval tUnit (heval_env E) Av /\
              Eval tTT (heval_env E) v /\ Sem B0 l E Av v.
Proof.
  intros. exists VUnit, VTT.
  split; [apply Eval_unit | split; [apply Eval_tt | apply Sem_unit; discriminate]].
Qed.

Lemma nbeC_T_Zero : forall (A0 B0 : nat) (G : context) (l : T) (E : HEnv),
  B0 <= A0 -> EnvOkS A0 G E ->
  exists Av v, Eval tNat (heval_env E) Av /\
              Eval tZero (heval_env E) v /\ Sem B0 l E Av v.
Proof.
  intros. exists VNat, VZero.
  split; [apply Eval_nat | split; [apply Eval_zero | apply Sem_nat; discriminate]].
Qed.

Lemma nbeC_T_Suc : forall (A0 B0 : nat) (G : context) (l : T) (a : tm),
  (forall E : HEnv, EnvOkS A0 G E ->
     exists Av v, Eval tNat (heval_env E) Av /\
                 Eval a (heval_env E) v /\ Sem B0 l E Av v) ->
  forall E : HEnv, EnvOkS A0 G E ->
     exists Av v, Eval tNat (heval_env E) Av /\
                 Eval (tSuc a) (heval_env E) v /\ Sem B0 l E Av v.
Proof.
  intros A0 B0 G l a IH E HE.
  destruct (IH E HE) as [Av [v [HA [Ha _]]]].
  assert (Av = VNat) by (apply (Eval_nat_inv (heval_env E) Av); exact HA).
  subst Av. exists VNat, (VSuc v).
  split; [apply Eval_nat | split; [apply Eval_suc; exact Ha | apply Sem_nat; discriminate]].
Qed.

Lemma nbeC_T_Absurd : forall (A0 B0 : nat) (G : context) (l l0 : T) (a A : tm),
  (forall E : HEnv, EnvOkS A0 G E ->
     exists Av v, Eval tVoid (heval_env E) Av /\
                 Eval a (heval_env E) v /\ Sem B0 l0 E Av v) ->
  forall E : HEnv, EnvOkS A0 G E ->
     exists Av v, Eval A (heval_env E) Av /\
                 Eval (tAbsurd a) (heval_env E) v /\ Sem B0 l E Av v.
Proof.
  intros A0 B0 G l l0 a A IH E HE.
  destruct (IH E HE) as [Av [v [HA [Ha HT]]]].
  assert (Av = VVoid) by (apply (Eval_void_inv (heval_env E) Av); exact HA).
  subst Av. exfalso. exact (Sem_void_absurd B0 l0 E v HT).
Qed.

(* ARITHMETIC OBSTRUCTION for the uniform-bound statement [B0 <= A0].
   T_Abs works: with conclusion [B0], the Pi clause at [B0] uses [B0-1]; the
   body is used at bounds ([B0-1], [B0-1]), and the extended environment's new
   entry has step [B0-1], so EnvOkS (B0-1) holds.
   T_App needs the function at conclusion [B0+1] (the Pi clause at [B0+1] then
   yields the result at [B0]).  The function statement requires EnvOkS (B0+1),
   which follows from EnvOkS A0 only when [B0+1 <= A0].  At the boundary
   [B0 = A0] this fails.  Strengthening the global hypothesis to
   [B0+1 <= A0] repairs T_App but breaks T_Abs, whose body statement at
   ([B0-1],[B0-1]) would then require [B0 <= B0-1].  A single uniform bound
   with per-entry steps therefore cannot satisfy both rules at the boundary;
   a two-index statement with an environment bound chosen per subderivation
   (or a "later" modality that lifts [Sem k] to [Sem (k+1)] for the
   application result) is required.  The latter lift is false at step 0 under
   this definition, which is the precise remaining obstruction. *)



Lemma lookup_shift : forall (i : nat) (G : context) (l : T) (A : tm)
  (l0 : T) (B : tm),
  lookup i G l A -> lookup (S i) ((l0, B) :: G) l A⟨shift⟩.
Proof. intros i G l A l0 B H. eapply there. exact H. Qed.

Lemma lookup_here_shift : forall (G : context) (l : T) (A : tm),
  lookup 0 ((l, A) :: G) l A⟨shift⟩.
Proof. intros G l A. apply here. Qed.


Lemma c2e_cons : forall (l : T) (A : tm) (G : context),
  c2e ((l, A) :: G) = l :: c2e G.
Proof. intros. reflexivity. Qed.

Lemma Wff_cons_inv : forall (G : context) (l0 : T) (A : tm),
  Wff ((l0, A) :: G) ->
  Wff G /\ exists (l : T) (i : fin), Wt G l A (tUniv i).
Proof.
  intros G l0 A H. inversion H; subst. split; [assumption | eauto].
Qed.


Lemma lookup_lt_length : forall (i : nat) (G : context) (l : T) (A : tm),
  lookup i G l A -> i < length G.
Proof.
  intros i G l A H. induction H; simpl.
  - auto with arith.
  - auto with arith.
Qed.


Lemma length_c2e : forall (G : context), length (c2e G) = length G.
Proof.
  intro G. induction G as [| [l A] G IH]; simpl.
  - reflexivity.
  - simpl. f_equal. exact IH.
Qed.


Lemma Wt_nil_var_absurd : forall (i : fin) (l : T) (A : tm),
  Wt nil l (var_tm i) A -> False.
Proof.
  intros i l A H. remember nil as G eqn:EG. remember (var_tm i) as a eqn:Ea.
  revert i Ea. induction H; intros i' Ea; subst; try discriminate.
  - match goal with
    | Hlk : lookup _ nil _ _ |- _ => apply lookup_nil in Hlk; exact Hlk
    end.
  - eauto 10.
Qed.


Lemma VoidFree_abs : forall (l : T) (a : tm), VoidFree (tAbs l a).
Proof.
  intros l a H. destruct (rtc_Par_abs_inv l a tVoid H) as [a' [E _]].
  discriminate E.
Qed.

Lemma VoidFree_suc : forall (a : tm), VoidFree (tSuc a).
Proof.
  intros a H. destruct (rtc_Par_suc_inv a tVoid H) as [a' [E _]].
  discriminate E.
Qed.

Lemma VoidFree_absurd : forall (a : tm), VoidFree (tAbsurd a).
Proof.
  intros a H. destruct (rtc_Par_absurd_inv a tVoid H) as [a' [E _]].
  discriminate E.
Qed.

Lemma VoidFree_pack : forall (l : T) (a b : tm), VoidFree (tPack l a b).
Proof.
  intros l a b H. destruct (rtc_Par_pack_inv l a b tVoid H) as [a' [b' [E _]]].
  discriminate E.
Qed.

Lemma VoidFree_pi' : forall (l : T) (A B : tm), VoidFree (tPi l A B).
Proof.
  intros l A B H. destruct (rtc_Par_pi_inv l A B tVoid H) as [A' [B' [E _]]].
  discriminate E.
Qed.

Lemma VoidFree_sig : forall (l : T) (A B : tm), VoidFree (tSig l A B).
Proof.
  intros l A B H. destruct (rtc_Par_sig_inv l A B tVoid H) as [A' [B' [E _]]].
  discriminate E.
Qed.

Lemma VoidFree_eq : forall (l : T) (a b : tm), VoidFree (tEq l a b).
Proof.
  intros l a b H. destruct (rtc_Par_eq_inv l a b tVoid H) as [a' [b' [E _]]].
  discriminate E.
Qed.


Lemma VoidFree_univ : forall (n : nat), VoidFree (tUniv n).
Proof.
  intros n H. assert (tVoid = tUniv n) as E by (apply (rtc_tUniv_eq n); exact H).
  discriminate E.
Qed.

Lemma VoidFree_nat : VoidFree tNat.
Proof.
  intro H. assert (tVoid = tNat) as E by (apply rtc_tNat_eq; exact H).
  discriminate E.
Qed.

Lemma VoidFree_unit : VoidFree tUnit.
Proof.
  intro H. assert (tVoid = tUnit) as E by (apply rtc_tUnit_eq; exact H).
  discriminate E.
Qed.


Lemma rtc_tZero_eq : forall c : tm, rtc Par tZero c -> c = tZero.
Proof.
  intros c H. remember tZero as t eqn:E. revert E.
  induction H; intros E; subst.
  - reflexivity.
  - inversion H. subst. apply IHrtc. reflexivity.
Qed.

Lemma rtc_tRefl_eq : forall c : tm, rtc Par tRefl c -> c = tRefl.
Proof.
  intros c H. remember tRefl as t eqn:E. revert E.
  induction H; intros E; subst.
  - reflexivity.
  - inversion H. subst. apply IHrtc. reflexivity.
Qed.

Lemma rtc_tTT_eq : forall c : tm, rtc Par tTT c -> c = tTT.
Proof.
  intros c H. remember tTT as t eqn:E. revert E.
  induction H; intros E; subst.
  - reflexivity.
  - inversion H. subst. apply IHrtc. reflexivity.
Qed.

Lemma VoidFree_zero : VoidFree tZero.
Proof. intro H. assert (tVoid = tZero) as E by (apply rtc_tZero_eq; exact H). discriminate E. Qed.
Lemma VoidFree_refl : VoidFree tRefl.
Proof. intro H. assert (tVoid = tRefl) as E by (apply rtc_tRefl_eq; exact H). discriminate E. Qed.
Lemma VoidFree_TT : VoidFree tTT.
Proof. intro H. assert (tVoid = tTT) as E by (apply rtc_tTT_eq; exact H). discriminate E. Qed.


Lemma rtc_tVar_eq : forall (i : fin) (c : tm), rtc Par (var_tm i) c -> c = var_tm i.
Proof.
  intros i c H. remember (var_tm i) as t eqn:E. revert E.
  induction H; intros E; subst.
  - reflexivity.
  - inversion H; subst; apply IHrtc; reflexivity.
Qed.

Lemma VoidFree_var : forall (i : fin), VoidFree (var_tm i).
Proof.
  intros i H. assert (tVoid = var_tm i) as E by (apply rtc_tVar_eq; exact H).
  discriminate E.
Qed.


Lemma conv_void_voidfree_absurd : forall (Xi : econtext) (A : tm),
  VoidFree A -> conv Xi A tVoid -> False.
Proof.
  intros Xi A HV Hc. apply HV. apply (conv_void Xi A); exact Hc.
Qed.

Lemma voidfree_conv_void_absurd : forall (Xi : econtext) (A : tm),
  conv Xi A tVoid -> VoidFree A -> False.
Proof. intros Xi A Hc HV. eapply conv_void_voidfree_absurd; eassumption. Qed.


Inductive SemTy : Type :=
| ST_Void
| ST_Unit
| ST_Nat
| ST_Univ
| ST_Var (P : Val -> Prop)
| ST_Pi (PA : Val -> Prop) (Brel : Val -> (Val -> Prop) -> Prop)
| ST_Sig (PA : Val -> Prop) (Brel : Val -> (Val -> Prop) -> Prop)
| ST_Code (P : Val -> Prop).

Definition El (s : SemTy) (x : Val) : Prop :=
  match s with
  | ST_Void => False
  | ST_Unit => True
  | ST_Nat => True
  | ST_Univ => True
  | ST_Var P => P x
  | ST_Pi PA Brel => forall y, PA y -> forall Q, Brel y Q -> Q x
  | ST_Sig PA Brel => PA x
  | ST_Code P => P x
  end.

Lemma El_void_elim : forall x, El ST_Void x -> False.
Proof. intros x H. cbn [El] in H. exact H. Qed.

Lemma El_pi_intro : forall PA Brel f,
  (forall y, PA y -> forall Q, Brel y Q -> Q f) -> El (ST_Pi PA Brel) f.
Proof. intros PA Brel f H. cbn [El]. exact H. Qed.

Lemma El_pi_elim : forall PA Brel f,
  El (ST_Pi PA Brel) f -> forall y, PA y -> forall Q, Brel y Q -> Q f.
Proof. intros PA Brel f H. cbn [El] in H. exact H. Qed.

Lemma El_code_intro : forall P x, P x -> El (ST_Code P) x.
Proof. intros P x H. cbn [El]. exact H. Qed.

Lemma El_code_elim : forall P x, El (ST_Code P) x -> P x.
Proof. intros P x H. cbn [El] in H. exact H. Qed.


Theorem consistency a ℓ : ~nil ⊢ a ; ℓ ∈ tVoid.

End consistency.
