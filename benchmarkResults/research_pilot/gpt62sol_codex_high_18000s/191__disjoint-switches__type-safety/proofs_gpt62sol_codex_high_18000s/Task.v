Require Import TLC.LibLN.

Require Import Program.Equality.

Require Import Coq.Lists.ListSet.

Require Import Lists.List.

Require Import equivalence.

Inductive Ord : typ -> Prop :=
| o_int   : Ord t_int
| o_arrow : forall t1 t2, Ord (t_arrow t1 t2)
| o_unit  : Ord t_unit
| o_prim  : forall i, Ord (t_prim i).

Definition DisjSpec PG A B := forall C, Ord C -> not (declarative_subtyping PG C (t_and A B)).

Notation "PG ||- A *s B" := (DisjSpec PG A B) (at level 80).

Module Typing_part.

Export Notations.

Inductive exp : Set :=
 | e_var_b  : nat -> exp
 | e_var_f  : var -> exp
 | e_lit    : nat -> exp
 | e_abs    : exp -> exp
 | e_app    : exp -> exp -> exp
 | e_typeof : exp -> typ -> exp -> typ -> exp -> exp
 | e_null   : exp
 | e_new    : MetatheoryAtom.Atom.atom -> exp.

Inductive bind : Set :=
 | bind_typ : typ -> bind.

Notation "x ~: T" := (x ~ T)
 (at level 23, left associativity) : env_scope.

Definition env := LibEnv.env typ.

Fixpoint open_exp_wrt_exp_rec (k:nat) (e_5:exp) (e__6:exp) {struct e__6}: exp :=
  match e__6 with
  | (e_var_b nat) => If (k = nat) then e_5 else (e_var_b nat)
  | (e_var_f x) => e_var_f x
  | (e_lit i5) => e_lit i5
  | (e_abs e) => e_abs (open_exp_wrt_exp_rec (S k) e_5 e)
  | (e_app e1 e2) => e_app (open_exp_wrt_exp_rec k e_5 e1) (open_exp_wrt_exp_rec k e_5 e2)
  | (e_typeof e A e1 B e2) => e_typeof (open_exp_wrt_exp_rec k e_5 e) A (open_exp_wrt_exp_rec (S k) e_5 e1) B (open_exp_wrt_exp_rec (S k) e_5 e2)
  | (e_null) => e_null
  | e_new A  => e_new A
end.

Definition open_exp_wrt_exp e_5 e__6 := open_exp_wrt_exp_rec 0 e__6 e_5.

Notation "t 'open_ee_var' x" := (open_exp_wrt_exp t (e_var_f x)) (at level 67).

Inductive lc_exp : exp -> Prop :=
 | lc_e_var_f : forall (x:var),
     (lc_exp (e_var_f x))
 | lc_e_lit : forall i5,
     (lc_exp (e_lit i5))
 | lc_e_abs : forall (L:vars) (e:exp),
      ( forall x , x \notin  L  -> lc_exp  ( open_exp_wrt_exp e (e_var_f x) )  )  ->
     (lc_exp (e_abs e))
 | lc_e_app : forall (e1 e2:exp),
     (lc_exp e1) ->
     (lc_exp e2) ->
     (lc_exp (e_app e1 e2))
 | lc_e_typeof : forall (L:vars) (e:exp) (A:typ) (e1:exp) (B:typ) (e2:exp),
     (lc_exp e) ->
     ( forall x , x \notin  L  -> lc_exp  ( open_exp_wrt_exp e1 (e_var_f x) )  ) ->
     ( forall x , x \notin  L  -> lc_exp  ( open_exp_wrt_exp e2 (e_var_f x) )  ) ->
     (lc_exp (e_typeof e A e1 B e2))
 | lec_e_null :
     lc_exp e_null
 | lc_e_new : forall A,
     lc_exp (e_new A).

Fixpoint fv_exp (e_5:exp) : vars :=
  match e_5 with
  | (e_var_b nat) => \{}
  | (e_var_f x) => \{x}
  | (e_lit i5) => \{}
  | (e_abs e) => (fv_exp e)
  | (e_app e1 e2) => (fv_exp e1) \u (fv_exp e2)
  | (e_typeof e A e1 B e2) => (fv_exp e) \u (fv_exp e1) \u (fv_exp e2)
  | (e_null) => \{}
  | e_new A  => \{}
end.

Fixpoint subst_exp (e_5:exp) (x5:var) (e__6:exp) {struct e__6} : exp :=
  match e__6 with
  | (e_var_b nat) => e_var_b nat
  | (e_var_f x) => (If x = x5 then e_5 else (e_var_f x))
  | (e_lit i5) => e_lit i5
  | (e_abs e) => e_abs (subst_exp e_5 x5 e)
  | (e_app e1 e2) => e_app (subst_exp e_5 x5 e1) (subst_exp e_5 x5 e2)
  | (e_typeof e A e1 B e2) => e_typeof (subst_exp e_5 x5 e) A (subst_exp e_5 x5 e1) B (subst_exp e_5 x5 e2)
  | (e_null) => e_null
  | (e_new A) => e_new A
  end.

Inductive value : exp -> Prop :=
 | val_int : forall i5,
     value (e_lit i5)
 | val_abs : forall e,
     lc_exp (e_abs e) ->
     value (e_abs e)
 | val_null :
     value e_null
 | val_new  : forall P,
     value  (e_new P).

Inductive findtype : exp -> typ -> Prop :=
 | findtype_int : forall i5,
     findtype (e_lit i5) t_int
 | findtype_arrow : forall (e:exp),
     lc_exp (e_abs e) ->
     findtype  (e_abs e) (t_arrow t_top t_bot)
 | findtype_null :
     findtype e_null t_unit
 | find_type_new : forall P,
     findtype (e_new P) (t_prim P).

Inductive typing (PG:envp) : env -> exp -> typ -> Prop :=
 | typ_lit : forall (G:env) i5,
      ok  G  ->
      okenvp PG ->
     typing PG G (e_lit i5) t_int
 | typ_null : forall G,
      ok G ->
      okenvp PG ->
      typing PG G e_null t_unit
 | typ_var : forall (G:env) (x:var) (A:typ),
      ok  G  ->
      okenvp PG ->
      wft PG A ->
      binds  x A G  ->
     typing PG G (e_var_f x) A
 | typ_app : forall (G:env) (e1 e2:exp) (B A:typ),
     okenvp PG -> wft PG A -> wft PG B ->
     typing PG G e1 (t_arrow A B) ->
     typing PG G e2 A ->
     typing PG G (e_app e1 e2) B
 | typ_sub : forall (G:env) (e:exp) (A B:typ),
     typing PG G e B ->
     declarative_subtyping PG B A ->
     typing PG G e A
 | typ_abs : forall (L:vars) (G:env) (e:exp) (A B:typ),
      okenvp PG -> wft PG A -> wft PG B ->
      ( forall x , x \notin  L  -> typing PG (G & x ~: A )   ( open_exp_wrt_exp e (e_var_f x) ) B )  ->
     typing PG G (e_abs e) (t_arrow A B)
 | typ_typeof : forall (L:vars) (G:env) (e:exp) (A:typ) (e1:exp) (B:typ) (e2:exp) (C:typ),
     typing PG G e (t_union A B) ->
     ( forall x , x \notin  L  -> typing PG  (G & x ~: A )   ( open_exp_wrt_exp e1 (e_var_f x) ) C ) ->
     ( forall x , x \notin  L  -> typing PG  (G & x ~: B )   ( open_exp_wrt_exp e2 (e_var_f x) ) C ) ->
     PG ||- A *s B ->
     typing PG G (e_typeof e A e1 B e2) C
 | typ_prim : forall i G,
    ok G ->
    okenvp PG -> wft PG (t_prim i) ->
     typing PG G (e_new i) (t_prim i).

Reserved Notation "PG ||- e --> e'" (at level 80).

Inductive step (PG:envp) : exp -> exp -> Prop :=
 | step_appl : forall (e1 e2 e1':exp),
     lc_exp e2 ->
     PG ||- e1 --> e1' ->
     PG ||- (e_app e1 e2) --> (e_app e1' e2)
 | step_appr : forall (v e e':exp),
     value v ->
     PG ||- e --> e' ->
     PG ||- (e_app v e) --> (e_app v e')
 | step_beta : forall (e:exp) (v:exp),
     lc_exp (e_abs e) ->
     value v ->
     PG ||- e_app  (e_abs e) v --> (open_exp_wrt_exp e v)
 | step_typeof : forall (e:exp) (A:typ) (e1:exp) (B:typ) (e2 e':exp),
     lc_exp (e_typeof e A e1 B e2) ->
     PG ||- e --> e' ->
     PG ||- (e_typeof e A e1 B e2) --> (e_typeof e' A e1 B e2)
 | step_typeofl : forall (v:exp) (A:typ) (e1:exp) (B:typ) (e2:exp) (C:typ),
     lc_exp (e_typeof v A e1 B e2) ->
     value v ->
     findtype v C ->
     declarative_subtyping PG C A ->
     PG ||- (e_typeof v A e1 B e2) -->  (open_exp_wrt_exp e1 v)
 | step_typeofr : forall (v:exp) (A:typ) (e1:exp) (B:typ) (e2:exp) (C:typ),
    lc_exp (e_typeof v A e1 B e2) ->
     value v ->
     findtype v C ->
     declarative_subtyping PG C B ->
     PG ||- (e_typeof v A e1 B e2) -->  (open_exp_wrt_exp  e2 v )
where "PG ||- e --> e'" := (step PG e e') : env_scope.

Require Import Program.Equality.

Lemma wft_primitive_env_cons PG i A T :
  wft PG T -> wft ((i, A) :: PG) T.
Proof.
  intro H. induction H; eauto using wft, Metatheory.EnvImpl.binds_cons_3.
Qed.

Lemma primitive_binding PG i A :
  okenvp PG -> Metatheory.EnvImpl.binds i A PG ->
  wft PG A /\ (A = t_top \/ exists j, A = t_prim j).
Proof.
  intros Hok. induction Hok; intro Hb.
  - now apply Metatheory.EnvImpl.binds_nil_iff in Hb.
  - apply Metatheory.EnvImpl.binds_cons_iff in Hb as [[_ ->] | Hb].
    + split.
      * constructor.
      * now left.
    + destruct (IHHok Hb) as [Hw Hshape].
      split; auto using wft_primitive_env_cons.
  - apply Metatheory.EnvImpl.binds_cons_iff in Hb as [[_ ->] | Hb].
    + split.
      * now apply wft_primitive_env_cons.
      * right. now exists j.
    + destruct (IHHok Hb) as [Hw Hshape].
      split; auto using wft_primitive_env_cons.
Qed.

Lemma subtyping_regular PG A B :
  declarative_subtyping PG A B -> okenvp PG /\ wft PG A /\ wft PG B.
Proof.
  intro H. induction H; intuition eauto 8 using wft.
  match goal with
  | Hok : okenvp PG, Hb : Metatheory.EnvImpl.binds _ _ PG |- _ =>
      exact (proj1 (primitive_binding PG _ _ Hok Hb))
  end.
Qed.

(* For an ordinary source S, interpret unions as disjunctions and
   intersections as conjunctions. An arrow target tests both variances. *)
Fixpoint accepts (PG : envp) (S T : typ) : Prop :=
  match T with
  | t_top => True
  | t_bot => False
  | t_union A B => accepts PG S A \/ accepts PG S B
  | t_and A B => accepts PG S A /\ accepts PG S B
  | t_int => S = t_int
  | t_unit => S = t_unit
  | t_arrow B D =>
      match S with
      | t_arrow A C =>
          declarative_subtyping PG B A /\ declarative_subtyping PG C D
      | _ => False
      end
  | t_prim j =>
      match S with
      | t_prim i => declarative_subtyping PG (t_prim i) (t_prim j)
      | _ => False
      end
  end.

Lemma accepts_subtyping PG A B :
  declarative_subtyping PG A B ->
  forall S, accepts PG S A -> accepts PG S B.
Proof.
  intros H S. induction H; intro HS; simpl in *; try tauto.
  - destruct S; simpl in *; try contradiction.
    destruct HS. split; eauto using DS_trans.
  - destruct S; simpl in *; try tauto.
    destruct HS as [[Hdom Hcod1] [_ Hcod2]].
    split; eauto using DS_and.
  - destruct S; simpl in *; try tauto.
    destruct HS as [[Hdom1 Hcod] [Hdom2 _]].
    split; eauto using DS_or.
  - destruct (primitive_binding PG i A H H0) as [_ [-> | [j ->]]].
    + exact I.
    + destruct S; simpl in *; try contradiction.
      eapply DS_trans; eauto using DS_prim.
Qed.

Lemma accepts_ordinary_refl PG S :
  Ord S -> okenvp PG -> wft PG S -> accepts PG S S.
Proof.
  intros Hord Hok Hw. destruct Hord; simpl; inversion Hw; try split; auto using DS_refl.
Qed.

Lemma accepts_sound PG S T :
  okenvp PG -> wft PG S -> wft PG T ->
  accepts PG S T -> declarative_subtyping PG S T.
Proof.
  intros Hok Hsrc Hwf. induction Hwf; simpl.
  - auto using DS_top.
  - contradiction.
  - intros ->. now apply DS_refl.
  - destruct S; try contradiction.
    intros [Hdom Hcod]. now apply DS_arrow.
  - intros [HA | HB].
    + eapply DS_trans; eauto using DS_orl.
    + eapply DS_trans; eauto using DS_orr.
  - intros [HA HB]. apply DS_and; auto.
  - intros ->. now apply DS_refl.
  - destruct S; tauto.
Qed.

Lemma subtyping_union_ordinary PG S A B :
  Ord S -> declarative_subtyping PG S (t_union A B) ->
  declarative_subtyping PG S A \/ declarative_subtyping PG S B.
Proof.
  intros Hord Hsub.
  destruct (subtyping_regular PG _ _ Hsub) as [Hok [HS HAB]].
  inversion HAB; subst.
  pose proof (accepts_subtyping PG _ _ Hsub S
    (accepts_ordinary_refl PG S Hord Hok HS)) as H.
  simpl in H. destruct H.
  - left. eauto using accepts_sound.
  - right. eauto using accepts_sound.
Qed.

Lemma subtyping_arrow_inv PG A B C D :
  declarative_subtyping PG (t_arrow A B) (t_arrow C D) ->
  declarative_subtyping PG C A /\ declarative_subtyping PG B D.
Proof.
  intro Hsub.
  destruct (subtyping_regular PG _ _ Hsub) as [Hok [Hwf _]].
  exact (accepts_subtyping PG _ _ Hsub _
    (accepts_ordinary_refl PG _ (o_arrow A B) Hok Hwf)).
Qed.

Lemma typing_lc PG G e T : typing PG G e T -> lc_exp e.
Proof.
  intro Hty.
  induction Hty as
    [G n Hok Hpg | G Hok Hpg | G x A Hok Hpg HA Hbind
    | G e1 e2 B A Hpg HA HB Hfun IHfun Harg IHarg
    | G e A B Hty IH Hsub
    | L G e A B Hpg HA HB Hbody IHbody
    | L G e A e1 B e2 C Htest IHtest Hleft IHleft Hright IHright Hdisj
    | i G Hok Hpg HA]; try solve [assumption | now constructor].
  - now apply lc_e_abs with (L := L).
  - now apply lc_e_typeof with (L := L).
Qed.

Lemma binds_push_mono (G G' : env) y B :
  (forall x A, binds x A G -> binds x A G') ->
  forall x A, binds x A (G & y ~: B) -> binds x A (G' & y ~: B).
Proof.
  intros Hin x A Hbind.
  apply binds_push_inv in Hbind as [[-> ->] | [Hxy Hbind]].
  - apply binds_push_eq.
  - apply binds_push_neq; auto.
Qed.

Lemma typing_weakening PG G e T :
  typing PG G e T ->
  forall G', ok G' ->
    (forall x A, binds x A G -> binds x A G') ->
    typing PG G' e T.
Proof.
  intro Hty.
  induction Hty as
    [G n HG Hpg | G HG Hpg | G x A HG Hpg HA Hbind
    | G e1 e2 B A Hpg HA HB Hfun IHfun Harg IHarg
    | G e A B Hty IH Hsub
    | L G e A B Hpg HA HB Hbody IHbody
    | L G e A e1 B e2 C Htest IHtest Hleft IHleft Hright IHright Hdisj
    | i G HG Hpg HA];
    intros G' Hok Hin; try solve [eauto using typing].
  - apply typ_abs with (L := L \u dom G'); auto.
    intros x Hx. apply notin_union in Hx as [Hx Hfresh].
    apply IHbody; [exact Hx | now apply ok_push | now apply binds_push_mono].
  - apply typ_typeof with (L := L \u dom G'); auto.
    + intros x Hx. apply notin_union in Hx as [Hx Hfresh].
      apply IHleft; [exact Hx | now apply ok_push | now apply binds_push_mono].
    + intros x Hx. apply notin_union in Hx as [Hx Hfresh].
      apply IHright; [exact Hx | now apply ok_push | now apply binds_push_mono].
Qed.

Lemma open_exp_rec_other_index e :
  forall i j u x, i <> j ->
  open_exp_wrt_exp_rec i u (open_exp_wrt_exp_rec j (e_var_f x) e) =
    open_exp_wrt_exp_rec j (e_var_f x) e ->
  open_exp_wrt_exp_rec i u e = e.
Proof.
  induction e; intros i j u x Hij H; simpl in *; try reflexivity.
  - destruct (classicT (j = n)) as [-> | Hjn].
    + now rewrite If_r.
    + exact H.
  - f_equal. apply (IHe (S i) (S j) u x); congruence.
  - f_equal.
    + apply (IHe1 i j u x); congruence.
    + apply (IHe2 i j u x); congruence.
  - f_equal.
    + apply (IHe1 i j u x); congruence.
    + apply (IHe2 (S i) (S j) u x); congruence.
    + apply (IHe3 (S i) (S j) u x); congruence.
Qed.

Lemma open_exp_rec_lc e :
  lc_exp e -> forall k u, open_exp_wrt_exp_rec k u e = e.
Proof.
  intros Hlc. induction Hlc; intros k u; simpl; try reflexivity.
  - destruct (var_fresh L) as [x Hx].
    f_equal. apply (open_exp_rec_other_index e (S k) 0 u x).
    + discriminate.
    + exact (H0 x Hx (S k) u).
  - now rewrite IHHlc1, IHHlc2.
  - destruct (var_fresh L) as [x Hx].
    rewrite IHHlc. f_equal.
    + apply (open_exp_rec_other_index e1 (S k) 0 u x).
      * discriminate.
      * exact (H0 x Hx (S k) u).
    + apply (open_exp_rec_other_index e2 (S k) 0 u x).
      * discriminate.
      * exact (H2 x Hx (S k) u).
Qed.

Lemma subst_exp_open_rec e u x :
  lc_exp u -> forall k w,
    subst_exp u x (open_exp_wrt_exp_rec k w e) =
    open_exp_wrt_exp_rec k (subst_exp u x w) (subst_exp u x e).
Proof.
  intro Hlc. induction e; intros k w; simpl; try reflexivity.
  - destruct (classicT (k = n)); reflexivity.
  - destruct (classicT (v = x)).
    + symmetry. now apply open_exp_rec_lc.
    + reflexivity.
  - now rewrite IHe.
  - now rewrite IHe1, IHe2.
  - now rewrite IHe1, IHe2, IHe3.
Qed.

Lemma subst_exp_open_var e u x y :
  lc_exp u -> y <> x ->
  subst_exp u x (e open_ee_var y) = subst_exp u x e open_ee_var y.
Proof.
  intros Hlc Hneq. unfold open_exp_wrt_exp.
  rewrite subst_exp_open_rec by exact Hlc.
  simpl. now rewrite If_r.
Qed.

Lemma subst_exp_intro e :
  forall k u x, x \notin fv_exp e ->
    open_exp_wrt_exp_rec k u e =
    subst_exp u x (open_exp_wrt_exp_rec k (e_var_f x) e).
Proof.
  induction e; intros k u x Hfresh; simpl in *; try reflexivity.
  - destruct (classicT (k = n)); simpl; [now rewrite If_l | reflexivity].
  - apply notin_singleton in Hfresh.
    rewrite If_r by congruence. reflexivity.
  - now rewrite <- IHe.
  - apply notin_union in Hfresh as [H1 H2].
    now rewrite <- IHe1, <- IHe2.
  - apply notin_union in Hfresh as [H1 H23].
    apply notin_union in H23 as [H2 H3].
    now rewrite <- IHe1, <- IHe2, <- IHe3.
Qed.

Lemma typing_substitution PG G e T :
  typing PG G e T ->
  forall E F x U u, G = E & x ~: U & F ->
    typing PG E u U ->
    typing PG (E & F) (subst_exp u x e) T.
Proof.
  intro Hty.
  induction Hty as
    [G n HG Hpg | G HG Hpg | G y A HG Hpg HA Hbind
    | G e1 e2 B A Hpg HA HB Hfun IHfun Harg IHarg
    | G e A B Hty IH Hsub
    | L G e A B Hpg HA HB Hbody IHbody
    | L G e A e1 B e2 C Htest IHtest Hleft IHleft Hright IHright Hdisj
    | i G HG Hpg HA];
    intros E F x U u Heq Hu; subst G; simpl.
  - eauto using typ_lit, ok_remove.
  - eauto using typ_null, ok_remove.
  - destruct (classicT (y = x)) as [-> | Hneq].
    + assert (A = U) by (eapply binds_middle_eq_inv; eassumption).
      subst A.
      eapply typing_weakening; eauto using ok_remove, binds_concat_left_ok.
    + eauto using typ_var, ok_remove, binds_subst.
  - eauto using typ_app.
  - eauto using typ_sub.
  - apply typ_abs with (L := L \u \{x}); auto.
    intros y Hy. apply notin_union in Hy as [Hy Hneq].
    apply notin_singleton in Hneq.
    rewrite <- subst_exp_open_var by eauto using typing_lc.
    rewrite <- (@concat_assoc typ E F (y ~: A)).
    eapply IHbody; eauto.
    now rewrite concat_assoc.
  - apply typ_typeof with (L := L \u \{x}); eauto.
    + intros y Hy. apply notin_union in Hy as [Hy Hneq].
      apply notin_singleton in Hneq.
      rewrite <- subst_exp_open_var by eauto using typing_lc.
      rewrite <- (@concat_assoc typ E F (y ~: A)).
      eapply IHleft; eauto.
      now rewrite concat_assoc.
    + intros y Hy. apply notin_union in Hy as [Hy Hneq].
      apply notin_singleton in Hneq.
      rewrite <- subst_exp_open_var by eauto using typing_lc.
      rewrite <- (@concat_assoc typ E F (y ~: B)).
      eapply IHright; eauto.
      now rewrite concat_assoc.
  - eauto using typ_prim, ok_remove.
Qed.

Lemma typing_open PG G L e u A B :
  (forall x, x \notin L -> typing PG (G & x ~: A) (e open_ee_var x) B) ->
  typing PG G u A ->
  typing PG G (open_exp_wrt_exp e u) B.
Proof.
  intros Hbody Hu.
  destruct (var_fresh (L \u fv_exp e)) as [x Hx].
  apply notin_union in Hx as [Hx Hfresh].
  assert (Hbody' : typing PG (G & x ~: A & empty) (e open_ee_var x) B).
  { rewrite concat_empty_r. now apply Hbody. }
  unfold open_exp_wrt_exp at 1.
  rewrite (subst_exp_intro e 0 u x Hfresh).
  pose proof (typing_substitution PG _ _ _ Hbody' G empty x A u eq_refl Hu) as H.
  now rewrite concat_empty_r in H.
Qed.

Lemma typing_abs_inv PG G e T :
  typing PG G (e_abs e) T ->
  exists L A B,
    (forall x, x \notin L -> typing PG (G & x ~: A) (e open_ee_var x) B) /\
    declarative_subtyping PG (t_arrow A B) T.
Proof.
  intro Hty. remember (e_abs e) as v eqn:Hev.
  induction Hty; inversion Hev; subst.
  - destruct (IHHty eq_refl) as [L [A0 [B0 [Hbody Hsub]]]].
    exists L, A0, B0. split; eauto using DS_trans.
  - exists L, A, B. split; eauto using DS_refl, wft_arrow.
Qed.

Lemma value_findtype v : value v -> exists C, findtype v C.
Proof.
  intro Hv. destruct Hv; eauto using findtype.
Qed.

Lemma findtype_ord v C : findtype v C -> Ord C.
Proof.
  intro H. destruct H; constructor.
Qed.

(* The type introduced before subsumption is ordinary and lies between
   the runtime tag and the type assigned to the value. *)
Lemma typing_findtype_source PG G v T C :
  typing PG G v T -> findtype v C ->
  exists S, Ord S /\ typing PG G v S /\
    declarative_subtyping PG S T /\ declarative_subtyping PG C S.
Proof.
  intro Hty.
  induction Hty as
    [G n HG Hpg | G HG Hpg | G x A HG Hpg HA Hbind
    | G e1 e2 B A Hpg HA HB Hfun IHfun Harg IHarg
    | G e A B Hty IH Hsub
    | L G e A B Hpg HA HB Hbody IHbody
    | L G e A e1 B e2 T Htest IHtest Hleft IHleft Hright IHright Hdisj
    | i G HG Hpg HA];
    intro Hfind; try solve [inversion Hfind].
  - inversion Hfind; subst. exists t_int.
    repeat split; eauto using o_int, typ_lit, DS_refl, wft_int.
  - inversion Hfind; subst. exists t_unit.
    repeat split; eauto using o_unit, typ_null, DS_refl, wft_unit.
  - destruct (IH Hfind) as [S [Hord [HS [HST HCS]]]].
    exists S. repeat split; eauto using DS_trans.
  - inversion Hfind; subst. exists (t_arrow A B).
    repeat split; eauto using o_arrow, typ_abs, DS_refl, wft_arrow.
    apply DS_arrow; eauto using DS_top, DS_bot.
  - inversion Hfind; subst. eexists (t_prim _).
    repeat split; eauto using o_prim, typ_prim, DS_refl.
Qed.

Lemma typing_findtype_subtyping PG G v T C :
  typing PG G v T -> findtype v C -> declarative_subtyping PG C T.
Proof.
  intros Hty Hfind.
  destruct (typing_findtype_source PG G v T C Hty Hfind)
    as [S [_ [_ [HST HCS]]]].
  eauto using DS_trans.
Qed.

Lemma typing_value_arrow PG G v A B :
  typing PG G v (t_arrow A B) -> value v ->
  exists e, v = e_abs e /\ lc_exp (e_abs e).
Proof.
  intros Hty Hv.
  destruct (value_findtype v Hv) as [C Hfind].
  pose proof (typing_findtype_subtyping PG G v _ C Hty Hfind) as Hsub.
  destruct (subtyping_regular PG _ _ Hsub) as [Hok [HC _]].
  pose proof (accepts_subtyping PG _ _ Hsub C
    (accepts_ordinary_refl PG C (findtype_ord v C Hfind) Hok HC)) as H.
  destruct Hfind; simpl in H; try contradiction.
  eauto.
Qed.

Lemma typing_switch_value PG G v A B C :
  typing PG G v (t_union A B) -> findtype v C -> PG ||- A *s B ->
  (declarative_subtyping PG C A -> typing PG G v A) /\
  (declarative_subtyping PG C B -> typing PG G v B).
Proof.
  intros Hty Hfind Hdisj.
  destruct (typing_findtype_source PG G v _ C Hty Hfind)
    as [S [Hord [HS [Hunion HCS]]]].
  (* The runtime tag cannot also be below the opposite branch. *)
  destruct (subtyping_union_ordinary PG S A B Hord Hunion) as [HSA | HSB].
  - split; intro Hbranch.
    + eauto using typ_sub.
    + exfalso. apply (Hdisj C (findtype_ord v C Hfind)).
      apply DS_and; eauto using DS_trans.
  - split; intro Hbranch.
    + exfalso. apply (Hdisj C (findtype_ord v C Hfind)).
      apply DS_and; eauto using DS_trans.
    + eauto using typ_sub.
Qed.

Theorem preservation : forall PG E e e' T,
  typing PG E e T ->
  PG ||- e --> e' ->
  typing PG E e' T.
Proof.
  intros PG E e e' T Hty. revert e'.
  induction Hty as
    [G n HG Hpg | G HG Hpg | G x A HG Hpg HA Hbind
    | G e1 e2 B A Hpg HA HB Hfun IHfun Harg IHarg
    | G e A B Hty IH Hsub
    | L G e A B Hpg HA HB Hbody IHbody
    | L G e A e1 B e2 C Htest IHtest Hleft IHleft Hright IHright Hdisj
    | i G HG Hpg HA];
    intros e' Hstep; try solve [inversion Hstep].
  - inversion Hstep as
      [f a f' Hlc Hfstep | f a a' Hv Hastep | body v Hlc Hv | | |]; subst.
    + eauto using typ_app.
    + eauto using typ_app.
    + destruct (typing_abs_inv PG G body _ Hfun)
        as [K [D [R [Hbody Harr]]]].
      destruct (subtyping_arrow_inv PG D R A B Harr) as [Hdom Hcod].
      eapply typ_sub.
      * eapply typing_open; eauto using typ_sub.
      * exact Hcod.
  - eauto using typ_sub.
  - inversion Hstep as
      [ | | | tested A0 l B0 r tested' Hlc Htested
      | v A0 l B0 r R Hlc Hv Hfind Hbranch
      | v A0 l B0 r R Hlc Hv Hfind Hbranch]; subst.
    + eauto using typ_typeof.
    + destruct (typing_switch_value PG G e A B R Htest Hfind Hdisj) as [Hl _].
      eapply typing_open; eauto.
    + destruct (typing_switch_value PG G e A B R Htest Hfind Hdisj) as [_ Hr].
      eapply typing_open; eauto.
Qed.

Theorem progress : forall PG e T,
    typing PG empty e T -> (value e) \/ (exists e', PG ||- e --> e').
Proof.
  intros PG e T Hty. remember (empty : env) as G eqn:HG.
  induction Hty as
    [G n Hok Hpg | G Hok Hpg | G x A Hok Hpg HA Hbind
    | G e1 e2 B A Hpg HA HB Hfun IHfun Harg IHarg
    | G e A B Hty IH Hsub
    | L G e A B Hpg HA HB Hbody IHbody
    | L G e A e1 B e2 C Htest IHtest Hleft IHleft Hright IHright Hdisj
    | i G Hok Hpg HA]; subst G.
  - left. constructor.
  - left. constructor.
  - exfalso. eapply binds_empty_inv; eassumption.
  - destruct (IHfun eq_refl) as [Hfval | [e1' Hstep]].
    + destruct (IHarg eq_refl) as [Haval | [e2' Hstep]].
      * destruct (typing_value_arrow PG empty e1 A B Hfun Hfval)
          as [body [-> Hlc]].
        right. eexists. now apply step_beta.
      * right. exists (e_app e1 e2'). now apply step_appr.
    + right. exists (e_app e1' e2).
      apply step_appl; eauto using typing_lc.
  - exact (IH eq_refl).
  - left. apply val_abs.
    apply lc_e_abs with (L := L). eauto using typing_lc.
  - assert (Hlc : lc_exp (e_typeof e A e1 B e2)).
    { apply lc_e_typeof with (L := L); eauto using typing_lc. }
    right. destruct (IHtest eq_refl) as [Hv | [e' Hstep]].
    + destruct (value_findtype e Hv) as [R Hfind].
      pose proof (typing_findtype_subtyping PG empty e _ R Htest Hfind) as Hsub.
      destruct (subtyping_union_ordinary PG R A B (findtype_ord e R Hfind) Hsub)
        as [HleftType | HrightType].
      * eexists. eapply step_typeofl; eassumption.
      * eexists. eapply step_typeofr; eassumption.
    + exists (e_typeof e' A e1 B e2). now apply step_typeof.
  - left. constructor.
Qed.

End Typing_part.
