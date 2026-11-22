Require Import TLC.LibLN.

Require Import Program.Equality.

Require Import Coq.Lists.ListSet.

Require Import Lists.List.

Require Import equivalence.

Require Import Lia.

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


(* ==================== from G1.v ==================== *)


Fixpoint lc_at (d:nat) (t:exp) {struct t} : Prop :=
  match t with
  | e_var_b n => n < d
  | e_var_f _ => True
  | e_lit _ => True
  | e_abs e => lc_at (S d) e
  | e_app e1 e2 => lc_at d e1 /\ lc_at d e2
  | e_typeof e A e1 B e2 => lc_at d e /\ lc_at (S d) e1 /\ lc_at (S d) e2
  | e_null => True
  | e_new _ => True
  end.

Lemma lc_at_open_rec : forall t d, lc_at d t -> forall k u, d <= k -> open_exp_wrt_exp_rec k u t = t.
Proof.
  induction t as [ n | x0 | i_lit | e0 IH0 | e1 IH1 e2 IH2 | e0 IH0 A e1 IH1 B e2 IH2 | | i_new ];
    intros d Hd k u Hk; simpl in *.
  - destruct (classicT (k = n)) as [Heq | Hne]; simpl.
    + exfalso. lia.
    + reflexivity.
  - reflexivity.
  - reflexivity.
  - f_equal. apply (IH0 (S d)). exact Hd. lia.
  - destruct Hd as [Hd1 Hd2]. rewrite (IH1 d Hd1 k u Hk). rewrite (IH2 d Hd2 k u Hk). reflexivity.
  - destruct Hd as [Hd0 [Hd1 Hd2]].
    rewrite (IH0 d Hd0 k u Hk). rewrite (IH1 (S d) Hd1 (S k) u) by lia.
    rewrite (IH2 (S d) Hd2 (S k) u) by lia. reflexivity.
  - reflexivity.
  - reflexivity.
Qed.

Lemma lc_at_open_inv : forall e k x, lc_at k (open_exp_wrt_exp_rec k (e_var_f x) e) -> lc_at (S k) e.
Proof.
  induction e as [ n | x0 | i_lit | e0 IH0 | e1 IH1 e2 IH2 | e0 IH0 A e1 IH1 B e2 IH2 | | i_new ];
    intros k x H; simpl in *.
  - destruct (classicT (k = n)) as [Heq | Hne]; simpl in *; lia.
  - auto.
  - auto.
  - apply (IH0 (S k) x). auto.
  - split; [apply (IH1 k x) | apply (IH2 k x)]; tauto.
  - split; [apply (IH0 k x) | split; [apply (IH1 (S k) x) | apply (IH2 (S k) x)]]; tauto.
  - auto.
  - auto.
Qed.

Lemma lc_lc_at : forall t, lc_exp t -> lc_at 0 t.
Proof.
  intros t H.
  induction H as [ x | i | L e0 Hbody IHbody | e1 e2 H1 IH1 H2 IH2
                 | L e0 A e1 B e2 H0 IH0 H1 IH1 H2 IH2 | | A ]; simpl.
  - exact I.
  - exact I.
  - destruct (var_fresh L) as [x Hx]. apply lc_at_open_inv with (k:=0) (x:=x). apply IHbody. auto.
  - split; auto.
  - destruct (var_fresh L) as [x Hx].
    split; [exact IH0 | split].
    + apply lc_at_open_inv with (k:=0) (x:=x). apply IH1. auto.
    + apply lc_at_open_inv with (k:=0) (x:=x). apply IH2. auto.
  - exact I.
  - exact I.
Qed.

Lemma lc_exp_open_rec : forall (t:exp) (k:nat) (u:exp), lc_exp t -> open_exp_wrt_exp_rec k u t = t.
Proof.
  intros. apply lc_at_open_rec with (d:=0); auto. apply lc_lc_at. auto. lia.
Qed.

Lemma open_subst_comm : forall k (e:exp) (v:exp) (x y:var),
  lc_exp v -> y <> x ->
  open_exp_wrt_exp_rec k (e_var_f y) (subst_exp v x e) =
  subst_exp v x (open_exp_wrt_exp_rec k (e_var_f y) e).
Proof.
  intros k e0. revert k.
  induction e0 as [ n | x0 | i_lit | e0 IH0 | e1 IH1 e2 IH2 | e0 IH0 A e1 IH1 B e2 IH2 | | i_new ];
    intros k v x y Hlc Hneq; simpl.
  - destruct (classicT (k = n)) as [Heq | Hne]; simpl.
    + destruct (classicT (y = x)) as [Heq2 | Hne2]; simpl; [exfalso; auto | reflexivity].
    + reflexivity.
  - destruct (classicT (x0 = x)) as [Heq | Hne]; simpl.
    + rewrite lc_exp_open_rec with (k:=k) (u:=e_var_f y) by auto. reflexivity.
    + reflexivity.
  - reflexivity.
  - f_equal. apply (IH0 (S k) v x y); auto.
  - rewrite (IH1 k v x y) by auto. rewrite (IH2 k v x y) by auto. reflexivity.
  - rewrite (IH0 k v x y) by auto. rewrite (IH1 (S k) v x y) by auto.
    rewrite (IH2 (S k) v x y) by auto. reflexivity.
  - reflexivity.
  - reflexivity.
Qed.

Lemma open_subst_comm' : forall (e:exp) (v:exp) (x y:var),
  lc_exp v -> y <> x ->
  open_exp_wrt_exp (subst_exp v x e) (e_var_f y) =
  subst_exp v x (open_exp_wrt_exp e (e_var_f y)).
Proof. intros. unfold open_exp_wrt_exp. apply open_subst_comm; auto. Qed.

Lemma subst_open_rec_ident : forall k (e:exp) (v:exp) (x:var),
  x \notin fv_exp e ->
  subst_exp v x (open_exp_wrt_exp_rec k (e_var_f x) e) = open_exp_wrt_exp_rec k v e.
Proof.
  intros k e0. revert k.
  induction e0 as [ n | x0 | i_lit | e0 IHe0 | e1 IHe1 e2 IHe2 | e0 IHe0 A e1 IHe1 B e2 IHe2 | | i_new ];
    intros k vv xx Hx; simpl.
  - destruct (classicT (k = n)) as [Heq | Hne]; simpl.
    + destruct (classicT (xx = xx)) as [Heq2 | Hne2]; simpl; [reflexivity | exfalso; apply Hne2; reflexivity].
    + reflexivity.
  - destruct (classicT (x0 = xx)) as [Heq | Hne]; simpl.
    + exfalso. apply (notin_singleton_r Hx). auto.
    + reflexivity.
  - reflexivity.
  - simpl in *. f_equal. apply IHe0. auto.
  - simpl in *. apply notin_union_r in Hx. destruct Hx as [Hx1 Hx2].
    rewrite IHe1 by auto. rewrite IHe2 by auto. reflexivity.
  - simpl in *. apply notin_union_r in Hx. destruct Hx as [Hx1 Hx2].
    apply notin_union_r in Hx2. destruct Hx2 as [Hx2 Hx3].
    rewrite IHe0 by auto. rewrite IHe1 by auto. rewrite IHe2 by auto. reflexivity.
  - reflexivity.
  - reflexivity.
Qed.

Lemma subst_open_ident : forall (e:exp) (v:exp) (x:var),
  x \notin fv_exp e ->
  subst_exp v x (open_exp_wrt_exp e (e_var_f x)) = open_exp_wrt_exp e v.
Proof.
  intros e v x Hx. unfold open_exp_wrt_exp. apply subst_open_rec_ident. auto.
Qed.

(* ==================== from G0.v ==================== *)


Lemma wft_arrow_inv : forall PG A B, wft PG (t_arrow A B) -> wft PG A /\ wft PG B.
Proof. intros. inversion H. auto. Qed.
Lemma wft_union_inv : forall PG A B, wft PG (t_union A B) -> wft PG A /\ wft PG B.
Proof. intros. inversion H. auto. Qed.
Lemma wft_and_inv : forall PG A B, wft PG (t_and A B) -> wft PG A /\ wft PG B.
Proof. intros. inversion H. auto. Qed.
Lemma wft_prim_inv : forall PG i, wft PG (t_prim i) -> exists A, Metatheory.EnvImpl.binds i A PG.
Proof. intros. inversion H. subst. eauto. Qed.

Lemma wft_mono : forall PG PG' A,
  (forall x B, Metatheory.EnvImpl.binds x B PG -> Metatheory.EnvImpl.binds x B PG') ->
  wft PG A -> wft PG' A.
Proof.
  intros PG PG' A Hmono H. induction H.
  - apply wft_top.
  - apply wft_bot.
  - apply wft_int.
  - apply wft_arrow; auto.
  - apply wft_or; auto.
  - apply wft_and; auto.
  - apply wft_unit.
  - eapply wft_prim; eauto.
Qed.

Lemma wft_cons : forall PG i v A, wft PG A -> wft ((i,v)::PG) A.
Proof.
  intros. apply wft_mono with (PG:=PG); auto. intros.
  rewrite Metatheory.EnvImpl.binds_cons_iff. right; auto.
Qed.

Lemma okenvp_binds_shape : forall PG (x:MetatheoryAtom.Atom.atom) (A:typ),
  okenvp PG -> Metatheory.EnvImpl.binds x A PG -> A = t_top \/ (exists j, A = t_prim j).
Proof.
  intros PG x A Hok. induction Hok as [| PG i Hok IH Hni | PG i j Hok IH Hwft Hni]; intros Hb.
  - rewrite Metatheory.EnvImpl.binds_nil_iff in Hb. destruct Hb.
  - rewrite Metatheory.EnvImpl.binds_cons_iff in Hb.
    destruct Hb as [[Heq1 Heq2] | Hb'].
    + left. subst. reflexivity.
    + apply IH. auto.
  - rewrite Metatheory.EnvImpl.binds_cons_iff in Hb.
    destruct Hb as [[Heq1 Heq2] | Hb'].
    + right. subst. exists j. reflexivity.
    + apply IH. auto.
Qed.

Lemma okenvp_binds_wft : forall PG (x:MetatheoryAtom.Atom.atom) (A:typ),
  okenvp PG -> Metatheory.EnvImpl.binds x A PG -> wft PG A.
Proof.
  intros PG x A Hok. induction Hok as [| PG i Hok IH Hni | PG i j Hok IH Hwft Hni]; intros Hb.
  - rewrite Metatheory.EnvImpl.binds_nil_iff in Hb. destruct Hb.
  - rewrite Metatheory.EnvImpl.binds_cons_iff in Hb.
    destruct Hb as [[Heq1 Heq2] | Hb'].
    + subst x. subst A. apply wft_cons. apply wft_top.
    + apply wft_cons. apply IH. auto.
  - rewrite Metatheory.EnvImpl.binds_cons_iff in Hb.
    destruct Hb as [[Heq1 Heq2] | Hb'].
    + subst x. subst A. apply wft_cons. exact Hwft.
    + apply wft_cons. apply IH. auto.
Qed.

Lemma typing_okenvp : forall PG G e T, typing PG G e T -> okenvp PG.
Proof. intros PG G e T H. induction H; auto. Qed.

(* ==================== from G2.v ==================== *)


Lemma env_one_r : forall (F:env) (x:var) (v:typ), F & x ~: v = (x, v) :: F.
Proof. intros. rewrite single_def. rewrite concat_def. reflexivity. Qed.

Lemma ok_insert_gen : forall (E F:env) (x:var) (v:typ),
  ok (E & F) -> x # (E & F) -> ok (E & x ~: v & F).
Proof.
  intros E F. induction F as [| [y b] F IH]; intros x v Hok Hx.
  - rewrite <- empty_def in Hok. rewrite concat_empty_r in Hok.
    rewrite <- empty_def in Hx. rewrite concat_empty_r in Hx.
    rewrite <- empty_def. rewrite concat_empty_r. apply ok_push; auto.
  - rewrite <- (env_one_r F y b) in Hok. rewrite <- (env_one_r F y b) in Hx.
    rewrite <- (env_one_r F y b).
    rewrite concat_assoc in Hok. rewrite concat_assoc in Hx.
    apply ok_push_inv in Hok. destruct Hok as [Hok' Hy].
    rewrite dom_concat in Hx. rewrite dom_concat in Hx. rewrite dom_single in Hx.
    apply notin_union_r in Hx. destruct Hx as [HxEF Hxy].
    apply notin_union_r in HxEF. destruct HxEF as [HxE HxF].
    rewrite concat_assoc.
    apply ok_push.
    + apply IH; auto.
    + rewrite dom_concat. rewrite dom_concat. rewrite dom_single.
      apply notin_union; split.
      * apply notin_union; split.
        -- rewrite dom_concat in Hy. apply notin_union_r in Hy; tauto.
        -- apply notin_singleton_l. auto.
      * rewrite dom_concat in Hy. apply notin_union_r in Hy; tauto.
Qed.


(* ==================== from G4.v ==================== *)


Lemma eq_middle : forall (G1 G2:env) (y:var) (A:typ),
  G1 & (G2 & y ~: A) = (G1 & G2) & y ~: A.
Proof. intros. rewrite concat_assoc. reflexivity. Qed.

Lemma notin_middle : forall (G1 G2:env) (x y:var) (A:typ),
  x # (G1 & G2) -> x <> y -> x # (G1 & (G2 & y ~: A)).
Proof.
  intros. rewrite eq_middle.
  rewrite dom_concat. rewrite dom_single.
  apply notin_union; split; auto.
Qed.

Lemma typing_weaken_gen : forall PG G1 G2 x A e T,
  typing PG (G1 & G2) e T -> x # (G1 & G2) -> typing PG (G1 & x ~: A & G2) e T.
Proof.
  intros PG G1 G2 x A e T H.
  remember (G1 & G2) as E eqn:HE.
  revert G1 G2 HE.
  induction H as [ G i Hok Hokp
                 | G Hok Hokp
                 | G y B Hok Hokp Hwft Hb
                 | G e1 e2 B A' Hokp HwftA HwftB Ht1 IH1 Ht2 IH2
                 | G e B A' Ht IHt Hsub
                 | L G e A' B Hokp HwftA HwftB Hbody IHbody
                 | L G e A' e1 B e2 C Ht IHt Hb1 IHb1 Hb2 IHb2 Hdisj
                 | i G Hok Hokp Hwft ];
    intros G1 G2 HE Hx.
  - (* lit *) apply typ_lit.
    + apply ok_insert_gen; [rewrite <- HE; auto | rewrite <- HE; exact Hx].
    + auto.
  - (* null *) apply typ_null.
    + apply ok_insert_gen; [rewrite <- HE; auto | rewrite <- HE; exact Hx].
    + auto.
  - (* var *) eapply typ_var.
    + apply ok_insert_gen; [rewrite <- HE; auto | rewrite <- HE; exact Hx].
    + auto.
    + auto.
    + rewrite HE in Hb. eapply binds_weaken.
      * exact Hb.
      * apply ok_insert_gen; [rewrite <- HE; auto | rewrite <- HE; exact Hx].
  - (* app *) eapply typ_app with (A := A') (B := B).
    + auto. + auto. + auto.
    + apply IH1; auto.
    + apply IH2; auto.
  - (* sub *) eapply typ_sub.
    + apply IHt; auto.
    + auto.
  - (* abs *)
    apply typ_abs with (L := L \u \{x}) (A := A') (B := B).
    + auto. + auto. + auto.
    + intros y Hy. apply notin_union_r in Hy. destruct Hy as [HyL Hyx].
      apply notin_singleton_r in Hyx.
      rewrite <- concat_assoc.
      apply (IHbody y HyL G1 (G2 & y ~: A')).
      * rewrite HE. rewrite eq_middle. reflexivity.
      * rewrite dom_concat. rewrite dom_single.
        apply notin_union; split; auto.
  - (* typeof *)
    eapply typ_typeof with (L := L \u \{x}).
    + apply IHt; auto.
    + intros y Hy. apply notin_union_r in Hy. destruct Hy as [HyL Hyx].
      apply notin_singleton_r in Hyx.
      rewrite <- concat_assoc.
      apply (IHb1 y HyL G1 (G2 & y ~: A')).
      * rewrite HE. rewrite eq_middle. reflexivity.
      * rewrite dom_concat. rewrite dom_single.
        apply notin_union; split; auto.
    + intros y Hy. apply notin_union_r in Hy. destruct Hy as [HyL Hyx].
      apply notin_singleton_r in Hyx.
      rewrite <- concat_assoc.
      apply (IHb2 y HyL G1 (G2 & y ~: B)).
      * rewrite HE. rewrite eq_middle. reflexivity.
      * rewrite dom_concat. rewrite dom_single.
        apply notin_union; split; auto.
    + auto.
  - (* prim *) apply typ_prim.
    + apply ok_insert_gen; [rewrite <- HE; auto | rewrite <- HE; exact Hx].
    + auto.
    + auto.
Qed.

(* ==================== from G3.v ==================== *)


Lemma typing_inv_lit : forall PG G i U,
  typing PG G (e_lit i) U -> ok G /\ okenvp PG /\ declarative_subtyping PG t_int U.
Proof.
  intros PG G i U H. dependent induction H.
  - split; [auto|]. split; [auto|]. apply DS_refl; [auto|apply wft_int].
  - destruct (IHtyping i eq_refl) as [Hok [Hokp Hsub]].
    split; [auto|]. split; [auto|]. eapply DS_trans; eauto.
Qed.

Lemma typing_inv_null : forall PG G U,
  typing PG G e_null U -> ok G /\ okenvp PG /\ declarative_subtyping PG t_unit U.
Proof.
  intros PG G U H. dependent induction H.
  - split; [auto|]. split; [auto|]. apply DS_refl; [auto|apply wft_unit].
  - destruct (IHtyping eq_refl) as [Hok [Hokp Hsub]].
    split; [auto|]. split; [auto|]. eapply DS_trans; eauto.
Qed.

Lemma typing_inv_new : forall PG G i U,
  typing PG G (e_new i) U -> ok G /\ okenvp PG /\ wft PG (t_prim i) /\ declarative_subtyping PG (t_prim i) U.
Proof.
  intros PG G i U H. dependent induction H.
  - destruct (IHtyping i eq_refl) as [Hok [Hokp [Hw Hsub]]].
    split; [auto|]. split; [auto|]. split; [auto|]. eapply DS_trans; eauto.
  - split; [auto|]. split; [auto|]. split; [auto|]. apply DS_refl; auto.
Qed.

Lemma typing_inv_abs : forall PG G e U,
  typing PG G (e_abs e) U ->
  exists L A B, okenvp PG /\ wft PG A /\ wft PG B /\
    (forall x, x \notin L -> typing PG (G & x ~: A) (open_exp_wrt_exp e (e_var_f x)) B) /\
    declarative_subtyping PG (t_arrow A B) U.
Proof.
  intros PG G e U H. dependent induction H.
  - destruct (IHtyping e eq_refl) as [L [A' [B' [Hok [Hw1 [Hw2 [Hbody Hsub]]]]]]].
    exists L, A', B'. split; [auto|]. split; [auto|]. split; [auto|]. split; [auto|].
    eapply DS_trans; eauto.
  - exists L, A, B. split; [auto|]. split; [auto|]. split; [auto|]. split; [auto|].
    apply DS_refl; [auto|apply wft_arrow; auto].
Qed.

Lemma typing_lc : forall PG G e T, typing PG G e T -> lc_exp e.
Proof.
  intros PG G e T H.
  induction H as [ G i Hok Hokp
                 | G Hok Hokp
                 | G x A Hok Hokp Hwft Hb
                 | G e1 e2 B A Hokp HwftA HwftB Ht1 IH1 Ht2 IH2
                 | G e A B Ht IHt Hsub
                 | L G e A B Hokp HwftA HwftB Hbody IHbody
                 | L G e A e1 B e2 C Ht IHt Hb1 IHb1 Hb2 IHb2 Hdisj
                 | i G Hok Hokp Hwft ].
  - simpl. constructor.
  - simpl. constructor.
  - simpl. constructor.
  - simpl. apply lc_e_app; auto.
  - simpl. exact IHt.
  - simpl. apply lc_e_abs with (L:=L). intros x Hx. apply IHbody. auto.
  - simpl. apply lc_e_typeof with (L:=L).
    + exact IHt.
    + intros x Hx. apply IHb1. auto.
    + intros x Hx. apply IHb2. auto.
  - simpl. constructor.
Qed.

Lemma value_lc : forall v, value v -> lc_exp v.
Proof. intros v H. induction H; auto; constructor; auto. Qed.

(* ==================== from G6.v ==================== *)


Lemma weaken_front : forall PG (E:env) (x:var) (A:typ) (e:exp) (T:typ),
  typing PG E e T -> x # E -> typing PG (E & x ~: A) e T.
Proof.
  intros.
  assert (H1 : typing PG (E & empty) e T) by (rewrite concat_empty_r; exact H).
  assert (H2 : x # (E & empty)) by (rewrite concat_empty_r; exact H0).
  pose proof (typing_weaken_gen PG E empty x A e T H1 H2) as Hw.
  rewrite concat_empty_r in Hw. exact Hw.
Qed.

Lemma typing_subst_gen : forall PG G1 G2 x A e T v,
  typing PG (G1 & x ~: A & G2) e T ->
  typing PG (G1 & G2) v A ->
  lc_exp v ->
  typing PG (G1 & G2) (subst_exp v x e) T.
Proof.
  intros PG G1 G2 x A e T v H.
  remember (G1 & x ~: A & G2) as C eqn:HC.
  revert G1 G2 x A v HC.
  induction H as [ G i Hok Hokp
                 | G Hok Hokp
                 | G y B Hok Hokp Hwft Hb
                 | G e1 e2 B A' Hokp HwftA HwftB Ht1 IH1 Ht2 IH2
                 | G e B A' Ht IHt Hsub
                 | L G e A' B Hokp HwftA HwftB Hbody IHbody
                 | L G e A' e1 B e2 C0 Ht IHt Hb1 IHb1 Hb2 IHb2 Hdisj
                 | i G Hok Hokp Hwft ];
    intros G1 G2 x A v HC Hv Hlc; simpl.
  - (* lit *) apply typ_lit.
    + rewrite HC in Hok. apply ok_remove in Hok. exact Hok.
    + auto.
  - (* null *) apply typ_null.
    + rewrite HC in Hok. apply ok_remove in Hok. exact Hok.
    + auto.
  - (* var *) destruct (classicT (y = x)) as [Heq | Hne]; simpl.
    + (* y = x *) subst y.
      assert (Hb2 : binds x B G) by exact Hb.
      rewrite HC in Hb2.
      assert (Hok' : ok (G1 & x ~: A & G2)) by (rewrite <- HC; exact Hok).
      assert (HeqBA : B = A) by (eapply binds_middle_eq_inv; [exact Hb2 | exact Hok']).
      subst B. exact Hv.
    + (* y <> x *) apply typ_var.
      * rewrite HC in Hok. apply ok_remove in Hok. exact Hok.
      * auto.
      * auto.
      * rewrite HC in Hb. eapply binds_remove.
        -- exact Hb.
        -- rewrite dom_single. apply notin_singleton_l; auto.
  - (* app *) eapply typ_app with (A := A') (B := B).
    + auto. + auto. + auto.
    + apply (IH1 G1 G2 x A v HC Hv Hlc).
    + apply (IH2 G1 G2 x A v HC Hv Hlc).
  - (* sub *) eapply typ_sub.
    + apply (IHt G1 G2 x A v HC Hv Hlc).
    + auto.
  - (* abs *)
    apply typ_abs with (L := L \u \{x} \u fv_exp v \u dom (G1 & G2)) (A := A') (B := B).
    + auto. + auto. + auto.
    + intros y Hy.
      apply notin_union_r in Hy. destruct Hy as [HyL Hy1].
      apply notin_union_r in Hy1. destruct Hy1 as [HyX Hy2].
      apply notin_union_r in Hy2. destruct Hy2 as [HyFv HyDom].
      apply notin_singleton_r in HyX.
      rewrite open_subst_comm' by auto.
      rewrite <- eq_middle.
      apply (IHbody y HyL G1 (G2 & y ~: A') x A v).
      * rewrite HC. rewrite eq_middle. reflexivity.
      * rewrite eq_middle. apply weaken_front; auto.
      * auto.
  - (* typeof *)
    eapply typ_typeof with (L := L \u \{x} \u fv_exp v \u dom (G1 & G2)).
    + apply (IHt G1 G2 x A v HC Hv Hlc).
    + intros y Hy.
      apply notin_union_r in Hy. destruct Hy as [HyL Hy1].
      apply notin_union_r in Hy1. destruct Hy1 as [HyX Hy2].
      apply notin_union_r in Hy2. destruct Hy2 as [HyFv HyDom].
      apply notin_singleton_r in HyX.
      rewrite open_subst_comm' by auto.
      rewrite <- eq_middle.
      apply (IHb1 y HyL G1 (G2 & y ~: A') x A v).
      * rewrite HC. rewrite eq_middle. reflexivity.
      * rewrite eq_middle. apply weaken_front; auto.
      * auto.
    + intros y Hy.
      apply notin_union_r in Hy. destruct Hy as [HyL Hy1].
      apply notin_union_r in Hy1. destruct Hy1 as [HyX Hy2].
      apply notin_union_r in Hy2. destruct Hy2 as [HyFv HyDom].
      apply notin_singleton_r in HyX.
      rewrite open_subst_comm' by auto.
      rewrite <- eq_middle.
      apply (IHb2 y HyL G1 (G2 & y ~: B) x A v).
      * rewrite HC. rewrite eq_middle. reflexivity.
      * rewrite eq_middle. apply weaken_front; auto.
      * auto.
    + auto.
  - (* prim *) apply typ_prim.
    + rewrite HC in Hok. apply ok_remove in Hok. exact Hok.
    + auto.
    + auto.
Qed.

(* ==================== from G7.v ==================== *)


Fixpoint isSup (PG:envp) (X U:typ) {struct U} : Prop :=
  match U with
  | t_int => X = t_int
  | t_top => True
  | t_bot => False
  | t_arrow A B =>
      match X with
      | t_arrow A' B' => declarative_subtyping PG A A' /\ declarative_subtyping PG B' B
      | _ => False
      end
  | t_union A B => (isSup PG X A /\ wft PG A /\ wft PG B) \/ (isSup PG X B /\ wft PG A /\ wft PG B)
  | t_and A B => isSup PG X A /\ isSup PG X B
  | t_unit => X = t_unit
  | t_prim i => False
  end.

Lemma isSup_trans : forall PG X Y U,
  declarative_subtyping PG Y U -> isSup PG X Y -> isSup PG X U.
Proof.
  intros PG X Y U H.
  induction H as [ A Hok Hwft
                 | A C B D1 IH1 D2 IH2
                 | A Hok Hwft
                 | A Hok Hwft
                 | A C B D D1 IH1 D2 IH2
                 | A B C D1 IH1 D2 IH2
                 | A B Hok HwftA HwftB
                 | A B Hok HwftA HwftB
                 | A B C D1 IH1 D2 IH2
                 | A B Hok HwftA HwftB
                 | B A Hok HwftA HwftB
                 | A B1 B2 Hok HwftA HwftB1 HwftB2
                 | A1 B A2 Hok HwftA1 HwftA2 HwftB
                 | A1 B A2 Hok HwftA1 HwftA2 HwftB
                 | i A Hok Hb ]; intros His; simpl in *.
  - auto.
  - eauto.
  - auto.
  - destruct His.
  - destruct X; simpl in *; try contradiction.
    split; [eapply DS_trans; [exact D1 | exact (proj1 His)] | eapply DS_trans; [exact (proj2 His) | exact D2]].
  - split; [apply IH1 | apply IH2]; exact His.
  - destruct His as [H1 H2]; auto.
  - destruct His as [H1 H2]; auto.
  - destruct His as [[HA _] | [HB _]]; [apply IH1; auto | apply IH2; auto].
  - left; repeat split; auto.
  - right; repeat split; auto.
  - destruct His as [H1 H2]. destruct X; simpl in *; try contradiction.
    split; [exact (proj1 H1) | apply DS_and; [exact (proj2 H1) | exact (proj2 H2)]].
  - destruct His as [H1 H2]. destruct X; simpl in *; try contradiction.
    split; [apply DS_or; [exact (proj1 H1) | exact (proj1 H2)] | exact (proj2 H1)].
  - destruct His as [H1 H2]. simpl in H1, H2.
    destruct H1 as [[HA1 [WA1 WB1]] | [HB1 [WA1 WB1]]];
    destruct H2 as [[HA2 [WA2 WB2]] | [HB2 [WA2 WB2]]].
    + left. split; [split; auto | split; [apply wft_and; auto | auto]].
    + right. split; [auto | split; [apply wft_and; auto | auto]].
    + right. split; [auto | split; [apply wft_and; auto | auto]].
    + right. split; [auto | split; [apply wft_and; auto | auto]].
  - destruct His.
Qed.

Definition atomicT (X:typ) : Prop :=
  X = t_int \/ X = t_unit \/ X = t_top \/ (exists A B, X = t_arrow A B).

Lemma isSup_refl : forall PG X, okenvp PG -> wft PG X -> atomicT X -> isSup PG X X.
Proof.
  intros PG X Hok Hwft [H | [H | [H | [A [B H]]]]]; subst X; simpl.
  - reflexivity.
  - reflexivity.
  - auto.
  - apply wft_arrow_inv in Hwft. destruct Hwft as [HA HB].
    split; apply DS_refl; auto.
Qed.

Lemma isSup_complete : forall PG X U,
  declarative_subtyping PG X U -> atomicT X -> isSup PG X U.
Proof.
  intros PG X U H.
  induction H as [ A Hok Hwft
                 | A C B D1 IH1 D2 IH2
                 | A Hok Hwft
                 | A Hok Hwft
                 | A C B D D1 IH1 D2 IH2
                 | A B C D1 IH1 D2 IH2
                 | A B Hok HwftA HwftB
                 | A B Hok HwftA HwftB
                 | A B C D1 IH1 D2 IH2
                 | A B Hok HwftA HwftB
                 | B A Hok HwftA HwftB
                 | A B1 B2 Hok HwftA HwftB1 HwftB2
                 | A1 B A2 Hok HwftA1 HwftA2 HwftB
                 | A1 B A2 Hok HwftA1 HwftA2 HwftB
                 | i A Hok Hb ]; intro Ha; simpl in *.
  - apply isSup_refl; auto.
  - eapply isSup_trans; [exact D2 | apply IH1; auto].
  - auto.
  - destruct Ha as [H | [H | [H | [A' [B' H]]]]]; discriminate H.
  - split; auto.
  - split; [apply IH1 | apply IH2]; auto.
  - destruct Ha as [H | [H | [H | [A' [B' H]]]]]; discriminate H.
  - destruct Ha as [H | [H | [H | [A' [B' H]]]]]; discriminate H.
  - destruct Ha as [H | [H | [H | [A' [B' H]]]]]; discriminate H.
  - left; split; [apply isSup_refl; auto | auto].
  - right; split; [apply isSup_refl; auto | auto].
  - destruct Ha as [H | [H | [H | [A' [B' H]]]]]; discriminate H.
  - destruct Ha as [H | [H | [H | [A' [B' H]]]]]; discriminate H.
  - destruct Ha as [H | [H | [H | [A' [B' H]]]]]; discriminate H.
  - destruct Ha as [H | [H | [H | [A' [B' H]]]]]; discriminate H.
Qed.

Lemma isSup_sound : forall PG X U,
  okenvp PG -> wft PG X -> isSup PG X U -> declarative_subtyping PG X U.
Proof.
  intros PG X U. revert X.
  induction U as [ | | | A IHA B IHB | A IHA B IHB | A IHA B IHB | | i ];
    intros X Hok Hwft His; simpl in His.
  - subst X. apply DS_refl; auto.
  - apply DS_top; auto.
  - destruct His.
  - destruct X; simpl in *; try contradiction.
    destruct His as [H1 H2]. apply DS_arrow; auto.
  - destruct His as [[HA [WA WB]] | [HB [WA WB]]].
    + eapply DS_trans. apply IHA; auto. apply DS_orl; auto.
    + eapply DS_trans. apply IHB; auto. apply DS_orr; auto.
  - destruct His as [HA HB]. apply DS_and.
    + apply IHA; auto.
    + apply IHB; auto.
  - subst X. apply DS_refl; auto.
  - destruct His.
Qed.

(* ==================== from G8.v ==================== *)


Inductive primReach (PG:envp) : MetatheoryAtom.Atom.atom -> MetatheoryAtom.Atom.atom -> Prop :=
 | primReach_refl : forall i, primReach PG i i
 | primReach_step : forall i j k,
     Metatheory.EnvImpl.binds i (t_prim j) PG -> primReach PG j k -> primReach PG i k.

Lemma primReach_trans : forall PG i j k,
  primReach PG i j -> primReach PG j k -> primReach PG i k.
Proof.
  intros PG i j k H. induction H; intros H2.
  - exact H2.
  - eapply primReach_step; eauto.
Qed.

Fixpoint isSupP (PG:envp) (i:MetatheoryAtom.Atom.atom) (U:typ) {struct U} : Prop :=
  match U with
  | t_int => False
  | t_top => True
  | t_bot => False
  | t_arrow _ _ => False
  | t_union A B => (isSupP PG i A /\ wft PG A /\ wft PG B) \/ (isSupP PG i B /\ wft PG A /\ wft PG B)
  | t_and A B => isSupP PG i A /\ isSupP PG i B
  | t_unit => False
  | t_prim j => primReach PG i j
  end.

Lemma primReach_cons : forall PG i j k,
  primReach PG i j -> Metatheory.EnvImpl.binds j (t_prim k) PG -> primReach PG i k.
Proof.
  intros PG i j k H. induction H as [x | x y z Hb Hr IH]; intros Hb2.
  - eapply primReach_step; [exact Hb2 | apply primReach_refl].
  - eapply primReach_step; [exact Hb | apply IH; exact Hb2].
Qed.

Lemma isSupP_trans : forall PG (i:MetatheoryAtom.Atom.atom) Y U,
  okenvp PG -> declarative_subtyping PG Y U -> isSupP PG i Y -> isSupP PG i U.
Proof.
  intros PG i Y U Hok H.
  induction H as [ A Hok' Hwft
                 | A C B D1 IH1 D2 IH2
                 | A Hok' Hwft
                 | A Hok' Hwft
                 | A C B D D1 IH1 D2 IH2
                 | A B C D1 IH1 D2 IH2
                 | A B Hok' HwftA HwftB
                 | A B Hok' HwftA HwftB
                 | A B C D1 IH1 D2 IH2
                 | A B Hok' HwftA HwftB
                 | B A Hok' HwftA HwftB
                 | A B1 B2 Hok' HwftA HwftB1 HwftB2
                 | A1 B A2 Hok' HwftA1 HwftA2 HwftB
                 | A1 B A2 Hok' HwftA1 HwftA2 HwftB
                 | i0 A Hok' Hb ]; intros His; simpl in *.
  - auto.
  - eapply IH2. apply IH1. exact His.
  - auto.
  - destruct His.
  - destruct His.
  - split; [apply IH1 | apply IH2]; auto.
  - destruct His as [H1 H2]; auto.
  - destruct His as [H1 H2]; auto.
  - destruct His as [[HA _] | [HB _]]; [apply IH1 | apply IH2]; auto.
  - left; repeat split; auto.
  - right; repeat split; auto.
  - destruct His as [H1 _]; destruct H1.
  - destruct His as [H1 _]; destruct H1.
  - destruct His as [H1 H2]. simpl in H1, H2.
    destruct H1 as [[HA1 [WA1 WB1]] | [HB1 [WA1 WB1]]];
    destruct H2 as [[HA2 [WA2 WB2]] | [HB2 [WA2 WB2]]].
    + left. split; [split; auto | split; [apply wft_and; auto | auto]].
    + right. split; [auto | split; [apply wft_and; auto | auto]].
    + right. split; [auto | split; [apply wft_and; auto | auto]].
    + right. split; [auto | split; [apply wft_and; auto | auto]].
  - destruct (okenvp_binds_shape PG i0 A Hok Hb) as [Heq | [j Heq]]; subst A.
    + simpl. exact I.
    + simpl. eapply primReach_cons; eauto.
Qed.

Lemma primReach_sub : forall PG (i j:MetatheoryAtom.Atom.atom),
  primReach PG i j -> okenvp PG -> wft PG (t_prim i) -> declarative_subtyping PG (t_prim i) (t_prim j).
Proof.
  intros PG i j H. induction H as [x | x y z Hb Hr IH]; intros Hok Hw.
  - apply DS_refl.
    + exact Hok.
    + exact Hw.
  - eapply DS_trans with (B := t_prim y).
    + apply DS_prim; auto.
    + apply IH; auto. eapply okenvp_binds_wft; eauto.
Qed.

Lemma isSupP_sound : forall PG (i:MetatheoryAtom.Atom.atom) U,
  okenvp PG -> wft PG (t_prim i) -> isSupP PG i U -> declarative_subtyping PG (t_prim i) U.
Proof.
  intros PG i U. revert i.
  induction U as [ | | | A IHA B IHB | A IHA B IHB | A IHA B IHB | | j ];
    intros i Hok Hw Hp; simpl in Hp.
  - destruct Hp.
  - apply DS_top; auto.
  - destruct Hp.
  - destruct Hp.
  - destruct Hp as [[HA [WA WB]] | [HB [WA WB]]].
    + eapply DS_trans. apply IHA; auto. apply DS_orl; auto.
    + eapply DS_trans. apply IHB; auto. apply DS_orr; auto.
  - destruct Hp as [HA HB]. apply DS_and.
    + apply IHA; auto.
    + apply IHB; auto.
  - destruct Hp.
  - apply primReach_sub; auto.
Qed.

Lemma isSupP_complete : forall PG (i:MetatheoryAtom.Atom.atom) U,
  declarative_subtyping PG (t_prim i) U -> okenvp PG -> isSupP PG i U.
Proof.
  intros PG i U H Hok.
  remember (t_prim i) as X eqn:HX.
  revert i HX.
  induction H as [ A Hok' Hwft
                 | A C B D1 IH1 D2 IH2
                 | A Hok' Hwft
                 | A Hok' Hwft
                 | A C B D D1 IH1 D2 IH2
                 | A B C D1 IH1 D2 IH2
                 | A B Hok' HwftA HwftB
                 | A B Hok' HwftA HwftB
                 | A B C D1 IH1 D2 IH2
                 | A B Hok' HwftA HwftB
                 | B A Hok' HwftA HwftB
                 | A B1 B2 Hok' HwftA HwftB1 HwftB2
                 | A1 B A2 Hok' HwftA1 HwftA2 HwftB
                 | A1 B A2 Hok' HwftA1 HwftA2 HwftB
                 | i1 A Hok' Hb ]; intros i0 HX.
  - subst A. simpl. apply primReach_refl.
  - subst A. eapply isSupP_trans; [exact Hok | exact D2 | apply (IH1 i0 eq_refl)].
  - subst A. simpl. exact I.
  - discriminate HX.
  - discriminate HX.
  - subst A. split; [apply (IH1 i0 eq_refl) | apply (IH2 i0 eq_refl)].
  - discriminate HX.
  - discriminate HX.
  - discriminate HX.
  - subst A. simpl. left. repeat split; auto. apply primReach_refl.
  - subst B. simpl. right. repeat split; auto. apply primReach_refl.
  - discriminate HX.
  - discriminate HX.
  - discriminate HX.
  - inversion HX. subst i0.
    destruct (okenvp_binds_shape PG i1 A Hok Hb) as [Heq | [j Heq]]; subst A.
    + simpl. auto.
    + simpl. eapply primReach_step; [exact Hb | apply primReach_refl].
Qed.

(* ==================== from G9.v ==================== *)


Lemma arrow_union_inv : forall PG A' B' A B,
  okenvp PG -> wft PG (t_arrow A' B') ->
  declarative_subtyping PG (t_arrow A' B') (t_union A B) ->
  declarative_subtyping PG (t_arrow A' B') A \/ declarative_subtyping PG (t_arrow A' B') B.
Proof.
  intros PG A' B' A B Hok Hw Hsub.
  assert (Ha : atomicT (t_arrow A' B')) by (right; right; right; exists A', B'; reflexivity).
  pose proof (isSup_complete PG (t_arrow A' B') (t_union A B) Hsub Ha) as Hs.
  simpl in Hs. destruct Hs as [[H1 [HW1 HW2]] | [H2 [HW1 HW2]]].
  - left. eapply isSup_sound; eauto.
  - right. eapply isSup_sound; eauto.
Qed.

Lemma arrow_arrow_inv : forall PG A' B' A B,
  declarative_subtyping PG (t_arrow A' B') (t_arrow A B) ->
  declarative_subtyping PG A A' /\ declarative_subtyping PG B' B.
Proof.
  intros PG A' B' A B Hsub.
  assert (Ha : atomicT (t_arrow A' B')) by (right; right; right; exists A', B'; reflexivity).
  pose proof (isSup_complete PG (t_arrow A' B') (t_arrow A B) Hsub Ha) as Hs.
  simpl in Hs. exact Hs.
Qed.

Lemma disjoint_arrow_l : forall PG A' B' A B,
  okenvp PG -> wft PG A' -> wft PG B' ->
  DisjSpec PG A B ->
  declarative_subtyping PG (t_arrow A' B') (t_union A B) ->
  declarative_subtyping PG (t_arrow t_top t_bot) A ->
  declarative_subtyping PG (t_arrow A' B') A.
Proof.
  intros PG A' B' A B Hok HwA HwB Hdisj Hsub Hbot.
  destruct (arrow_union_inv PG A' B' A B Hok (wft_arrow PG A' B' HwA HwB) Hsub) as [Hl | Hr]; auto.
  exfalso.
  pose (D := t_arrow (t_union A' t_top) (t_and B' t_bot)).
  assert (HDX : declarative_subtyping PG D (t_arrow A' B')).
  { unfold D. apply DS_arrow.
    - apply DS_orl; [exact Hok | exact HwA | apply wft_top].
    - apply DS_andl; [exact Hok | exact HwB | apply wft_bot]. }
  assert (HDT : declarative_subtyping PG D (t_arrow t_top t_bot)).
  { unfold D. apply DS_arrow.
    - apply DS_orr; [exact Hok | exact HwA | apply wft_top].
    - apply DS_andr; [exact Hok | exact HwB | apply wft_bot]. }
  assert (HDA : declarative_subtyping PG D A) by (eapply DS_trans with (B := t_arrow t_top t_bot); eauto).
  assert (HDB : declarative_subtyping PG D B) by (eapply DS_trans with (B := t_arrow A' B'); eauto).
  assert (Hand : declarative_subtyping PG D (t_and A B)) by (apply DS_and; auto).
  exact (Hdisj D (o_arrow _ _) Hand).
Qed.

Lemma disjoint_arrow_r : forall PG A' B' A B,
  okenvp PG -> wft PG A' -> wft PG B' ->
  DisjSpec PG A B ->
  declarative_subtyping PG (t_arrow A' B') (t_union A B) ->
  declarative_subtyping PG (t_arrow t_top t_bot) B ->
  declarative_subtyping PG (t_arrow A' B') B.
Proof.
  intros PG A' B' A B Hok HwA HwB Hdisj Hsub Hbot.
  destruct (arrow_union_inv PG A' B' A B Hok (wft_arrow PG A' B' HwA HwB) Hsub) as [Hl | Hr]; auto.
  exfalso.
  pose (D := t_arrow (t_union A' t_top) (t_and B' t_bot)).
  assert (HDX : declarative_subtyping PG D (t_arrow A' B')).
  { unfold D. apply DS_arrow.
    - apply DS_orl; [exact Hok | exact HwA | apply wft_top].
    - apply DS_andl; [exact Hok | exact HwB | apply wft_bot]. }
  assert (HDT : declarative_subtyping PG D (t_arrow t_top t_bot)).
  { unfold D. apply DS_arrow.
    - apply DS_orr; [exact Hok | exact HwA | apply wft_top].
    - apply DS_andr; [exact Hok | exact HwB | apply wft_bot]. }
  assert (HDA : declarative_subtyping PG D A) by (eapply DS_trans with (B := t_arrow A' B'); eauto).
  assert (HDB : declarative_subtyping PG D B) by (eapply DS_trans with (B := t_arrow t_top t_bot); eauto).
  assert (Hand : declarative_subtyping PG D (t_and A B)) by (apply DS_and; auto).
  exact (Hdisj D (o_arrow _ _) Hand).
Qed.

(* ==================== from G10.v ==================== *)


Lemma findtype_int_inv : forall (i:nat) C, findtype (e_lit i) C -> C = t_int.
Proof. intros. inversion H. reflexivity. Qed.
Lemma findtype_abs_inv : forall (e:exp) C, findtype (e_abs e) C -> C = t_arrow t_top t_bot.
Proof. intros. inversion H. reflexivity. Qed.
Lemma findtype_null_inv : forall C, findtype e_null C -> C = t_unit.
Proof. intros. inversion H. reflexivity. Qed.
Lemma findtype_new_inv : forall (P:MetatheoryAtom.Atom.atom) C, findtype (e_new P) C -> C = t_prim P.
Proof. intros. inversion H. reflexivity. Qed.

Lemma findtype_least : forall PG G v U C,
  value v -> typing PG G v U -> findtype v C -> declarative_subtyping PG C U.
Proof.
  intros PG G v U C Hv Hty Hf. destruct Hv as [i | e0 Hlc | | P].
  - inversion Hf; subst C. apply typing_inv_lit in Hty. destruct Hty as [_ [_ Hsub]]. exact Hsub.
  - inversion Hf; subst C.
    apply typing_inv_abs in Hty.
    destruct Hty as [L [A [B [Hok [HwA [HwB [Hbody Hsub]]]]]]].
    eapply DS_trans; [| exact Hsub].
    apply DS_arrow.
    + apply DS_top; auto.
    + apply DS_bot; auto.
  - inversion Hf; subst C. apply typing_inv_null in Hty. destruct Hty as [_ [_ Hsub]]. exact Hsub.
  - inversion Hf; subst C. apply typing_inv_new in Hty. destruct Hty as [_ [_ [_ Hsub]]]. exact Hsub.
Qed.

Lemma findtype_union_branch : forall PG G v A B C,
  okenvp PG -> value v -> typing PG G v (t_union A B) -> findtype v C ->
  declarative_subtyping PG C A \/ declarative_subtyping PG C B.
Proof.
  intros PG G v A B C Hok Hv Hty Hf. destruct Hv as [i | e0 Hlc | | P].
  - inversion Hf; subst C.
    pose proof (findtype_least PG G (e_lit i) (t_union A B) t_int (val_int i) Hty (findtype_int i)) as Hs.
    assert (Ha : atomicT t_int) by (left; reflexivity).
    pose proof (isSup_complete PG t_int (t_union A B) Hs Ha) as H1. simpl in H1.
    destruct H1 as [[H2 [HW1 HW2]] | [H3 [HW1 HW2]]].
    + left. eapply isSup_sound; eauto. apply wft_int.
    + right. eapply isSup_sound; eauto. apply wft_int.
  - inversion Hf; subst C.
    pose proof (findtype_least PG G (e_abs e0) (t_union A B) (t_arrow t_top t_bot) (val_abs e0 Hlc) Hty (findtype_arrow e0 Hlc)) as Hs.
    assert (Ha : atomicT (t_arrow t_top t_bot)) by (right; right; right; exists t_top, t_bot; reflexivity).
    pose proof (isSup_complete PG (t_arrow t_top t_bot) (t_union A B) Hs Ha) as H1. simpl in H1.
    destruct H1 as [[H2 [HW1 HW2]] | [H3 [HW1 HW2]]].
    + left. eapply isSup_sound; eauto. apply wft_arrow; [apply wft_top | apply wft_bot].
    + right. eapply isSup_sound; eauto. apply wft_arrow; [apply wft_top | apply wft_bot].
  - inversion Hf; subst C.
    pose proof (findtype_least PG G e_null (t_union A B) t_unit val_null Hty findtype_null) as Hs.
    assert (Ha : atomicT t_unit) by (right; left; reflexivity).
    pose proof (isSup_complete PG t_unit (t_union A B) Hs Ha) as H1. simpl in H1.
    destruct H1 as [[H2 [HW1 HW2]] | [H3 [HW1 HW2]]].
    + left. eapply isSup_sound; eauto. apply wft_unit.
    + right. eapply isSup_sound; eauto. apply wft_unit.
  - inversion Hf; subst C.
    apply typing_inv_new in Hty. destruct Hty as [_ [_ [Hw Hsub]]].
    pose proof (isSupP_complete PG P (t_union A B) Hsub Hok) as H1. simpl in H1.
    destruct H1 as [[H2 [HW1 HW2]] | [H3 [HW1 HW2]]].
    + left. eapply isSupP_sound; eauto.
    + right. eapply isSupP_sound; eauto.
Qed.

Lemma value_arrow_abs : forall PG G v A B,
  okenvp PG -> value v -> typing PG G v (t_arrow A B) -> exists e, v = e_abs e.
Proof.
  intros PG G v A B Hok Hv Hty. destruct Hv as [i | e0 Hlc | | P].
  - exfalso. apply typing_inv_lit in Hty. destruct Hty as [_ [_ Hsub]].
    assert (Ha : atomicT t_int) by (left; reflexivity).
    pose proof (isSup_complete PG t_int (t_arrow A B) Hsub Ha) as H1. simpl in H1. exact H1.
  - exists e0. reflexivity.
  - exfalso. apply typing_inv_null in Hty. destruct Hty as [_ [_ Hsub]].
    assert (Ha : atomicT t_unit) by (right; left; reflexivity).
    pose proof (isSup_complete PG t_unit (t_arrow A B) Hsub Ha) as H1. simpl in H1. exact H1.
  - exfalso. apply typing_inv_new in Hty. destruct Hty as [_ [_ [Hw Hsub]]].
    pose proof (isSupP_complete PG P (t_arrow A B) Hsub Hok) as H1. simpl in H1. exact H1.
Qed.

Lemma value_type_left : forall PG G v A B C,
  okenvp PG -> value v -> typing PG G v (t_union A B) ->
  findtype v C -> declarative_subtyping PG C A -> DisjSpec PG A B ->
  typing PG G v A.
Proof.
  intros PG G v A B C Hok Hv Hty Hf HC Hdisj. destruct Hv as [i | e0 Hlc | | P].
  - inversion Hf; subst C.
    apply typing_inv_lit in Hty. destruct Hty as [HokG [Hokp Hsub]].
    eapply typ_sub; [apply typ_lit; auto | exact HC].
  - inversion Hf; subst C.
    apply typing_inv_abs in Hty.
    destruct Hty as [L [A' [B' [Hokp [HwA [HwB [Hbody Hsub]]]]]]].
    eapply typ_sub.
    + apply typ_abs with (L:=L) (A:=A') (B:=B'); auto.
    + eapply disjoint_arrow_l; eauto.
  - inversion Hf; subst C.
    apply typing_inv_null in Hty. destruct Hty as [HokG [Hokp Hsub]].
    eapply typ_sub; [apply typ_null; auto | exact HC].
  - inversion Hf; subst C.
    apply typing_inv_new in Hty. destruct Hty as [HokG [Hokp [Hw Hsub]]].
    eapply typ_sub; [apply typ_prim; auto | exact HC].
Qed.

Lemma value_type_right : forall PG G v A B C,
  okenvp PG -> value v -> typing PG G v (t_union A B) ->
  findtype v C -> declarative_subtyping PG C B -> DisjSpec PG A B ->
  typing PG G v B.
Proof.
  intros PG G v A B C Hok Hv Hty Hf HC Hdisj. destruct Hv as [i | e0 Hlc | | P].
  - inversion Hf; subst C.
    apply typing_inv_lit in Hty. destruct Hty as [HokG [Hokp Hsub]].
    eapply typ_sub; [apply typ_lit; auto | exact HC].
  - inversion Hf; subst C.
    apply typing_inv_abs in Hty.
    destruct Hty as [L [A' [B' [Hokp [HwA [HwB [Hbody Hsub]]]]]]].
    eapply typ_sub.
    + apply typ_abs with (L:=L) (A:=A') (B:=B'); auto.
    + eapply disjoint_arrow_r; eauto.
  - inversion Hf; subst C.
    apply typing_inv_null in Hty. destruct Hty as [HokG [Hokp Hsub]].
    eapply typ_sub; [apply typ_null; auto | exact HC].
  - inversion Hf; subst C.
    apply typing_inv_new in Hty. destruct Hty as [HokG [Hokp [Hw Hsub]]].
    eapply typ_sub; [apply typ_prim; auto | exact HC].
Qed.

(* ==================== from G11.v ==================== *)


Theorem preservation : forall PG E e e' T,
  typing PG E e T ->
  PG ||- e --> e' ->
  typing PG E e' T.
Proof.
  intros PG E e e' T Hty Hstep. revert e' Hstep.
  induction Hty as [ G i Hok Hokp
                 | G Hok Hokp
                 | G x A Hok Hokp Hwft Hb
                 | G e1 e2 B A Hokp HwftA HwftB Ht1 IH1 Ht2 IH2
                 | G e A B Ht IHt Hsub
                 | L G e A B Hokp HwftA HwftB Hbody IHbody
                 | L G e A e1 B e2 C Ht IHt Hb1 IHb1 Hb2 IHb2 Hdisj
                 | i G Hok Hokp Hwft ]; intros e' Hstep.
  - (* lit *) dependent destruction Hstep.
  - (* null *) dependent destruction Hstep.
  - (* var *) dependent destruction Hstep.
  - (* app *)
    dependent destruction Hstep.
    + (* step_appl *) eapply typ_app with (A:=A) (B:=B); eauto.
    + (* step_appr *) eapply typ_app with (A:=A) (B:=B); eauto.
    + (* step_beta *)
      apply typing_inv_abs in Ht1.
      destruct Ht1 as [L' [A' [B' [Hok' [HwA' [HwB' [Hbody' Hsub']]]]]]].
      apply arrow_arrow_inv in Hsub'. destruct Hsub' as [HsubA HsubB].
      assert (Hv' : typing PG G e2 A') by (eapply typ_sub; eauto).
      destruct (var_fresh (L' \u fv_exp e \u dom G)) as [y Hy].
      apply notin_union_r in Hy. destruct Hy as [HyL HyRest].
      apply notin_union_r in HyRest. destruct HyRest as [HyFv HyDom].
      assert (Htyp : typing PG (G & y ~: A' & empty) (open_exp_wrt_exp e (e_var_f y)) B').
      { rewrite concat_empty_r. apply (Hbody' y HyL). }
      assert (Hval : typing PG (G & empty) e2 A').
      { rewrite concat_empty_r. exact Hv'. }
      pose proof (typing_subst_gen PG G empty y A' (open_exp_wrt_exp e (e_var_f y)) B' e2
                    Htyp Hval (value_lc e2 H0)) as Hres.
      rewrite concat_empty_r in Hres.
      rewrite subst_open_ident in Hres by auto.
      eapply typ_sub; eauto.
  - (* sub *) eapply typ_sub; eauto.
  - (* abs *) dependent destruction Hstep.
  - (* typeof *)
    dependent destruction Hstep.
    + (* step_typeof *) eapply typ_typeof with (L:=L).
      * apply IHt; exact Hstep.
      * exact Hb1.
      * exact Hb2.
      * exact Hdisj.
    + (* step_typeofl *)
      assert (Hokp : okenvp PG) by (eapply typing_okenvp; eauto).
      assert (HvA : typing PG G e A).
      { eapply value_type_left; eauto. }
      destruct (var_fresh (L \u fv_exp e \u dom G \u fv_exp e1)) as [x Hx].
      apply notin_union_r in Hx. destruct Hx as [HxL Hx1].
      apply notin_union_r in Hx1. destruct Hx1 as [HxFv Hx2].
      apply notin_union_r in Hx2. destruct Hx2 as [HxDom HxE1].
      assert (Htyp : typing PG (G & x ~: A & empty) (open_exp_wrt_exp e1 (e_var_f x)) C).
      { rewrite concat_empty_r. apply (Hb1 x HxL). }
      assert (Hval : typing PG (G & empty) e A).
      { rewrite concat_empty_r. exact HvA. }
      pose proof (typing_subst_gen PG G empty x A (open_exp_wrt_exp e1 (e_var_f x)) C e
                    Htyp Hval (value_lc e H0)) as Hres.
      rewrite concat_empty_r in Hres.
      rewrite subst_open_ident in Hres by auto.
      exact Hres.
    + (* step_typeofr *)
      assert (Hokp : okenvp PG) by (eapply typing_okenvp; eauto).
      assert (HvB : typing PG G e B).
      { eapply value_type_right; eauto. }
      destruct (var_fresh (L \u fv_exp e \u dom G \u fv_exp e2)) as [x Hx].
      apply notin_union_r in Hx. destruct Hx as [HxL Hx1].
      apply notin_union_r in Hx1. destruct Hx1 as [HxFv Hx2].
      apply notin_union_r in Hx2. destruct Hx2 as [HxDom HxE2].
      assert (Htyp : typing PG (G & x ~: B & empty) (open_exp_wrt_exp e2 (e_var_f x)) C).
      { rewrite concat_empty_r. apply (Hb2 x HxL). }
      assert (Hval : typing PG (G & empty) e B).
      { rewrite concat_empty_r. exact HvB. }
      pose proof (typing_subst_gen PG G empty x B (open_exp_wrt_exp e2 (e_var_f x)) C e
                    Htyp Hval (value_lc e H0)) as Hres.
      rewrite concat_empty_r in Hres.
      rewrite subst_open_ident in Hres by auto.
      exact Hres.
  - (* prim *) dependent destruction Hstep.
Qed.

Lemma value_findtype : forall v, value v -> exists C, findtype v C.
Proof.
  intros v Hv. destruct Hv as [i | e0 Hlc | | P].
  - exists t_int. apply findtype_int.
  - exists (t_arrow t_top t_bot). apply findtype_arrow; auto.
  - exists t_unit. apply findtype_null.
  - exists (t_prim P). apply find_type_new.
Qed.

Lemma progress_gen : forall PG G e T,
  typing PG G e T -> G = empty -> value e \/ (exists e', step PG e e').
Proof.
  intros PG G e T H.
  induction H as [ G i Hok Hokp
                 | G Hok Hokp
                 | G x A Hok Hokp Hwft Hb
                 | G e1 e2 B A Hokp HwftA HwftB Ht1 IH1 Ht2 IH2
                 | G e A B Ht IHt Hsub
                 | L G e A B Hokp HwftA HwftB Hbody IHbody
                 | L G e A e1 B e2 C Ht IHt Hb1 IHb1 Hb2 IHb2 Hdisj
                 | i G Hok Hokp Hwft ]; intros HG.
  - left. apply val_int.
  - left. apply val_null.
  - subst G. exfalso. eapply binds_empty_inv; eauto.
  - destruct (IH1 HG) as [Hval1 | [e1' Hstep1]].
    + destruct (value_arrow_abs PG G e1 A B Hokp Hval1 Ht1) as [e0 Heq].
      subst e1.
      destruct (IH2 HG) as [Hval2 | [e2' Hstep2]].
      * right. exists (open_exp_wrt_exp e0 e2). apply step_beta.
        -- apply value_lc. exact Hval1.
        -- exact Hval2.
      * right. exists (e_app (e_abs e0) e2'). apply step_appr.
        -- exact Hval1.
        -- exact Hstep2.
    + right. exists (e_app e1' e2). apply step_appl.
      * eapply typing_lc; eauto.
      * exact Hstep1.
  - apply IHt in HG. exact HG.
  - left. apply val_abs. apply lc_e_abs with (L:=L). intros x Hx.
    eapply typing_lc; eauto.
  - assert (Hty' : typing PG G (e_typeof e A e1 B e2) C).
    { apply typ_typeof with (L:=L); auto. }
    pose proof (typing_lc PG G (e_typeof e A e1 B e2) C Hty') as Hlc.
    destruct (IHt HG) as [Hval | [e' Hstep]].
    + destruct (value_findtype e Hval) as [C0 Hfind].
      assert (Hokp : okenvp PG) by (eapply typing_okenvp; eauto).
      assert (Hsub : declarative_subtyping PG C0 A \/ declarative_subtyping PG C0 B).
      { eapply findtype_union_branch; eauto. }
      right. destruct Hsub as [HsubA | HsubB].
      * exists (open_exp_wrt_exp e1 e). eapply step_typeofl; eauto.
      * exists (open_exp_wrt_exp e2 e). eapply step_typeofr; eauto.
    + right. exists (e_typeof e' A e1 B e2). apply step_typeof; auto.
  - left. apply val_new.
Qed.

Theorem progress : forall PG e T,
    typing PG empty e T -> (value e) \/ (exists e', PG ||- e --> e').
Proof.
  intros PG e T H. apply (progress_gen PG empty e T H eq_refl).
Qed.

End Typing_part.
