Set Implicit Arguments.

Require Import LibExtra.
Require Import Coq.Lists.List.

Require Import AbstractSyntax PreTyping Typing GeneralTyping RecordTypes InertTypes DefRecordInertTyping HeapCorrespondence OperationalSemantics Effects Initialization InitTyping InitLookup ConfigTyping.
Require Import CommittedSubHeap FreeSubHeapSingle FreeSubHeapStack StackTyping InertInitContexts InitWeakening EffectCorrespondence HeapEffects HeapDefsPointsTo WellPointed FreeItems.
Require Import PreciseTyping.
Require Import HeapUpdate.

(** * Auxiliary syntax lemmas *)

Lemma open_rec_avar_b_eq : forall (n:nat) (x:var), open_rec n x (avar_b n) = avar_f x.
Proof. intros. unfold open_rec. cbn. rewrite If_l; auto. Qed.

Lemma open_rec_avar_b_neq : forall (n m:nat) (x:var), m <> n -> open_rec m x (avar_b n) = avar_b n.
Proof. intros. unfold open_rec. cbn. rewrite If_r; auto. Qed.

Lemma open_rec_avar_f : forall (n:nat) (x y:var), open_rec n x (avar_f y) = avar_f y.
Proof. intros. unfold open_rec. cbn. reflexivity. Qed.

Lemma subst_avar_b : forall (x y:var) (n:nat), subst_var x y (avar_b n) = avar_b n.
Proof. intros. unfold subst_var. cbn. reflexivity. Qed.

Lemma subst_avar_f : forall (x y z:var), subst_var x y (avar_f z) = avar_f (z \[x -> y]).
Proof. intros. unfold subst_var. cbn. reflexivity. Qed.

Lemma subst_avar_fresh : forall (x y:var) (a:avar), x \notin fv a -> subst_var x y a = a.
Proof.
  intros. destruct a as [n|z].
  - rewrite subst_avar_b. reflexivity.
  - rewrite subst_avar_f. f_equal. simpl in H.
    apply notin_singleton_r in H.
    rewrite If_r; auto.
Qed.

Lemma length_s_subst_typs : forall (x y:var) (Ts:typs), length_s (subst_var x y Ts) = length_s Ts.
Proof.
  intros x y Ts. induction Ts as [|T Ts IH]; simpl; auto.
Qed.

Lemma length_s_open_rec_typs : forall (n:nat) (z:var) (Ts:typs), length_s (open_rec n z Ts) = length_s Ts.
Proof.
  intros n z Ts. induction Ts as [|T Ts IH]; simpl; auto.
Qed.

Lemma subst_open_avar : forall (x y z:var) (n:nat) (a:avar),
  subst_var x y (open_rec n z a) = open_rec n (z \[x -> y]) (subst_var x y a).
Proof.
  intros x y z n a. destruct a as [i|w].
  - unfold open_rec, subst_var. cbn.
    destruct (Nat.eq_dec n i) as [Heq|Hne].
    + rewrite (If_l (P:=n=i) _ _ Heq). rewrite (If_l (P:=n=i) _ _ Heq).
      unfold AvarSubstVar. cbn. reflexivity.
    + rewrite (If_r (P:=n=i) _ _ Hne). rewrite (If_r (P:=n=i) _ _ Hne).
      unfold AvarSubstVar. cbn. reflexivity.
  - unfold open_rec, subst_var. cbn.
    unfold AvarSubstVar, AvarOpenable. cbn. reflexivity.
Qed.

Lemma subst_open_rec_mut :
  (forall (T:typ) (x y z:var) (n:nat),
      subst_var x y (open_rec n z T) =
      open_rec n (z \[x -> y]) (subst_var x y T)) /\
  (forall (Ts:typs) (x y z:var) (n:nat),
      subst_var x y (open_rec n z Ts) =
      open_rec n (z \[x -> y]) (subst_var x y Ts)) /\
  (forall (D:dec) (x y z:var) (n:nat),
      subst_var x y (open_rec n z D) =
      open_rec n (z \[x -> y]) (subst_var x y D)).
Proof.
  apply typ_mutind; intros; simpl.
  - reflexivity.
  - reflexivity.
  - rewrite H. reflexivity.
  - rewrite H, H0. reflexivity.
  - f_equal. apply subst_open_avar.
  - rewrite H. reflexivity.
  - rewrite H, H0. reflexivity.
  - rewrite H, H0. cbn. rewrite length_s_subst_typs. reflexivity.
  - reflexivity.
  - rewrite H, H0. reflexivity.
  - rewrite H, H0. reflexivity.
  - rewrite H, H0. reflexivity.
Qed.

(** * Environment extension *)

Section BindsExtends.

Definition binds_extends {A : Set} (G G' : env A) : Prop :=
  forall z v, binds z v G -> binds z v G'.

Lemma binds_extends_refl : forall (A:Set) (G:env A), binds_extends G G.
Proof. intros. intros z v Hz. auto. Qed.

Lemma binds_extends_trans : forall (A:Set) (G1 G2 G3:env A),
  binds_extends G1 G2 -> binds_extends G2 G3 -> binds_extends G1 G3.
Proof. intros A G1 G2 G3 H12 H23 z v Hz. apply H23. apply H12. auto. Qed.

Lemma binds_extends_push : forall (A:Set) (G G':env A) (x:var) (v:A),
  binds_extends G G' -> binds_extends (G & x ~ v) (G' & x ~ v).
Proof.
  intros A G G' x v He z w Hz.
  destruct (classic (z = x)) as [->|Hne].
  - apply binds_push_eq_inv in Hz. subst w. apply binds_push_eq.
  - apply binds_push_neq_inv in Hz; auto.
Qed.

Lemma concat_single_eq : forall (A:Type) (G:env A) (y:var) (v:A),
  G & y ~ v = cons (y,v) G.
Proof. intros. rewrite (concat_def A). rewrite (single_def A). cbn. reflexivity. Qed.

Lemma binds_extends_push_env : forall (A:Set) (G G' E:env A),
  binds_extends G G' -> binds_extends (G & E) (G' & E).
Proof.
  intros A G G' E. rewrite !(concat_def A).
  induction E as [|[y v] E' IH]; intros He.
  - rewrite !LibList.app_nil_l. exact He.
  - rewrite !LibList.app_cons_l.
    rewrite <- (concat_single_eq (A:=A) (LibList.app E' G) y v).
    rewrite <- (concat_single_eq (A:=A) (LibList.app E' G') y v).
    apply binds_extends_push. apply IH. exact He.
Qed.

Lemma binds_extends_push_env_fresh : forall (A:Set) (G E:env A),
  (forall y, y \in dom E -> y \notin dom G) -> binds_extends G (G & E).
Proof.
  intros A G E H z v Hz. apply binds_concat_left; [exact Hz|].
  intro HzE. exact (H z HzE (get_some_inv Hz)).
Qed.

End BindsExtends.

(** * Transfer of typing judgements along environment extension *)

Section DefsTransfer.

Context {A : Set} `{LabelOf A} `{DTA : DecTyping A}.

Hypothesis dec_transfer :
  forall (G:ctx) (d:A) (D:dec), G ⊢ d ∶d D ->
    forall G', binds_extends G G' -> G' ⊢ d ∶d D.

Lemma ty_defs_binds_extends : forall (G:ctx) (ds:list A) (T:typ),
  G ⊢ ds ∶ T -> forall G', binds_extends G G' -> G' ⊢ ds ∶ T.
Proof.
  intros G ds T Hds. induction Hds; intros G' He.
  - eapply ty_defs_one. eapply (dec_transfer (G:=Gamma) (d:=d) (D:=D) H0). exact He.
  - eapply ty_defs_cons.
    + apply IHHds. exact He.
    + eapply (dec_transfer (G:=Gamma) (d:=d) (D:=D) H1). exact He.
    + assumption.
Qed.

End DefsTransfer.

Lemma ty_def_binds_extends : forall (G:ctx) (d:def) (D:dec),
  G ⊢ d ∶d D -> forall G', binds_extends G G' -> G' ⊢ d ∶d D.
Proof.
  intros G d D H G' He.
  change (ty_def G d D) in H.
  change (ty_def G' d D).
  destruct H.
  - apply ty_def_typ.
  - apply ty_def_trm. exact t.
Qed.

Lemma ty_defs_def_binds_extends : forall (G:ctx) (ds:defs) (T:typ),
  G ⊢ ds ∶ T -> forall G', binds_extends G G' -> G' ⊢ ds ∶ T.
Proof.
  intros. eapply ty_defs_binds_extends; eauto using ty_def_binds_extends.
Qed.

Section TransferHelpers.

Lemma tr_ty_var : forall (G:ctx) (x:var) (T:typ),
  binds x T G -> forall G', binds_extends G G' -> G' ⊢ trm_var (avar_f x) ∶ T.
Proof. intros. eapply ty_var; eauto. Qed.

Lemma tr_ty_all_elim : forall (G:ctx) (x z:var) (S T:typ),
  (forall G', binds_extends G G' -> G' ⊢ trm_var (avar_f x) ∶ typ_all S T) ->
  (forall G', binds_extends G G' -> G' ⊢ trm_var (avar_f z) ∶ S) ->
  forall G', binds_extends G G' -> G' ⊢ trm_app (avar_f x) (avar_f z) ∶ open z T.
Proof.
  intros. eapply ty_all_elim.
  - eapply H; eauto.
  - eapply H0; eauto.
Qed.

Lemma tr_ty_new : forall (G:ctx) (x:var) (avs:avars) (xs:list var) (Ts:typs) (is':inits) (T:typ),
  (forall G', binds_extends G G' -> G' ⊢ trm_var (avar_f x) ∶ typ_con Ts is' T) ->
  (forall G', binds_extends G G' -> G' ⊢ avs :: Ts) ->
  vars_of_avars xs avs ->
  forall G', binds_extends G G' -> G' ⊢ trm_new (avar_f x) avs ∶ typ_bnd (open_rec_vars 1 xs T).
Proof.
  intros. eapply ty_new.
  - eapply H; eauto.
  - eapply H0; eauto.
  - eauto.
Qed.

Lemma tr_ty_rcd_elim : forall (G:ctx) (x:var) (a:trm_label) (S T:typ),
  (forall G', binds_extends G G' -> G' ⊢ trm_var (avar_f x) ∶ typ_rcd (dec_trm a S T)) ->
  forall G', binds_extends G G' -> G' ⊢ trm_sel (avar_f x) a ∶ T.
Proof. intros. eapply ty_rcd_elim; eauto. Qed.

Lemma tr_ty_fld_asn : forall (G:ctx) (x y:var) (a:trm_label) (S T:typ),
  (forall G', binds_extends G G' -> G' ⊢ trm_var (avar_f x) ∶ typ_rcd (dec_trm a S T)) ->
  (forall G', binds_extends G G' -> G' ⊢ trm_var (avar_f y) ∶ S) ->
  forall G', binds_extends G G' -> G' ⊢ trm_asn (avar_f x) a (avar_f y) ∶ T.
Proof.
  intros. eapply ty_fld_asn.
  - eapply H; eauto.
  - eapply H0; eauto.
Qed.

Lemma tr_ty_let : forall (L:fset var) (G:ctx) (t u:trm) (T U:typ),
  (forall G', binds_extends G G' -> G' ⊢ t ∶ T) ->
  (forall x, x \notin L -> forall G', binds_extends (G & x ~ T) G' -> G' ⊢ open x u ∶ U) ->
  forall G', binds_extends G G' -> G' ⊢ trm_let T t u ∶ U.
Proof.
  intros. eapply ty_let.
  - eapply H; eauto.
  - intros x Hx. eapply H0; eauto. apply binds_extends_push; eauto.
Qed.

Lemma tr_ty_llit : forall (L:fset var) (G:ctx) (l:lit) (u:trm) (T U:typ),
  (forall G', binds_extends G G' -> G' ⊢ l ∶ T) ->
  (forall x, x \notin L -> forall G', binds_extends (G & x ~ T) G' -> G' ⊢ open x u ∶ U) ->
  forall G', binds_extends G G' -> G' ⊢ trm_lit T l u ∶ U.
Proof.
  intros. eapply ty_llit.
  - eapply H; eauto.
  - intros x Hx. eapply H0; eauto. apply binds_extends_push; eauto.
Qed.

Lemma tr_ty_rec_intro : forall (G:ctx) (x:var) (T:typ),
  (forall G', binds_extends G G' -> G' ⊢ trm_var (avar_f x) ∶ open x T) ->
  forall G', binds_extends G G' -> G' ⊢ trm_var (avar_f x) ∶ typ_bnd T.
Proof. intros. eapply ty_rec_intro; eauto. Qed.

Lemma tr_ty_rec_elim : forall (G:ctx) (x:var) (T:typ),
  (forall G', binds_extends G G' -> G' ⊢ trm_var (avar_f x) ∶ typ_bnd T) ->
  forall G', binds_extends G G' -> G' ⊢ trm_var (avar_f x) ∶ open x T.
Proof. intros. eapply ty_rec_elim; eauto. Qed.

Lemma tr_ty_and_intro : forall (G:ctx) (x:var) (T U:typ),
  (forall G', binds_extends G G' -> G' ⊢ trm_var (avar_f x) ∶ T) ->
  (forall G', binds_extends G G' -> G' ⊢ trm_var (avar_f x) ∶ U) ->
  forall G', binds_extends G G' -> G' ⊢ trm_var (avar_f x) ∶ typ_and T U.
Proof.
  intros. eapply ty_and_intro.
  - eapply H; eauto.
  - eapply H0; eauto.
Qed.

Lemma tr_ty_sub : forall (G:ctx) (t:trm) (T U:typ),
  (forall G', binds_extends G G' -> G' ⊢ t ∶ T) ->
  (forall G', binds_extends G G' -> G' ⊢ T <: U) ->
  forall G', binds_extends G G' -> G' ⊢ t ∶ U.
Proof.
  intros. eapply ty_sub.
  - eapply H; eauto.
  - eapply H0; eauto.
Qed.

Lemma tr_ty_all_intro : forall (L:fset var) (G:ctx) (T:typ) (t:trm) (U:typ),
  (forall x, x \notin L -> forall G', binds_extends (G & x ~ T) G' -> G' ⊢ open x t ∶ open x U) ->
  forall G', binds_extends G G' -> G' ⊢ lit_fun T t ∶ typ_all T U.
Proof.
  intros. eapply ty_all_intro. intros x Hx. eapply H; eauto.
  apply binds_extends_push; eauto.
Qed.

Lemma tr_ty_con_intro : forall (L:fset var) (G:ctx) (Ts:typs) (is':inits) (T:typ)
  (ds:defs) (t:trm) (T':typ),
  (forall x ys, length ys = length_s Ts ->
     fresh L (S (length ys)) (cons x ys) ->
     G & (ys ~** (to_list Ts)) & (x ~ open_vars (cons x ys) T)
       ⊢ (open_vars (cons x ys) ds) ∶ (open_vars (cons x ys) T)) ->
  (forall x ys, length ys = length_s Ts ->
     fresh L (S (length ys)) (cons x ys) ->
     forall G', binds_extends (G & (ys ~** (to_list Ts)) & (x ~ open_vars (cons x ys) T)) G' ->
       G' ⊢ (open_vars (cons x ys) t) ∶ (open_vars (cons x ys) T')) ->
  forall G', binds_extends G G' -> G' ⊢ lit_con Ts is' T ds t ∶ typ_con Ts is' T.
Proof.
  intros. eapply ty_con_intro.
  - intros x ys Hl Hf.
    eapply ty_defs_def_binds_extends.
    + eapply H; eauto.
    + eapply binds_extends_push. eapply binds_extends_push_env. exact H1.
  - intros x ys Hl Hf. eapply H0; eauto.
    eapply binds_extends_push. eapply binds_extends_push_env. exact H1.
Qed.

Lemma tr_subtyp_top : forall (G:ctx) (T:typ),
  forall G', binds_extends G G' -> G' ⊢ T <: typ_top.
Proof. intros. eapply subtyp_top. Qed.

Lemma tr_subtyp_bot : forall (G:ctx) (T:typ),
  forall G', binds_extends G G' -> G' ⊢ typ_bot <: T.
Proof. intros. eapply subtyp_bot. Qed.

Lemma tr_subtyp_refl : forall (G:ctx) (T:typ),
  forall G', binds_extends G G' -> G' ⊢ T <: T.
Proof. intros. eapply subtyp_refl. Qed.

Lemma tr_subtyp_trans : forall (G:ctx) (S T U:typ),
  (forall G', binds_extends G G' -> G' ⊢ S <: T) ->
  (forall G', binds_extends G G' -> G' ⊢ T <: U) ->
  forall G', binds_extends G G' -> G' ⊢ S <: U.
Proof.
  intros. eapply subtyp_trans.
  - eapply H; eauto.
  - eapply H0; eauto.
Qed.

Lemma tr_subtyp_and11 : forall (G:ctx) (T U:typ),
  forall G', binds_extends G G' -> G' ⊢ typ_and T U <: T.
Proof. intros. eapply subtyp_and11. Qed.

Lemma tr_subtyp_and12 : forall (G:ctx) (T U:typ),
  forall G', binds_extends G G' -> G' ⊢ typ_and T U <: U.
Proof. intros. eapply subtyp_and12. Qed.

Lemma tr_subtyp_and2 : forall (G:ctx) (S T U:typ),
  (forall G', binds_extends G G' -> G' ⊢ S <: T) ->
  (forall G', binds_extends G G' -> G' ⊢ S <: U) ->
  forall G', binds_extends G G' -> G' ⊢ S <: typ_and T U.
Proof.
  intros. eapply subtyp_and2.
  - eapply H; eauto.
  - eapply H0; eauto.
Qed.

Lemma tr_subtyp_fld : forall (G:ctx) (a:trm_label) (T1 T2 U1 U2:typ),
  (forall G', binds_extends G G' -> G' ⊢ T1 <: T2) ->
  (forall G', binds_extends G G' -> G' ⊢ U1 <: U2) ->
  forall G', binds_extends G G' ->
    G' ⊢ typ_rcd (dec_trm a T2 U1) <: typ_rcd (dec_trm a T1 U2).
Proof.
  intros. eapply subtyp_fld.
  - eapply H; eauto.
  - eapply H0; eauto.
Qed.

Lemma tr_subtyp_typ : forall (G:ctx) (A:typ_label) (S1 T1 S2 T2:typ),
  (forall G', binds_extends G G' -> G' ⊢ S2 <: S1) ->
  (forall G', binds_extends G G' -> G' ⊢ T1 <: T2) ->
  forall G', binds_extends G G' ->
    G' ⊢ typ_rcd (dec_typ A S1 T1) <: typ_rcd (dec_typ A S2 T2).
Proof.
  intros. eapply subtyp_typ.
  - eapply H; eauto.
  - eapply H0; eauto.
Qed.

Lemma tr_subtyp_sel2 : forall (G:ctx) (x:var) (A:typ_label) (S T:typ),
  (forall G', binds_extends G G' -> G' ⊢ trm_var (avar_f x) ∶ typ_rcd (dec_typ A S T)) ->
  forall G', binds_extends G G' -> G' ⊢ S <: typ_sel (avar_f x) A.
Proof. intros. eapply subtyp_sel2; eauto. Qed.

Lemma tr_subtyp_sel1 : forall (G:ctx) (x:var) (A:typ_label) (S T:typ),
  (forall G', binds_extends G G' -> G' ⊢ trm_var (avar_f x) ∶ typ_rcd (dec_typ A S T)) ->
  forall G', binds_extends G G' -> G' ⊢ typ_sel (avar_f x) A <: T.
Proof. intros. eapply subtyp_sel1; eauto. Qed.

Lemma tr_subtyp_all : forall (L:fset var) (G:ctx) (S1 T1 S2 T2:typ),
  (forall G', binds_extends G G' -> G' ⊢ S2 <: S1) ->
  (forall x, x \notin L -> forall G', binds_extends (G & x ~ S2) G' -> G' ⊢ open x T1 <: open x T2) ->
  forall G', binds_extends G G' -> G' ⊢ typ_all S1 T1 <: typ_all S2 T2.
Proof.
  intros. eapply subtyp_all.
  - eapply H; eauto.
  - intros x Hx. eapply H0; eauto. apply binds_extends_push; eauto.
Qed.

Lemma tr_typ_avars_nil : forall (G:ctx),
  forall G', binds_extends G G' -> G' ⊢ (nil:avars) :: typs_nil.
Proof. intros. eapply typ_avars_nil. Qed.

Lemma tr_typ_avars_cons : forall (G:ctx) (x:var) (T:typ) (avs:avars) (Ts:typs),
  (forall G', binds_extends G G' -> G' ⊢ trm_var (avar_f x) ∶ T) ->
  (forall G', binds_extends G G' -> G' ⊢ avs :: Ts) ->
  forall G', binds_extends G G' -> G' ⊢ (cons (avar_f x) avs) :: (typs_cons T Ts).
Proof.
  intros. eapply typ_avars_cons.
  - eapply H; eauto.
  - eapply H0; eauto.
Qed.

End TransferHelpers.

Lemma typing_binds_extends_mut :
  (forall (G:ctx) (t:trm) (T:typ), G ⊢ t ∶ T ->
     forall G', binds_extends G G' -> G' ⊢ t ∶ T) /\
  (forall (G:ctx) (l:lit) (T:typ), G ⊢ l ∶ T ->
     forall G', binds_extends G G' -> G' ⊢ l ∶ T) /\
  (forall (G:ctx) (T U:typ), G ⊢ T <: U ->
     forall G', binds_extends G G' -> G' ⊢ T <: U) /\
  (forall (G:ctx) (avs:avars) (Ts:typs), G ⊢ avs :: Ts ->
     forall G', binds_extends G G' -> G' ⊢ avs :: Ts).
Proof.
  apply (rules_mutind
    (fun (G:ctx) (t:trm) (T:typ) (_:G ⊢ t ∶ T) =>
       forall G', binds_extends G G' -> G' ⊢ t ∶ T)
    (fun (G:ctx) (l:lit) (T:typ) (_:G ⊢ l ∶ T) =>
       forall G', binds_extends G G' -> G' ⊢ l ∶ T)
    (fun (G:ctx) (T U:typ) (_:G ⊢ T <: U) =>
       forall G', binds_extends G G' -> G' ⊢ T <: U)
    (fun (G:ctx) (avs:avars) (Ts:typs) (_:G ⊢ avs :: Ts) =>
       forall G', binds_extends G G' -> G' ⊢ avs :: Ts));
  intros;
  first [ solve [ eapply tr_ty_var; eauto 4 ]
        | solve [ eapply tr_ty_all_elim; eauto 4 ]
        | solve [ eapply tr_ty_new; eauto 4 ]
        | solve [ eapply tr_ty_rcd_elim; eauto 4 ]
        | solve [ eapply tr_ty_fld_asn; eauto 4 ]
        | solve [ eapply tr_ty_let; eauto 4 ]
        | solve [ eapply tr_ty_llit; eauto 4 ]
        | solve [ eapply tr_ty_rec_intro; eauto 4 ]
        | solve [ eapply tr_ty_rec_elim; eauto 4 ]
        | solve [ eapply tr_ty_and_intro; eauto 4 ]
        | solve [ eapply tr_ty_sub; eauto 4 ]
        | solve [ eapply tr_ty_all_intro; eauto 4 ]
        | solve [ eapply tr_ty_con_intro; eauto 4 ]
        | solve [ eapply tr_subtyp_top; eauto 4 ]
        | solve [ eapply tr_subtyp_bot; eauto 4 ]
        | solve [ eapply tr_subtyp_refl; eauto 4 ]
        | solve [ eapply tr_subtyp_trans; eauto 4 ]
        | solve [ eapply tr_subtyp_and11; eauto 4 ]
        | solve [ eapply tr_subtyp_and12; eauto 4 ]
        | solve [ eapply tr_subtyp_and2; eauto 4 ]
        | solve [ eapply tr_subtyp_fld; eauto 4 ]
        | solve [ eapply tr_subtyp_typ; eauto 4 ]
        | solve [ eapply tr_subtyp_sel2; eauto 4 ]
        | solve [ eapply tr_subtyp_sel1; eauto 4 ]
        | solve [ eapply tr_subtyp_all; eauto 4 ]
        | solve [ eapply tr_typ_avars_nil; eauto 4 ]
        | solve [ eapply tr_typ_avars_cons; eauto 4 ] ].
Qed.

Corollary ty_trm_binds_extends : forall (G:ctx) (t:trm) (T:typ), G ⊢ t ∶ T ->
  forall G', binds_extends G G' -> G' ⊢ t ∶ T.
Proof. intros G t T H G' He. exact (proj1 typing_binds_extends_mut G t T H G' He). Qed.

Corollary ty_lit_binds_extends : forall (G:ctx) (l:lit) (T:typ), G ⊢ l ∶ T ->
  forall G', binds_extends G G' -> G' ⊢ l ∶ T.
Proof. intros G l T H G' He. exact (proj1 (proj2 typing_binds_extends_mut) G l T H G' He). Qed.

Corollary subtyp_binds_extends : forall (G:ctx) (T U:typ), G ⊢ T <: U ->
  forall G', binds_extends G G' -> G' ⊢ T <: U.
Proof. intros G T U H G' He. exact (proj1 (proj2 (proj2 typing_binds_extends_mut)) G T U H G' He). Qed.

Corollary ty_avars_binds_extends : forall (G:ctx) (avs:avars) (Ts:typs), G ⊢ avs :: Ts ->
  forall G', binds_extends G G' -> G' ⊢ avs :: Ts.
Proof. intros G avs Ts H G' He. exact (proj2 (proj2 (proj2 typing_binds_extends_mut)) G avs Ts H G' He). Qed.

(** * Freshness in lists *)

Lemma fresh_cons_head : forall (L:vars) (n:nat) (x:var) (ys:list var),
  fresh L (S n) (cons x ys) -> x \notin L.
Proof. intros L n x ys H. simpl in H. destruct H as [Hx _]. exact Hx. Qed.

Lemma fresh_cons_tail : forall (L:vars) (n:nat) (x:var) (ys:list var),
  fresh L (S n) (cons x ys) -> fresh (L \u \{x}) n ys.
Proof. intros L n x ys H. simpl in H. destruct H as [_ H]. exact H. Qed.

Lemma fresh_from_list_notin : forall (L:vars) (n:nat) (xs:list var),
  fresh L n xs -> forall y, y \in from_list xs -> y \notin L.
Proof.
  intros L n xs. revert L n. induction xs as [|z zs IH]; intros L n Hf y Hy.
  - simpl in Hy. apply in_empty_inv in Hy. destruct Hy.
  - destruct n as [|n]; [inversion Hf|].
    simpl in Hf. destruct Hf as [Hz Hf'].
    rewrite from_list_cons in Hy. rewrite in_union in Hy. destruct Hy as [Hy|Hy].
    + rewrite in_singleton in Hy. subst y. exact Hz.
    + assert (Hnot : y \notin (L \u \{z})).
      { eapply IH; eauto. }
      apply notin_union_r1 in Hnot. exact Hnot.
Qed.

Lemma from_list_app : forall (A:Type) (l1 l2:list A),
  from_list (List.app l1 l2) = from_list l1 \u from_list l2.
Proof.
  intros A l1 l2. induction l1 as [|a l1 IH]; simpl.
  - rewrite union_empty_l. reflexivity.
  - rewrite from_list_cons, IH, from_list_cons. rewrite <- union_assoc. reflexivity.
Qed.

Lemma from_list_rev : forall (xs:list var), from_list (List.rev xs) = from_list xs.
Proof.
  intros xs. induction xs as [|x xs IH]; simpl.
  - reflexivity.
  - rewrite from_list_app, IH, from_list_cons, union_empty_r, union_comm. reflexivity.
Qed.

Lemma LibList_length_List_app : forall (A:Type) (l1 l2:list A),
  LibList.length (List.app l1 l2) = LibList.length l1 + LibList.length l2.
Proof.
  intros A l1 l2. induction l1 as [|a l1 IH]; simpl.
  - rewrite LibList.length_nil. rewrite Nat.add_0_l. reflexivity.
  - change (1 + LibList.length (l1 ++ l2) = (1 + LibList.length l1) + LibList.length l2).
    rewrite IH. rewrite Nat.add_assoc. reflexivity.
Qed.

Lemma LibList_length_List_rev : forall (A:Type) (l:list A),
  LibList.length (List.rev l) = LibList.length l.
Proof.
  intros A l. induction l as [|x xs IH]; simpl.
  - reflexivity.
  - rewrite LibList_length_List_app, IH.
    change (LibList.length xs + 1 = 1 + LibList.length xs).
    rewrite Nat.add_comm. reflexivity.
Qed.

Lemma List_length_LibList_length : forall (A:Type) (l:list A),
  List.length l = LibList.length l.
Proof.
  intros A l. induction l as [|a l IH]; simpl.
  - reflexivity.
  - change (S (List.length l) = 1 + LibList.length l). rewrite IH. reflexivity.
Qed.

(** * Environment simulation *)

Definition env_sim (Gtarget Gsource : ctx) : Prop :=
  forall x T, binds x T Gsource -> Gtarget ⊢ trm_var (avar_f x) ∶ T.

Lemma env_sim_push : forall (G' G:ctx) (x:var) (T:typ),
  env_sim G' G -> x \notin dom G' -> env_sim (G' & x ~ T) (G & x ~ T).
Proof.
  intros G' G x T He Hx z U Hz.
  destruct (classic (z = x)) as [->|Hne].
  - apply binds_push_eq_inv in Hz. subst U. apply ty_var. apply binds_push_eq.
  - apply binds_push_neq_inv in Hz; auto.
    eapply ty_trm_binds_extends; [apply He; eauto|].
    intros a v Ha. apply binds_push_neq; [exact Ha|].
    intro Hax. subst a. exact (binds_fresh_inv Ha Hx).
Qed.

Lemma env_sim_push_env : forall (G' G:ctx) (E:env typ),
  (forall y, y \in dom E -> y \notin dom G') ->
  env_sim G' G ->
  env_sim (G' & E) (G & E).
Proof.
  intros G' G E Hfresh He z U Hz.
  destruct (classic (z \in dom E)) as [Hin|Hnot].
  - apply get_some in Hin. destruct Hin as [U' HbE].
    assert (HbGE : binds z U' (G & E)) by (apply binds_concat_right; exact HbE).
    assert (U = U') by (eapply binds_functional; eauto). subst U'.
    eapply ty_var. apply binds_concat_right. exact HbE.
  - assert (HbG : binds z U G).
    { eapply binds_concat_left_inv; eauto. }
    eapply ty_trm_binds_extends; [apply He; exact HbG|].
    intros a v Ha. apply binds_concat_left.
    + exact Ha.
    + apply get_some_inv in Ha.
      intro HinE. exact (Hfresh a HinE Ha).
Qed.

(** * env_sim for ty_defs *)

Section DefsEnvSim.

Context {A : Set} `{LabelOf A} `{DTA : DecTyping A}.

Hypothesis dec_sim :
  forall (G:ctx) (d:A) (D:dec), G ⊢ d ∶d D ->
    forall G', env_sim G' G -> G' ⊢ d ∶d D.

Lemma ty_defs_env_sim : forall (G:ctx) (ds:list A) (T:typ),
  G ⊢ ds ∶ T -> forall G', env_sim G' G -> G' ⊢ ds ∶ T.
Proof.
  intros G ds T Hds. induction Hds; intros G' He.
  - eapply ty_defs_one. eapply (dec_sim (G:=Gamma) (d:=d) (D:=D) H0). exact He.
  - eapply ty_defs_cons.
    + apply IHHds. exact He.
    + eapply (dec_sim (G:=Gamma) (d:=d) (D:=D) H1). exact He.
    + assumption.
Qed.

End DefsEnvSim.

Lemma ty_def_env_sim : forall (G:ctx) (d:def) (D:dec),
  G ⊢ d ∶d D -> forall G', env_sim G' G -> G' ⊢ d ∶d D.
Proof.
  intros G d D H G' He.
  change (ty_def G d D) in H. change (ty_def G' d D).
  destruct H.
  - apply ty_def_typ.
  - apply ty_def_trm. exact t.
Qed.

Lemma ty_defs_def_env_sim : forall (G:ctx) (ds:defs) (T:typ),
  G ⊢ ds ∶ T -> forall G', env_sim G' G -> G' ⊢ ds ∶ T.
Proof.
  intros. eapply ty_defs_env_sim; eauto using ty_def_env_sim.
Qed.

(** * Helpers for env_sim *)

Section EnvSimHelpers.

Lemma env_sim_singles : forall (G' G:ctx) (x:var) (ys:list var) (Ts:typs) (T:typ),
  env_sim G' G ->
  length ys = length_s Ts ->
  (forall y, y \in from_list ys -> y \notin dom G') ->
  x \notin dom G' ->
  x \notin from_list ys ->
  env_sim (G' & (ys ~** (to_list Ts)) & (x ~ open_vars (cons x ys) T))
          (G & (ys ~** (to_list Ts)) & (x ~ open_vars (cons x ys) T)).
Proof.
  intros G' G x ys Ts T He Hlen Hys Hx Hxys.
  unfold length_s in Hlen.
  change (List.length ys = List.length (to_list Ts)) in Hlen.
  rewrite !List_length_LibList_length in Hlen.
  assert (Hs : dom (ys ~** (to_list Ts)) = from_list ys).
  { rewrite (dom_singles (List.rev ys) (List.rev (to_list Ts))).
    - rewrite from_list_rev. reflexivity.
    - rewrite !LibList_length_List_rev. exact Hlen. }
  eapply env_sim_push.
  - eapply env_sim_push_env.
    + intros y Hy. rewrite Hs in Hy. apply Hys. exact Hy.
    + exact He.
  - rewrite dom_concat. apply notin_union_l.
    + exact Hx.
    + rewrite Hs. exact Hxys.
Qed.

Lemma fresh_conj : forall (L:vars) (G':ctx) (n:nat) (x:var) (ys:list var),
  fresh (L \u dom G') (S n) (cons x ys) ->
  x \notin L /\
  x \notin dom G' /\
  x \notin from_list ys /\
  (forall y, y \in from_list ys -> y \notin dom G').
Proof.
  intros L G' n x ys Hf.
  assert (Hhead : x \notin L \u dom G') by (eapply fresh_cons_head; exact Hf).
  assert (Htail : fresh ((L \u dom G') \u \{x}) n ys) by (eapply fresh_cons_tail; exact Hf).
  repeat split.
  - apply notin_union_r1 in Hhead. exact Hhead.
  - apply notin_union_r2 in Hhead. exact Hhead.
  - intro Hxin.
    assert (Hc : x \notin ((L \u dom G') \u \{x})).
    { eapply fresh_from_list_notin; eauto. }
    apply notin_union_r2 in Hc. exact (Hc (in_singleton_self x)).
  - intros y Hy.
    assert (Hc : y \notin ((L \u dom G') \u \{x})).
    { eapply fresh_from_list_notin; eauto. }
    apply notin_union_r1 in Hc. apply notin_union_r2 in Hc. exact Hc.
Qed.

Lemma es_ty_var : forall (G:ctx) (x:var) (T:typ),
  binds x T G -> forall G', env_sim G' G -> G' ⊢ trm_var (avar_f x) ∶ T.
Proof. intros. eapply H0; eauto. Qed.

Lemma es_ty_all_elim : forall (G:ctx) (x z:var) (S T:typ),
  (forall G', env_sim G' G -> G' ⊢ trm_var (avar_f x) ∶ typ_all S T) ->
  (forall G', env_sim G' G -> G' ⊢ trm_var (avar_f z) ∶ S) ->
  forall G', env_sim G' G -> G' ⊢ trm_app (avar_f x) (avar_f z) ∶ open z T.
Proof. intros. eapply ty_all_elim; [eapply H; eauto|eapply H0; eauto]. Qed.

Lemma es_ty_new : forall (G:ctx) (x:var) (avs:avars) (xs:list var) (Ts:typs) (is':inits) (T:typ),
  (forall G', env_sim G' G -> G' ⊢ trm_var (avar_f x) ∶ typ_con Ts is' T) ->
  (forall G', env_sim G' G -> G' ⊢ avs :: Ts) ->
  vars_of_avars xs avs ->
  forall G', env_sim G' G -> G' ⊢ trm_new (avar_f x) avs ∶ typ_bnd (open_rec_vars 1 xs T).
Proof.
  intros. eapply ty_new.
  - eapply H; eauto.
  - eapply H0; eauto.
  - eauto.
Qed.

Lemma es_ty_rcd_elim : forall (G:ctx) (x:var) (a:trm_label) (S T:typ),
  (forall G', env_sim G' G -> G' ⊢ trm_var (avar_f x) ∶ typ_rcd (dec_trm a S T)) ->
  forall G', env_sim G' G -> G' ⊢ trm_sel (avar_f x) a ∶ T.
Proof. intros. eapply ty_rcd_elim; eauto. Qed.

Lemma es_ty_fld_asn : forall (G:ctx) (x y:var) (a:trm_label) (S T:typ),
  (forall G', env_sim G' G -> G' ⊢ trm_var (avar_f x) ∶ typ_rcd (dec_trm a S T)) ->
  (forall G', env_sim G' G -> G' ⊢ trm_var (avar_f y) ∶ S) ->
  forall G', env_sim G' G -> G' ⊢ trm_asn (avar_f x) a (avar_f y) ∶ T.
Proof. intros. eapply ty_fld_asn; [eapply H; eauto|eapply H0; eauto]. Qed.

Lemma es_ty_let : forall (L:fset var) (G:ctx) (t u:trm) (T U:typ),
  (forall G', env_sim G' G -> G' ⊢ t ∶ T) ->
  (forall x, x \notin L -> forall G', env_sim G' (G & x ~ T) -> G' ⊢ open x u ∶ U) ->
  forall G', env_sim G' G -> G' ⊢ trm_let T t u ∶ U.
Proof.
  intros L G t u T U H1 H2 G' He.
  eapply ty_let with (L := L \u dom G').
  - eapply H1; eauto.
  - intros x Hx. eapply H2.
    + apply notin_union_r1 in Hx. exact Hx.
    + eapply env_sim_push; [exact He|]. apply notin_union_r2 in Hx. exact Hx.
Qed.

Lemma es_ty_llit : forall (L:fset var) (G:ctx) (l:lit) (u:trm) (T U:typ),
  (forall G', env_sim G' G -> G' ⊢ l ∶ T) ->
  (forall x, x \notin L -> forall G', env_sim G' (G & x ~ T) -> G' ⊢ open x u ∶ U) ->
  forall G', env_sim G' G -> G' ⊢ trm_lit T l u ∶ U.
Proof.
  intros L G l u T U H1 H2 G' He.
  eapply ty_llit with (L := L \u dom G').
  - eapply H1; eauto.
  - intros x Hx. eapply H2.
    + apply notin_union_r1 in Hx. exact Hx.
    + eapply env_sim_push; [exact He|]. apply notin_union_r2 in Hx. exact Hx.
Qed.

Lemma es_ty_rec_intro : forall (G:ctx) (x:var) (T:typ),
  (forall G', env_sim G' G -> G' ⊢ trm_var (avar_f x) ∶ open x T) ->
  forall G', env_sim G' G -> G' ⊢ trm_var (avar_f x) ∶ typ_bnd T.
Proof. intros. eapply ty_rec_intro; eauto. Qed.

Lemma es_ty_rec_elim : forall (G:ctx) (x:var) (T:typ),
  (forall G', env_sim G' G -> G' ⊢ trm_var (avar_f x) ∶ typ_bnd T) ->
  forall G', env_sim G' G -> G' ⊢ trm_var (avar_f x) ∶ open x T.
Proof. intros. eapply ty_rec_elim; eauto. Qed.

Lemma es_ty_and_intro : forall (G:ctx) (x:var) (T U:typ),
  (forall G', env_sim G' G -> G' ⊢ trm_var (avar_f x) ∶ T) ->
  (forall G', env_sim G' G -> G' ⊢ trm_var (avar_f x) ∶ U) ->
  forall G', env_sim G' G -> G' ⊢ trm_var (avar_f x) ∶ typ_and T U.
Proof. intros. eapply ty_and_intro; [eapply H; eauto|eapply H0; eauto]. Qed.

Lemma es_ty_sub : forall (G:ctx) (t:trm) (T U:typ),
  (forall G', env_sim G' G -> G' ⊢ t ∶ T) ->
  (forall G', env_sim G' G -> G' ⊢ T <: U) ->
  forall G', env_sim G' G -> G' ⊢ t ∶ U.
Proof. intros. eapply ty_sub; [eapply H; eauto|eapply H0; eauto]. Qed.

Lemma es_ty_all_intro : forall (L:fset var) (G:ctx) (T:typ) (t:trm) (U:typ),
  (forall x, x \notin L -> forall G', env_sim G' (G & x ~ T) -> G' ⊢ open x t ∶ open x U) ->
  forall G', env_sim G' G -> G' ⊢ lit_fun T t ∶ typ_all T U.
Proof.
  intros L G T t U H G' He.
  eapply ty_all_intro with (L := L \u dom G').
  intros x Hx. eapply H.
  - apply notin_union_r1 in Hx. exact Hx.
  - eapply env_sim_push; [exact He|]. apply notin_union_r2 in Hx. exact Hx.
Qed.

Lemma es_ty_con_intro : forall (L:fset var) (G:ctx) (Ts:typs) (is':inits) (T:typ)
  (ds:defs) (t:trm) (T':typ),
  (forall x ys, length ys = length_s Ts ->
     fresh L (S (length ys)) (cons x ys) ->
     G & (ys ~** (to_list Ts)) & (x ~ open_vars (cons x ys) T)
       ⊢ (open_vars (cons x ys) ds) ∶ (open_vars (cons x ys) T)) ->
  (forall x ys, length ys = length_s Ts ->
     fresh L (S (length ys)) (cons x ys) ->
     forall G', env_sim G' (G & (ys ~** (to_list Ts)) & (x ~ open_vars (cons x ys) T)) ->
       G' ⊢ (open_vars (cons x ys) t) ∶ (open_vars (cons x ys) T')) ->
  forall G', env_sim G' G -> G' ⊢ lit_con Ts is' T ds t ∶ typ_con Ts is' T.
Proof.
  intros L G Ts is' T ds t T' Hds Ht G' He.
  eapply ty_con_intro with (L := L \u dom G').
  - intros x ys Hlen Hf.
    destruct (fresh_conj Hf) as [HxL [HxG [Hxys HysG]]].
    eapply ty_defs_def_env_sim.
    + eapply Hds.
      * exact Hlen.
      * eapply fresh_union_r1; exact Hf.
    + eapply env_sim_singles; eauto.
  - intros x ys Hlen Hf.
    destruct (fresh_conj Hf) as [HxL [HxG [Hxys HysG]]].
    eapply Ht.
    + exact Hlen.
    + eapply fresh_union_r1; exact Hf.
    + eapply env_sim_singles; eauto.
Qed.

Lemma es_subtyp_top : forall (G:ctx) (T:typ),
  forall G', env_sim G' G -> G' ⊢ T <: typ_top.
Proof. intros. eapply subtyp_top. Qed.

Lemma es_subtyp_bot : forall (G:ctx) (T:typ),
  forall G', env_sim G' G -> G' ⊢ typ_bot <: T.
Proof. intros. eapply subtyp_bot. Qed.

Lemma es_subtyp_refl : forall (G:ctx) (T:typ),
  forall G', env_sim G' G -> G' ⊢ T <: T.
Proof. intros. eapply subtyp_refl. Qed.

Lemma es_subtyp_trans : forall (G:ctx) (S T U:typ),
  (forall G', env_sim G' G -> G' ⊢ S <: T) ->
  (forall G', env_sim G' G -> G' ⊢ T <: U) ->
  forall G', env_sim G' G -> G' ⊢ S <: U.
Proof. intros. eapply subtyp_trans; [eapply H; eauto|eapply H0; eauto]. Qed.

Lemma es_subtyp_and11 : forall (G:ctx) (T U:typ),
  forall G', env_sim G' G -> G' ⊢ typ_and T U <: T.
Proof. intros. eapply subtyp_and11. Qed.

Lemma es_subtyp_and12 : forall (G:ctx) (T U:typ),
  forall G', env_sim G' G -> G' ⊢ typ_and T U <: U.
Proof. intros. eapply subtyp_and12. Qed.

Lemma es_subtyp_and2 : forall (G:ctx) (S T U:typ),
  (forall G', env_sim G' G -> G' ⊢ S <: T) ->
  (forall G', env_sim G' G -> G' ⊢ S <: U) ->
  forall G', env_sim G' G -> G' ⊢ S <: typ_and T U.
Proof. intros. eapply subtyp_and2; [eapply H; eauto|eapply H0; eauto]. Qed.

Lemma es_subtyp_fld : forall (G:ctx) (a:trm_label) (T1 T2 U1 U2:typ),
  (forall G', env_sim G' G -> G' ⊢ T1 <: T2) ->
  (forall G', env_sim G' G -> G' ⊢ U1 <: U2) ->
  forall G', env_sim G' G ->
    G' ⊢ typ_rcd (dec_trm a T2 U1) <: typ_rcd (dec_trm a T1 U2).
Proof. intros. eapply subtyp_fld; [eapply H; eauto|eapply H0; eauto]. Qed.

Lemma es_subtyp_typ : forall (G:ctx) (A:typ_label) (S1 T1 S2 T2:typ),
  (forall G', env_sim G' G -> G' ⊢ S2 <: S1) ->
  (forall G', env_sim G' G -> G' ⊢ T1 <: T2) ->
  forall G', env_sim G' G ->
    G' ⊢ typ_rcd (dec_typ A S1 T1) <: typ_rcd (dec_typ A S2 T2).
Proof. intros. eapply subtyp_typ; [eapply H; eauto|eapply H0; eauto]. Qed.

Lemma es_subtyp_sel2 : forall (G:ctx) (x:var) (A:typ_label) (S T:typ),
  (forall G', env_sim G' G -> G' ⊢ trm_var (avar_f x) ∶ typ_rcd (dec_typ A S T)) ->
  forall G', env_sim G' G -> G' ⊢ S <: typ_sel (avar_f x) A.
Proof. intros. eapply subtyp_sel2; eauto. Qed.

Lemma es_subtyp_sel1 : forall (G:ctx) (x:var) (A:typ_label) (S T:typ),
  (forall G', env_sim G' G -> G' ⊢ trm_var (avar_f x) ∶ typ_rcd (dec_typ A S T)) ->
  forall G', env_sim G' G -> G' ⊢ typ_sel (avar_f x) A <: T.
Proof. intros. eapply subtyp_sel1; eauto. Qed.

Lemma es_subtyp_all : forall (L:fset var) (G:ctx) (S1 T1 S2 T2:typ),
  (forall G', env_sim G' G -> G' ⊢ S2 <: S1) ->
  (forall x, x \notin L -> forall G', env_sim G' (G & x ~ S2) -> G' ⊢ open x T1 <: open x T2) ->
  forall G', env_sim G' G -> G' ⊢ typ_all S1 T1 <: typ_all S2 T2.
Proof.
  intros L G S1 T1 S2 T2 H1 H2 G' He.
  eapply subtyp_all with (L := L \u dom G').
  - eapply H1; eauto.
  - intros x Hx. eapply H2.
    + apply notin_union_r1 in Hx. exact Hx.
    + eapply env_sim_push; [exact He|]. apply notin_union_r2 in Hx. exact Hx.
Qed.

Lemma es_typ_avars_nil : forall (G:ctx),
  forall G', env_sim G' G -> G' ⊢ (nil:avars) :: typs_nil.
Proof. intros. eapply typ_avars_nil. Qed.

Lemma es_typ_avars_cons : forall (G:ctx) (x:var) (T:typ) (avs:avars) (Ts:typs),
  (forall G', env_sim G' G -> G' ⊢ trm_var (avar_f x) ∶ T) ->
  (forall G', env_sim G' G -> G' ⊢ avs :: Ts) ->
  forall G', env_sim G' G -> G' ⊢ (cons (avar_f x) avs) :: (typs_cons T Ts).
Proof. intros. eapply typ_avars_cons; [eapply H; eauto|eapply H0; eauto]. Qed.

End EnvSimHelpers.

Lemma typing_env_sim_mut :
  (forall (G:ctx) (t:trm) (T:typ), G ⊢ t ∶ T ->
     forall G', env_sim G' G -> G' ⊢ t ∶ T) /\
  (forall (G:ctx) (l:lit) (T:typ), G ⊢ l ∶ T ->
     forall G', env_sim G' G -> G' ⊢ l ∶ T) /\
  (forall (G:ctx) (T U:typ), G ⊢ T <: U ->
     forall G', env_sim G' G -> G' ⊢ T <: U) /\
  (forall (G:ctx) (avs:avars) (Ts:typs), G ⊢ avs :: Ts ->
     forall G', env_sim G' G -> G' ⊢ avs :: Ts).
Proof.
  apply (rules_mutind
    (fun (G:ctx) (t:trm) (T:typ) (_:G ⊢ t ∶ T) =>
       forall G', env_sim G' G -> G' ⊢ t ∶ T)
    (fun (G:ctx) (l:lit) (T:typ) (_:G ⊢ l ∶ T) =>
       forall G', env_sim G' G -> G' ⊢ l ∶ T)
    (fun (G:ctx) (T U:typ) (_:G ⊢ T <: U) =>
       forall G', env_sim G' G -> G' ⊢ T <: U)
    (fun (G:ctx) (avs:avars) (Ts:typs) (_:G ⊢ avs :: Ts) =>
       forall G', env_sim G' G -> G' ⊢ avs :: Ts));
  intros;
  first [ solve [ eapply es_ty_var; eauto 4 ]
        | solve [ eapply es_ty_all_elim; eauto 4 ]
        | solve [ eapply es_ty_new; eauto 4 ]
        | solve [ eapply es_ty_rcd_elim; eauto 4 ]
        | solve [ eapply es_ty_fld_asn; eauto 4 ]
        | solve [ eapply es_ty_let; eauto 4 ]
        | solve [ eapply es_ty_llit; eauto 4 ]
        | solve [ eapply es_ty_rec_intro; eauto 4 ]
        | solve [ eapply es_ty_rec_elim; eauto 4 ]
        | solve [ eapply es_ty_and_intro; eauto 4 ]
        | solve [ eapply es_ty_sub; eauto 4 ]
        | solve [ eapply es_ty_all_intro; eauto 4 ]
        | solve [ eapply es_ty_con_intro; eauto 4 ]
        | solve [ eapply es_subtyp_top; eauto 4 ]
        | solve [ eapply es_subtyp_bot; eauto 4 ]
        | solve [ eapply es_subtyp_refl; eauto 4 ]
        | solve [ eapply es_subtyp_trans; eauto 4 ]
        | solve [ eapply es_subtyp_and11; eauto 4 ]
        | solve [ eapply es_subtyp_and12; eauto 4 ]
        | solve [ eapply es_subtyp_and2; eauto 4 ]
        | solve [ eapply es_subtyp_fld; eauto 4 ]
        | solve [ eapply es_subtyp_typ; eauto 4 ]
        | solve [ eapply es_subtyp_sel2; eauto 4 ]
        | solve [ eapply es_subtyp_sel1; eauto 4 ]
        | solve [ eapply es_subtyp_all; eauto 4 ]
        | solve [ eapply es_typ_avars_nil; eauto 4 ]
        | solve [ eapply es_typ_avars_cons; eauto 4 ] ].
Qed.

Corollary ty_trm_env_sim : forall (G:ctx) (t:trm) (T:typ), G ⊢ t ∶ T ->
  forall G', env_sim G' G -> G' ⊢ t ∶ T.
Proof. intros G t T H G' He. exact (proj1 typing_env_sim_mut G t T H G' He). Qed.

Corollary ty_lit_env_sim : forall (G:ctx) (l:lit) (T:typ), G ⊢ l ∶ T ->
  forall G', env_sim G' G -> G' ⊢ l ∶ T.
Proof. intros G l T H G' He. exact (proj1 (proj2 typing_env_sim_mut) G l T H G' He). Qed.

Corollary subtyp_env_sim : forall (G:ctx) (T U:typ), G ⊢ T <: U ->
  forall G', env_sim G' G -> G' ⊢ T <: U.
Proof. intros G T U H G' He. exact (proj1 (proj2 (proj2 typing_env_sim_mut)) G T U H G' He). Qed.

Corollary ty_avars_env_sim : forall (G:ctx) (avs:avars) (Ts:typs), G ⊢ avs :: Ts ->
  forall G', env_sim G' G -> G' ⊢ avs :: Ts.
Proof. intros G avs Ts H G' He. exact (proj2 (proj2 (proj2 typing_env_sim_mut)) G avs Ts H G' He). Qed.

(** * Substitution commutation with opening for terms, lits, defs, lists *)

Lemma subst_open_rec_avars : forall (avs:avars) (x y z:var) (n:nat),
  subst_var x y (open_rec n z avs) =
  open_rec n (z \[x -> y]) (subst_var x y avs).
Proof.
  intros avs. induction avs as [|a avs IH]; intros x y z n.
  - simpl. reflexivity.
  - change (subst_var x y (open_rec n z a) :: subst_var x y (open_rec n z avs)
            = open_rec n (z \[x -> y]) (subst_var x y a)
              :: open_rec n (z \[x -> y]) (subst_var x y avs)).
    f_equal.
    + apply subst_open_avar.
    + apply IH.
Qed.

Lemma subst_open_rec_def : forall (d:def) (x y z:var) (n:nat),
  subst_var x y (open_rec n z d) =
  open_rec n (z \[x -> y]) (subst_var x y d).
Proof.
  intros d. destruct d as [A T|a]; intros x y z n; simpl.
  - f_equal. apply (proj1 subst_open_rec_mut).
  - reflexivity.
Qed.

Lemma subst_open_rec_defs : forall (ds:defs) (x y z:var) (n:nat),
  subst_var x y (open_rec n z ds) =
  open_rec n (z \[x -> y]) (subst_var x y ds).
Proof.
  intros ds. induction ds as [|d ds IH]; intros x y z n.
  - simpl. reflexivity.
  - change (subst_var x y (open_rec n z d) :: subst_var x y (open_rec n z ds)
            = open_rec n (z \[x -> y]) (subst_var x y d)
              :: open_rec n (z \[x -> y]) (subst_var x y ds)).
    f_equal.
    + apply subst_open_rec_def.
    + apply IH.
Qed.

Lemma subst_open_rec_trm_mut :
  (forall (t:trm) (x y z:var) (n:nat),
      subst_var x y (open_rec n z t) =
      open_rec n (z \[x -> y]) (subst_var x y t)) /\
  (forall (l:lit) (x y z:var) (n:nat),
      subst_var x y (open_rec n z l) =
      open_rec n (z \[x -> y]) (subst_var x y l)).
Proof.
  apply trm_mutind; intros; simpl.
  - f_equal. apply subst_open_avar.
  - f_equal. apply subst_open_avar.
  - f_equal; [apply subst_open_avar|apply subst_open_avar].
  - f_equal.
    + apply (proj1 subst_open_rec_mut).
    + apply H.
    + apply H0.
  - f_equal.
    + apply (proj1 subst_open_rec_mut).
    + apply H.
    + apply H0.
  - f_equal; [apply subst_open_avar|apply subst_open_avar].
  - f_equal.
    + apply subst_open_avar.
    + apply subst_open_rec_avars.
  - f_equal.
    + apply (proj1 subst_open_rec_mut).
    + apply H.
  - rewrite length_s_subst_typs.
    f_equal.
    + apply (proj1 (proj2 subst_open_rec_mut)).
    + apply (proj1 subst_open_rec_mut).
    + apply subst_open_rec_defs.
    + apply H.
Qed.

(** * Substitution of a fresh variable is the identity *)

Ltac finish_fresh :=
  unfold fv in *; try unfold TypFreeVar in *; try unfold TypsFreeVar in *;
  try unfold TrmFreeVar in *; try unfold LitFreeVar in *;
  try unfold DefFreeVar in *; try unfold AvarFreeVar in *; cbn in *; eauto.

Lemma fv_subst_typ_mut :
  (forall (T:typ) (x y:var), x \notin fv T -> subst_var x y T = T) /\
  (forall (Ts:typs) (x y:var), x \notin fv Ts -> subst_var x y Ts = Ts) /\
  (forall (D:dec) (x y:var), x \notin fv D -> subst_var x y D = D).
Proof.
  apply typ_mutind; intros; simpl; simpl in *.
  - reflexivity.
  - reflexivity.
  - f_equal. eapply H; finish_fresh.
  - f_equal; [eapply H; finish_fresh|eapply H0; finish_fresh].
  - f_equal. apply subst_avar_fresh; finish_fresh.
  - f_equal. eapply H; finish_fresh.
  - f_equal; [eapply H; finish_fresh|eapply H0; finish_fresh].
  - f_equal; [eapply H; finish_fresh|eapply H0; finish_fresh].
  - reflexivity.
  - f_equal; [eapply H; finish_fresh|eapply H0; finish_fresh].
  - f_equal; [eapply H; finish_fresh|eapply H0; finish_fresh].
  - f_equal; [eapply H; finish_fresh|eapply H0; finish_fresh].
Qed.

Lemma fv_subst_typ : forall (T:typ) (x y:var), x \notin fv T -> subst_var x y T = T.
Proof. apply (proj1 fv_subst_typ_mut). Qed.

Lemma fv_subst_typs : forall (Ts:typs) (x y:var), x \notin fv Ts -> subst_var x y Ts = Ts.
Proof. apply (proj1 (proj2 fv_subst_typ_mut)). Qed.

Lemma fv_subst_dec : forall (D:dec) (x y:var), x \notin fv D -> subst_var x y D = D.
Proof. apply (proj2 (proj2 fv_subst_typ_mut)). Qed.

Lemma fv_subst_avars : forall (avs:avars) (x y:var), x \notin fv avs -> subst_var x y avs = avs.
Proof.
  intros avs. induction avs as [|a avs IH]; intros x y H; simpl in *.
  - reflexivity.
  - f_equal.
    + apply subst_avar_fresh; finish_fresh.
    + eapply IH; finish_fresh.
Qed.

Lemma fv_subst_def : forall (d:def) (x y:var), x \notin fv d -> subst_var x y d = d.
Proof.
  intros d. destruct d as [A T|a]; intros x y H; simpl in *.
  - f_equal. apply fv_subst_typ; finish_fresh.
  - reflexivity.
Qed.

Lemma fv_subst_defs : forall (ds:defs) (x y:var), x \notin fv ds -> subst_var x y ds = ds.
Proof.
  intros ds. induction ds as [|d ds IH]; intros x y H; simpl in *.
  - reflexivity.
  - f_equal.
    + apply fv_subst_def; finish_fresh.
    + eapply IH; finish_fresh.
Qed.

Lemma fv_subst_trm_mut :
  (forall (t:trm) (x y:var), x \notin fv t -> subst_var x y t = t) /\
  (forall (l:lit) (x y:var), x \notin fv l -> subst_var x y l = l).
Proof.
  apply trm_mutind; intros; simpl; simpl in *.
  - f_equal. apply subst_avar_fresh; finish_fresh.
  - f_equal. apply subst_avar_fresh; finish_fresh.
  - f_equal; [apply subst_avar_fresh; finish_fresh|apply subst_avar_fresh; finish_fresh].
  - f_equal.
    + apply fv_subst_typ; finish_fresh.
    + eapply H; finish_fresh.
    + eapply H0; finish_fresh.
  - f_equal.
    + apply fv_subst_typ; finish_fresh.
    + eapply H; finish_fresh.
    + eapply H0; finish_fresh.
  - f_equal; [apply subst_avar_fresh; finish_fresh|apply subst_avar_fresh; finish_fresh].
  - f_equal.
    + apply subst_avar_fresh; finish_fresh.
    + apply fv_subst_avars; finish_fresh.
  - f_equal.
    + apply fv_subst_typ; finish_fresh.
    + eapply H; finish_fresh.
  - f_equal.
    + apply fv_subst_typs; finish_fresh.
    + apply fv_subst_typ; finish_fresh.
    + apply fv_subst_defs; finish_fresh.
    + eapply H; finish_fresh.
Qed.

Lemma fv_subst_trm : forall (t:trm) (x y:var), x \notin fv t -> subst_var x y t = t.
Proof. apply (proj1 fv_subst_trm_mut). Qed.

Lemma fv_subst_lit : forall (l:lit) (x y:var), x \notin fv l -> subst_var x y l = l.
Proof. apply (proj2 fv_subst_trm_mut). Qed.

(** * Auxiliary lemmas for substitution *)

Lemma subst_fvar_eq : forall (x y:var), subst_fvar x y x = y.
Proof. intros. unfold subst_fvar. rewrite If_l; auto. Qed.

Lemma subst_fvar_neq : forall (x y z:var), z <> x -> subst_fvar x y z = z.
Proof. intros. unfold subst_fvar. rewrite If_r; auto. Qed.

Lemma subst_open_fresh_typ : forall (x y z:var) (n:nat) (T:typ), z <> x ->
  subst_var x y (open_rec n z T) = open_rec n z (subst_var x y T).
Proof. intros. rewrite (proj1 subst_open_rec_mut). f_equal. apply subst_fvar_neq; auto. Qed.

Lemma subst_open_fresh_trm : forall (x y z:var) (n:nat) (t:trm), z <> x ->
  subst_var x y (open_rec n z t) = open_rec n z (subst_var x y t).
Proof. intros. rewrite (proj1 subst_open_rec_trm_mut). f_equal. apply subst_fvar_neq; auto. Qed.

Lemma subst_open_fresh_lit : forall (x y z:var) (n:nat) (l:lit), z <> x ->
  subst_var x y (open_rec n z l) = open_rec n z (subst_var x y l).
Proof. intros. rewrite (proj2 subst_open_rec_trm_mut). f_equal. apply subst_fvar_neq; auto. Qed.

Lemma vars_of_avars_subst : forall (xs:list var) (avs:avars) (x y:var),
  vars_of_avars xs avs ->
  vars_of_avars (List.map (fun z => z \[x -> y]) xs) (subst_var x y avs).
Proof.
  intros xs avs x y H. induction H; simpl.
  - constructor.
  - change (vars_of_avars
              ((x0 \[x -> y]) :: List.map (fun z => z \[x -> y]) vs)
              (cons (avar_f (x0 \[x -> y])) (subst_var x y avs))).
    constructor; auto.
Qed.

Lemma label_of_subst_def : forall (x y:var) (d:def),
  label_of (subst_var x y d) = label_of d.
Proof. intros. destruct d; simpl. reflexivity. reflexivity. Qed.

Lemma labels_hasnt_subst_defs : forall (x y:var) (ds:defs) (l:label),
  labels_hasnt ds l -> labels_hasnt (subst_var x y ds) l.
Proof.
  intros x y ds. induction ds as [|a ds IH]; intros l H;
    unfold labels_hasnt in *; cbn in *.
  - exact H.
  - destruct (classic (label_of a = l)) as [E|NE].
    + rewrite (If_l (P:=label_of a = l) _ _ E) in H. discriminate.
    + rewrite (If_r (P:=label_of a = l) _ _ NE) in H.
      rewrite (label_of_subst_def x y a).
      rewrite (If_r (P:=label_of a = l) _ _ NE).
      rewrite (IH l H). reflexivity.
Qed.

(** * Substitution for defs *)

Lemma ty_def_subst : forall (G1 G2:ctx) (x y:var) (S:typ) (d:def) (D:dec),
  G1 & x ~ S & G2 ⊢ d ∶d D ->
  x # G2 ->
  x \notin fv_env G1 ->
  (G1 & subst_env x y G2 ⊢ trm_var (avar_f y) ∶ subst_var x y S) ->
  G1 & subst_env x y G2 ⊢ subst_var x y d ∶d subst_var x y D.
Proof.
  intros G1 G2 x y S d D Hd Hx Hfv Hpre.
  change (ty_def (G1 & x ~ S & G2) d D) in Hd.
  change (ty_def (G1 & subst_env x y G2) (subst_var x y d) (subst_var x y D)).
  destruct Hd.
  - change (ty_def (G1 & subst_env x y G2) (def_typ A (subst_var x y T))
                    (dec_typ A (subst_var x y T) (subst_var x y T))).
    apply ty_def_typ.
  - change (ty_def (G1 & subst_env x y G2) (def_trm a)
                    (dec_trm a (subst_var x y T) (subst_var x y T))).
    apply ty_def_trm. exact (trm_var (avar_f x)).
Qed.

Lemma ty_defs_subst : forall (G1 G2:ctx) (x y:var) (S:typ) (ds:defs) (T:typ),
  G1 & x ~ S & G2 ⊢ ds ∶ T ->
  x # G2 ->
  x \notin fv_env G1 ->
  (G1 & subst_env x y G2 ⊢ trm_var (avar_f y) ∶ subst_var x y S) ->
  G1 & subst_env x y G2 ⊢ subst_var x y ds ∶ subst_var x y T.
Proof.
  intros G1 G2 x y S ds T Hds Hx Hfv Hpre.
  remember (G1 & x ~ S & G2) as G eqn:EG.
  revert G1 G2 x y S Hx Hfv Hpre EG.
  induction Hds; intros G1 G2 x y S Hx Hfv Hpre EG; subst.
  - simpl.
    eapply ty_defs_one.
    eapply ty_def_subst; eauto.
  - simpl.
    eapply ty_defs_cons.
    + eapply IHHds; eauto.
    + eapply ty_def_subst; eauto.
    + apply labels_hasnt_subst_defs. rewrite label_of_subst_def. assumption.
Qed.

(** * Environment lemmas for substitution *)

Lemma subst_env_push_single : forall (G:ctx) (x y z:var) (T:typ),
  subst_env x y (G & z ~ T) = subst_env x y G & z ~ subst_var x y T.
Proof. intros. rewrite map_push. reflexivity. Qed.

Lemma dom_subst_env : forall (G:ctx) (x y:var), dom (subst_env x y G) = dom G.
Proof. intros. apply dom_map. Qed.

Lemma binds_extends_push_fresh : forall (A:Set) (G:env A) (x:var) (v:A),
  x \notin dom G -> binds_extends G (G & x ~ v).
Proof.
  intros A G x v Hx z w Hz. apply binds_push_neq; [exact Hz|].
  intro E. subst z. exact (binds_fresh_inv Hz Hx).
Qed.

Lemma notin_binder_setup : forall (L:vars) (G1 G2:ctx) (x z:var),
  z \notin (((L \u dom G1) \u dom G2) \u \{x}) ->
  z \notin L /\ z \notin dom G1 /\ z \notin dom G2 /\ z <> x.
Proof.
  intros L G1 G2 x z H.
  apply notin_union_r1 in H as H1. apply notin_union_r2 in H as Hx.
  apply notin_union_r1 in H1 as H2. apply notin_union_r2 in H1 as HG2.
  apply notin_union_r1 in H2 as HL. apply notin_union_r2 in H2 as HG1.
  apply notin_singleton_r in Hx.
  split; [exact HL|split;[exact HG1|split;[exact HG2|exact Hx]]].
Qed.

(** * Auxiliary lemmas for the constructor case *)

Lemma subst_if_eq : forall (x y:var), (x \[x -> y]) = y.
Proof. intros. rewrite If_l; auto. Qed.

Lemma subst_if_neq : forall (x y z:var), z <> x -> (z \[x -> y]) = z.
Proof. intros. rewrite If_r; auto. Qed.

Lemma subst_open_rec_vars_typ : forall (xm ym:var) (zs:list var) (k:nat) (T:typ),
  subst_var xm ym (open_rec_vars k zs T) =
  open_rec_vars k (List.map (fun z => z \[xm -> ym]) zs) (subst_var xm ym T).
Proof.
  intros xm ym zs. induction zs as [|z zs IH]; intros k T; simpl.
  - reflexivity.
  - rewrite IH. rewrite (proj1 subst_open_rec_mut). reflexivity.
Qed.

Lemma subst_open_rec_vars_trm : forall (xm ym:var) (zs:list var) (k:nat) (t:trm),
  subst_var xm ym (open_rec_vars k zs t) =
  open_rec_vars k (List.map (fun z => z \[xm -> ym]) zs) (subst_var xm ym t).
Proof.
  intros xm ym zs. induction zs as [|z zs IH]; intros k t; simpl.
  - reflexivity.
  - rewrite IH. rewrite (proj1 subst_open_rec_trm_mut). reflexivity.
Qed.

Lemma subst_open_rec_vars_defs : forall (xm ym:var) (zs:list var) (k:nat) (ds:defs),
  subst_var xm ym (open_rec_vars k zs ds) =
  open_rec_vars k (List.map (fun z => z \[xm -> ym]) zs) (subst_var xm ym ds).
Proof.
  intros xm ym zs. induction zs as [|z zs IH]; intros k ds; simpl.
  - reflexivity.
  - rewrite IH. rewrite subst_open_rec_defs. reflexivity.
Qed.

Lemma in_from_list : forall (A:Type) (x:A) (l:list A),
  (x \in from_list l) <-> List.In x l.
Proof.
  intros A x l. induction l as [|a l IH]; simpl.
  - rewrite in_empty. split; [intros []|intros []].
  - rewrite from_list_cons, in_union, in_singleton. split.
    + intros [E|E]; [left; symmetry; exact E | right; apply IH; exact E].
    + intros [E|E]; [left; symmetry; exact E | right; apply IH; exact E].
Qed.

Lemma map_ren_id : forall (xm ym:var) (zs:list var),
  (forall z, List.In z zs -> z <> xm) ->
  List.map (fun z => z \[xm -> ym]) zs = zs.
Proof.
  intros xm ym zs. induction zs as [|z zs IH]; intros H; simpl.
  - reflexivity.
  - rewrite (@subst_if_neq xm ym z (H z (or_introl eq_refl))).
    rewrite IH; [reflexivity|]. intros y Hy. apply H. right. exact Hy.
Qed.

Lemma to_list_subst_typs : forall (xm ym:var) (Ts:typs),
  typs_to_list (subst_typs xm ym Ts) = List.map (subst_typ xm ym) (typs_to_list Ts).
Proof.
  intros xm ym Ts. induction Ts as [|T Ts IH]; simpl.
  - reflexivity.
  - rewrite IH. reflexivity.
Qed.

Lemma LibList_map_List : forall (A B:Type) (f:A->B) (l:list A),
  LibList.map f l = List.map f l.
Proof.
  intros. induction l as [|a l IH].
  - rewrite LibList.map_nil. reflexivity.
  - rewrite LibList.map_cons, IH. reflexivity.
Qed.

Lemma LibList_map_app : forall (A B:Type) (f:A->B) (l1 l2:list A),
  LibList.map f (List.app l1 l2) = List.app (LibList.map f l1) (LibList.map f l2).
Proof.
  intros. induction l1 as [|a l1 IH]; simpl.
  - rewrite LibList.map_nil. reflexivity.
  - rewrite !LibList.map_cons, IH. reflexivity.
Qed.

Lemma singles_map_rev : forall (xm ym:var) (Ts:typs),
  LibList.map (subst_var xm ym) (List.rev (typs_to_list Ts))
  = List.rev (typs_to_list (subst_typs xm ym Ts)).
Proof.
  intros xm ym Ts. induction Ts as [|T Ts IH]; simpl.
  - rewrite LibList.map_nil. reflexivity.
  - rewrite LibList_map_app, IH. rewrite LibList.map_cons, LibList.map_nil. reflexivity.
Qed.

Lemma subst_env_singles : forall (xm ym:var) (ys:list var) (Ts:typs),
  LibList.length ys = LibList.length (to_list Ts) ->
  subst_env xm ym (ys ~** to_list Ts) = ys ~** to_list (subst_var xm ym Ts).
Proof.
  intros xm ym ys Ts Hlen.
  rewrite (map_singles (subst_var xm ym) (List.rev ys) (List.rev (to_list Ts))).
  - change (singles (List.rev ys) (LibList.map (subst_var xm ym) (List.rev (to_list Ts)))
            = singles (List.rev ys) (List.rev (to_list (subst_var xm ym Ts)))).
    rewrite singles_map_rev.
    change (singles (List.rev ys) (List.rev (typs_to_list (subst_typs xm ym Ts)))
            = singles (List.rev ys) (List.rev (typs_to_list (subst_typs xm ym Ts)))).
    reflexivity.
  - rewrite !LibList_length_List_rev. exact Hlen.
Qed.

Lemma subst_env_single_cons : forall (xm ym:var) (x:var) (ys:list var) (T:typ),
  x <> xm ->
  (forall z, List.In z ys -> z <> xm) ->
  subst_env xm ym (x ~ open_vars (cons x ys) T)
  = x ~ open_vars (cons x ys) (subst_var xm ym T).
Proof.
  intros xm ym x ys T Hx Hys.
  rewrite map_single.
  rewrite subst_open_rec_vars_typ.
  rewrite map_ren_id; [reflexivity|].
  intros z Hz. destruct Hz as [E|E]; [subst z; exact Hx|]. apply Hys. exact E.
Qed.

Lemma concat4 : forall (A:Type) (a b c d:env A), ((a & b) & c) & d = a & b & (c & d).
Proof. intros. repeat rewrite concat_assoc. reflexivity. Qed.

Lemma LibList_length_List_map : forall (A B:Type) (f:A->B) (l:list A),
  LibList.length (List.map f l) = LibList.length l.
Proof.
  intros. induction l as [|a l IH]; simpl.
  - rewrite LibList.length_nil. reflexivity.
  - change (1 + LibList.length (List.map f l) = 1 + LibList.length l).
    rewrite IH. reflexivity.
Qed.

Lemma length_to_list_subst : forall (xm ym:var) (Ts:typs),
  LibList.length (to_list (subst_typs xm ym Ts)) = LibList.length (to_list Ts).
Proof.
  intros. change (LibList.length (typs_to_list (subst_typs xm ym Ts))
                 = LibList.length (typs_to_list Ts)).
  rewrite to_list_subst_typs. apply LibList_length_List_map.
Qed.

Lemma con_setup : forall (L:vars) (G1 G2:ctx) (xm ym:var) (Sm:typ)
  (ys:list var) (Ts:typs) (x:var) (T:typ),
  LibList.length ys = LibList.length (to_list Ts) ->
  fresh (((L \u dom G1) \u dom G2) \u \{xm}) (S (length ys)) (cons x ys) ->
  fresh L (S (length ys)) (cons x ys) /\
  x <> xm /\
  x \notin dom G1 /\
  x \notin dom G2 /\
  x \notin from_list ys /\
  (forall z, List.In z ys -> z <> xm) /\
  (forall z, List.In z ys -> z \notin dom G1 /\ z \notin dom G2) /\
  xm \notin dom (ys ~** to_list Ts) /\
  xm \notin dom (x ~ open_vars (cons x ys) T) /\
  (List.map (fun z => z \[xm -> ym]) (cons x ys) = cons x ys) /\
  subst_env xm ym ((G2 & (ys ~** to_list Ts)) & (x ~ open_vars (cons x ys) T))
  = (subst_env xm ym G2 & (ys ~** to_list (subst_var xm ym Ts)))
    & (x ~ open_vars (cons x ys) (subst_var xm ym T)).
Proof.
  intros L G1 G2 xm ym Sm ys Ts x T Hlen Hf.
  assert (HfL : fresh L (S (length ys)) (cons x ys)) by
    (apply fresh_union_r1 in Hf; apply fresh_union_r1 in Hf;
     apply fresh_union_r1 in Hf; exact Hf).
  assert (HxL' : x \notin (((L \u dom G1) \u dom G2) \u \{xm}))
    by (eapply fresh_cons_head; exact Hf).
  assert (Htail : fresh ((((L \u dom G1) \u dom G2) \u \{xm}) \u \{x}) (length ys) ys)
    by (eapply fresh_cons_tail; exact Hf).
  assert (Hxm : xm \in (((L \u dom G1) \u dom G2) \u \{xm}))
    by (rewrite in_union; right; apply in_singleton_self).
  assert (Hxne : x <> xm) by (intro E; subst x; exact (HxL' Hxm)).
  assert (Hysne : forall z, List.In z ys -> z <> xm).
  { intros z Hz. apply in_from_list in Hz.
    assert (Hc := @fresh_from_list_notin ((((L \u dom G1) \u dom G2) \u \{xm}) \u \{x}) (length ys) ys Htail z Hz).
    apply notin_union_r1 in Hc. intro E; subst z; exact (Hc Hxm). }
  assert (Hxm_ys : xm \notin from_list ys).
  { intro Hxin. assert (Hc := @fresh_from_list_notin ((((L \u dom G1) \u dom G2) \u \{xm}) \u \{x}) (length ys) ys Htail xm Hxin).
    apply notin_union_r1 in Hc. exact (Hc Hxm). }
  assert (HxmYs : xm \notin dom (ys ~** to_list Ts)).
  { rewrite (dom_singles (List.rev ys) (List.rev (to_list Ts))).
    - rewrite from_list_rev. exact Hxm_ys.
    - rewrite !LibList_length_List_rev. exact Hlen. }
  assert (HxmX : xm \notin dom (x ~ open_vars (cons x ys) T)).
  { rewrite dom_single. apply notin_singleton_l. intro E; apply Hxne; symmetry; exact E. }
  assert (HxL : x \notin ((L \u dom G1) \u dom G2))
    by (apply notin_union_r1 in HxL'; exact HxL').
  assert (HxLG1 : x \notin (L \u dom G1)) by (apply notin_union_r1 in HxL; exact HxL).
  assert (HxG1 : x \notin dom G1) by (apply notin_union_r2 in HxLG1; exact HxLG1).
  assert (HxG2 : x \notin dom G2) by (apply notin_union_r2 in HxL; exact HxL).
  assert (Hx_ys : x \notin from_list ys).
  { intro Hxin.
    assert (Hc := @fresh_from_list_notin ((((L \u dom G1) \u dom G2) \u \{xm}) \u \{x}) (length ys) ys Htail x Hxin).
    apply notin_union_r2 in Hc. exact (Hc (in_singleton_self x)). }
  assert (HyG : forall z, List.In z ys -> z \notin dom G1 /\ z \notin dom G2).
  { intros z Hz. apply in_from_list in Hz.
    assert (Hc := @fresh_from_list_notin ((((L \u dom G1) \u dom G2) \u \{xm}) \u \{x}) (length ys) ys Htail z Hz).
    apply notin_union_r1 in Hc. apply notin_union_r1 in Hc.
    assert (HzG2 : z \notin dom G2) by (apply notin_union_r2 in Hc; exact Hc).
    apply notin_union_r1 in Hc.
    assert (HzG1 : z \notin dom G1) by (apply notin_union_r2 in Hc; exact Hc).
    split; [exact HzG1|exact HzG2]. }
  assert (Hmap : List.map (fun z => z \[xm -> ym]) (cons x ys) = cons x ys).
  { simpl. rewrite (@subst_if_neq xm ym x Hxne). rewrite map_ren_id; auto. }
  split; [exact HfL|].
  split; [exact Hxne|].
  split; [exact HxG1|].
  split; [exact HxG2|].
  split; [exact Hx_ys|].
  split; [exact Hysne|].
  split; [exact HyG|].
  split; [exact HxmYs|].
  split; [exact HxmX|].
  split; [exact Hmap|].
  rewrite map_concat, map_concat.
  rewrite subst_env_singles; [|exact Hlen].
  rewrite subst_env_single_cons; auto.
Qed.

(** * Substitution lemma *)

Lemma dom_ys_subst : forall (xm ym:var) (ys:list var) (Ts:typs),
  LibList.length ys = LibList.length (to_list Ts) ->
  dom (ys ~** to_list (subst_var xm ym Ts)) = from_list ys.
Proof.
  intros xm ym ys Ts Hlen.
  rewrite (dom_singles (List.rev ys) (List.rev (to_list (subst_var xm ym Ts)))).
  - rewrite from_list_rev. reflexivity.
  - rewrite !LibList_length_List_rev. rewrite length_to_list_subst. exact Hlen.
Qed.

Definition P_trm (G:ctx) (t:trm) (T:typ) (_: G ⊢ t ∶ T) : Prop :=
  forall G1 G2 (xm ym:var) (Sm:typ),
    G = G1 & xm ~ Sm & G2 ->
    xm # G2 -> xm \notin fv_env G1 ->
    (G1 & subst_env xm ym G2 ⊢ trm_var (avar_f ym) ∶ subst_var xm ym Sm) ->
    G1 & subst_env xm ym G2 ⊢ subst_var xm ym t ∶ subst_var xm ym T.
Arguments P_trm G t T _ : clear implicits.

Definition P_lit (G:ctx) (l:lit) (T:typ) (_: G ⊢ l ∶ T) : Prop :=
  forall G1 G2 (xm ym:var) (Sm:typ),
    G = G1 & xm ~ Sm & G2 ->
    xm # G2 -> xm \notin fv_env G1 ->
    (G1 & subst_env xm ym G2 ⊢ trm_var (avar_f ym) ∶ subst_var xm ym Sm) ->
    G1 & subst_env xm ym G2 ⊢ subst_var xm ym l ∶ subst_var xm ym T.
Arguments P_lit G l T _ : clear implicits.

Definition P_sub (G:ctx) (T U:typ) (_: G ⊢ T <: U) : Prop :=
  forall G1 G2 (xm ym:var) (Sm:typ),
    G = G1 & xm ~ Sm & G2 ->
    xm # G2 -> xm \notin fv_env G1 ->
    (G1 & subst_env xm ym G2 ⊢ trm_var (avar_f ym) ∶ subst_var xm ym Sm) ->
    G1 & subst_env xm ym G2 ⊢ subst_var xm ym T <: subst_var xm ym U.
Arguments P_sub G T U _ : clear implicits.

Definition P_avars (G:ctx) (avs:avars) (Ts:typs) (_: G ⊢ avs :: Ts) : Prop :=
  forall G1 G2 (xm ym:var) (Sm:typ),
    G = G1 & xm ~ Sm & G2 ->
    xm # G2 -> xm \notin fv_env G1 ->
    (G1 & subst_env xm ym G2 ⊢ trm_var (avar_f ym) ∶ subst_var xm ym Sm) ->
    G1 & subst_env xm ym G2 ⊢ subst_var xm ym avs :: subst_var xm ym Ts.
Arguments P_avars G avs Ts _ : clear implicits.

Section SubstTyping.

Lemma typing_subst_mut :
  (forall (G:ctx) (t:trm) (T:typ) (H:G ⊢ t ∶ T), P_trm G t T H) /\
  (forall (G:ctx) (l:lit) (T:typ) (H:G ⊢ l ∶ T), P_lit G l T H) /\
  (forall (G:ctx) (T U:typ) (H:G ⊢ T <: U), P_sub G T U H) /\
  (forall (G:ctx) (avs:avars) (Ts:typs) (H:G ⊢ avs :: Ts), P_avars G avs Ts H).
Proof.
  apply (rules_mutind P_trm P_lit P_sub P_avars);
  intros; unfold P_trm, P_lit, P_sub, P_avars in *;
  intros G1 G2 xm ym Sm Heq Hx Hfv Hpre; subst.
  - (* ty_var *)
    destruct (binds_concat_inv b) as [HG2 | [Hz2 HG12]].
    + assert (Hne : x <> xm) by (intro E; subst x; exact (binds_fresh_inv HG2 Hx)).
      change (G1 & subst_env xm ym G2 ⊢ trm_var (avar_f (x \[xm -> ym])) ∶ subst_var xm ym T).
      rewrite (@subst_if_neq xm ym x Hne).
      eapply ty_var. eapply binds_concat_right. eapply binds_map. exact HG2.
    + destruct (binds_concat_inv HG12) as [HxS | [HzS HG1]].
      * apply binds_single_inv in HxS. destruct HxS as [E1 E2]. subst x. subst T.
        change (G1 & subst_env xm ym G2 ⊢ trm_var (avar_f (xm \[xm -> ym])) ∶ subst_var xm ym Sm).
        rewrite (@subst_if_eq xm ym). exact Hpre.
      * assert (Hne : x <> xm) by (rewrite dom_single in HzS; apply notin_singleton_r in HzS; exact HzS).
        assert (Hxv : xm \notin fv T) by (eapply fv_in_values_binds; eauto).
        change (G1 & subst_env xm ym G2 ⊢ trm_var (avar_f (x \[xm -> ym])) ∶ subst_var xm ym T).
        rewrite (@subst_if_neq xm ym x Hne).
        rewrite (@fv_subst_typ T xm ym Hxv).
        eapply ty_var. eapply binds_concat_left.
        -- exact HG1.
        -- rewrite dom_subst_env. exact Hz2.
  - (* ty_all_elim *)
    simpl.
    assert (Hrw : subst_var xm ym (open_rec 0 z T) = open_rec 0 (z \[xm -> ym]) (subst_var xm ym T))
      by (apply (proj1 subst_open_rec_mut)).
    rewrite Hrw.
    eapply ty_all_elim.
    + eapply H; eauto.
    + eapply H0; eauto.
  - (* ty_new *)
    simpl.
    assert (Hv : subst_typ xm ym (open_rec_vars 1 xs T) =
                 open_rec_vars 1 (List.map (fun z => z \[xm -> ym]) xs) (subst_typ xm ym T))
      by (apply subst_open_rec_vars_typ).
    rewrite Hv.
    eapply ty_new.
    + eapply H; eauto.
    + eapply H0; eauto.
    + apply vars_of_avars_subst. exact v.
  - (* ty_rcd_elim *)
    simpl.
    eapply ty_rcd_elim. eapply H; eauto.
  - (* ty_fld_asn *)
    simpl.
    eapply ty_fld_asn.
    + eapply H; eauto.
    + eapply H0; eauto.
  - (* ty_let *)
    simpl.
    eapply ty_let with (L := ((L \u dom G1) \u dom G2) \u \{xm}).
    + eapply H; eauto.
    + intros z Hz.
      destruct (notin_binder_setup Hz) as [HzL [HzG1 [HzG2 Hzx]]].
      assert (Heq' : ((G1 & xm ~ Sm & G2) & z ~ T) = G1 & xm ~ Sm & (G2 & z ~ T)).
      { symmetry. apply concat_assoc. }
      assert (Hru : subst_trm xm ym (open_rec 0 z u) = open_rec 0 z (subst_trm xm ym u))
        by (apply subst_open_fresh_trm; auto).
      rewrite <- Hru.
      rewrite <- concat_assoc.
      rewrite <- map_push.
      eapply (H0 z HzL G1 (G2 & z ~ T) xm ym Sm).
      * exact Heq'.
      * rewrite dom_push. apply notin_union_l.
        -- apply notin_singleton_l. intro E; apply Hzx; symmetry; exact E.
        -- exact Hx.
      * exact Hfv.
      * rewrite map_push. rewrite concat_assoc.
        eapply ty_trm_binds_extends; [exact Hpre|].
        apply binds_extends_push_fresh.
        rewrite dom_concat. apply notin_union_l; [exact HzG1|].
        rewrite dom_subst_env. exact HzG2.
  - (* ty_llit *)
    simpl.
    eapply ty_llit with (L := ((L \u dom G1) \u dom G2) \u \{xm}).
    + eapply H; eauto.
    + intros z Hz.
      destruct (notin_binder_setup Hz) as [HzL [HzG1 [HzG2 Hzx]]].
      assert (Heq' : ((G1 & xm ~ Sm & G2) & z ~ T) = G1 & xm ~ Sm & (G2 & z ~ T)).
      { symmetry. apply concat_assoc. }
      assert (Hru : subst_trm xm ym (open_rec 0 z u) = open_rec 0 z (subst_trm xm ym u))
        by (apply subst_open_fresh_trm; auto).
      rewrite <- Hru.
      rewrite <- concat_assoc.
      rewrite <- map_push.
      eapply (H0 z HzL G1 (G2 & z ~ T) xm ym Sm).
      * exact Heq'.
      * rewrite dom_push. apply notin_union_l.
        -- apply notin_singleton_l. intro E; apply Hzx; symmetry; exact E.
        -- exact Hx.
      * exact Hfv.
      * rewrite map_push. rewrite concat_assoc.
        eapply ty_trm_binds_extends; [exact Hpre|].
        apply binds_extends_push_fresh.
        rewrite dom_concat. apply notin_union_l; [exact HzG1|].
        rewrite dom_subst_env. exact HzG2.
  - (* ty_rec_intro *)
    change (G1 & subst_env xm ym G2 ⊢ trm_var (avar_f (x \[xm -> ym])) ∶ typ_bnd (subst_typ xm ym T)).
    eapply ty_rec_intro.
    assert (Hrw : subst_typ xm ym (open_rec 0 x T) = open_rec 0 (x \[xm -> ym]) (subst_typ xm ym T))
      by (apply (proj1 subst_open_rec_mut)).
    rewrite <- Hrw.
    eapply H; eauto.
  - (* ty_rec_elim *)
    change (G1 & subst_env xm ym G2 ⊢ trm_var (avar_f (x \[xm -> ym]))
              ∶ subst_typ xm ym (open_rec 0 x T)).
    assert (Hrw : subst_typ xm ym (open_rec 0 x T) =
                  open_rec 0 (x \[xm -> ym]) (subst_typ xm ym T))
      by (apply (proj1 subst_open_rec_mut)).
    rewrite Hrw.
    eapply ty_rec_elim.
    eapply H; eauto.
  - (* ty_and_intro *)
    simpl.
    eapply ty_and_intro.
    + eapply H; eauto.
    + eapply H0; eauto.
  - (* ty_sub *)
    simpl.
    eapply ty_sub.
    + eapply H; eauto.
    + eapply H0; eauto.
  - (* ty_all_intro *)
    simpl.
    eapply ty_all_intro with (L := ((L \u dom G1) \u dom G2) \u \{xm}).
    intros z Hz.
    destruct (notin_binder_setup Hz) as [HzL [HzG1 [HzG2 Hzx]]].
    assert (Heq' : ((G1 & xm ~ Sm & G2) & z ~ T) = G1 & xm ~ Sm & (G2 & z ~ T)).
    { symmetry. apply concat_assoc. }
    assert (Hru_t : subst_trm xm ym (open_rec 0 z t) = open_rec 0 z (subst_trm xm ym t))
      by (apply subst_open_fresh_trm; auto).
    assert (Hru_T : subst_typ xm ym (open_rec 0 z U) = open_rec 0 z (subst_typ xm ym U))
      by (apply subst_open_fresh_typ; auto).
    rewrite <- Hru_t. rewrite <- Hru_T.
    rewrite <- concat_assoc.
    rewrite <- map_push.
    eapply (H z HzL G1 (G2 & z ~ T) xm ym Sm).
    + exact Heq'.
    + rewrite dom_push. apply notin_union_l.
      * apply notin_singleton_l. intro E; apply Hzx; symmetry; exact E.
      * exact Hx.
    + exact Hfv.
    + rewrite map_push. rewrite concat_assoc.
      eapply ty_trm_binds_extends; [exact Hpre|].
      apply binds_extends_push_fresh.
      rewrite dom_concat. apply notin_union_l; [exact HzG1|].
      rewrite dom_subst_env. exact HzG2.
  - (* ty_con_intro *)
    simpl.
    eapply ty_con_intro with (L := ((L \u dom G1) \u dom G2) \u \{xm}).
    + intros x ys Hlen' Hf.
      rewrite length_s_subst_typs in Hlen'.
      assert (HlenL : LibList.length ys = LibList.length (to_list Ts)).
      { unfold length_s in Hlen'.
        change (List.length ys = List.length (to_list Ts)) in Hlen'.
        rewrite !List_length_LibList_length in Hlen'. exact Hlen'. }
      destruct (@con_setup L G1 G2 xm ym Sm ys Ts x T HlenL Hf) as
        [HfL [Hxne [HxG1 [HxG2 [Hx_ys [Hysne [HyG [HxmYs [HxmX [Hmap HenvEq]]]]]]]]]].
      assert (HTrw : subst_typ xm ym (open_rec_vars 0 (cons x ys) T)
                     = open_rec_vars 0 (cons x ys) (subst_typ xm ym T)).
      { rewrite subst_open_rec_vars_typ. rewrite Hmap. reflexivity. }
      assert (Hdsrw : subst_var xm ym (open_rec_vars 0 (cons x ys) ds)
                      = open_rec_vars 0 (cons x ys) (subst_var xm ym ds)).
      { rewrite subst_open_rec_vars_defs. rewrite Hmap. reflexivity. }
      assert (HenvEq' : (((G1 & subst_env xm ym G2) & (ys ~** to_list (subst_typs xm ym Ts)))
                          & (x ~ open_vars (cons x ys) (subst_typ xm ym T)))
                         = G1 & subst_env xm ym ((G2 & (ys ~** to_list Ts)) & (x ~ open_vars (cons x ys) T))).
      { rewrite HenvEq. repeat rewrite concat_assoc. reflexivity. }
      assert (HxmEnv : xm \notin dom ((G2 & (ys ~** to_list Ts)) & (x ~ open_vars (cons x ys) T))).
      { rewrite dom_concat. apply notin_union_l.
        - rewrite dom_concat. apply notin_union_l; [exact Hx|exact HxmYs].
        - exact HxmX. }
      assert (Hpre' : G1 & subst_env xm ym ((G2 & (ys ~** to_list Ts)) & (x ~ open_vars (cons x ys) T))
                      ⊢ trm_var (avar_f ym) ∶ subst_var xm ym Sm).
      { rewrite HenvEq. rewrite <- concat_assoc. rewrite concat_assoc.
        eapply ty_trm_binds_extends; [exact Hpre|].
        eapply binds_extends_push_env_fresh. intros y Hy.
        rewrite dom_concat in Hy. rewrite in_union in Hy. destruct Hy as [Hy|Hy].
        - assert (Hyin : List.In y ys).
          { apply (proj1 (@in_from_list var y ys)).
            rewrite <- (dom_ys_subst xm ym ys Ts HlenL). exact Hy. }
          destruct (HyG y Hyin) as [H1 H2].
          rewrite dom_concat, dom_subst_env. apply notin_union_l; assumption.
        - rewrite dom_single in Hy. rewrite in_singleton in Hy. subst y.
          rewrite dom_concat, dom_subst_env. apply notin_union_l; assumption. }
      rewrite HenvEq'. rewrite <- Hdsrw. rewrite <- HTrw.
      eapply ty_defs_subst with (G1:=G1)
        (G2 := (G2 & (ys ~** to_list Ts)) & (x ~ open_vars (cons x ys) T))
        (x:=xm) (y:=ym) (S:=Sm).
      * repeat rewrite concat_assoc. apply t0; eauto.
      * exact HxmEnv.
      * exact Hfv.
      * exact Hpre'.
    + intros x ys Hlen' Hf.
      rewrite length_s_subst_typs in Hlen'.
      assert (HlenL : LibList.length ys = LibList.length (to_list Ts)).
      { unfold length_s in Hlen'.
        change (List.length ys = List.length (to_list Ts)) in Hlen'.
        rewrite !List_length_LibList_length in Hlen'. exact Hlen'. }
      destruct (@con_setup L G1 G2 xm ym Sm ys Ts x T HlenL Hf) as
        [HfL [Hxne [HxG1 [HxG2 [Hx_ys [Hysne [HyG [HxmYs [HxmX [Hmap HenvEq]]]]]]]]]].
      assert (Htrw : subst_trm xm ym (open_rec_vars 0 (cons x ys) t)
                     = open_rec_vars 0 (cons x ys) (subst_trm xm ym t)).
      { rewrite subst_open_rec_vars_trm. rewrite Hmap. reflexivity. }
      assert (HTrw2 : subst_typ xm ym (open_rec_vars 0 (cons x ys) T')
                      = open_rec_vars 0 (cons x ys) (subst_typ xm ym T')).
      { rewrite subst_open_rec_vars_typ. rewrite Hmap. reflexivity. }
      assert (HenvEq' : (((G1 & subst_env xm ym G2) & (ys ~** to_list (subst_typs xm ym Ts)))
                          & (x ~ open_vars (cons x ys) (subst_typ xm ym T)))
                         = G1 & subst_env xm ym ((G2 & (ys ~** to_list Ts)) & (x ~ open_vars (cons x ys) T))).
      { rewrite HenvEq. repeat rewrite concat_assoc. reflexivity. }
      assert (HxmEnv : xm \notin dom ((G2 & (ys ~** to_list Ts)) & (x ~ open_vars (cons x ys) T))).
      { rewrite dom_concat. apply notin_union_l.
        - rewrite dom_concat. apply notin_union_l; [exact Hx|exact HxmYs].
        - exact HxmX. }
      assert (Hpre' : G1 & subst_env xm ym ((G2 & (ys ~** to_list Ts)) & (x ~ open_vars (cons x ys) T))
                      ⊢ trm_var (avar_f ym) ∶ subst_var xm ym Sm).
      { rewrite HenvEq. rewrite <- concat_assoc. rewrite concat_assoc.
        eapply ty_trm_binds_extends; [exact Hpre|].
        eapply binds_extends_push_env_fresh. intros y Hy.
        rewrite dom_concat in Hy. rewrite in_union in Hy. destruct Hy as [Hy|Hy].
        - assert (Hyin : List.In y ys).
          { apply (proj1 (@in_from_list var y ys)).
            rewrite <- (dom_ys_subst xm ym ys Ts HlenL). exact Hy. }
          destruct (HyG y Hyin) as [H1 H2].
          rewrite dom_concat, dom_subst_env. apply notin_union_l; assumption.
        - rewrite dom_single in Hy. rewrite in_singleton in Hy. subst y.
          rewrite dom_concat, dom_subst_env. apply notin_union_l; assumption. }
      rewrite HenvEq'. rewrite <- Htrw. rewrite <- HTrw2.
      eapply (H x ys Hlen' HfL G1 ((G2 & (ys ~** to_list Ts)) & (x ~ open_vars (cons x ys) T)) xm ym Sm).
      * repeat rewrite concat_assoc. reflexivity.
      * exact HxmEnv.
      * exact Hfv.
      * exact Hpre'.
  - (* subtyp_top *) eapply subtyp_top.
  - (* subtyp_bot *) eapply subtyp_bot.
  - (* subtyp_refl *) eapply subtyp_refl.
  - (* subtyp_trans *)
    simpl.
    eapply subtyp_trans.
    + eapply H; eauto.
    + eapply H0; eauto.
  - (* and11 *) eapply subtyp_and11.
  - (* and12 *) eapply subtyp_and12.
  - (* and2 *) eapply subtyp_and2; [eapply H; eauto|eapply H0; eauto].
  - (* fld *)
    simpl.
    eapply subtyp_fld.
    + eapply H; eauto.
    + eapply H0; eauto.
  - (* typ *)
    simpl.
    eapply subtyp_typ.
    + eapply H; eauto.
    + eapply H0; eauto.
  - (* sel2 *) eapply subtyp_sel2. eapply H; eauto.
  - (* sel1 *) eapply subtyp_sel1. eapply H; eauto.
  - (* subtyp_all *)
    simpl.
    eapply subtyp_all with (L := ((L \u dom G1) \u dom G2) \u \{xm}).
    + eapply H; eauto.
    + intros z Hz.
      destruct (notin_binder_setup Hz) as [HzL [HzG1 [HzG2 Hzx]]].
      assert (Heq' : ((G1 & xm ~ Sm & G2) & z ~ S2) = G1 & xm ~ Sm & (G2 & z ~ S2)).
      { symmetry. apply concat_assoc. }
      assert (Hru1 : subst_typ xm ym (open_rec 0 z T1) = open_rec 0 z (subst_typ xm ym T1))
        by (apply subst_open_fresh_typ; auto).
      assert (Hru2 : subst_typ xm ym (open_rec 0 z T2) = open_rec 0 z (subst_typ xm ym T2))
        by (apply subst_open_fresh_typ; auto).
      rewrite <- Hru1. rewrite <- Hru2.
      rewrite <- concat_assoc.
      rewrite <- map_push.
      eapply (H0 z HzL G1 (G2 & z ~ S2) xm ym Sm).
      * exact Heq'.
      * rewrite dom_push. apply notin_union_l.
        -- apply notin_singleton_l. intro E; apply Hzx; symmetry; exact E.
        -- exact Hx.
      * exact Hfv.
      * rewrite map_push. rewrite concat_assoc.
        eapply ty_trm_binds_extends; [exact Hpre|].
        apply binds_extends_push_fresh.
        rewrite dom_concat. apply notin_union_l; [exact HzG1|].
        rewrite dom_subst_env. exact HzG2.
  - (* avars nil *) eapply typ_avars_nil.
  - (* avars cons *)
    simpl.
    eapply typ_avars_cons.
    + eapply H; eauto.
    + eapply H0; eauto.
Qed.

Corollary ty_trm_subst : forall (G1 G2:ctx) (xm ym:var) (Sm:typ) (t:trm) (T:typ),
  G1 & xm ~ Sm & G2 ⊢ t ∶ T ->
  xm # G2 ->
  xm \notin fv_env G1 ->
  (G1 & subst_env xm ym G2 ⊢ trm_var (avar_f ym) ∶ subst_var xm ym Sm) ->
  G1 & subst_env xm ym G2 ⊢ subst_var xm ym t ∶ subst_var xm ym T.
Proof. intros. eapply (proj1 typing_subst_mut); eauto. Qed.

Corollary ty_lit_subst : forall (G1 G2:ctx) (xm ym:var) (Sm:typ) (l:lit) (T:typ),
  G1 & xm ~ Sm & G2 ⊢ l ∶ T ->
  xm # G2 ->
  xm \notin fv_env G1 ->
  (G1 & subst_env xm ym G2 ⊢ trm_var (avar_f ym) ∶ subst_var xm ym Sm) ->
  G1 & subst_env xm ym G2 ⊢ subst_var xm ym l ∶ subst_var xm ym T.
Proof. intros. eapply (proj1 (proj2 typing_subst_mut)); eauto. Qed.

Corollary subtyp_subst : forall (G1 G2:ctx) (xm ym:var) (Sm:typ) (T U:typ),
  G1 & xm ~ Sm & G2 ⊢ T <: U ->
  xm # G2 ->
  xm \notin fv_env G1 ->
  (G1 & subst_env xm ym G2 ⊢ trm_var (avar_f ym) ∶ subst_var xm ym Sm) ->
  G1 & subst_env xm ym G2 ⊢ subst_var xm ym T <: subst_var xm ym U.
Proof. intros. eapply (proj1 (proj2 (proj2 typing_subst_mut))); eauto. Qed.

Corollary ty_avars_subst : forall (G1 G2:ctx) (xm ym:var) (Sm:typ) (avs:avars) (Ts:typs),
  G1 & xm ~ Sm & G2 ⊢ avs :: Ts ->
  xm # G2 ->
  xm \notin fv_env G1 ->
  (G1 & subst_env xm ym G2 ⊢ trm_var (avar_f ym) ∶ subst_var xm ym Sm) ->
  G1 & subst_env xm ym G2 ⊢ subst_var xm ym avs :: subst_var xm ym Ts.
Proof. intros. eapply (proj2 (proj2 (proj2 typing_subst_mut))); eauto. Qed.

End SubstTyping.

Definition vs_subset (vs vs' : vars) : Prop :=
  forall x, x \in vs -> x \in vs'.

Lemma vs_subset_remove : forall (vs vs':vars) (x:var),
  vs_subset vs vs' -> vs_subset (vs \u \{x}) (vs' \u \{x}).
Proof.
  intros vs vs' x H y Hy. rewrite in_union in Hy. rewrite in_union.
  destruct Hy as [Hy|Hy]; [left; apply H; exact Hy|right; exact Hy].
Qed.

Lemma init_var_transfer : forall (Delta Delta':init_ctx) (vs vs':vars) (x:var) (i:init_typ),
  binds_extends Delta Delta' -> vs_subset vs vs' ->
  init_var Delta vs x i -> init_var Delta' vs' x i.
Proof.
  intros Delta Delta' vs vs' x i He Hvs H. induction H.
  - apply init_var_commit. apply He. exact H.
  - apply init_var_free; auto.
  - apply init_var_unspec; auto.
  - apply init_var_sub with (i':=i'); auto.
Qed.

Section InitCommitTransfer.

Lemma hc_commit_var : forall (G:ctx) (D:init_ctx) (x:var),
  binds x committed D ->
  forall G' D' vs vs', binds_extends G G' -> binds_extends D D' ->
    vs_subset vs vs' -> G' ⸴ D' ⊢c trm_var (avar_f x).
Proof. intros. apply commit_var. apply H1. exact H. Qed.

Lemma hc_commit_all_elim : forall (G:ctx) (D:init_ctx) (x z:var),
  (forall G' D' vs vs', binds_extends G G' -> binds_extends D D' ->
     vs_subset vs vs' -> G' ⸴ D' ⊢c trm_var (avar_f x)) ->
  (forall G' D' vs vs', binds_extends G G' -> binds_extends D D' ->
     vs_subset vs vs' -> G' ⸴ D' ⊢c trm_var (avar_f z)) ->
  forall G' D' vs vs', binds_extends G G' -> binds_extends D D' ->
    vs_subset vs vs' -> G' ⸴ D' ⊢c trm_app (avar_f x) (avar_f z).
Proof. intros. apply commit_all_elim; eauto. Qed.

Lemma hc_commit_new : forall (G:ctx) (D:init_ctx) (x:var) (avs:avars) (Ts:typs) (is':inits) (T:typ),
  (forall G' D' vs vs', binds_extends G G' -> binds_extends D D' ->
     vs_subset vs vs' -> G' ⸴ D' ⊢c trm_var (avar_f x)) ->
  (G ⊢ trm_var (avar_f x) ∶ typ_con Ts is' T) ->
  all_comm_unspec is' ->
  (forall G' D' vs vs', binds_extends G G' -> binds_extends D D' ->
     vs_subset vs vs' -> G' ⸴ D' ⊢c avs) ->
  forall G' D' vs vs', binds_extends G G' -> binds_extends D D' ->
    vs_subset vs vs' -> G' ⸴ D' ⊢c trm_new (avar_f x) avs.
Proof.
  intros. eapply commit_new.
  - eapply H; eauto.
  - eapply ty_trm_binds_extends; [exact H0|exact H3].
  - eauto.
  - eapply H2; eauto.
Qed.

Lemma hc_commit_rcd_elim : forall (G:ctx) (D:init_ctx) (x:var) (a:trm_label),
  (forall G' D' vs vs', binds_extends G G' -> binds_extends D D' ->
     vs_subset vs vs' -> G' ⸴ D' ⊢c trm_var (avar_f x)) ->
  forall G' D' vs vs', binds_extends G G' -> binds_extends D D' ->
    vs_subset vs vs' -> G' ⸴ D' ⊢c trm_sel (avar_f x) a.
Proof. intros. apply commit_rcd_elim. eapply H; eauto. Qed.

Lemma hc_commit_fld_asn : forall (G:ctx) (D:init_ctx) (x y:var) (a:trm_label),
  (forall G' D' vs vs', binds_extends G G' -> binds_extends D D' ->
     vs_subset vs vs' -> G' ⸴ D' ⊢c trm_var (avar_f x)) ->
  (forall G' D' vs vs', binds_extends G G' -> binds_extends D D' ->
     vs_subset vs vs' -> G' ⸴ D' ⊢c trm_var (avar_f y)) ->
  forall G' D' vs vs', binds_extends G G' -> binds_extends D D' ->
    vs_subset vs vs' -> G' ⸴ D' ⊢c trm_asn (avar_f x) a (avar_f y).
Proof.
  intros. eapply (@commit_fld_asn _ _ _ unspecified _ _).
  - eapply H; eauto.
  - eapply H0; eauto.
Qed.

Lemma hc_commit_let : forall (L:fset var) (G:ctx) (D:init_ctx) (t u:trm) (T:typ),
  (forall G' D' vs vs', binds_extends G G' -> binds_extends D D' ->
     vs_subset vs vs' -> G' ⸴ D' ⊢c t) ->
  (forall x, x \notin L -> forall G' D' vs vs',
     binds_extends (G & x ~ T) G' -> binds_extends (D & x ~ committed) D' ->
     vs_subset vs vs' -> G' ⸴ D' ⊢c open x u) ->
  forall G' D' vs vs', binds_extends G G' -> binds_extends D D' ->
    vs_subset vs vs' -> G' ⸴ D' ⊢c trm_let T t u.
Proof.
  intros. eapply (@commit_let L _ _ _ _ _).
  - eapply H; eauto.
  - intros x Hx. eapply H0; eauto using binds_extends_push.
Qed.

Lemma hc_commit_llit : forall (L:fset var) (G:ctx) (D:init_ctx) (l:lit) (u:trm) (T:typ),
  (forall G' D' vs vs', binds_extends G G' -> binds_extends D D' ->
     vs_subset vs vs' -> G' ⸴ D' ⊢c l) ->
  (forall x, x \notin L -> forall G' D' vs vs',
     binds_extends (G & x ~ T) G' -> binds_extends (D & x ~ committed) D' ->
     vs_subset vs vs' -> G' ⸴ D' ⊢c open x u) ->
  forall G' D' vs vs', binds_extends G G' -> binds_extends D D' ->
    vs_subset vs vs' -> G' ⸴ D' ⊢c trm_lit T l u.
Proof.
  intros. eapply (@commit_llit L _ _ _ _ _).
  - eapply H; eauto.
  - intros x Hx. eapply H0; eauto using binds_extends_push.
Qed.

Lemma hc_commit_all_intro : forall (L:fset var) (G:ctx) (D:init_ctx) (T:typ) (t:trm),
  (forall x, x \notin L -> forall G' D' vs vs',
     binds_extends (G & x ~ T) G' -> binds_extends (D & x ~ committed) D' ->
     vs_subset vs vs' -> G' ⸴ D' ⊢c open x t) ->
  forall G' D' vs vs', binds_extends G G' -> binds_extends D D' ->
    vs_subset vs vs' -> G' ⸴ D' ⊢c lit_fun T t.
Proof.
  intros. eapply (@commit_all_intro L _ _ _ _). intros x Hx. eapply H; eauto using binds_extends_push.
Qed.

Lemma hc_commit_con_intro : forall (L:fset var) (G:ctx) (D:init_ctx) (Ts:typs) (is':inits)
  (T:typ) (i:init_typ) (ds:defs) (t:trm),
  length is' = length_s Ts ->
  (forall x ys, length ys = length_s Ts ->
     fresh L (S (length ys)) (cons x ys) ->
     has_effs (open_vars (cons x ys) t) (def_eff x ds)) ->
  (forall x ys, length ys = length_s Ts ->
     fresh L (S (length ys)) (cons x ys) ->
     forall G' D' vs',
       binds_extends (G & (ys ~** (to_list Ts)) & (x ~ open_vars (cons x ys) T)) G' ->
       binds_extends (D & (ys ~** is') & (x ~ free)) D' ->
       vs_subset ((from_list ys \u \{x})) vs' ->
       G' ⸴ D' ⸴ vs' ⊢i (open_vars (cons x ys) t) ∶ i) ->
  forall G' D' vs vs', binds_extends G G' -> binds_extends D D' ->
    vs_subset vs vs' -> G' ⸴ D' ⊢c lit_con Ts is' T ds t.
Proof.
  intros. eapply (@commit_con_intro L _ _ _ _ _ _ _ _).
  - exact H.
  - exact H0.
  - intros x ys Hlen Hfresh. eapply (H1 x ys Hlen Hfresh).
    + eapply binds_extends_push. eapply binds_extends_push_env. exact H2.
    + eapply binds_extends_push. eapply binds_extends_push_env. exact H3.
    + intros y Hy. exact Hy.
Qed.

Lemma hc_commit_avars_nil : forall (G:ctx) (D:init_ctx),
  forall G' D' vs vs', binds_extends G G' -> binds_extends D D' ->
    vs_subset vs vs' -> G' ⸴ D' ⊢c (nil:avars).
Proof. intros. apply committed_nil. Qed.

Lemma hc_commit_avars_cons : forall (G:ctx) (D:init_ctx) (x:var) (avs:avars),
  (forall G' D' vs vs', binds_extends G G' -> binds_extends D D' ->
     vs_subset vs vs' -> G' ⸴ D' ⊢c trm_var (avar_f x)) ->
  (forall G' D' vs vs', binds_extends G G' -> binds_extends D D' ->
     vs_subset vs vs' -> G' ⸴ D' ⊢c avs) ->
  forall G' D' vs vs', binds_extends G G' -> binds_extends D D' ->
    vs_subset vs vs' -> G' ⸴ D' ⊢c (cons (avar_f x) avs).
Proof.
  intros. eapply committed_cons.
  - eapply H; eauto.
  - eapply H0; eauto.
Qed.

Lemma hc_init_var_binds : forall (G:ctx) (D:init_ctx) (vs:vars) (x:var) (i:init_typ),
  init_var D vs x i ->
  forall G' D' vs', binds_extends G G' -> binds_extends D D' ->
    vs_subset vs vs' -> G' ⸴ D' ⸴ vs' ⊢i trm_var (avar_f x) ∶ i.
Proof. intros. apply init_var_binds. eapply init_var_transfer; eauto. Qed.

Lemma hc_init_commit : forall (G:ctx) (D:init_ctx) (vs:vars) (t:trm),
  (forall G' D' vs vs', binds_extends G G' -> binds_extends D D' ->
     vs_subset vs vs' -> G' ⸴ D' ⊢c t) ->
  forall G' D' vs', binds_extends G G' -> binds_extends D D' ->
    vs_subset vs vs' -> G' ⸴ D' ⸴ vs' ⊢i t ∶ committed.
Proof. intros. apply init_commit. eapply H; eauto. Qed.

Lemma hc_init_new_free : forall (G:ctx) (D:init_ctx) (vs:vars) (x:var) (avs:avars) (Ts:typs) (is':inits) (T:typ),
  (forall G' D' vs vs', binds_extends G G' -> binds_extends D D' ->
     vs_subset vs vs' -> G' ⸴ D' ⊢c trm_var (avar_f x)) ->
  (G ⊢ trm_var (avar_f x) ∶ typ_con Ts is' T) ->
  (forall G' D' vs', binds_extends G G' -> binds_extends D D' ->
     vs_subset vs vs' -> G' ⸴ D' ⸴ vs' ⊢i avs :: is') ->
  forall G' D' vs', binds_extends G G' -> binds_extends D D' ->
    vs_subset vs vs' -> G' ⸴ D' ⸴ vs' ⊢i trm_new (avar_f x) avs ∶ free.
Proof.
  intros. eapply init_new_free.
  - eapply H; eauto.
  - eapply ty_trm_binds_extends; [exact H0|exact H2].
  - eapply H1; eauto.
Qed.

Lemma hc_init_fld_asn_ac : forall (G:ctx) (D:init_ctx) (vs:vars) (x:var) (i:init_typ) (y:var) (a:trm_label),
  (forall G' D' vs', binds_extends G G' -> binds_extends D D' ->
     vs_subset vs vs' -> G' ⸴ D' ⸴ vs' ⊢i trm_var (avar_f x) ∶ i) ->
  (forall G' D' vs', binds_extends G G' -> binds_extends D D' ->
     vs_subset vs vs' -> G' ⸴ D' ⸴ vs' ⊢i trm_var (avar_f y) ∶ committed) ->
  forall G' D' vs', binds_extends G G' -> binds_extends D D' ->
    vs_subset vs vs' -> G' ⸴ D' ⸴ vs' ⊢i trm_asn (avar_f x) a (avar_f y) ∶ committed.
Proof.
  intros. eapply init_fld_asn_ac.
  - eapply H; eauto.
  - eapply H0; eauto.
Qed.

Lemma hc_init_fld_asn_ff : forall (G:ctx) (D:init_ctx) (vs:vars) (x:var) (y:var) (a:trm_label),
  (forall G' D' vs', binds_extends G G' -> binds_extends D D' ->
     vs_subset vs vs' -> G' ⸴ D' ⸴ vs' ⊢i trm_var (avar_f x) ∶ free) ->
  (forall G' D' vs', binds_extends G G' -> binds_extends D D' ->
     vs_subset vs vs' -> G' ⸴ D' ⸴ vs' ⊢i trm_var (avar_f y) ∶ free) ->
  forall G' D' vs', binds_extends G G' -> binds_extends D D' ->
    vs_subset vs vs' -> G' ⸴ D' ⸴ vs' ⊢i trm_asn (avar_f x) a (avar_f y) ∶ free.
Proof.
  intros. eapply init_fld_asn_ff.
  - eapply H; eauto.
  - eapply H0; eauto.
Qed.

Lemma hc_init_let : forall (L:fset var) (G:ctx) (D:init_ctx) (vs:vars) (t u:trm) (T:typ) (i i':init_typ),
  (forall G' D' vs', binds_extends G G' -> binds_extends D D' ->
     vs_subset vs vs' -> G' ⸴ D' ⸴ vs' ⊢i t ∶ i) ->
  (forall x, x \notin L -> forall G' D' vs',
     binds_extends (G & x ~ T) G' -> binds_extends (D & x ~ i) D' ->
     vs_subset (vs \u \{x}) vs' -> G' ⸴ D' ⸴ vs' ⊢i open x u ∶ i') ->
  forall G' D' vs', binds_extends G G' -> binds_extends D D' ->
    vs_subset vs vs' -> G' ⸴ D' ⸴ vs' ⊢i trm_let T t u ∶ i'.
Proof.
  intros. eapply (@init_let L _ _ _ _ _ _ _ _).
  - eapply H; eauto.
  - intros x Hx. eapply H0; eauto using binds_extends_push, vs_subset_remove.
Qed.

Lemma hc_init_llit : forall (L:fset var) (G:ctx) (D:init_ctx) (vs:vars) (l:lit) (u:trm) (T:typ) (i:init_typ),
  (forall G' D' vs', binds_extends G G' -> binds_extends D D' ->
     vs_subset vs vs' -> G' ⸴ D' ⊢c l) ->
  (forall x, x \notin L -> forall G' D' vs',
     binds_extends (G & x ~ T) G' -> binds_extends (D & x ~ committed) D' ->
     vs_subset vs vs' -> G' ⸴ D' ⸴ vs' ⊢i open x u ∶ i) ->
  forall G' D' vs', binds_extends G G' -> binds_extends D D' ->
    vs_subset vs vs' -> G' ⸴ D' ⸴ vs' ⊢i trm_lit T l u ∶ i.
Proof.
  intros. eapply (@init_llit L _ _ _ _ _ _ _).
  - eapply H; eauto.
  - intros x Hx. eapply H0; eauto using binds_extends_push.
Qed.

Lemma hc_inits_nil : forall (G:ctx) (D:init_ctx) (vs:vars),
  forall G' D' vs', binds_extends G G' -> binds_extends D D' ->
    vs_subset vs vs' -> G' ⸴ D' ⸴ vs' ⊢i (nil:avars) :: nil.
Proof. intros. apply well_inits_nil. Qed.

Lemma hc_inits_cons : forall (G:ctx) (D:init_ctx) (vs:vars) (x:var) (i:init_typ) (avs:avars) (is':inits),
  (forall G' D' vs', binds_extends G G' -> binds_extends D D' ->
     vs_subset vs vs' -> G' ⸴ D' ⸴ vs' ⊢i (trm_var (avar_f x)) ∶ i) ->
  (forall G' D' vs', binds_extends G G' -> binds_extends D D' ->
     vs_subset vs vs' -> G' ⸴ D' ⸴ vs' ⊢i avs :: is') ->
  forall G' D' vs', binds_extends G G' -> binds_extends D D' ->
    vs_subset vs vs' -> G' ⸴ D' ⸴ vs' ⊢i (cons (avar_f x) avs) :: (cons i is').
Proof.
  intros. eapply well_inits_cons.
  - eapply H; eauto.
  - eapply H0; eauto.
Qed.

End InitCommitTransfer.
Lemma init_commit_rules_binds_extends :
  (forall (G:ctx) (D:init_ctx) (t:trm), G ⸴ D ⊢c t ->
     forall G' D' vs vs', binds_extends G G' -> binds_extends D D' ->
       vs_subset vs vs' -> G' ⸴ D' ⊢c t) /\
  (forall (G:ctx) (D:init_ctx) (avs:avars), G ⸴ D ⊢c avs ->
     forall G' D' vs vs', binds_extends G G' -> binds_extends D D' ->
       vs_subset vs vs' -> G' ⸴ D' ⊢c avs) /\
  (forall (G:ctx) (D:init_ctx) (l:lit), G ⸴ D ⊢c l ->
     forall G' D' vs vs', binds_extends G G' -> binds_extends D D' ->
       vs_subset vs vs' -> G' ⸴ D' ⊢c l) /\
  (forall (G:ctx) (D:init_ctx) (vs:vars) (t:trm) (i:init_typ), G ⸴ D ⸴ vs ⊢i t ∶ i ->
     forall G' D' vs', binds_extends G G' -> binds_extends D D' ->
       vs_subset vs vs' -> G' ⸴ D' ⸴ vs' ⊢i t ∶ i) /\
  (forall (G:ctx) (D:init_ctx) (vs:vars) (avs:avars) (is':inits), G ⸴ D ⸴ vs ⊢i avs :: is' ->
     forall G' D' vs', binds_extends G G' -> binds_extends D D' ->
       vs_subset vs vs' -> G' ⸴ D' ⸴ vs' ⊢i avs :: is').
Proof.
  apply (well_init_mut_ind
    (fun (G:ctx) (D:init_ctx) (t:trm) (_:G ⸴ D ⊢c t) =>
       forall G' D' vs vs', binds_extends G G' -> binds_extends D D' ->
         vs_subset vs vs' -> G' ⸴ D' ⊢c t)
    (fun (G:ctx) (D:init_ctx) (avs:avars) (_:G ⸴ D ⊢c avs) =>
       forall G' D' vs vs', binds_extends G G' -> binds_extends D D' ->
         vs_subset vs vs' -> G' ⸴ D' ⊢c avs)
    (fun (G:ctx) (D:init_ctx) (l:lit) (_:G ⸴ D ⊢c l) =>
       forall G' D' vs vs', binds_extends G G' -> binds_extends D D' ->
         vs_subset vs vs' -> G' ⸴ D' ⊢c l)
    (fun (G:ctx) (D:init_ctx) (vs:vars) (t:trm) (i:init_typ) (_:G ⸴ D ⸴ vs ⊢i t ∶ i) =>
       forall G' D' vs', binds_extends G G' -> binds_extends D D' ->
         vs_subset vs vs' -> G' ⸴ D' ⸴ vs' ⊢i t ∶ i)
    (fun (G:ctx) (D:init_ctx) (vs:vars) (avs:avars) (is':inits) (_:G ⸴ D ⸴ vs ⊢i avs :: is') =>
       forall G' D' vs', binds_extends G G' -> binds_extends D D' ->
         vs_subset vs vs' -> G' ⸴ D' ⸴ vs' ⊢i avs :: is'));
  intros;
  first [ solve [ eapply hc_commit_var; eauto 4 ]
        | solve [ eapply hc_commit_all_elim; eauto 4 ]
        | solve [ eapply hc_commit_new; eauto 4 ]
        | solve [ eapply hc_commit_rcd_elim; eauto 4 ]
        | solve [ eapply hc_commit_fld_asn; eauto 4 ]
        | solve [ eapply hc_commit_let; eauto 4 ]
        | solve [ eapply hc_commit_llit; eauto 4 ]
        | solve [ eapply hc_commit_avars_nil; eauto 4 ]
        | solve [ eapply hc_commit_avars_cons; eauto 4 ]
        | solve [ eapply hc_commit_all_intro; eauto 4 ]
        | solve [ eapply hc_commit_con_intro; eauto 4 ]
        | solve [ eapply hc_init_var_binds; eauto 4 ]
        | solve [ eapply hc_init_commit; eauto 4 ]
        | solve [ eapply hc_init_new_free; eauto 4 ]
        | solve [ eapply hc_init_fld_asn_ac; eauto 4 ]
        | solve [ eapply hc_init_fld_asn_ff; eauto 4 ]
        | solve [ eapply hc_init_let; eauto 4 ]
        | solve [ eapply hc_init_llit; eauto 4 ]
        | solve [ eapply hc_inits_nil; eauto 4 ]
        | solve [ eapply hc_inits_cons; eauto 4 ] ].
Qed.

Corollary commit_binds_extends : forall (G:ctx) (D:init_ctx) (t:trm),
  G ⸴ D ⊢c t ->
  forall G' D' vs vs', binds_extends G G' -> binds_extends D D' ->
    vs_subset vs vs' -> G' ⸴ D' ⊢c t.
Proof. intros. eapply (proj1 init_commit_rules_binds_extends); eauto. Qed.

Corollary commit_avars_binds_extends : forall (G:ctx) (D:init_ctx) (avs:avars),
  G ⸴ D ⊢c avs ->
  forall G' D' vs vs', binds_extends G G' -> binds_extends D D' ->
    vs_subset vs vs' -> G' ⸴ D' ⊢c avs.
Proof. intros. eapply (proj1 (proj2 init_commit_rules_binds_extends)); eauto. Qed.

Corollary commit_lit_binds_extends : forall (G:ctx) (D:init_ctx) (l:lit),
  G ⸴ D ⊢c l ->
  forall G' D' vs vs', binds_extends G G' -> binds_extends D D' ->
    vs_subset vs vs' -> G' ⸴ D' ⊢c l.
Proof. intros. eapply (proj1 (proj2 (proj2 init_commit_rules_binds_extends))); eauto. Qed.

Corollary init_binds_extends : forall (G:ctx) (D:init_ctx) (vs:vars) (t:trm) (i:init_typ),
  G ⸴ D ⸴ vs ⊢i t ∶ i ->
  forall G' D' vs', binds_extends G G' -> binds_extends D D' ->
    vs_subset vs vs' -> G' ⸴ D' ⸴ vs' ⊢i t ∶ i.
Proof. intros. eapply (proj1 (proj2 (proj2 (proj2 init_commit_rules_binds_extends)))); eauto. Qed.

Corollary init_avars_binds_extends : forall (G:ctx) (D:init_ctx) (vs:vars) (avs:avars) (is':inits),
  G ⸴ D ⸴ vs ⊢i avs :: is' ->
  forall G' D' vs', binds_extends G G' -> binds_extends D D' ->
    vs_subset vs vs' -> G' ⸴ D' ⸴ vs' ⊢i avs :: is'.
Proof. intros. eapply (proj2 (proj2 (proj2 (proj2 init_commit_rules_binds_extends)))); eauto. Qed.

(** * Record structure of dec typings *)

Lemma record_dec_typ : forall (A:typ_label) (T:typ), record_dec (dec_typ A T T).
Proof. intros. apply rd_typ. Qed.

Lemma record_dec_trm : forall (a:trm_label) (T:typ), record_dec (dec_trm a T T).
Proof. intros. apply rd_trm. Qed.

Lemma label_of_ty_def : forall (G:ctx) (d:def) (D:dec),
  G ⊢ d ∶d D -> label_of D = label_of d.
Proof.
  intros G d D H. change (ty_def G d D) in H. destruct H; reflexivity.
Qed.

Lemma label_of_ty_heap_def : forall (G:ctx) (d:heap_def) (D:dec),
  G ⊢ d ∶d D -> label_of D = label_of d.
Proof.
  intros G d D H. change (ty_heap_def G d D) in H. destruct H; reflexivity.
Qed.

Lemma ty_def_record_dec : forall (G:ctx) (d:def) (D:dec),
  G ⊢ d ∶d D -> record_dec D.
Proof.
  intros G d D H. change (ty_def G d D) in H. destruct H.
  - apply record_dec_typ.
  - apply record_dec_trm.
Qed.

Lemma ty_heap_def_record_dec : forall (G:ctx) (d:heap_def) (D:dec),
  G ⊢ d ∶d D -> record_dec D.
Proof.
  intros G d D H. change (ty_heap_def G d D) in H. destruct H.
  - apply record_dec_typ.
  - apply record_dec_trm.
  - apply record_dec_trm.
Qed.

(** * Record correspondence of ty_defs *)

Lemma labels_hasnt_sound : forall (A:Set) `{LabelOf A} (ds:list A) (l:label),
  labels_hasnt ds l -> forall d, List.In d ds -> label_of d <> l.
Proof.
  intros A LA ds. induction ds as [|a ds IH]; intros l H d Hin.
  - inversion Hin.
  - unfold labels_hasnt in H. cbn in H.
    destruct (classic (label_of a = l)) as [E|NE].
    + rewrite (If_l (P:=label_of a = l) _ _ E) in H. discriminate.
    + rewrite (If_r (P:=label_of a = l) _ _ NE) in H.
      destruct Hin as [->|Hin].
      * intro E; exact (NE E).
      * eapply IH; eauto.
Qed.

Lemma record_typ_labels : forall (T:typ) (ls:fset label),
  record_typ T ls -> forall D, record_has T D -> label_of D \in ls.
Proof.
  intros T ls H. induction H; intros D0 Hrh.
  - inversion Hrh; subst. apply in_singleton_self.
  - inversion Hrh; subst.
    + rewrite in_union. left. eapply IHrecord_typ. eassumption.
    + match goal with
      | Hr : record_has (typ_rcd ?DD) ?D0 |- _ => inversion Hr; subst
      end.
      try subst l. rewrite in_union. right. apply in_singleton_self.
Qed.

Lemma record_typ_has : forall (T:typ) (ls:fset label),
  record_typ T ls -> forall l, l \in ls -> exists D, record_has T D /\ label_of D = l.
Proof.
  intros T ls H. induction H; intros l0 Hin.
  - rewrite in_singleton in Hin. subst l0.
    exists D. split; [apply rh_one|symmetry; assumption].
  - rewrite in_union in Hin. destruct Hin as [Hin|Hin].
    + destruct (IHrecord_typ l0 Hin) as [D' [Hrh Heq]]. exists D'.
      split; [apply rh_andl; exact Hrh|exact Heq].
    + rewrite in_singleton in Hin. subst l0. exists D.
      split; [apply rh_andr, rh_one|symmetry; assumption].
Qed.

Lemma In_singleton_eq : forall (A:Type) (x y:A),
  List.In x (cons y nil) -> x = y.
Proof.
  intros A x y H. simpl in H. destruct H as [E|F]; [symmetry; exact E|destruct F].
Qed.

Lemma In_cons_inv : forall (A:Type) (x y:A) (l:list A),
  List.In x (cons y l) -> y = x \/ List.In x l.
Proof. intros. simpl in H. exact H. Qed.

Section TyDefsRecord.

Context {A:Set} `{LA:LabelOf A} `{DTA:DecTyping A}.
Hypothesis DTR : forall (G:ctx) (d:A) (D:dec), G ⊢ d ∶d D -> record_dec D.
Hypothesis DTL : forall (G:ctx) (d:A) (D:dec), G ⊢ d ∶d D -> label_of D = label_of d.

Lemma ty_defs_record_correspond : forall (G:ctx) (ds:list A) (T:typ),
  G ⊢ ds ∶ T ->
  (exists ls, record_typ T ls /\
     (forall d, List.In d ds -> exists D, record_has T D /\ G ⊢ d ∶d D) /\
     (forall D, record_has T D -> exists d, List.In d ds /\ label_of D = label_of d)).
Proof.
  intros G ds T Hds. induction Hds.
  - (* one *)
    exists (\{label_of D}). split.
    + apply rt_one; [apply DTR with (G:=Gamma) (d:=d); exact H|reflexivity].
    + split.
      * intros d0 Hin. apply In_singleton_eq in Hin. subst d0.
        exists D. split; [apply rh_one|exact H].
      * intros D0 Hrh. inversion Hrh; subst. exists d. split; [apply in_eq|].
        eapply DTL; eauto.
  - (* cons *)
    destruct IHHds as [ls [Hrt [Hfwd Hbwd]]].
    assert (Hnotin : label_of D \notin ls).
    { intro Hin.
      destruct (@record_typ_has T ls Hrt (label_of D) Hin) as [D' [Hrh Heql]].
      destruct (Hbwd D' Hrh) as [d0 [Hin0 Heq0]].
      assert (HeqD : label_of D = label_of d) by (eapply DTL; eauto).
      assert (Heq1 : label_of d = label_of d0).
      { rewrite <- HeqD. rewrite <- Heql. exact Heq0. }
      apply (labels_hasnt_sound H1 d0 Hin0). symmetry. exact Heq1. }
    exists (ls \u \{label_of D}). split.
    + apply rt_cons with (T:=T) (ls:=ls) (D:=D) (l:=label_of D).
      * exact Hrt.
      * eapply DTR; eauto.
      * reflexivity.
      * exact Hnotin.
    + split.
      * intros d0 Hin.
        destruct Hin as [->|Hin].
        -- exists D. split; [apply rh_andr, rh_one|exact H0].
        -- destruct (Hfwd d0 Hin) as [D0 [Hrh Hty]].
           exists D0. split; [apply rh_andl; exact Hrh|exact Hty].
      * intros D0 Hrh.
        inversion Hrh; subst.
        -- destruct (Hbwd D0 H5) as [d' [Hin' Heq']].
           exists d'. split; [apply List.in_cons; exact Hin'|exact Heq'].
        -- match goal with
           | Hr : record_has (typ_rcd ?DD) ?D0 |- _ => inversion Hr; subst
           end.
           exists d. split; [apply in_eq|]. eapply DTL; eauto.
Qed.

Lemma ty_defs_record_type : forall (G:ctx) (ds:list A) (T:typ),
  G ⊢ ds ∶ T -> record_type T.
Proof.
  intros G ds T Hds. destruct (ty_defs_record_correspond Hds) as [ls [Hrt _]].
  exists ls. exact Hrt.
Qed.

End TyDefsRecord.

Lemma ty_defs_def_record_type : forall (G:ctx) (ds:defs) (T:typ),
  G ⊢ ds ∶ T -> record_type T.
Proof.
  intros. eapply ty_defs_record_type;
    eauto using ty_def_record_dec, label_of_ty_def.
Qed.

Lemma ty_heap_defs_record_type : forall (G:ctx) (hds:heap_defs) (T:typ),
  G ⊢ hds ∶ T -> record_type T.
Proof.
  intros. apply (@ty_defs_record_type heap_def _ _
    ty_heap_def_record_dec label_of_ty_heap_def G hds T H).
Qed.

Lemma ty_defs_def_correspond : forall (G:ctx) (ds:defs) (T:typ),
  G ⊢ ds ∶ T ->
  (exists ls, record_typ T ls /\
     (forall d, List.In d ds -> exists D, record_has T D /\ G ⊢ d ∶d D) /\
     (forall D, record_has T D -> exists d, List.In d ds /\ label_of D = label_of d)).
Proof.
  intros. eapply ty_defs_record_correspond;
    eauto using ty_def_record_dec, label_of_ty_def.
Qed.

Lemma ty_heap_defs_correspond : forall (G:ctx) (hds:heap_defs) (T:typ),
  G ⊢ hds ∶ T ->
  (exists ls, record_typ T ls /\
     (forall d, List.In d hds -> exists D, record_has T D /\ G ⊢ d ∶d D) /\
     (forall D, record_has T D -> exists d, List.In d hds /\ label_of D = label_of d)).
Proof.
  intros. apply (@ty_defs_record_correspond heap_def _ _
    ty_heap_def_record_dec label_of_ty_heap_def G hds T H).
Qed.

(** * Commit/init facts about variable-shaped terms *)

Lemma commit_var_binds : forall (G:ctx) (D:init_ctx) (x:var),
  G ⸴ D ⊢c trm_var (avar_f x) -> binds x committed D.
Proof.
  intros G D x H. change (well_committed G D (trm_var (avar_f x))) in H.
  inversion H; subst; assumption.
Qed.

Lemma init_sel_commit : forall (G:ctx) (D:init_ctx) (vs:vars) (x:var) (a:trm_label) (i:init_typ),
  G ⸴ D ⸴ vs ⊢i trm_sel (avar_f x) a ∶ i ->
  i = committed /\ (G ⸴ D ⊢c trm_sel (avar_f x) a).
Proof.
  intros G D vs x a i H. change (well_init G D vs (trm_sel (avar_f x) a) i) in H.
  inversion H; subst.
  - split; [reflexivity|assumption].
Qed.

Lemma init_app_commit : forall (G:ctx) (D:init_ctx) (vs:vars) (x z:var) (i:init_typ),
  G ⸴ D ⸴ vs ⊢i trm_app (avar_f x) (avar_f z) ∶ i ->
  i = committed /\ (G ⸴ D ⊢c trm_app (avar_f x) (avar_f z)).
Proof.
  intros G D vs x z i H. change (well_init G D vs (trm_app (avar_f x) (avar_f z)) i) in H.
  inversion H; subst.
  - split; [reflexivity|assumption].
Qed.

Lemma commit_sel_binds : forall (G:ctx) (D:init_ctx) (x:var) (a:trm_label),
  G ⸴ D ⊢c trm_sel (avar_f x) a -> binds x committed D.
Proof.
  intros G D x a H. change (well_committed G D (trm_sel (avar_f x) a)) in H.
  inversion H; subst. eapply commit_var_binds; eauto.
Qed.

Lemma commit_app_binds : forall (G:ctx) (D:init_ctx) (x z:var),
  G ⸴ D ⊢c trm_app (avar_f x) (avar_f z) ->
  binds x committed D /\ binds z committed D.
Proof.
  intros G D x z H. change (well_committed G D (trm_app (avar_f x) (avar_f z))) in H.
  inversion H; subst. split; eapply commit_var_binds; eauto.
Qed.

(** * Generic environment facts *)

Lemma binds_in_dom : forall (A:Type) (E:env A) (x:var) (v:A),
  binds x v E -> x \in dom E.
Proof.
  intros A E x v H.
  eapply (@LibEnv.get_some_inv A x v E).
  eapply LibEnv.binds_get. eassumption.
Qed.

Lemma dom_binds_exists : forall (A:Type) (E:env A) (x:var),
  x \in dom E -> exists v, binds x v E.
Proof.
  intros A E x H. destruct (@LibEnv.get_some A x E H) as [v Hv].
  exists v. exact Hv.
Qed.

(** * Heap correspondence *)

Lemma heap_correspond_dom : forall (G:ctx) (Sigma:heap),
  heap_correspond G Sigma -> dom G = dom Sigma.
Proof. intros G Sigma [Hdom _]. exact Hdom. Qed.

Lemma heap_correspond_ty_item : forall (G:ctx) (Sigma:heap) (x:var),
  heap_correspond G Sigma -> x \in dom G -> ty_item_s G Sigma x.
Proof. intros G Sigma x [_ H]. exact (H x). Qed.

Lemma ty_item_s_obj_inv : forall (G:ctx) (Sigma:heap) (x:var) (T:typ) (hds:heap_defs),
  ty_item_s G Sigma x ->
  binds x (item_obj T hds) Sigma ->
  binds x (typ_bnd T) G /\ G ⊢ hds ∶ open x T.
Proof.
  intros G Sigma x T hds Hty Hb. inversion Hty; subst.
  - (* lit item *)
    match goal with
    | Hl : binds x (item_lit l) Sigma |- _ =>
      assert (Heq : item_lit l = item_obj T hds) by
        (eapply LibEnv.binds_functional; [exact Hl|exact Hb]);
      discriminate Heq
    end.
  - (* obj item *)
    match goal with
    | Hu : binds x (item_obj U hds0) Sigma |- _ =>
      assert (Heq : item_obj U hds0 = item_obj T hds) by
        (eapply LibEnv.binds_functional; [exact Hu|exact Hb]);
      injection Heq as HU Hh; subst; split; assumption
    end.
Qed.

Lemma ty_item_s_lit_inv : forall (G:ctx) (Sigma:heap) (x:var) (l:lit),
  ty_item_s G Sigma x ->
  binds x (item_lit l) Sigma ->
  exists T, binds x T G /\ G ⊢ l ∶ T.
Proof.
  intros G Sigma x l Hty Hb. inversion Hty; subst.
  - assert (Heq : item_lit l0 = item_lit l) by
      (eapply LibEnv.binds_functional; eassumption).
    injection Heq as Hl. subst. eexists. split; eassumption.
  - match goal with
    | Hu : binds x (item_obj U hds) Sigma |- _ =>
      assert (Heq : item_obj U hds = item_lit l) by
        (eapply LibEnv.binds_functional; [exact Hu|exact Hb]);
      discriminate Heq
    end.
Qed.

Lemma heap_correspond_obj : forall (G:ctx) (Sigma:heap) (x:var) (T:typ) (hds:heap_defs),
  heap_correspond G Sigma ->
  binds x (item_obj T hds) Sigma ->
  binds x (typ_bnd T) G /\ G ⊢ hds ∶ open x T.
Proof.
  intros G Sigma x T hds HC Hb.
  destruct HC as [Hdom Hitem].
  assert (Hin : x \in dom G).
  { rewrite Hdom. eapply binds_in_dom; eexact Hb. }
  eapply ty_item_s_obj_inv; [eapply Hitem; exact Hin|exact Hb].
Qed.

Lemma heap_correspond_lit : forall (G:ctx) (Sigma:heap) (x:var) (l:lit),
  heap_correspond G Sigma ->
  binds x (item_lit l) Sigma ->
  exists T, binds x T G /\ G ⊢ l ∶ T.
Proof.
  intros G Sigma x l HC Hb.
  destruct HC as [Hdom Hitem].
  assert (Hin : x \in dom G).
  { rewrite Hdom. eapply binds_in_dom; eexact Hb. }
  eapply ty_item_s_lit_inv; [eapply Hitem; exact Hin|exact Hb].
Qed.

(** * Free sub heaps *)

Lemma free_sub_heaps_well_committed : forall (G:ctx) (D:init_ctx) (Sigma:heap) (Es:list eff_ctx),
  free_sub_heaps G D Sigma Es -> well_committed_heap G D Sigma.
Proof.
  intros G D Sigma Es H. induction H.
  - assumption.
  - assumption.
Qed.

Lemma free_sub_heaps_cons_inv : forall (G:ctx) (D:init_ctx) (Sigma:heap) (E:eff_ctx) (Es:list eff_ctx),
  free_sub_heaps G D Sigma (E :: Es) ->
  free_sub_heap E Sigma D /\ free_sub_heaps G D Sigma Es.
Proof.
  intros G D Sigma E Es H. inversion H; subst.
  split; assumption.
Qed.

Lemma free_sub_heap_item : forall (E:eff_ctx) (Sigma:heap) (D:init_ctx) (x:var) (effs:effects),
  free_sub_heap E Sigma D ->
  binds x effs E ->
  exists itm, binds x itm Sigma /\ free_heap_item D E x itm.
Proof.
  intros E Sigma D x effs Hf Hb. unfold free_sub_heap in Hf.
  destruct (Hf x effs Hb) as [_ [itm [Hbind Hitem]]].
  exists itm. split; assumption.
Qed.

Lemma free_heap_item_obj_inv : forall (D:init_ctx) (E:eff_ctx) (y:var) (T:typ) (hds:heap_defs),
  free_heap_item D E y (item_obj T hds) -> free_heap_defs D E y hds.
Proof. intros D E y T hds H. inversion H; subst. assumption. Qed.

(** * Committed heaps *)

Lemma well_committed_heap_item : forall (G:ctx) (D:init_ctx) (Sigma:heap) (x:var) (itm:item),
  well_committed_heap G D Sigma ->
  binds x committed D ->
  binds x itm Sigma ->
  committed_heap_item G D itm.
Proof.
  intros G D Sigma x itm [_ [_ H]] Hb1 Hb2. eapply H; eassumption.
Qed.

Lemma committed_heap_item_obj_inv : forall (G:ctx) (D:init_ctx) (T:typ) (hds:heap_defs),
  committed_heap_item G D (item_obj T hds) -> committed_heap_defs D hds.
Proof. intros G D T hds H. inversion H; subst. assumption. Qed.

Lemma committed_heap_item_lit_inv : forall (G:ctx) (D:init_ctx) (l:lit),
  committed_heap_item G D (item_lit l) -> G ⸴ D ⊢c l.
Proof. intros G D l H. inversion H; subst. assumption. Qed.

(** * Inert contexts *)

Lemma inert_binds_inert_typ : forall (G:ctx) (x:var) (T:typ),
  inert G -> binds x T G -> inert_typ T.
Proof.
  intros G x T Hi. induction Hi as [| G0 y U Hi IH]; intros Hb.
  - exfalso. eapply LibEnv.binds_empty_inv; eexact Hb.
  - eapply LibEnv.binds_push_inv in Hb.
    destruct Hb as [[Heq1 Heq2]|[Hneq Hb]].
    + inversion Heq1; inversion Heq2; subst. assumption.
    + eapply IH; eassumption.
Qed.

Lemma inert_inits_binds_inv : forall (D:init_ctx) (x:var) (i:init_typ),
  inert_inits D -> binds x i D -> i = free \/ i = committed.
Proof. intros D x i H Hb. unfold inert_inits in H. eapply H; eassumption. Qed.

(** * Record shapes *)

Lemma record_type_has_rt : forall (T:typ),
  record_type T -> exists ls, record_typ T ls.
Proof. intros T H. exact H. Qed.

Lemma record_typ_rcd_inv : forall (D:dec) (ls:fset label),
  record_typ (typ_rcd D) ls ->
  record_dec D /\ ls = \{label_of D}.
Proof.
  intros D ls H. inversion H; subst.
  split; [assumption|]. subst. reflexivity.
Qed.

Lemma record_typ_and_inv : forall (T U:typ) (ls:fset label),
  record_typ (typ_and T U) ls ->
  exists ls' D, record_typ T ls' /\ U = typ_rcd D /\ record_dec D /\
                label_of D \notin ls' /\ ls = ls' \u \{label_of D}.
Proof.
  intros T U ls H. inversion H; subst.
  eexists _, _. repeat split; eauto.
Qed.

Lemma vs_subset_refl : forall (vs:vars), vs_subset vs vs.
Proof. intros vs x Hx. exact Hx. Qed.

Lemma ty_stack_binds_extends : forall (G:ctx) (D:init_ctx) (Es:list eff_ctx) (Fs:stack)
    (T:typ) (i:init_typ) (effs:list effects) (U:typ),
  ty_stack G D Es Fs T i effs U ->
  forall G', binds_extends G G' -> ty_stack G' D Es Fs T i effs U.
Proof.
  intros G D Es Fs T i effs U H. induction H; intros G' Hext.
  - eapply ty_stack_nil. eapply subtyp_binds_extends; eassumption.
  - eapply ty_stack_let with (L:=L).
    + eapply IHty_stack. assumption.
    + intros x Hx. eapply ty_trm_binds_extends.
      * eapply H0; eassumption.
      * apply binds_extends_push. assumption.
    + intros x Hx. eapply init_binds_extends.
      * eapply H1; eassumption.
      * apply binds_extends_push. assumption.
      * apply binds_extends_refl.
      * apply vs_subset_refl.
    + intros x Hx. eapply H2; eassumption.
  - eapply ty_stack_ret_free with (T:=T).
    + eapply IHty_stack. assumption.
    + eapply ty_trm_binds_extends; [eassumption|assumption].
    + eapply init_binds_extends.
      * eassumption.
      * assumption.
      * apply binds_extends_refl.
      * apply vs_subset_refl.
  - eapply ty_stack_ret_committed with (T:=T).
    + eapply IHty_stack. assumption.
    + eapply ty_trm_binds_extends; [eassumption|assumption].
    + eapply init_binds_extends.
      * eassumption.
      * assumption.
      * apply binds_extends_refl.
      * apply vs_subset_refl.
Qed.

(** * Uniqueness of labels in a typed dec list *)

Lemma ty_defs_label_unique : forall (A:Set) `{LA:LabelOf A} `{DTA:DecTyping A}
    (G:ctx) (ds:list A) (T:typ),
  G ⊢ ds ∶ T ->
  forall d1 d2, List.In d1 ds -> List.In d2 ds ->
    label_of d1 = label_of d2 -> d1 = d2.
Proof.
  intros A LA DTA G ds T H. induction H; intros d1 d2 I1 I2 E.
  - destruct I1 as [E1|F1]; [|inversion F1].
    destruct I2 as [E2|F2]; [|inversion F2].
    subst. reflexivity.
  - destruct I1 as [->|I1]; destruct I2 as [->|I2].
    + reflexivity.
    + exfalso. eapply (labels_hasnt_sound H1 d2 I2). symmetry. exact E.
    + exfalso. eapply (labels_hasnt_sound H1 d1 I1). exact E.
    + eapply IHty_defs; eassumption.
Qed.

Lemma ty_defs_def_label_unique : forall (G:ctx) (ds:defs) (T:typ),
  G ⊢ ds ∶ T ->
  forall d1 d2, List.In d1 ds -> List.In d2 ds ->
    label_of d1 = label_of d2 -> d1 = d2.
Proof.
  intros G ds T H d1 d2 I1 I2 E.
  eapply (@ty_defs_label_unique def _ _ G ds T H d1 d2 I1 I2 E).
Qed.

Lemma ty_heap_defs_label_unique : forall (G:ctx) (hds:heap_defs) (T:typ),
  G ⊢ hds ∶ T ->
  forall d1 d2, List.In d1 hds -> List.In d2 hds ->
    label_of d1 = label_of d2 -> d1 = d2.
Proof.
  intros G hds T H d1 d2 I1 I2 E.
  eapply (@ty_defs_label_unique heap_def _ _ G hds T H d1 d2 I1 I2 E).
Qed.

(** * get_labeld_list and labels_has *)

Lemma get_labeld_list_in : forall (A:Set) `{LA:LabelOf A}
    (l:label) (ds:list A) (d:A),
  (forall d1 d2, List.In d1 ds -> List.In d2 ds ->
     label_of d1 = label_of d2 -> d1 = d2) ->
  List.In d ds ->
  label_of d = l ->
  get_labeld_list l ds = Some d.
Proof.
  intros A LA l ds. induction ds as [|a ds IH]; intros d Huniq Hin Hl.
  - inversion Hin.
  - cbn.
    destruct (classic (label_of a = l)) as [E|NE].
    + rewrite (If_l (P:=label_of a = l) _ _ E).
      f_equal. symmetry. eapply Huniq.
      * exact Hin.
      * apply List.in_eq.
      * rewrite E. exact Hl.
    + rewrite (If_r (P:=label_of a = l) _ _ NE).
      destruct Hin as [->|Hin].
      * exfalso. apply NE. exact Hl.
      * eapply IH.
        -- intros d1 d2 I1 I2 E12. eapply Huniq.
           ++ apply List.in_cons. exact I1.
           ++ apply List.in_cons. exact I2.
           ++ exact E12.
        -- exact Hin.
        -- exact Hl.
Qed.

Lemma labels_has_in : forall (A:Set) `{LA:LabelOf A} (ds:list A) (d:A),
  (forall d1 d2, List.In d1 ds -> List.In d2 ds ->
     label_of d1 = label_of d2 -> d1 = d2) ->
  List.In d ds ->
  labels_has ds d.
Proof.
  intros A LA ds d Huniq Hin. unfold labels_has.
  eapply get_labeld_list_in; eauto.
Qed.

Lemma subst_intro_typ : forall (T:typ) (x y:var) (n:nat),
  x \notin fv T -> open_rec n y T = subst_var x y (open_rec n x T).
Proof.
  intros. symmetry. rewrite (proj1 subst_open_rec_mut).
  rewrite subst_if_eq. rewrite (@fv_subst_typ T x y H). reflexivity.
Qed.

Lemma subst_intro_trm : forall (t:trm) (x y:var) (n:nat),
  x \notin fv t -> open_rec n y t = subst_var x y (open_rec n x t).
Proof.
  intros. symmetry. rewrite (proj1 subst_open_rec_trm_mut).
  rewrite subst_if_eq. rewrite (@fv_subst_trm t x y H). reflexivity.
Qed.

Lemma subst_intro_lit : forall (l:lit) (x y:var) (n:nat),
  x \notin fv l -> open_rec n y l = subst_var x y (open_rec n x l).
Proof.
  intros. symmetry. rewrite (proj2 subst_open_rec_trm_mut).
  rewrite subst_if_eq. rewrite (@fv_subst_lit l x y H). reflexivity.
Qed.

Lemma eff_ctx_corr_cons_inv : forall (E:eff_ctx) (Es:list eff_ctx) (effs:effects) (effss:list effects),
  eff_ctx_corr (E :: Es) (effs :: effss) ->
  eff_ctx_corr Es effss /\ eff_ctx_corr_one E effs.
Proof. intros. inversion H; subst. split; assumption. Qed.

Lemma eff_ctx_corr_one_in : forall (E:eff_ctx) (effs:effects) (x:var) (effs':effects) (e:effect),
  eff_ctx_corr_one E effs ->
  binds x effs' E ->
  e \in from_list effs' ->
  e \in from_list effs.
Proof.
  intros E effs x effs' e H Hb Hin. unfold eff_ctx_corr_one in H.
  eapply H; eassumption.
Qed.

Lemma free_sub_heap_effect_same : forall (E:eff_ctx) (Sigma:heap) (D:init_ctx) (x:var) (effs:effects) (y:var) (a:trm_label),
  free_sub_heap E Sigma D ->
  binds x effs E ->
  (y,a) \in from_list effs ->
  y = x.
Proof.
  intros. unfold free_sub_heap in H. exact (proj1 (H x effs H0) y a H1).
Qed.

Lemma in_list_dom_union : forall (A:Type) (Es:list (env A)) (x:var),
  x \in list_dom_union Es <-> exists E, List.In E Es /\ x \in dom E.
Proof.
  intros A Es. induction Es as [|E Es IH]; intros x.
  - cbn. split.
    + intros H. exfalso. exact (in_empty_inv H).
    + intros [E' [Hin _]]. inversion Hin.
  - cbn. rewrite in_union. split.
    + intros [H|H].
      * exists E. split; [apply List.in_eq|exact H].
      * destruct (proj1 (IH x) H) as [E' [Hin Hdom]].
        exists E'. split; [apply List.in_cons; exact Hin|exact Hdom].
    + intros [E' [Hin Hdom]]. destruct Hin as [->|Hin].
      * left. exact Hdom.
      * right. apply (proj2 (IH x)). exists E'. split; assumption.
Qed.

Lemma free_sub_heaps_all_notin : forall (G:ctx) (D:init_ctx) (Sigma:heap) (E:eff_ctx) (Es:list eff_ctx),
  free_sub_heaps G D Sigma (E :: Es) ->
  all_notin (dom E) (list_dom_union Es).
Proof.
  intros. inversion H; subst.
  match goal with H' : all_notin _ _ |- _ => exact H' end.
Qed.

Lemma well_committed_heap_doms : forall (G:ctx) (D:init_ctx) (Sigma:heap),
  well_committed_heap G D Sigma ->
  dom G = dom D /\ dom D = dom Sigma.
Proof. intros G D Sigma [H1 [H2 _]]. split; assumption. Qed.

Lemma ty_stack_nil_inv : forall (G:ctx) (D:init_ctx) (Es:list eff_ctx) (T:typ) (i:init_typ) (effs:list effects) (U:typ),
  ty_stack G D Es nil T i effs U ->
  exists E, Es = E :: nil /\ effs = (nil :: nil)%list /\ G ⊢ T <: U.
Proof.
  intros G D Es T i effs U H. inversion H; subst.
  eexists. split; [reflexivity|split; [reflexivity|assumption]].
Qed.

(** * Opening preserves record structure *)

Lemma label_of_open_dec : forall (D:dec) (n:nat) (u:var),
  label_of (open_rec n u D) = label_of D.
Proof. intros D n u. destruct D; reflexivity. Qed.

Lemma record_dec_open : forall (D:dec) (n:nat) (u:var),
  record_dec D -> record_dec (open_rec n u D).
Proof. intros D n u H. destruct H; simpl; [apply rd_typ|apply rd_trm]. Qed.

Lemma record_typ_open : forall (T:typ) (ls:fset label) (n:nat) (u:var),
  record_typ T ls -> record_typ (open_rec n u T) ls.
Proof.
  intros T ls n u H. induction H.
  - cbn. apply rt_one.
    + apply record_dec_open; assumption.
    + rewrite label_of_open_dec. assumption.
  - cbn. apply rt_cons.
    + match goal with IH : record_typ (open_rec n u ?X) ?LX
                       |- record_typ (open_rec n u ?X) ?LX => exact IH end.
    + apply record_dec_open; assumption.
    + rewrite label_of_open_dec. assumption.
    + assumption.
Qed.

Lemma record_type_open : forall (T:typ) (n:nat) (u:var),
  record_type T -> record_type (open_rec n u T).
Proof.
  intros T n u [ls Hrt]. exists ls. apply record_typ_open. assumption.
Qed.

(** * Shape facts *)

Lemma record_type_not_top : record_type typ_top -> False.
Proof. intros [ls H]. inversion H. Qed.
Lemma record_type_not_bot : record_type typ_bot -> False.
Proof. intros [ls H]. inversion H. Qed.
Lemma record_type_not_sel : forall (a:avar) (A:typ_label), record_type (typ_sel a A) -> False.
Proof. intros a A [ls H]. inversion H. Qed.
Lemma record_type_not_all : forall (S T:typ), record_type (typ_all S T) -> False.
Proof. intros S T [ls H]. inversion H. Qed.
Lemma record_type_not_con : forall (Ts:typs) (is':inits) (T:typ), record_type (typ_con Ts is' T) -> False.
Proof. intros Ts is' T [ls H]. inversion H. Qed.
Lemma record_type_not_bnd : forall (T:typ), record_type (typ_bnd T) -> False.
Proof. intros T [ls H]. inversion H. Qed.

Lemma inert_typ_not_top : inert_typ typ_top -> False.
Proof. intros H. inversion H. Qed.
Lemma inert_typ_not_bot : inert_typ typ_bot -> False.
Proof. intros H. inversion H. Qed.
Lemma inert_typ_not_sel : forall (a:avar) (A:typ_label), inert_typ (typ_sel a A) -> False.
Proof. intros a A H. inversion H. Qed.
Lemma inert_typ_not_rcd : forall (D:dec), inert_typ (typ_rcd D) -> False.
Proof. intros D H. inversion H. Qed.
Lemma inert_typ_not_and : forall (T U:typ), inert_typ (typ_and T U) -> False.
Proof. intros T U H. inversion H. Qed.

(** * Shape of precise flow tips in an inert setting *)

Lemma flow_shape : forall (x:var) (G:ctx) (T0 V:typ),
  G ⊢! x ∶ T0 ⪼ V ->
  inert_typ T0 ->
  binds x T0 G ->
  (V = T0 /\ inert_typ T0) \/ record_type V.
Proof.
  intros x G T0 V Hf. induction Hf; intros Hi Hb.
  - left. split; [reflexivity|assumption].
  - specialize (IHHf Hi Hb). destruct IHHf as [[Heq Hi2]|[ls Hr]].
    + inversion Heq; subst. inversion Hi2; subst.
      right. apply record_type_open. assumption.
    + exfalso. eapply record_type_not_bnd. exists ls. exact Hr.
  - specialize (IHHf Hi Hb). destruct IHHf as [[Heq Hi2]|[ls Hr]].
    + exfalso. inversion Heq; subst. exact (@inert_typ_not_and U1 U2 Hi2).
    + right. destruct (@record_typ_and_inv _ _ ls Hr) as [ls' [D HP]].
      exists ls'. exact (proj1 HP).
  - specialize (IHHf Hi Hb). destruct IHHf as [[Heq Hi2]|[ls Hr]].
    + exfalso. inversion Heq; subst. exact (@inert_typ_not_and U1 U2 Hi2).
    + right. destruct (@record_typ_and_inv _ _ ls Hr) as [ls' [D HP]].
      exists (\{label_of D}).
      assert (HeqU : U2 = typ_rcd D) by exact (proj1 (proj2 HP)).
      assert (Hrd : record_dec D) by exact (proj1 (proj2 (proj2 HP))).
      rewrite HeqU. apply rt_one; [exact Hrd|reflexivity].
Qed.

Lemma flow_typing : forall (x:var) (G:ctx) (T0 V:typ),
  G ⊢! x ∶ T0 ⪼ V ->
  G ⊢ trm_var (avar_f x) ∶ V.
Proof.
  intros x G T0 V Hf. induction Hf.
  - apply ty_var. assumption.
  - eapply ty_rec_elim. exact IHHf.
  - eapply ty_sub; [exact IHHf|apply subtyp_and11].
  - eapply ty_sub; [exact IHHf|apply subtyp_and12].
Qed.

(** * Corollaries: no flow tip is a top/bottom/selection type *)

Lemma flow_not_top : forall (x:var) (G:ctx) (T0:typ),
  inert_typ T0 -> binds x T0 G ->
  G ⊢! x ∶ T0 ⪼ typ_top -> False.
Proof.
  intros x G T0 Hi Hb Hf.
  destruct (@flow_shape x G T0 typ_top Hf Hi Hb) as [[Heq Hi2]|Hr].
  - inversion Heq; subst. exact (inert_typ_not_top Hi2).
  - eapply record_type_not_top. exact Hr.
Qed.

Lemma flow_not_bot : forall (x:var) (G:ctx) (T0:typ),
  inert_typ T0 -> binds x T0 G ->
  G ⊢! x ∶ T0 ⪼ typ_bot -> False.
Proof.
  intros x G T0 Hi Hb Hf.
  destruct (@flow_shape x G T0 typ_bot Hf Hi Hb) as [[Heq Hi2]|Hr].
  - inversion Heq; subst. exact (inert_typ_not_bot Hi2).
  - eapply record_type_not_bot. exact Hr.
Qed.

Lemma flow_not_sel : forall (x:var) (G:ctx) (T0:typ) (a:avar) (A:typ_label),
  inert_typ T0 -> binds x T0 G ->
  G ⊢! x ∶ T0 ⪼ typ_sel a A -> False.
Proof.
  intros x G T0 a A Hi Hb Hf.
  destruct (@flow_shape x G T0 (typ_sel a A) Hf Hi Hb) as [[Heq Hi2]|Hr].
  - inversion Heq; subst. exact (@inert_typ_not_sel a A Hi2).
  - exact (@record_type_not_sel a A Hr).
Qed.

Lemma flow_bnd_eq : forall (x:var) (G:ctx) (T0 U:typ),
  inert_typ T0 -> binds x T0 G ->
  G ⊢! x ∶ T0 ⪼ typ_bnd U -> typ_bnd U = T0.
Proof.
  intros x G T0 U Hi Hb Hf.
  destruct (@flow_shape x G T0 (typ_bnd U) Hf Hi Hb) as [[Heq Hi2]|Hr].
  - exact Heq.
  - exfalso. eapply record_type_not_bnd. exact Hr.
Qed.

Lemma record_has_rcd_inv : forall (D D':dec), record_has (typ_rcd D) D' -> D' = D.
Proof. intros D D' H. inversion H; subst; reflexivity. Qed.

Lemma record_has_and_inv : forall (T U:typ) (D:dec),
  record_has (typ_and T U) D -> record_has T D \/ record_has U D.
Proof. intros T U D H. inversion H; subst; [left|right]; assumption. Qed.

Lemma defs_update_label_in : forall (hds hds':heap_defs) (a:trm_label) (y:var),
  defs_update hds a y hds' ->
  exists d, List.In d hds /\ label_of d = label_trm a.
Proof.
  intros hds hds' a y H. induction H.
  - exists (heap_def_trm a o). split; [apply List.in_eq|reflexivity].
  - destruct IHdefs_update as [d0 [Hin Hl]]. exists d0.
    split; [apply List.in_cons; exact Hin|exact Hl].
Qed.

Lemma labels_hasnt_update : forall (hds hds':heap_defs) (a:trm_label) (y:var) (l:label),
  defs_update hds a y hds' ->
  labels_hasnt hds l ->
  labels_hasnt hds' l.
Proof.
  intros hds hds' a y l Hup. revert l. induction Hup; intros l Hl.
  - unfold labels_hasnt in *. cbn in *.
    destruct (classic (label_trm a = l)) as [E|NE].
    + rewrite (If_l (P:=label_trm a = l) _ _ E) in Hl. discriminate.
    + rewrite (If_r (P:=label_trm a = l) _ _ NE) in Hl.
      rewrite (If_r (P:=label_trm a = l) _ _ NE). exact Hl.
  - unfold labels_hasnt in *. cbn in *.
    destruct (classic (label_of d = l)) as [E|NE].
    + rewrite (If_l (P:=label_of d = l) _ _ E) in Hl. discriminate.
    + rewrite (If_r (P:=label_of d = l) _ _ NE) in Hl.
      rewrite (If_r (P:=label_of d = l) _ _ NE).
      eapply IHHup. exact Hl.
Qed.

Lemma ty_heap_defs_update : forall (G:ctx) (hds:heap_defs) (T:typ),
  G ⊢ hds ∶ T ->
  forall (a:trm_label) (y:var) (hds':heap_defs),
    defs_update hds a y hds' ->
    forall (Tf:typ),
      record_has T (dec_trm a Tf Tf) ->
      G ⊢ trm_var (avar_f y) ∶ Tf ->
      G ⊢ hds' ∶ T.
Proof.
  intros G hds T Hds. induction Hds; intros a y hds' Hup Tf Hrh Hy.
  - inversion Hup; subst.
    + assert (HeqD : D = dec_trm a Tf Tf) by
        (symmetry; eapply record_has_rcd_inv; eassumption).
      subst D. eapply ty_defs_one. eapply ty_heap_def_trm_some. exact Hy.
    + match goal with
      | Hx : defs_update nil _ _ _ |- _ => inversion Hx
      end.
  - inversion Hup; subst.
    + (* head updated: d = heap_def_trm a o *)
      assert (HeqD : D = dec_trm a Tf Tf).
      { destruct (@record_has_and_inv T (typ_rcd D) (dec_trm a Tf Tf) Hrh) as [HinTs|HinR].
        - destruct (ty_heap_defs_correspond H) as [ls [_ [_ Hbwd]]].
          destruct (Hbwd (dec_trm a Tf Tf) HinTs) as [d0 [Hin0 Heq0]].
          exfalso. eapply (labels_hasnt_sound H1 d0 Hin0).
          rewrite <- Heq0. reflexivity.
        - symmetry. eapply record_has_rcd_inv. eassumption. }
      subst D. eapply ty_defs_cons.
      * exact H.
      * eapply ty_heap_def_trm_some. exact Hy.
      * simpl. exact H1.
    + (* update in the tail *)
      assert (Htail : defs_update ds a y hds'0) by
        (match goal with Hx : defs_update ds _ _ hds'0 |- _ => exact Hx end).
      eapply ty_defs_cons.
      * eapply IHHds; [exact Htail| |exact Hy].
        destruct (@record_has_and_inv T (typ_rcd D) (dec_trm a Tf Tf) Hrh) as [HinTs|HinR].
        -- exact HinTs.
        -- exfalso.
           assert (HeqD : D = dec_trm a Tf Tf) by
             (symmetry; eapply record_has_rcd_inv; eassumption).
           destruct (@defs_update_label_in ds hds'0 a y Htail) as [d0 [Hin0 Hl0]].
           assert (Hld : label_of d = label_of D) by
             (symmetry; exact (@label_of_ty_heap_def Gamma d D H0)).
           assert (Hla : label_of D = label_trm a) by (rewrite HeqD; reflexivity).
           assert (Heq1 : label_of d0 = label_of d) by (rewrite Hl0, Hld, Hla; reflexivity).
           eapply (labels_hasnt_sound H1 d0 Hin0). exact Heq1.
      * exact H0.
      * eapply labels_hasnt_update; eassumption.
Qed.

Lemma ty_stack_let_inv : forall (G:ctx) (D:init_ctx) (Es:list eff_ctx)
    (t0:trm) (Fs:stack) (S:typ) (i:init_typ) (effs:list effects) (U:typ),
  ty_stack G D Es (frame_let t0 :: Fs) S i effs U ->
  exists ℰ ℰs L T i' effs0 effss effs',
    Es = ℰ :: ℰs /\
    effs = ((effs' ++ effs0) :: effss)%list /\
    ty_stack G D (ℰ :: ℰs) Fs T i' (effs0 :: effss) U /\
    (forall x, x \notin L -> G & x ~ S ⊢ open x t0 ∶ T) /\
    (forall x, x \notin L ->
       G & x ~ S ⸴ D & x ~ i ⸴ dom ℰ \u \{x} ⊢i open x t0 ∶ i') /\
    (forall x, x \notin L -> ⊢e open x t0 ∶ effs').
Proof.
  intros. inversion H; subst.
  eexists _, _, _, _, _, _, _, _. repeat split; try reflexivity; eassumption.
Qed.

Lemma ty_stack_ret_inv : forall (G:ctx) (D:init_ctx) (Es:list eff_ctx)
    (x0:var) (Fs:stack) (S:typ) (i:init_typ) (effs:list effects) (U:typ),
  ty_stack G D Es (frame_ret x0 :: Fs) S i effs U ->
  (exists ℰ ℰs T effs0 effss,
     Es = ℰ :: ℰs /\
     effs = (effs0 :: effss) /\
     ty_stack G D (ℰ :: ℰs) Fs T free (effs0 :: effss) U /\
     G ⊢ trm_var (avar_f x0) ∶ T /\
     G ⸴ D ⸴ dom ℰ ⊢i trm_var (avar_f x0) ∶ free)
  \/
  (exists ℰ ℰs T effss,
     Es = ℰ :: ℰs /\
     effs = (nil :: effss) /\
     ty_stack G D ℰs Fs T committed effss U /\
     G ⊢ trm_var (avar_f x0) ∶ T /\
     G ⸴ D ⸴ dom ℰ ⊢i trm_var (avar_f x0) ∶ free).
Proof.
  intros. inversion H; subst.
  - left. eexists _, _, _, _, _. repeat split; try reflexivity; eassumption.
  - right. eexists _, _, _, _. repeat split; try reflexivity; eassumption.
Qed.

Lemma heap_correspond_binds : forall (G:ctx) (Sigma:heap) (x:var) (T:typ),
  heap_correspond G Sigma -> binds x T G ->
  exists itm, binds x itm Sigma.
Proof.
  intros G Sigma x T [Hdom _] Hb.
  assert (Hin : x \in dom Sigma).
  { rewrite <- Hdom. eapply binds_in_dom; eexact Hb. }
  eapply dom_binds_exists. exact Hin.
Qed.

Lemma heap_correspond_binds_rev : forall (G:ctx) (Sigma:heap) (x:var) (itm:item),
  heap_correspond G Sigma -> binds x itm Sigma ->
  exists T, binds x T G.
Proof.
  intros G Sigma x itm [Hdom _] Hb.
  assert (Hin : x \in dom G).
  { rewrite Hdom. eapply binds_in_dom; eexact Hb. }
  eapply dom_binds_exists. exact Hin.
Qed.

Lemma ty_config_inv : forall (G:ctx) (D:init_ctx) (Es:list eff_ctx) (effss:list effects)
    (t:trm) (s:stack) (Sigma:heap) (U:typ),
  ty_config G D Es effss (t ; s ; Sigma) U ->
  exists ℰ ℰs Fs T i effs effs' effss0,
    Es = ℰ :: ℰs /\
    effss = ((effs' ++ effs) :: effss0)%list /\
    inert G /\
    inert_inits D /\
    heap_correspond G Sigma /\
    free_sub_heaps G D Sigma (ℰ :: ℰs) /\
    ty_stack G D (ℰ :: ℰs) Fs T i (effs :: effss0) U /\
    G ⊢ t ∶ T /\
    ⊢e t ∶ effs' /\
    G ⸴ D ⸴ dom ℰ ⊢i t ∶ i /\
    eff_ctx_corr (ℰ :: ℰs) (List.app effs' effs :: effss0).
Proof.
  intros G D Es effss t s Sigma U H. inversion H; subst.
  eexists ℰ, ℰs, s, T, i, effs, effs', effss0. repeat split; try reflexivity; try eassumption; try (exact (proj1 H5)); try (exact (proj2 H5)).
Qed.

Lemma vars_of_avars_length : forall (xs:list var) (avs:avars),
  vars_of_avars xs avs -> List.length xs = List.length avs.
Proof.
  intros xs avs H. induction H; simpl; [reflexivity|f_equal; assumption].
Qed.

Lemma vars_of_avars_in : forall (xs:list var) (avs:avars) (x:var),
  vars_of_avars xs avs -> List.In (avar_f x) avs -> List.In x xs.
Proof.
  intros xs avs x H. induction H; intros Hin.
  - inversion Hin.
  - simpl in Hin. destruct Hin as [Heq|Hin].
    + injection Heq as Hxy. subst. apply List.in_eq.
    + apply List.in_cons. eapply IHvars_of_avars. exact Hin.
Qed.

Lemma eff_ctx_corr_length : forall (Es:list eff_ctx) (effss:list effects),
  eff_ctx_corr Es effss -> List.length Es = List.length effss.
Proof.
  intros Es effss H. induction H; simpl; [reflexivity|f_equal; assumption].
Qed.

Lemma binds_replace : forall (A:Type) (E1 E2:env A) (x0 z:var) (v v' itm:A),
  z <> x0 ->
  binds z itm (E1 & x0 ~ v & E2) ->
  binds z itm (E1 & x0 ~ v' & E2).
Proof.
  intros A E1 E2 x0 z v v' itm Hne Hb.
  destruct (LibEnv.binds_concat_inv Hb) as [H2|[Hnot H1]].
  - eapply LibEnv.binds_concat_right. exact H2.
  - eapply LibEnv.binds_concat_left.
    + eapply LibEnv.binds_push_neq.
      * eapply LibEnv.binds_push_neq_inv; [exact H1|exact Hne].
      * exact Hne.
    + exact Hnot.
Qed.

Lemma heap_correspond_update : forall (G:ctx) (Sigma1 Sigma2:heap) (x0:var) (T:typ)
    (hds hds':heap_defs) (a:trm_label) (y:var),
  x0 # Sigma2 ->
  heap_correspond G (Sigma1 & x0 ~ (item_obj T hds) & Sigma2) ->
  defs_update hds a y hds' ->
  G ⊢ hds' ∶ open x0 T ->
  heap_correspond G (Sigma1 & x0 ~ (item_obj T hds') & Sigma2).
Proof.
  intros G S1 S2 x0 T hds hds' a y Hfresh HC Hup Hty.
  destruct HC as [Hdom Hitem]. split.
  - rewrite Hdom. rewrite !LibEnv.dom_concat, !LibEnv.dom_single. reflexivity.
  - intros z Hz. pose proof (Hitem z Hz) as Hts.
    destruct (classic (z = x0)) as [->|Hne].
    + assert (Hbinds_old : binds x0 (item_obj T hds)
                             (S1 & x0 ~ item_obj T hds & S2)).
      { eapply LibEnv.binds_concat_left.
        - apply LibEnv.binds_push_eq.
        - exact Hfresh. }
      destruct (ty_item_s_obj_inv Hts Hbinds_old) as [Hbnd _].
      eapply ty_item_obj_s.
      * exact Hbnd.
      * eapply LibEnv.binds_concat_left.
        -- apply LibEnv.binds_push_eq.
        -- exact Hfresh.
      * exact Hty.
    + inversion Hts; subst.
      * eapply ty_item_lit_s.
        -- eassumption.
        -- eapply binds_replace; [exact Hne|eassumption].
        -- eassumption.
      * eapply ty_item_obj_s.
        -- eassumption.
        -- eapply binds_replace; [exact Hne|eassumption].
        -- eassumption.
Qed.

Lemma ty_stack_weaken_GD : forall (G:ctx) (D:init_ctx) (Es:list eff_ctx) (Fs:stack)
    (T:typ) (i:init_typ) (effs:list effects) (U:typ),
  ty_stack G D Es Fs T i effs U ->
  forall G' D', binds_extends G G' -> binds_extends D D' ->
    ty_stack G' D' Es Fs T i effs U.
Proof.
  intros G D Es Fs T i effs U H. induction H; intros G' D' HG HD.
  - eapply ty_stack_nil. eapply subtyp_binds_extends; eassumption.
  - eapply ty_stack_let with (L:=L).
    + eapply IHty_stack; eassumption.
    + intros x Hx. eapply ty_trm_binds_extends.
      * eapply H0; eassumption.
      * apply binds_extends_push. assumption.
    + intros x Hx. eapply init_binds_extends.
      * eapply H1; eassumption.
      * apply binds_extends_push. assumption.
      * apply binds_extends_push. assumption.
      * apply vs_subset_refl.
    + intros x Hx. eapply H2; eassumption.
  - eapply ty_stack_ret_free with (T:=T).
    + eapply IHty_stack; eassumption.
    + eapply ty_trm_binds_extends; [eassumption|assumption].
    + eapply init_binds_extends; [eassumption|assumption|assumption|apply vs_subset_refl].
  - eapply ty_stack_ret_committed with (T:=T).
    + eapply IHty_stack; eassumption.
    + eapply ty_trm_binds_extends; [eassumption|assumption].
    + eapply init_binds_extends; [eassumption|assumption|assumption|apply vs_subset_refl].
Qed.

Lemma ty_stack_weaken_head : forall (G:ctx) (D:init_ctx) (Es0:list eff_ctx)
    (Fs:stack) (T:typ) (i:init_typ) (effs:list effects) (U:typ),
  ty_stack G D Es0 Fs T i effs U ->
  forall (Es:list eff_ctx) (ℰ:eff_ctx), Es0 = ℰ :: Es ->
  forall G' D' ℰ',
    binds_extends G G' -> binds_extends D D' ->
    vs_subset (dom ℰ) (dom ℰ') ->
    ty_stack G' D' (ℰ' :: Es) Fs T i effs U.
Proof.
  intros G D Es0 Fs T i effs U H.
  induction H; intros Es E Heq G' D' ℰ' HG HD Hsub.
  - inversion Heq; subst. eapply ty_stack_nil.
    eapply subtyp_binds_extends; eassumption.
  - inversion Heq; subst.
    eapply ty_stack_let with (L:=L).
    + eapply IHty_stack; [reflexivity|exact HG|exact HD|exact Hsub].
    + intros x Hx. eapply ty_trm_binds_extends.
      * eapply H0; eassumption.
      * apply binds_extends_push. assumption.
    + intros x Hx. eapply init_binds_extends.
      * eapply H1; eassumption.
      * apply binds_extends_push. assumption.
      * apply binds_extends_push. assumption.
      * intros y Hy. rewrite in_union in Hy. rewrite in_union.
        destruct Hy as [Hy|Hy].
        -- left. eapply Hsub; eassumption.
        -- right. exact Hy.
    + intros x Hx. eapply H2; eassumption.
  - inversion Heq; subst.
    eapply ty_stack_ret_free with (T:=T).
    + eapply IHty_stack; [reflexivity|exact HG|exact HD|exact Hsub].
    + eapply ty_trm_binds_extends; [eassumption|assumption].
    + eapply init_binds_extends.
      * eassumption.
      * assumption.
      * assumption.
      * exact Hsub.
  - inversion Heq; subst.
    eapply ty_stack_ret_committed with (T:=T).
    + eapply ty_stack_weaken_GD; [exact H|exact HG|exact HD].
    + eapply ty_trm_binds_extends; [eassumption|assumption].
    + eapply init_binds_extends.
      * eassumption.
      * assumption.
      * assumption.
      * exact Hsub.
Qed.

Lemma binds_drop_middle : forall (A:Type) (D1 D2:env A) (xm z:var) (v v0:A),
  z <> xm ->
  binds z v (D1 & xm ~ v0 & D2) ->
  binds z v (D1 & D2).
Proof.
  intros A D1 D2 xm z v v0 Hne Hb.
  destruct (LibEnv.binds_concat_inv Hb) as [H2|[Hnot H1]].
  - eapply LibEnv.binds_concat_right. exact H2.
  - eapply LibEnv.binds_concat_left.
    + destruct (LibEnv.binds_push_inv H1) as [[Heq _]|[_ H0]].
      * exfalso. apply Hne. exact Heq.
      * exact H0.
    + exact Hnot.
Qed.

Lemma in_vars_subst : forall (vs:vars) (xm ym z:var),
  z \in vs -> z <> xm -> z \in (subst_var xm ym vs).
Proof.
  intros vs xm ym z Hin Hne.
  unfold subst_var, VarsSubstVar. cbn.
  destruct (classic (xm \in vs)) as [Hx|Hx].
  - rewrite (If_l (P:=xm \in vs) _ _ Hx).
    rewrite in_union. left. rewrite FsetImpl.in_remove. split; [exact Hin|].
    intro E. apply Hne. rewrite in_singleton in E. exact E.
  - rewrite (If_r (P:=xm \in vs) _ _ Hx). exact Hin.
Qed.

Lemma in_vars_subst_self : forall (vs:vars) (xm ym:var),
  xm \in vs -> ym \in (subst_var xm ym vs).
Proof.
  intros vs xm ym Hx. unfold subst_var, VarsSubstVar. cbn.
  rewrite (If_l (P:=xm \in vs) _ _ Hx).
  rewrite in_union. right. apply in_singleton_self.
Qed.

Lemma subst_vars_union_singleton : forall (vs:vars) (xm ym z:var),
  z <> xm ->
  subst_var xm ym (vs \u \{z}) = (subst_var xm ym vs) \u \{z}.
Proof.
  intros vs xm ym z Hne.
  unfold subst_var, VarsSubstVar. cbn.
  destruct (classic (xm \in vs \u \{z})) as [Hx|Hx].
  - destruct (classic (xm \in vs)) as [Hv|Hv].
    + rewrite (If_l (P:=xm \in vs \u \{z}) _ _ Hx).
      rewrite (If_l (P:=xm \in vs) _ _ Hv).
      apply fset_extens.
      * intros a Ha. rewrite in_union in Ha. destruct Ha as [Ha|Ha].
        -- rewrite FsetImpl.in_remove in Ha. destruct Ha as [Hin Hnot].
           rewrite in_union in Hin. destruct Hin as [Hvs|Hz].
           ++ rewrite in_union. left. rewrite in_union. left.
              rewrite FsetImpl.in_remove. split; [exact Hvs|exact Hnot].
           ++ rewrite in_singleton in Hz. subst a. rewrite in_union. right.
              apply in_singleton_self.
        -- rewrite in_singleton in Ha. subst a. rewrite in_union. left.
           rewrite in_union. right. apply in_singleton_self.
      * intros a Ha. rewrite in_union in Ha. destruct Ha as [Ha|Ha].
        -- rewrite in_union in Ha. destruct Ha as [Ha|Ha].
           ++ rewrite FsetImpl.in_remove in Ha. destruct Ha as [Hvs Hnot].
              rewrite in_union. left. rewrite FsetImpl.in_remove. split.
              ** rewrite in_union. left. exact Hvs.
              ** exact Hnot.
           ++ rewrite in_singleton in Ha. subst a. rewrite in_union. right.
              apply in_singleton_self.
        -- rewrite in_singleton in Ha. subst a. rewrite in_union. left.
           rewrite FsetImpl.in_remove. split.
           ++ rewrite in_union. right. apply in_singleton_self.
           ++ intro E. apply Hne. rewrite in_singleton in E. exact E.
    + rewrite in_union in Hx. destruct Hx as [Hx|Hx].
      * exfalso. apply Hv. exact Hx.
      * rewrite in_singleton in Hx. subst z. exfalso. apply Hne. reflexivity.
  - assert (Hv : ~ xm \in vs) by (intro H; apply Hx; rewrite in_union; left; exact H).
    rewrite (If_r (P:=xm \in vs \u \{z}) _ _ Hx).
    rewrite (If_r (P:=xm \in vs) _ _ Hv). reflexivity.
Qed.

Lemma init_var_committed_split : forall (D1 D2:init_ctx) (xm:var),
  xm # D2 -> binds xm committed (D1 & xm ~ committed & D2).
Proof.
  intros D1 D2 xm Hnot.
  eapply LibEnv.binds_concat_left.
  - apply LibEnv.binds_push_eq.
  - exact Hnot.
Qed.

Lemma init_var_subst : forall (D1 D2:init_ctx) (vs:vars) (xm ym x:var) (i:init_typ),
  xm # D2 ->
  binds ym committed (D1 & D2) ->
  init_var (D1 & xm ~ committed & D2) vs x i ->
  init_var (D1 & D2) (subst_var xm ym vs) (x \[xm -> ym]) i.
Proof.
  intros D1 D2 vs xm ym x i HxD Hbinds Hin.
  remember (D1 & xm ~ committed & D2) as Delta eqn:Heq.
  induction Hin.
  - (* commit *)
    subst Delta.
    destruct (classic (x = xm)) as [->|Hne].
    + rewrite (@subst_if_eq xm ym). apply init_var_commit.
      exact Hbinds.
    + rewrite (@subst_if_neq xm ym x Hne). apply init_var_commit.
      eapply (@binds_drop_middle init_typ D1 D2 xm x committed committed);
        [exact Hne|exact H].
  - (* free *)
    subst Delta.
    destruct (classic (x = xm)) as [->|Hne].
    + exfalso.
      pose proof (@init_var_committed_split D1 D2 xm HxD) as Hc.
      match goal with
      | Hb : binds xm free (D1 & xm ~ committed & D2) |- _ =>
          pose proof (@LibEnv.binds_functional init_typ xm committed free
                        (D1 & xm ~ committed & D2) Hc Hb) as HeqF
      end.
      discriminate HeqF.
    + rewrite (@subst_if_neq xm ym x Hne). apply init_var_free.
      * eapply (@in_vars_subst vs xm ym x); [exact H|exact Hne].
      * eapply (@binds_drop_middle init_typ D1 D2 xm x free committed);
          [exact Hne|].
        match goal with
        | Hb : binds x free (D1 & xm ~ committed & D2) |- _ => exact Hb
        end.
  - (* unspec *)
    subst Delta.
    destruct (classic (x = xm)) as [->|Hne].
    + exfalso.
      pose proof (@init_var_committed_split D1 D2 xm HxD) as Hc.
      match goal with
      | Hb : binds xm unspecified (D1 & xm ~ committed & D2) |- _ =>
          pose proof (@LibEnv.binds_functional init_typ xm committed unspecified
                        (D1 & xm ~ committed & D2) Hc Hb) as HeqU
      end.
      discriminate HeqU.
    + rewrite (@subst_if_neq xm ym x Hne). apply init_var_unspec.
      * eapply (@in_vars_subst vs xm ym x); [exact H|exact Hne].
      * eapply (@binds_drop_middle init_typ D1 D2 xm x unspecified committed);
          [exact Hne|].
        match goal with
        | Hb : binds x unspecified (D1 & xm ~ committed & D2) |- _ => exact Hb
        end.
  - (* sub *)
    eapply init_var_sub.
    + apply IHHin. exact Heq.
    + exact H.
Qed.

Lemma ty_all_intro_open : forall (L:fset var) (G:ctx) (S U:typ) (t:trm) (a:var),
  (forall x, x \notin L -> G & x ~ S ⊢ open x t ∶ open x U) ->
  G ⊢ trm_var (avar_f a) ∶ S ->
  G ⊢ open a t ∶ open a U.
Proof.
  intros L G S U t a Hbody Ha.
  destruct (@var_fresh ((((L \u fv_env G) \u fv t) \u fv U) \u fv S)) as [x Hx].
  pose proof (notin_union_r1 Hx) as Hx1.
  pose proof (notin_union_r1 Hx1) as Hx2.
  pose proof (notin_union_r1 Hx2) as Hx3.
  pose proof (notin_union_r1 Hx3) as HxL.
  pose proof (notin_union_r2 Hx3) as HxG.
  pose proof (notin_union_r2 Hx2) as Hxt.
  pose proof (notin_union_r2 Hx1) as HxU.
  pose proof (notin_union_r2 Hx) as HxS.
  assert (Hty : G & x ~ S ⊢ open x t ∶ open x U) by (apply Hbody; exact HxL).
  assert (Hpre : G & subst_env x a empty ⊢ trm_var (avar_f a) ∶ subst_var x a S).
  { rewrite (@fv_subst_typ S x a HxS).
    rewrite map_empty. rewrite concat_empty_r. exact Ha. }
  assert (Hty' : G & x ~ S & empty ⊢ open x t ∶ open x U).
  { rewrite concat_empty_r. exact Hty. }
  assert (Hxempty : x # (empty:ctx)) by (rewrite dom_empty; apply notin_empty).
  pose proof (@ty_trm_subst G empty x a S (open x t) (open x U)
                Hty' Hxempty HxG Hpre) as Hres.
  rewrite map_empty in Hres. rewrite concat_empty_r in Hres.
  rewrite (@subst_intro_trm t x a 0 Hxt).
  rewrite (@subst_intro_typ U x a 0 HxU).
  exact Hres.
Qed.

Unset Implicit Arguments.

Definition QcF (G:ctx) (D:init_ctx) (t:trm) : Prop :=
  forall G1 G2 D1 D2 xm ym Sm,
    G = G1 & xm ~ Sm & G2 ->
    D = D1 & xm ~ committed & D2 ->
    xm # G2 -> xm # D2 -> xm \notin fv_env G1 ->
    (G1 & subst_env xm ym G2 ⊢ trm_var (avar_f ym) ∶ subst_var xm ym Sm) ->
    binds ym committed (D1 & D2) ->
    G1 & subst_env xm ym G2 ⸴ D1 & D2 ⊢c subst_var xm ym t.

Definition QaF (G:ctx) (D:init_ctx) (avs:avars) : Prop :=
  forall G1 G2 D1 D2 xm ym Sm,
    G = G1 & xm ~ Sm & G2 ->
    D = D1 & xm ~ committed & D2 ->
    xm # G2 -> xm # D2 -> xm \notin fv_env G1 ->
    (G1 & subst_env xm ym G2 ⊢ trm_var (avar_f ym) ∶ subst_var xm ym Sm) ->
    binds ym committed (D1 & D2) ->
    G1 & subst_env xm ym G2 ⸴ D1 & D2 ⊢c subst_var xm ym avs.

Definition QlF (G:ctx) (D:init_ctx) (l:lit) : Prop :=
  forall G1 G2 D1 D2 xm ym Sm,
    G = G1 & xm ~ Sm & G2 ->
    D = D1 & xm ~ committed & D2 ->
    xm # G2 -> xm # D2 -> xm \notin fv_env G1 ->
    (G1 & subst_env xm ym G2 ⊢ trm_var (avar_f ym) ∶ subst_var xm ym Sm) ->
    binds ym committed (D1 & D2) ->
    G1 & subst_env xm ym G2 ⸴ D1 & D2 ⊢c subst_var xm ym l.

Definition QiF (G:ctx) (D:init_ctx) (vs:vars) (t:trm) (i:init_typ) : Prop :=
  forall G1 G2 D1 D2 xm ym Sm,
    G = G1 & xm ~ Sm & G2 ->
    D = D1 & xm ~ committed & D2 ->
    xm # G2 -> xm # D2 -> xm \notin fv_env G1 ->
    (G1 & subst_env xm ym G2 ⊢ trm_var (avar_f ym) ∶ subst_var xm ym Sm) ->
    binds ym committed (D1 & D2) ->
    G1 & subst_env xm ym G2 ⸴ D1 & D2 ⸴ subst_var xm ym vs
      ⊢i subst_var xm ym t ∶ i.

Definition QisF (G:ctx) (D:init_ctx) (vs:vars) (avs:avars) (is':inits) : Prop :=
  forall G1 G2 D1 D2 xm ym Sm,
    G = G1 & xm ~ Sm & G2 ->
    D = D1 & xm ~ committed & D2 ->
    xm # G2 -> xm # D2 -> xm \notin fv_env G1 ->
    (G1 & subst_env xm ym G2 ⊢ trm_var (avar_f ym) ∶ subst_var xm ym Sm) ->
    binds ym committed (D1 & D2) ->
    G1 & subst_env xm ym G2 ⸴ D1 & D2 ⸴ subst_var xm ym vs
      ⊢i subst_var xm ym avs :: is'.

Set Implicit Arguments.

(** * Helpers for the easy commit rules *)

Lemma sc_commit_var : forall (G1 G2:ctx) (D1 D2:init_ctx) (xm ym:var) (Sm:typ) (x:var),
  xm # D2 ->
  binds ym committed (D1 & D2) ->
  binds x committed (D1 & xm ~ committed & D2) ->
  G1 & subst_env xm ym G2 ⸴ D1 & D2 ⊢c subst_var xm ym (trm_var (avar_f x)).
Proof.
  intros G1 G2 D1 D2 xm ym Sm x HxD Hbinds Hb.
  simpl.
  destruct (classic (x = xm)) as [->|Hne].
  - rewrite (@subst_if_eq xm ym). apply commit_var. exact Hbinds.
  - rewrite (@subst_if_neq xm ym x Hne). apply commit_var.
    eapply (@binds_drop_middle init_typ D1 D2 xm x committed committed);
      [exact Hne|exact Hb].
Qed.

Lemma sc_commit_all_elim : forall (G1 G2:ctx) (D1 D2:init_ctx) (xm ym:var) (Sm:typ) (x z:var),
  QcF (G1 & xm ~ Sm & G2) (D1 & xm ~ committed & D2) (trm_var (avar_f x)) ->
  QcF (G1 & xm ~ Sm & G2) (D1 & xm ~ committed & D2) (trm_var (avar_f z)) ->
  xm # G2 -> xm # D2 -> xm \notin fv_env G1 ->
  (G1 & subst_env xm ym G2 ⊢ trm_var (avar_f ym) ∶ subst_var xm ym Sm) ->
  binds ym committed (D1 & D2) ->
  G1 & subst_env xm ym G2 ⸴ D1 & D2
    ⊢c subst_var xm ym (trm_app (avar_f x) (avar_f z)).
Proof.
  intros G1 G2 D1 D2 xm ym Sm x z Hx Hz HxG HxD Hfv Hpre Hbinds.
  unfold QcF in Hx, Hz. simpl. eapply commit_all_elim.
  - refine (Hx G1 G2 D1 D2 xm ym Sm _ _ _ _ _ _ _);
      [reflexivity|reflexivity|exact HxG|exact HxD|exact Hfv|exact Hpre|exact Hbinds].
  - refine (Hz G1 G2 D1 D2 xm ym Sm _ _ _ _ _ _ _);
      [reflexivity|reflexivity|exact HxG|exact HxD|exact Hfv|exact Hpre|exact Hbinds].
Qed.

Lemma sc_commit_new : forall (G1 G2:ctx) (D1 D2:init_ctx) (xm ym:var) (Sm:typ)
    (x:var) (avs:avars) (Ts:typs) (is':inits) (T:typ),
  QcF (G1 & xm ~ Sm & G2) (D1 & xm ~ committed & D2) (trm_var (avar_f x)) ->
  QaF (G1 & xm ~ Sm & G2) (D1 & xm ~ committed & D2) avs ->
  (G1 & xm ~ Sm & G2 ⊢ trm_var (avar_f x) ∶ typ_con Ts is' T) ->
  all_comm_unspec is' ->
  xm # G2 -> xm # D2 -> xm \notin fv_env G1 ->
  (G1 & subst_env xm ym G2 ⊢ trm_var (avar_f ym) ∶ subst_var xm ym Sm) ->
  binds ym committed (D1 & D2) ->
  G1 & subst_env xm ym G2 ⸴ D1 & D2
    ⊢c subst_var xm ym (trm_new (avar_f x) avs).
Proof.
  intros G1 G2 D1 D2 xm ym Sm x avs Ts is' T Hx Havs Hty Hacu HxG HxD Hfv Hpre Hbinds.
  unfold QcF in Hx. unfold QaF in Havs. simpl. eapply commit_new.
  - eapply Hx; [reflexivity|reflexivity|exact HxG|exact HxD|exact Hfv|exact Hpre|exact Hbinds].
  - pose proof (@ty_trm_subst G1 G2 xm ym Sm (trm_var (avar_f x))
                  (typ_con Ts is' T) Hty HxG Hfv Hpre) as Hty'.
    simpl in Hty'. exact Hty'.
  - exact Hacu.
  - refine (Havs G1 G2 D1 D2 xm ym Sm _ _ _ _ _ _ _);
      [reflexivity|reflexivity|exact HxG|exact HxD|exact Hfv|exact Hpre|exact Hbinds].
Qed.

Lemma sc_commit_rcd_elim : forall (G1 G2:ctx) (D1 D2:init_ctx) (xm ym:var) (Sm:typ)
    (x:var) (a:trm_label),
  QcF (G1 & xm ~ Sm & G2) (D1 & xm ~ committed & D2) (trm_var (avar_f x)) ->
  xm # G2 -> xm # D2 -> xm \notin fv_env G1 ->
  (G1 & subst_env xm ym G2 ⊢ trm_var (avar_f ym) ∶ subst_var xm ym Sm) ->
  binds ym committed (D1 & D2) ->
  G1 & subst_env xm ym G2 ⸴ D1 & D2
    ⊢c subst_var xm ym (trm_sel (avar_f x) a).
Proof.
  intros G1 G2 D1 D2 xm ym Sm x a Hx HxG HxD Hfv Hpre Hbinds.
  unfold QcF in Hx. simpl. eapply commit_rcd_elim.
  eapply Hx; [reflexivity|reflexivity|exact HxG|exact HxD|exact Hfv|exact Hpre|exact Hbinds].
Qed.

Lemma sc_commit_fld_asn : forall (G1 G2:ctx) (D1 D2:init_ctx) (xm ym:var) (Sm:typ)
    (x y:var) (a:trm_label),
  QcF (G1 & xm ~ Sm & G2) (D1 & xm ~ committed & D2) (trm_var (avar_f x)) ->
  QcF (G1 & xm ~ Sm & G2) (D1 & xm ~ committed & D2) (trm_var (avar_f y)) ->
  xm # G2 -> xm # D2 -> xm \notin fv_env G1 ->
  (G1 & subst_env xm ym G2 ⊢ trm_var (avar_f ym) ∶ subst_var xm ym Sm) ->
  binds ym committed (D1 & D2) ->
  G1 & subst_env xm ym G2 ⸴ D1 & D2
    ⊢c subst_var xm ym (trm_asn (avar_f x) a (avar_f y)).
Proof.
  intros G1 G2 D1 D2 xm ym Sm x y a Hx Hy HxG HxD Hfv Hpre Hbinds.
  unfold QcF in Hx, Hy. simpl. eapply (@commit_fld_asn _ _ _ unspecified _ _).
  - refine (Hx G1 G2 D1 D2 xm ym Sm _ _ _ _ _ _ _);
      [reflexivity|reflexivity|exact HxG|exact HxD|exact Hfv|exact Hpre|exact Hbinds].
  - refine (Hy G1 G2 D1 D2 xm ym Sm _ _ _ _ _ _ _);
      [reflexivity|reflexivity|exact HxG|exact HxD|exact Hfv|exact Hpre|exact Hbinds].
Qed.

Lemma sc_commit_avars_nil : forall (G1 G2:ctx) (D1 D2:init_ctx) (xm ym:var) (Sm:typ),
  G1 & subst_env xm ym G2 ⸴ D1 & D2 ⊢c subst_var xm ym (@nil avar).
Proof. intros. simpl. apply committed_nil. Qed.

Lemma sc_commit_avars_cons : forall (G1 G2:ctx) (D1 D2:init_ctx) (xm ym:var) (Sm:typ)
    (x:var) (avs:avars),
  QcF (G1 & xm ~ Sm & G2) (D1 & xm ~ committed & D2) (trm_var (avar_f x)) ->
  QaF (G1 & xm ~ Sm & G2) (D1 & xm ~ committed & D2) avs ->
  xm # G2 -> xm # D2 -> xm \notin fv_env G1 ->
  (G1 & subst_env xm ym G2 ⊢ trm_var (avar_f ym) ∶ subst_var xm ym Sm) ->
  binds ym committed (D1 & D2) ->
  G1 & subst_env xm ym G2 ⸴ D1 & D2
    ⊢c subst_var xm ym (cons (avar_f x) avs).
Proof.
  intros G1 G2 D1 D2 xm ym Sm x avs Hx Havs HxG HxD Hfv Hpre Hbinds.
  unfold QcF in Hx. unfold QaF in Havs. simpl. eapply committed_cons.
  - refine (Hx G1 G2 D1 D2 xm ym Sm _ _ _ _ _ _ _);
      [reflexivity|reflexivity|exact HxG|exact HxD|exact Hfv|exact Hpre|exact Hbinds].
  - refine (Havs G1 G2 D1 D2 xm ym Sm _ _ _ _ _ _ _);
      [reflexivity|reflexivity|exact HxG|exact HxD|exact Hfv|exact Hpre|exact Hbinds].
Qed.

(** * Helpers for the easy init rules *)

Lemma si_init_var_binds : forall (G1 G2:ctx) (D1 D2:init_ctx) (xm ym:var) (Sm:typ)
    (vs:vars) (x:var) (i:init_typ),
  xm # D2 ->
  binds ym committed (D1 & D2) ->
  init_var (D1 & xm ~ committed & D2) vs x i ->
  G1 & subst_env xm ym G2 ⸴ D1 & D2 ⸴ subst_var xm ym vs
    ⊢i subst_var xm ym (trm_var (avar_f x)) ∶ i.
Proof.
  intros G1 G2 D1 D2 xm ym Sm vs x i HxD Hbinds Hin.
  simpl. apply init_var_binds.
  eapply (@init_var_subst D1 D2 vs xm ym x i); eassumption.
Qed.

Lemma si_init_commit : forall (G1 G2:ctx) (D1 D2:init_ctx) (xm ym:var) (Sm:typ)
    (vs:vars) (t:trm),
  QcF (G1 & xm ~ Sm & G2) (D1 & xm ~ committed & D2) t ->
  xm # G2 -> xm # D2 -> xm \notin fv_env G1 ->
  (G1 & subst_env xm ym G2 ⊢ trm_var (avar_f ym) ∶ subst_var xm ym Sm) ->
  binds ym committed (D1 & D2) ->
  G1 & subst_env xm ym G2 ⸴ D1 & D2 ⸴ subst_var xm ym vs
    ⊢i subst_var xm ym t ∶ committed.
Proof.
  intros G1 G2 D1 D2 xm ym Sm vs t Ht HxG HxD Hfv Hpre Hbinds.
  unfold QcF in Ht. simpl. apply init_commit.
  refine (Ht G1 G2 D1 D2 xm ym Sm _ _ _ _ _ _ _);
    [reflexivity|reflexivity|exact HxG|exact HxD|exact Hfv|exact Hpre|exact Hbinds].
Qed.

Lemma si_init_new_free : forall (G1 G2:ctx) (D1 D2:init_ctx) (xm ym:var) (Sm:typ)
    (vs:vars) (x:var) (avs:avars) (Ts:typs) (is':inits) (T:typ),
  QcF (G1 & xm ~ Sm & G2) (D1 & xm ~ committed & D2) (trm_var (avar_f x)) ->
  QisF (G1 & xm ~ Sm & G2) (D1 & xm ~ committed & D2) vs avs is' ->
  (G1 & xm ~ Sm & G2 ⊢ trm_var (avar_f x) ∶ typ_con Ts is' T) ->
  xm # G2 -> xm # D2 -> xm \notin fv_env G1 ->
  (G1 & subst_env xm ym G2 ⊢ trm_var (avar_f ym) ∶ subst_var xm ym Sm) ->
  binds ym committed (D1 & D2) ->
  G1 & subst_env xm ym G2 ⸴ D1 & D2 ⸴ subst_var xm ym vs
    ⊢i subst_var xm ym (trm_new (avar_f x) avs) ∶ free.
Proof.
  intros G1 G2 D1 D2 xm ym Sm vs x avs Ts is' T Hx Havs Hty HxG HxD Hfv Hpre Hbinds.
  unfold QcF in Hx. unfold QisF in Havs. simpl. eapply init_new_free.
  - refine (Hx G1 G2 D1 D2 xm ym Sm _ _ _ _ _ _ _);
      [reflexivity|reflexivity|exact HxG|exact HxD|exact Hfv|exact Hpre|exact Hbinds].
  - pose proof (@ty_trm_subst G1 G2 xm ym Sm (trm_var (avar_f x))
                  (typ_con Ts is' T) Hty HxG Hfv Hpre) as Hty'.
    simpl in Hty'. exact Hty'.
  - refine (Havs G1 G2 D1 D2 xm ym Sm _ _ _ _ _ _ _);
      [reflexivity|reflexivity|exact HxG|exact HxD|exact Hfv|exact Hpre|exact Hbinds].
Qed.

Lemma si_init_fld_asn_ac : forall (G1 G2:ctx) (D1 D2:init_ctx) (xm ym:var) (Sm:typ)
    (vs:vars) (x:var) (i:init_typ) (y:var) (a:trm_label),
  QiF (G1 & xm ~ Sm & G2) (D1 & xm ~ committed & D2) vs (trm_var (avar_f x)) i ->
  QiF (G1 & xm ~ Sm & G2) (D1 & xm ~ committed & D2) vs (trm_var (avar_f y)) committed ->
  xm # G2 -> xm # D2 -> xm \notin fv_env G1 ->
  (G1 & subst_env xm ym G2 ⊢ trm_var (avar_f ym) ∶ subst_var xm ym Sm) ->
  binds ym committed (D1 & D2) ->
  G1 & subst_env xm ym G2 ⸴ D1 & D2 ⸴ subst_var xm ym vs
    ⊢i subst_var xm ym (trm_asn (avar_f x) a (avar_f y)) ∶ committed.
Proof.
  intros G1 G2 D1 D2 xm ym Sm vs x i y a Hx Hy HxG HxD Hfv Hpre Hbinds.
  unfold QiF in Hx, Hy. simpl. eapply init_fld_asn_ac.
  - refine (Hx G1 G2 D1 D2 xm ym Sm _ _ _ _ _ _ _);
      [reflexivity|reflexivity|exact HxG|exact HxD|exact Hfv|exact Hpre|exact Hbinds].
  - refine (Hy G1 G2 D1 D2 xm ym Sm _ _ _ _ _ _ _);
      [reflexivity|reflexivity|exact HxG|exact HxD|exact Hfv|exact Hpre|exact Hbinds].
Qed.

Lemma si_init_fld_asn_ff : forall (G1 G2:ctx) (D1 D2:init_ctx) (xm ym:var) (Sm:typ)
    (vs:vars) (x:var) (y:var) (a:trm_label),
  QiF (G1 & xm ~ Sm & G2) (D1 & xm ~ committed & D2) vs (trm_var (avar_f x)) free ->
  QiF (G1 & xm ~ Sm & G2) (D1 & xm ~ committed & D2) vs (trm_var (avar_f y)) free ->
  xm # G2 -> xm # D2 -> xm \notin fv_env G1 ->
  (G1 & subst_env xm ym G2 ⊢ trm_var (avar_f ym) ∶ subst_var xm ym Sm) ->
  binds ym committed (D1 & D2) ->
  G1 & subst_env xm ym G2 ⸴ D1 & D2 ⸴ subst_var xm ym vs
    ⊢i subst_var xm ym (trm_asn (avar_f x) a (avar_f y)) ∶ free.
Proof.
  intros G1 G2 D1 D2 xm ym Sm vs x y a Hx Hy HxG HxD Hfv Hpre Hbinds.
  unfold QiF in Hx, Hy. simpl. eapply init_fld_asn_ff.
  - refine (Hx G1 G2 D1 D2 xm ym Sm _ _ _ _ _ _ _);
      [reflexivity|reflexivity|exact HxG|exact HxD|exact Hfv|exact Hpre|exact Hbinds].
  - refine (Hy G1 G2 D1 D2 xm ym Sm _ _ _ _ _ _ _);
      [reflexivity|reflexivity|exact HxG|exact HxD|exact Hfv|exact Hpre|exact Hbinds].
Qed.

Lemma si_inits_nil : forall (G1 G2:ctx) (D1 D2:init_ctx) (xm ym:var) (Sm:typ) (vs:vars),
  G1 & subst_env xm ym G2 ⸴ D1 & D2 ⸴ subst_var xm ym vs
    ⊢i subst_var xm ym (@nil avar) :: (@nil init_typ).
Proof. intros. simpl. apply well_inits_nil. Qed.

Lemma si_inits_cons : forall (G1 G2:ctx) (D1 D2:init_ctx) (xm ym:var) (Sm:typ)
    (vs:vars) (x:var) (i:init_typ) (avs:avars) (is':inits),
  QiF (G1 & xm ~ Sm & G2) (D1 & xm ~ committed & D2) vs (trm_var (avar_f x)) i ->
  QisF (G1 & xm ~ Sm & G2) (D1 & xm ~ committed & D2) vs avs is' ->
  xm # G2 -> xm # D2 -> xm \notin fv_env G1 ->
  (G1 & subst_env xm ym G2 ⊢ trm_var (avar_f ym) ∶ subst_var xm ym Sm) ->
  binds ym committed (D1 & D2) ->
  G1 & subst_env xm ym G2 ⸴ D1 & D2 ⸴ subst_var xm ym vs
    ⊢i subst_var xm ym (cons (avar_f x) avs) :: (cons i is').
Proof.
  intros G1 G2 D1 D2 xm ym Sm vs x i avs is' Hx Havs HxG HxD Hfv Hpre Hbinds.
  unfold QiF in Hx. unfold QisF in Havs. simpl. eapply well_inits_cons.
  - refine (Hx G1 G2 D1 D2 xm ym Sm _ _ _ _ _ _ _);
      [reflexivity|reflexivity|exact HxG|exact HxD|exact Hfv|exact Hpre|exact Hbinds].
  - refine (Havs G1 G2 D1 D2 xm ym Sm _ _ _ _ _ _ _);
      [reflexivity|reflexivity|exact HxG|exact HxD|exact Hfv|exact Hpre|exact Hbinds].
Qed.

(** * Helper for commit_let *)

Lemma sc_commit_let : forall (L:fset var) (G1 G2:ctx) (D1 D2:init_ctx)
    (xm ym:var) (Sm:typ) (t u:trm) (T:typ),
  QcF (G1 & xm ~ Sm & G2) (D1 & xm ~ committed & D2) t ->
  (forall z, z \notin L ->
     QcF ((G1 & xm ~ Sm & G2) & z ~ T)
         ((D1 & xm ~ committed & D2) & z ~ committed)
         (open z u)) ->
  xm # G2 -> xm # D2 -> xm \notin fv_env G1 ->
  (G1 & subst_env xm ym G2 ⊢ trm_var (avar_f ym) ∶ subst_var xm ym Sm) ->
  binds ym committed (D1 & D2) ->
  G1 & subst_env xm ym G2 ⸴ D1 & D2
    ⊢c subst_var xm ym (trm_let T t u).
Proof.
  intros L G1 G2 D1 D2 xm ym Sm t u T Ht Hu HxG HxD Hfv Hpre Hbinds.
  set (L' := ((L \u dom G1) \u dom G2) \u \{xm}).
  unfold QcF in Ht, Hu. simpl.
  eapply (@commit_let L' _ _ _ _ _).
  - refine (Ht G1 G2 D1 D2 xm ym Sm _ _ _ _ _ _ _);
      [reflexivity|reflexivity|exact HxG|exact HxD|exact Hfv|exact Hpre|exact Hbinds].
  - intros z Hz.
    assert (Hz1 : z \notin (L \u dom G1) \u dom G2) by
      (exact (@notin_union_r1 z ((L \u dom G1) \u dom G2) \{xm} Hz)).
    assert (HzL1 : z \notin L \u dom G1) by
      (exact (@notin_union_r1 z (L \u dom G1) (dom G2) Hz1)).
    assert (HzG2 : z \notin dom G2) by
      (exact (@notin_union_r2 z (L \u dom G1) (dom G2) Hz1)).
    assert (HzL : z \notin L) by
      (exact (@notin_union_r1 z L (dom G1) HzL1)).
    assert (HzG1 : z \notin dom G1) by
      (exact (@notin_union_r2 z L (dom G1) HzL1)).
    assert (Hzxm : z \notin \{xm}) by
      (exact (@notin_union_r2 z ((L \u dom G1) \u dom G2) \{xm} Hz)).
    assert (Hzx : z <> xm) by (exact (@notin_singleton_r z xm Hzxm)).
    assert (Hru : subst_var xm ym (open_rec 0 z u) = open_rec 0 z (subst_var xm ym u))
      by (apply subst_open_fresh_trm; auto).
    assert (HeqG : ((G1 & xm ~ Sm & G2) & z ~ T) = G1 & xm ~ Sm & (G2 & z ~ T)).
    { symmetry. apply concat_assoc. }
    assert (HeqD : ((D1 & xm ~ committed & D2) & z ~ committed)
                    = D1 & xm ~ committed & (D2 & z ~ committed)).
    { symmetry. apply concat_assoc. }
    assert (Hpre' : G1 & subst_env xm ym (G2 & z ~ T)
                    ⊢ trm_var (avar_f ym) ∶ subst_var xm ym Sm).
    { rewrite map_push. rewrite concat_assoc.
      eapply ty_trm_binds_extends; [exact Hpre|].
      apply binds_extends_push_fresh.
      rewrite dom_concat. apply notin_union_l; [exact HzG1|].
      rewrite dom_subst_env. exact HzG2. }
    assert (HxG' : xm # (G2 & z ~ T)).
    { rewrite dom_push. apply notin_union_l.
      - apply notin_singleton_l. intro E; apply Hzx; symmetry; exact E.
      - exact HxG. }
    assert (HxD' : xm # (D2 & z ~ committed)).
    { rewrite dom_push. apply notin_union_l.
      - apply notin_singleton_l. intro E; apply Hzx; symmetry; exact E.
      - exact HxD. }
    repeat rewrite <- concat_assoc.
    rewrite <- map_push.
    change (G1 & subst_env xm ym (G2 & z ~ T) ⸴ D1 & (D2 & z ~ committed)
            ⊢c open_rec 0 z (subst_var xm ym u)).
    rewrite <- Hru.
    assert (Hbinds' : binds ym committed (D1 & (D2 & z ~ committed))).
    { destruct (classic (ym = z)) as [Heq|Hne].
      - subst z. eapply LibEnv.binds_concat_right. apply LibEnv.binds_push_eq.
      - assert (Hb : binds ym committed ((D1 & D2) & z ~ committed)).
        { eapply LibEnv.binds_push_neq; [exact Hbinds|exact Hne]. }
        rewrite concat_assoc. exact Hb. }
    refine (Hu z HzL G1 (G2 & z ~ T) D1 (D2 & z ~ committed) xm ym Sm
              _ _ _ _ _ _ _);
      [exact HeqG|exact HeqD|exact HxG'|exact HxD'|exact Hfv|exact Hpre'|exact Hbinds'].
Qed.

Lemma def_eff_first : forall (ds:defs) (x y:var) (a:trm_label),
  (y,a) \in from_list (def_eff x ds) -> y = x.
Proof.
  intros ds. induction ds as [|d ds IH]; intros x y a Hin.
  - cbn in Hin. exfalso. exact (in_empty_inv Hin).
  - destruct d.
    + cbn in Hin. eapply IH; eassumption.
    + cbn in Hin. rewrite from_list_cons in Hin. rewrite in_union in Hin.
      destruct Hin as [Hin|Hin].
      * rewrite in_singleton in Hin. injection Hin as Hy _. subst y. reflexivity.
      * eapply IH; eassumption.
Qed.

Lemma def_eff_no_subst : forall (ds:defs) (x xm:var) (a:trm_label),
  xm <> x -> (xm,a) \notin from_list (def_eff x ds).
Proof.
  intros ds x xm a Hne Hin.
  pose proof (@def_eff_first ds x xm a Hin) as Heq. subst xm. exfalso. apply Hne. reflexivity.
Qed.

Lemma eff_trm_subst_fresh : forall (t:trm) (effs:effects),
  eff_trm t effs ->
  forall (xm ym:var),
    (forall a, (xm,a) \notin from_list effs) ->
    eff_trm (subst_var xm ym t) effs.
Proof.
  intros t effs H. induction H; intros xm ym Hno.
  - apply eff_ignore.
  - assert (Hne : x <> xm).
    { intro E. apply (Hno a).
      rewrite <- E. rewrite from_list_cons. rewrite in_union. left. apply in_singleton_self. }
    simpl. rewrite (@subst_if_neq xm ym x Hne). apply eff_fld_asn.
  - simpl. eapply eff_let with (L := (L \u \{xm}) \u \{ym}).
    + apply IHeff_trm.
      intros a Ha. apply (Hno a). rewrite from_list_app. rewrite in_union. left. exact Ha.
    + intros z Hz.
      assert (HzL : z \notin L).
      { apply notin_union_r1 in Hz as Hza. apply notin_union_r1 in Hza. exact Hza. }
      assert (Hzx : z <> xm).
      { apply notin_union_r1 in Hz as Hza. apply notin_union_r2 in Hza.
        intro E; subst z; apply Hza; apply in_singleton_self. }
      assert (Hru : subst_var xm ym (open_rec 0 z u) = open_rec 0 z (subst_var xm ym u))
        by (apply subst_open_fresh_trm; auto).
      change (eff_trm (open_rec 0 z (subst_var xm ym u)) eff2).
      rewrite <- Hru.
      apply H1; [exact HzL|].
      intros a Ha. apply (Hno a). rewrite from_list_app. rewrite in_union. right. exact Ha.
  - simpl. eapply eff_llit with (L := (L \u \{xm}) \u \{ym}).
    intros z Hz.
    assert (HzL : z \notin L).
    { apply notin_union_r1 in Hz as Hza. apply notin_union_r1 in Hza. exact Hza. }
    assert (Hzx : z <> xm).
    { apply notin_union_r1 in Hz as Hza. apply notin_union_r2 in Hza.
      intro E; subst z; apply Hza; apply in_singleton_self. }
    assert (Hru : subst_var xm ym (open_rec 0 z u) = open_rec 0 z (subst_var xm ym u))
      by (apply subst_open_fresh_trm; auto).
    change (eff_trm (open_rec 0 z (subst_var xm ym u)) eff).
    rewrite <- Hru.
    apply H0; [exact HzL|exact Hno].
Qed.

Lemma has_effs_subst_fresh : forall (t:trm) (effs:effects) (x y:var),
  has_effs t effs ->
  (forall a, (x,a) \notin from_list effs) ->
  has_effs (subst_var x y t) effs.
Proof.
  intros t effs x y [effs' [Heff Heq]] Hno.
  exists effs'. split; [|exact Heq].
  eapply eff_trm_subst_fresh; [exact Heff|].
  intros a Ha. apply (Hno a). rewrite Heq. exact Ha.
Qed.

Lemma def_eff_subst : forall (ds:defs) (xm ym:var) (z:var),
  def_eff z (subst_var xm ym ds) = def_eff z ds.
Proof.
  intros ds. induction ds as [|d ds IH]; intros xm ym z.
  - reflexivity.
  - destruct d; cbn.
    + change (def_eff z (subst_var xm ym ds) = def_eff z ds). exact (IH xm ym z).
    + f_equal. change (def_eff z (subst_var xm ym ds) = def_eff z ds). exact (IH xm ym z).
Qed.

Lemma vars_subst_notin : forall (vs:vars) (xm ym:var),
  xm \notin vs -> subst_var xm ym vs = vs.
Proof.
  intros vs xm ym Hx. unfold subst_var, VarsSubstVar. cbn.
  rewrite (If_r (P:=xm \in vs) _ _ Hx). reflexivity.
Qed.

Lemma sc_commit_llit : forall (L:fset var) (G1 G2:ctx) (D1 D2:init_ctx)
    (xm ym:var) (Sm:typ) (l:lit) (u:trm) (T:typ),
  QlF (G1 & xm ~ Sm & G2) (D1 & xm ~ committed & D2) l ->
  (forall z, z \notin L ->
     QcF ((G1 & xm ~ Sm & G2) & z ~ T)
         ((D1 & xm ~ committed & D2) & z ~ committed)
         (open z u)) ->
  xm # G2 -> xm # D2 -> xm \notin fv_env G1 ->
  (G1 & subst_env xm ym G2 ⊢ trm_var (avar_f ym) ∶ subst_var xm ym Sm) ->
  binds ym committed (D1 & D2) ->
  G1 & subst_env xm ym G2 ⸴ D1 & D2
    ⊢c subst_var xm ym (trm_lit T l u).
Proof.
  intros L G1 G2 D1 D2 xm ym Sm l u T Hl Hu HxG HxD Hfv Hpre Hbinds.
  set (L' := ((L \u dom G1) \u dom G2) \u \{xm}).
  unfold QlF in Hl. unfold QcF in Hu. simpl.
  eapply (@commit_llit L' _ _ _ _ _).
  - refine (Hl G1 G2 D1 D2 xm ym Sm _ _ _ _ _ _ _);
      [reflexivity|reflexivity|exact HxG|exact HxD|exact Hfv|exact Hpre|exact Hbinds].
  - intros z Hz.
    assert (Hz1 : z \notin (L \u dom G1) \u dom G2) by
      (exact (@notin_union_r1 z ((L \u dom G1) \u dom G2) \{xm} Hz)).
    assert (HzL1 : z \notin L \u dom G1) by
      (exact (@notin_union_r1 z (L \u dom G1) (dom G2) Hz1)).
    assert (HzG2 : z \notin dom G2) by
      (exact (@notin_union_r2 z (L \u dom G1) (dom G2) Hz1)).
    assert (HzL : z \notin L) by
      (exact (@notin_union_r1 z L (dom G1) HzL1)).
    assert (HzG1 : z \notin dom G1) by
      (exact (@notin_union_r2 z L (dom G1) HzL1)).
    assert (Hzxm : z \notin \{xm}) by
      (exact (@notin_union_r2 z ((L \u dom G1) \u dom G2) \{xm} Hz)).
    assert (Hzx : z <> xm) by (exact (@notin_singleton_r z xm Hzxm)).
    assert (Hru : subst_var xm ym (open_rec 0 z u) = open_rec 0 z (subst_var xm ym u))
      by (apply subst_open_fresh_trm; auto).
    assert (HeqG : ((G1 & xm ~ Sm & G2) & z ~ T) = G1 & xm ~ Sm & (G2 & z ~ T)).
    { symmetry. apply concat_assoc. }
    assert (HeqD : ((D1 & xm ~ committed & D2) & z ~ committed)
                    = D1 & xm ~ committed & (D2 & z ~ committed)).
    { symmetry. apply concat_assoc. }
    assert (Hpre' : G1 & subst_env xm ym (G2 & z ~ T)
                    ⊢ trm_var (avar_f ym) ∶ subst_var xm ym Sm).
    { rewrite map_push. rewrite concat_assoc.
      eapply ty_trm_binds_extends; [exact Hpre|].
      apply binds_extends_push_fresh.
      rewrite dom_concat. apply notin_union_l; [exact HzG1|].
      rewrite dom_subst_env. exact HzG2. }
    assert (HxG' : xm # (G2 & z ~ T)).
    { rewrite dom_push. apply notin_union_l.
      - apply notin_singleton_l. intro E; apply Hzx; symmetry; exact E.
      - exact HxG. }
    assert (HxD' : xm # (D2 & z ~ committed)).
    { rewrite dom_push. apply notin_union_l.
      - apply notin_singleton_l. intro E; apply Hzx; symmetry; exact E.
      - exact HxD. }
    repeat rewrite <- concat_assoc.
    rewrite <- map_push.
    change (G1 & subst_env xm ym (G2 & z ~ T) ⸴ D1 & (D2 & z ~ committed)
            ⊢c open_rec 0 z (subst_var xm ym u)).
    rewrite <- Hru.
    assert (Hbinds' : binds ym committed (D1 & (D2 & z ~ committed))).
    { destruct (classic (ym = z)) as [Heq|Hne].
      - subst z. eapply LibEnv.binds_concat_right. apply LibEnv.binds_push_eq.
      - assert (Hb : binds ym committed ((D1 & D2) & z ~ committed)).
        { eapply LibEnv.binds_push_neq; [exact Hbinds|exact Hne]. }
        rewrite concat_assoc. exact Hb. }
    refine (Hu z HzL G1 (G2 & z ~ T) D1 (D2 & z ~ committed) xm ym Sm
              _ _ _ _ _ _ _);
      [exact HeqG|exact HeqD|exact HxG'|exact HxD'|exact Hfv|exact Hpre'|exact Hbinds'].
Qed.

Lemma sc_commit_all_intro : forall (L:fset var) (G1 G2:ctx) (D1 D2:init_ctx)
    (xm ym:var) (Sm:typ) (T:typ) (t:trm),
  (forall z, z \notin L ->
     QcF ((G1 & xm ~ Sm & G2) & z ~ T)
         ((D1 & xm ~ committed & D2) & z ~ committed)
         (open z t)) ->
  xm # G2 -> xm # D2 -> xm \notin fv_env G1 ->
  (G1 & subst_env xm ym G2 ⊢ trm_var (avar_f ym) ∶ subst_var xm ym Sm) ->
  binds ym committed (D1 & D2) ->
  G1 & subst_env xm ym G2 ⸴ D1 & D2
    ⊢c subst_var xm ym (lit_fun T t).
Proof.
  intros L G1 G2 D1 D2 xm ym Sm T t Hu HxG HxD Hfv Hpre Hbinds.
  set (L' := ((L \u dom G1) \u dom G2) \u \{xm}).
  unfold QcF in Hu. simpl.
  eapply (@commit_all_intro L' _ _ _ _).
  intros z Hz.
  assert (Hz1 : z \notin (L \u dom G1) \u dom G2) by
    (exact (@notin_union_r1 z ((L \u dom G1) \u dom G2) \{xm} Hz)).
  assert (HzL1 : z \notin L \u dom G1) by
    (exact (@notin_union_r1 z (L \u dom G1) (dom G2) Hz1)).
  assert (HzG2 : z \notin dom G2) by
    (exact (@notin_union_r2 z (L \u dom G1) (dom G2) Hz1)).
  assert (HzL : z \notin L) by
    (exact (@notin_union_r1 z L (dom G1) HzL1)).
  assert (HzG1 : z \notin dom G1) by
    (exact (@notin_union_r2 z L (dom G1) HzL1)).
  assert (Hzxm : z \notin \{xm}) by
    (exact (@notin_union_r2 z ((L \u dom G1) \u dom G2) \{xm} Hz)).
  assert (Hzx : z <> xm) by (exact (@notin_singleton_r z xm Hzxm)).
  assert (Hru : subst_var xm ym (open_rec 0 z t) = open_rec 0 z (subst_var xm ym t))
    by (apply subst_open_fresh_trm; auto).
  assert (HeqG : ((G1 & xm ~ Sm & G2) & z ~ T) = G1 & xm ~ Sm & (G2 & z ~ T)).
  { symmetry. apply concat_assoc. }
  assert (HeqD : ((D1 & xm ~ committed & D2) & z ~ committed)
                  = D1 & xm ~ committed & (D2 & z ~ committed)).
  { symmetry. apply concat_assoc. }
  assert (Hpre' : G1 & subst_env xm ym (G2 & z ~ T)
                  ⊢ trm_var (avar_f ym) ∶ subst_var xm ym Sm).
  { rewrite map_push. rewrite concat_assoc.
    eapply ty_trm_binds_extends; [exact Hpre|].
    apply binds_extends_push_fresh.
    rewrite dom_concat. apply notin_union_l; [exact HzG1|].
    rewrite dom_subst_env. exact HzG2. }
  assert (HxG' : xm # (G2 & z ~ T)).
  { rewrite dom_push. apply notin_union_l.
    - apply notin_singleton_l. intro E; apply Hzx; symmetry; exact E.
    - exact HxG. }
  assert (HxD' : xm # (D2 & z ~ committed)).
  { rewrite dom_push. apply notin_union_l.
    - apply notin_singleton_l. intro E; apply Hzx; symmetry; exact E.
    - exact HxD. }
  repeat rewrite <- concat_assoc.
  rewrite <- map_push.
  change (G1 & subst_env xm ym (G2 & z ~ T) ⸴ D1 & (D2 & z ~ committed)
          ⊢c open_rec 0 z (subst_var xm ym t)).
  rewrite <- Hru.
  assert (Hbinds' : binds ym committed (D1 & (D2 & z ~ committed))).
  { destruct (classic (ym = z)) as [Heq|Hne].
    - subst z. eapply LibEnv.binds_concat_right. apply LibEnv.binds_push_eq.
    - assert (Hb : binds ym committed ((D1 & D2) & z ~ committed)).
      { eapply LibEnv.binds_push_neq; [exact Hbinds|exact Hne]. }
      rewrite concat_assoc. exact Hb. }
  refine (Hu z HzL G1 (G2 & z ~ T) D1 (D2 & z ~ committed) xm ym Sm
            _ _ _ _ _ _ _);
    [exact HeqG|exact HeqD|exact HxG'|exact HxD'|exact Hfv|exact Hpre'|exact Hbinds'].
Qed.

Lemma notin_from_list_intro : forall (ys:list var) (x:var),
  (forall y, List.In y ys -> y <> x) -> x \notin from_list ys.
Proof.
  intros ys x H Hin.
  rewrite in_from_list in Hin.
  exact (H x Hin eq_refl).
Qed.

Lemma dom_ys_tolist : forall (ys:list var) (Ts:typs),
  LibList.length ys = LibList.length (to_list Ts) ->
  dom (ys ~** to_list Ts) = from_list ys.
Proof.
  intros ys Ts Hlenxy.
  rewrite (@dom_singles typ (List.rev ys) (List.rev (to_list Ts))).
  - rewrite from_list_rev. reflexivity.
  - rewrite !LibList_length_List_rev. exact Hlenxy.
Qed.

Lemma dom_ys_inits : forall (ys:list var) (is':inits),
  List.length ys = List.length is' ->
  dom (ys ~** is') = from_list ys.
Proof.
  intros ys is' Hlenxy.
  rewrite (@dom_singles init_typ (List.rev ys) (List.rev is')).
  - rewrite from_list_rev. reflexivity.
  - rewrite !LibList_length_List_rev.
    rewrite !List_length_LibList_length in Hlenxy. exact Hlenxy.
Qed.

Lemma fresh_head_L : forall (L:fset var) (G1 G2:ctx) (xm ym:var) (n:nat) (x:var) (ys:list var),
  fresh ((((L \u dom G1) \u dom G2) \u \{xm}) \u \{ym}) (S n) (cons x ys) ->
  x \notin L /\ x \notin dom G1 /\ x \notin dom G2 /\ x <> xm /\ x <> ym.
Proof.
  intros L G1 G2 xm ym n x ys Hf.
  assert (Hx1 : x \notin (((L \u dom G1) \u dom G2) \u \{xm}) \u \{ym})
    by (eapply fresh_cons_head; exact Hf).
  assert (Hx2 : x \notin ((L \u dom G1) \u dom G2) \u \{xm})
    by (exact (@notin_union_r1 x (((L \u dom G1) \u dom G2) \u \{xm}) \{ym} Hx1)).
  assert (Hx3 : x \notin (L \u dom G1) \u dom G2)
    by (exact (@notin_union_r1 x ((L \u dom G1) \u dom G2) \{xm} Hx2)).
  assert (Hx4 : x \notin L \u dom G1)
    by (exact (@notin_union_r1 x (L \u dom G1) (dom G2) Hx3)).
  assert (HxL : x \notin L) by (exact (@notin_union_r1 x L (dom G1) Hx4)).
  assert (HxG1 : x \notin dom G1) by (exact (@notin_union_r2 x L (dom G1) Hx4)).
  assert (HxG2 : x \notin dom G2) by (exact (@notin_union_r2 x (L \u dom G1) (dom G2) Hx3)).
  assert (Hxxm : x \notin \{xm}) by (exact (@notin_union_r2 x ((L \u dom G1) \u dom G2) \{xm} Hx2)).
  assert (Hxym : x \notin \{ym}) by (exact (@notin_union_r2 x ((((L \u dom G1) \u dom G2) \u \{xm})) \{ym} Hx1)).
  split; [exact HxL|]. split; [exact HxG1|]. split; [exact HxG2|]. split.
  - exact (@notin_singleton_r x xm Hxxm).
  - exact (@notin_singleton_r x ym Hxym).
Qed.

Lemma fresh_tail_L : forall (L:fset var) (G1 G2:ctx) (xm ym:var) (n:nat) (x:var) (ys:list var),
  fresh ((((L \u dom G1) \u dom G2) \u \{xm}) \u \{ym}) (S n) (cons x ys) ->
  forall y, List.In y ys ->
    y \notin L /\ y \notin dom G1 /\ y \notin dom G2 /\ y <> xm /\ y <> ym.
Proof.
  intros L G1 G2 xm ym n x ys Hf y Hy.
  set (Lb := ((((L \u dom G1) \u dom G2) \u \{xm}) \u \{ym})).
  assert (Ht : fresh (Lb \u \{x}) n ys)
    by (eapply fresh_cons_tail; exact Hf).
  assert (Hy1 : y \notin Lb \u \{x}).
  { eapply fresh_from_list_notin; [exact Ht|].
    rewrite in_from_list. exact Hy. }
  assert (Hy2 : y \notin Lb)
    by (exact (@notin_union_r1 y Lb \{x} Hy1)).
  assert (Hy3 : y \notin ((L \u dom G1) \u dom G2) \u \{xm})
    by (exact (@notin_union_r1 y (((L \u dom G1) \u dom G2) \u \{xm}) \{ym} Hy2)).
  assert (Hy4 : y \notin (L \u dom G1) \u dom G2)
    by (exact (@notin_union_r1 y ((L \u dom G1) \u dom G2) \{xm} Hy3)).
  assert (Hy5 : y \notin L \u dom G1)
    by (exact (@notin_union_r1 y (L \u dom G1) (dom G2) Hy4)).
  assert (HyL : y \notin L) by (exact (@notin_union_r1 y L (dom G1) Hy5)).
  assert (HyG1 : y \notin dom G1) by (exact (@notin_union_r2 y L (dom G1) Hy5)).
  assert (HyG2 : y \notin dom G2) by (exact (@notin_union_r2 y (L \u dom G1) (dom G2) Hy4)).
  assert (Hyxm : y \notin \{xm}) by (exact (@notin_union_r2 y ((L \u dom G1) \u dom G2) \{xm} Hy3)).
  assert (Hyym : y \notin \{ym}) by (exact (@notin_union_r2 y (((L \u dom G1) \u dom G2) \u \{xm}) \{ym} Hy2)).
  split; [exact HyL|]. split; [exact HyG1|]. split; [exact HyG2|]. split.
  - exact (@notin_singleton_r y xm Hyxm).
  - exact (@notin_singleton_r y ym Hyym).
Qed.

Lemma sc_commit_con_intro : forall (L:fset var) (G1 G2:ctx) (D1 D2:init_ctx)
    (xm ym:var) (Sm:typ) (Ts:typs) (is':inits) (T:typ) (i:init_typ) (ds:defs) (t:trm),
  List.length is' = length_s Ts ->
  (forall x ys, List.length ys = length_s Ts ->
     fresh L (S (List.length ys)) (cons x ys) ->
     has_effs (open_vars (cons x ys) t) (def_eff x ds)) ->
  (forall x ys, List.length ys = length_s Ts ->
     fresh L (S (List.length ys)) (cons x ys) ->
     QiF ((G1 & xm ~ Sm & G2) & (ys ~** to_list Ts) & (x ~ open_vars (cons x ys) T))
         ((D1 & xm ~ committed & D2) & (ys ~** is') & (x ~ free))
         ((from_list ys) \u \{x}) (open_vars (cons x ys) t) i) ->
  xm # G2 -> xm # D2 -> xm \notin fv_env G1 ->
  (G1 & subst_env xm ym G2 ⊢ trm_var (avar_f ym) ∶ subst_var xm ym Sm) ->
  binds ym committed (D1 & D2) ->
  G1 & subst_env xm ym G2 ⸴ D1 & D2
    ⊢c subst_var xm ym (lit_con Ts is' T ds t).
Proof.
  intros L G1 G2 D1 D2 xm ym Sm Ts is' T i ds t Hlenis Heff Hinit HxG HxD Hfv Hpre Hbinds.
  set (L' := (((L \u dom G1) \u dom G2) \u \{xm}) \u \{ym}).
  unfold QiF in Hinit. simpl.
  eapply (@commit_con_intro L' _ _ _ _ _ i _ _).
  - rewrite length_s_subst_typs. exact Hlenis.
  - intros x ys Hlenxy Hf.
    rewrite length_s_subst_typs in Hlenxy.
    destruct (@fresh_head_L L G1 G2 xm ym (List.length ys) x ys Hf) as [HxL [HxG1 [HxG2 [Hxxm Hxym]]]].
    assert (Hf1 : fresh (((L \u dom G1) \u dom G2) \u \{xm}) (S (List.length ys)) (cons x ys))
      by (exact (@fresh_union_r1 (cons x ys) (((L \u dom G1) \u dom G2) \u \{xm}) \{ym} (S (List.length ys)) Hf)).
    assert (Hf2 : fresh ((L \u dom G1) \u dom G2) (S (List.length ys)) (cons x ys))
      by (exact (@fresh_union_r1 (cons x ys) ((L \u dom G1) \u dom G2) \{xm} (S (List.length ys)) Hf1)).
    assert (Hf3 : fresh (L \u dom G1) (S (List.length ys)) (cons x ys))
      by (exact (@fresh_union_r1 (cons x ys) (L \u dom G1) (dom G2) (S (List.length ys)) Hf2)).
    assert (HfL : fresh L (S (List.length ys)) (cons x ys))
      by (exact (@fresh_union_r1 (cons x ys) L (dom G1) (S (List.length ys)) Hf3)).
    pose proof (Heff x ys Hlenxy HfL) as Heffxy.
    assert (Htrw : subst_var xm ym (open_vars (cons x ys) t) = open_vars (cons x ys) (subst_var xm ym t)).
    { rewrite subst_open_rec_vars_trm. rewrite map_ren_id.
      - reflexivity.
      - intros z Hz. destruct Hz as [->|Hz].
        + exact Hxxm.
        + destruct (@fresh_tail_L L G1 G2 xm ym (List.length ys) x ys Hf z Hz) as [_ [_ [_ [Hzxm _]]]]. exact Hzxm. }
    assert (Heffsub : has_effs (subst_var xm ym (open_vars (cons x ys) t)) (def_eff x ds)).
    { eapply has_effs_subst_fresh; [exact Heffxy|].
      intros a Ha. exact (@def_eff_no_subst ds x xm a (not_eq_sym Hxxm) Ha). }
    rewrite Htrw in Heffsub. rewrite <- (@def_eff_subst ds xm ym x) in Heffsub. exact Heffsub.
  - intros x ys Hlenxy Hf.
    rewrite length_s_subst_typs in Hlenxy.
    destruct (@fresh_head_L L G1 G2 xm ym (List.length ys) x ys Hf) as [HxL [HxG1 [HxG2 [Hxxm Hxym]]]].
    assert (Hf1 : fresh (((L \u dom G1) \u dom G2) \u \{xm}) (S (List.length ys)) (cons x ys))
      by (exact (@fresh_union_r1 (cons x ys) (((L \u dom G1) \u dom G2) \u \{xm}) \{ym} (S (List.length ys)) Hf)).
    assert (Hf2 : fresh ((L \u dom G1) \u dom G2) (S (List.length ys)) (cons x ys))
      by (exact (@fresh_union_r1 (cons x ys) ((L \u dom G1) \u dom G2) \{xm} (S (List.length ys)) Hf1)).
    assert (Hf3 : fresh (L \u dom G1) (S (List.length ys)) (cons x ys))
      by (exact (@fresh_union_r1 (cons x ys) (L \u dom G1) (dom G2) (S (List.length ys)) Hf2)).
    assert (HfL : fresh L (S (List.length ys)) (cons x ys))
      by (exact (@fresh_union_r1 (cons x ys) L (dom G1) (S (List.length ys)) Hf3)).
    pose proof (Hinit x ys Hlenxy HfL) as HIH.
    assert (HlenL : LibList.length ys = LibList.length (to_list Ts)).
    { unfold length_s in Hlenxy. change (List.length ys = List.length (to_list Ts)) in Hlenxy.
      rewrite !List_length_LibList_length in Hlenxy. exact Hlenxy. }
    assert (HlenI : List.length ys = List.length is').
    { rewrite <- Hlenis in Hlenxy. exact Hlenxy. }
    assert (Htrw : subst_var xm ym (open_vars (cons x ys) t) = open_vars (cons x ys) (subst_var xm ym t)).
    { rewrite subst_open_rec_vars_trm. rewrite map_ren_id.
      - reflexivity.
      - intros z Hz. destruct Hz as [->|Hz].
        + exact Hxxm.
        + destruct (@fresh_tail_L L G1 G2 xm ym (List.length ys) x ys Hf z Hz) as [_ [_ [_ [Hzxm _]]]]. exact Hzxm. }
    assert (HTrwT : subst_var xm ym (open_vars (cons x ys) T) = open_vars (cons x ys) (subst_var xm ym T)).
    { rewrite subst_open_rec_vars_typ. rewrite map_ren_id.
      - reflexivity.
      - intros z Hz. destruct Hz as [->|Hz].
        + exact Hxxm.
        + destruct (@fresh_tail_L L G1 G2 xm ym (List.length ys) x ys Hf z Hz) as [_ [_ [_ [Hzxm _]]]]. exact Hzxm. }
    assert (HnotxmYs : xm \notin from_list ys).
    { apply notin_from_list_intro. intros z Hz.
      destruct (@fresh_tail_L L G1 G2 xm ym (List.length ys) x ys Hf z Hz) as [_ [_ [_ [Hzxm _]]]]. exact Hzxm. }
    assert (HnotymYs : ym \notin from_list ys).
    { apply notin_from_list_intro. intros z Hz.
      destruct (@fresh_tail_L L G1 G2 xm ym (List.length ys) x ys Hf z Hz) as [_ [_ [_ [_ Hzyn]]]]. exact Hzyn. }
    assert (HxG' : xm # ((G2 & (ys ~** to_list Ts)) & (x ~ open_vars (cons x ys) T))).
    { rewrite !dom_concat, !dom_single. apply notin_union_l.
      - apply notin_union_l.
        + exact HxG.
        + rewrite (@dom_ys_tolist ys Ts HlenL). exact HnotxmYs.
      - apply notin_singleton_l. exact (not_eq_sym Hxxm). }
    assert (HxD' : xm # ((D2 & (ys ~** is')) & (x ~ free))).
    { rewrite !dom_concat, !dom_single. apply notin_union_l.
      - apply notin_union_l.
        + exact HxD.
        + rewrite (@dom_ys_inits ys is' HlenI). exact HnotxmYs.
      - apply notin_singleton_l. exact (not_eq_sym Hxxm). }
    assert (Hpre' : G1 & subst_env xm ym ((G2 & (ys ~** to_list Ts)) & (x ~ open_vars (cons x ys) T))
                    ⊢ trm_var (avar_f ym) ∶ subst_var xm ym Sm).
    { rewrite map_concat. rewrite map_single. rewrite map_concat.
      rewrite (subst_env_singles xm ym ys Ts HlenL).
      eapply ty_trm_binds_extends; [exact Hpre|].
      rewrite <- concat_assoc. rewrite concat_assoc.
      eapply binds_extends_push_env_fresh.
      intros z Hz. rewrite !dom_concat, !dom_single in Hz. rewrite in_union in Hz.
      destruct Hz as [Hz|Hz].
      - assert (HL2 : LibList.length ys = LibList.length (to_list (subst_var xm ym Ts))).
        { change (LibList.length ys = LibList.length (to_list (subst_typs xm ym Ts))).
          rewrite length_to_list_subst. exact HlenL. }
        rewrite (@dom_ys_tolist ys (subst_var xm ym Ts) HL2) in Hz.
        destruct (@fresh_tail_L L G1 G2 xm ym (List.length ys) x ys Hf z
                    (proj1 (@in_from_list var z ys) Hz)) as [HzL [HzG1 [HzG2 _]]].
        rewrite !dom_concat, dom_map. apply notin_union_l; assumption.
      - rewrite in_singleton in Hz. subst z.
        rewrite !dom_concat, dom_map. apply notin_union_l; assumption. }
    assert (Hbinds' : binds ym committed (D1 & ((D2 & (ys ~** is')) & (x ~ free)))).
    { repeat rewrite concat_assoc.
      eapply LibEnv.binds_push_neq.
      - eapply LibEnv.binds_concat_left.
        + exact Hbinds.
        + rewrite (@dom_ys_inits ys is' HlenI). exact HnotymYs.
      - exact (not_eq_sym Hxym). }
    assert (HeqG : ((G1 & xm ~ Sm & G2) & (ys ~** to_list Ts)) & (x ~ open_vars (cons x ys) T)
                 = G1 & xm ~ Sm & ((G2 & (ys ~** to_list Ts)) & (x ~ open_vars (cons x ys) T))).
    { repeat rewrite concat_assoc. reflexivity. }
    assert (HeqD : ((D1 & xm ~ committed & D2) & (ys ~** is')) & (x ~ free)
                 = D1 & xm ~ committed & ((D2 & (ys ~** is')) & (x ~ free))).
    { repeat rewrite concat_assoc. reflexivity. }
    pose proof (HIH G1 ((G2 & (ys ~** to_list Ts)) & (x ~ open_vars (cons x ys) T))
                  D1 ((D2 & (ys ~** is')) & (x ~ free)) xm ym Sm
                  HeqG HeqD HxG' HxD' Hfv Hpre' Hbinds') as Hres.
    rewrite map_concat in Hres. rewrite map_single in Hres. rewrite map_concat in Hres.
    rewrite (subst_env_singles xm ym ys Ts HlenL) in Hres.
    rewrite HTrwT in Hres. rewrite Htrw in Hres.
    assert (Hvs : subst_var xm ym ((from_list ys) \u \{x}) = (from_list ys) \u \{x}).
    { apply (@vars_subst_notin ((from_list ys) \u \{x}) xm ym).
      apply notin_union_l.
      - exact HnotxmYs.
      - apply notin_singleton_l. exact (not_eq_sym Hxxm). }
    repeat rewrite concat_assoc in Hres.
    rewrite <- Hvs.
    exact Hres.
Qed.

Lemma notin_L_prime : forall (L:fset var) (G1 G2:ctx) (xm ym z:var),
  z \notin (((L \u dom G1) \u dom G2) \u \{xm}) \u \{ym} ->
  z \notin L /\ z \notin dom G1 /\ z \notin dom G2 /\ z <> xm /\ z <> ym.
Proof.
  intros L G1 G2 xm ym z Hz.
  assert (Hz1 : z \notin ((L \u dom G1) \u dom G2) \u \{xm})
    by (exact (@notin_union_r1 z (((L \u dom G1) \u dom G2) \u \{xm}) \{ym} Hz)).
  assert (Hz2 : z \notin (L \u dom G1) \u dom G2)
    by (exact (@notin_union_r1 z ((L \u dom G1) \u dom G2) \{xm} Hz1)).
  assert (Hz3 : z \notin L \u dom G1)
    by (exact (@notin_union_r1 z (L \u dom G1) (dom G2) Hz2)).
  assert (HzL : z \notin L) by (exact (@notin_union_r1 z L (dom G1) Hz3)).
  assert (HzG1 : z \notin dom G1) by (exact (@notin_union_r2 z L (dom G1) Hz3)).
  assert (HzG2 : z \notin dom G2) by (exact (@notin_union_r2 z (L \u dom G1) (dom G2) Hz2)).
  assert (Hzxm : z \notin \{xm}) by (exact (@notin_union_r2 z ((L \u dom G1) \u dom G2) \{xm} Hz1)).
  assert (Hzym : z \notin \{ym}) by (exact (@notin_union_r2 z (((L \u dom G1) \u dom G2) \u \{xm}) \{ym} Hz)).
  split; [exact HzL|]. split; [exact HzG1|]. split; [exact HzG2|]. split.
  - exact (@notin_singleton_r z xm Hzxm).
  - exact (@notin_singleton_r z ym Hzym).
Qed.

Lemma si_init_let : forall (L:fset var) (G1 G2:ctx) (D1 D2:init_ctx)
    (xm ym:var) (Sm:typ) (vs:vars) (t u:trm) (T:typ) (i i':init_typ),
  QiF (G1 & xm ~ Sm & G2) (D1 & xm ~ committed & D2) vs t i ->
  (forall z, z \notin L ->
     QiF ((G1 & xm ~ Sm & G2) & z ~ T)
         ((D1 & xm ~ committed & D2) & z ~ i)
         (vs \u \{z}) (open z u) i') ->
  xm # G2 -> xm # D2 -> xm \notin fv_env G1 ->
  (G1 & subst_env xm ym G2 ⊢ trm_var (avar_f ym) ∶ subst_var xm ym Sm) ->
  binds ym committed (D1 & D2) ->
  G1 & subst_env xm ym G2 ⸴ D1 & D2 ⸴ subst_var xm ym vs
    ⊢i subst_var xm ym (trm_let T t u) ∶ i'.
Proof.
  intros L G1 G2 D1 D2 xm ym Sm vs t u T i i' Ht Hu HxG HxD Hfv Hpre Hbinds.
  set (L' := (((L \u dom G1) \u dom G2) \u \{xm}) \u \{ym}).
  unfold QiF in Ht, Hu. simpl.
  eapply (@init_let L' _ _ _ _ _ _ i _).
  - refine (Ht G1 G2 D1 D2 xm ym Sm _ _ _ _ _ _ _);
      [reflexivity|reflexivity|exact HxG|exact HxD|exact Hfv|exact Hpre|exact Hbinds].
  - intros z Hz.
    destruct (@notin_L_prime L G1 G2 xm ym z Hz) as [HzL [HzG1 [HzG2 [Hzxm Hzym]]]].
    assert (Hzx : z <> xm) by exact Hzxm.
    assert (Hru : subst_var xm ym (open_rec 0 z u) = open_rec 0 z (subst_var xm ym u))
      by (apply subst_open_fresh_trm; auto).
    assert (HeqG : ((G1 & xm ~ Sm & G2) & z ~ T) = G1 & xm ~ Sm & (G2 & z ~ T)).
    { symmetry. apply concat_assoc. }
    assert (HeqD : ((D1 & xm ~ committed & D2) & z ~ i)
                    = D1 & xm ~ committed & (D2 & z ~ i)).
    { symmetry. apply concat_assoc. }
    assert (Hpre' : G1 & subst_env xm ym (G2 & z ~ T)
                    ⊢ trm_var (avar_f ym) ∶ subst_var xm ym Sm).
    { rewrite map_push. rewrite concat_assoc.
      eapply ty_trm_binds_extends; [exact Hpre|].
      apply binds_extends_push_fresh.
      rewrite dom_concat. apply notin_union_l; [exact HzG1|].
      rewrite dom_subst_env. exact HzG2. }
    assert (HxG' : xm # (G2 & z ~ T)).
    { rewrite dom_push. apply notin_union_l.
      - apply notin_singleton_l. exact (not_eq_sym Hzxm).
      - exact HxG. }
    assert (HxD' : xm # (D2 & z ~ i)).
    { rewrite dom_push. apply notin_union_l.
      - apply notin_singleton_l. exact (not_eq_sym Hzxm).
      - exact HxD. }
    assert (Hbinds' : binds ym committed (D1 & (D2 & z ~ i))).
    { rewrite concat_assoc.
      eapply LibEnv.binds_push_neq.
      - exact Hbinds.
      - exact (not_eq_sym Hzym). }
    pose proof (Hu z HzL G1 (G2 & z ~ T) D1 (D2 & z ~ i) xm ym Sm
                  HeqG HeqD HxG' HxD' Hfv Hpre' Hbinds') as Hres.
    rewrite map_push in Hres.
    rewrite Hru in Hres.
    assert (Hvs : subst_var xm ym (vs \u \{z}) = (subst_var xm ym vs) \u \{z})
      by (apply (@subst_vars_union_singleton vs xm ym z Hzx)).
    repeat rewrite concat_assoc in Hres.
    rewrite <- Hvs. exact Hres.
Qed.

Lemma si_init_llit : forall (L:fset var) (G1 G2:ctx) (D1 D2:init_ctx)
    (xm ym:var) (Sm:typ) (vs:vars) (l:lit) (u:trm) (T:typ) (i:init_typ),
  QlF (G1 & xm ~ Sm & G2) (D1 & xm ~ committed & D2) l ->
  (forall z, z \notin L ->
     QiF ((G1 & xm ~ Sm & G2) & z ~ T)
         ((D1 & xm ~ committed & D2) & z ~ committed)
         vs (open z u) i) ->
  xm # G2 -> xm # D2 -> xm \notin fv_env G1 ->
  (G1 & subst_env xm ym G2 ⊢ trm_var (avar_f ym) ∶ subst_var xm ym Sm) ->
  binds ym committed (D1 & D2) ->
  G1 & subst_env xm ym G2 ⸴ D1 & D2 ⸴ subst_var xm ym vs
    ⊢i subst_var xm ym (trm_lit T l u) ∶ i.
Proof.
  intros L G1 G2 D1 D2 xm ym Sm vs l u T i Hl Hu HxG HxD Hfv Hpre Hbinds.
  set (L' := (((L \u dom G1) \u dom G2) \u \{xm}) \u \{ym}).
  unfold QlF in Hl. unfold QiF in Hu. simpl.
  eapply (@init_llit L' _ _ _ _ _ _).
  - refine (Hl G1 G2 D1 D2 xm ym Sm _ _ _ _ _ _ _);
      [reflexivity|reflexivity|exact HxG|exact HxD|exact Hfv|exact Hpre|exact Hbinds].
  - intros z Hz.
    destruct (@notin_L_prime L G1 G2 xm ym z Hz) as [HzL [HzG1 [HzG2 [Hzxm Hzym]]]].
    assert (Hzx : z <> xm) by exact Hzxm.
    assert (Hru : subst_var xm ym (open_rec 0 z u) = open_rec 0 z (subst_var xm ym u))
      by (apply subst_open_fresh_trm; auto).
    assert (HeqG : ((G1 & xm ~ Sm & G2) & z ~ T) = G1 & xm ~ Sm & (G2 & z ~ T)).
    { symmetry. apply concat_assoc. }
    assert (HeqD : ((D1 & xm ~ committed & D2) & z ~ committed)
                    = D1 & xm ~ committed & (D2 & z ~ committed)).
    { symmetry. apply concat_assoc. }
    assert (Hpre' : G1 & subst_env xm ym (G2 & z ~ T)
                    ⊢ trm_var (avar_f ym) ∶ subst_var xm ym Sm).
    { rewrite map_push. rewrite concat_assoc.
      eapply ty_trm_binds_extends; [exact Hpre|].
      apply binds_extends_push_fresh.
      rewrite dom_concat. apply notin_union_l; [exact HzG1|].
      rewrite dom_subst_env. exact HzG2. }
    assert (HxG' : xm # (G2 & z ~ T)).
    { rewrite dom_push. apply notin_union_l.
      - apply notin_singleton_l. exact (not_eq_sym Hzxm).
      - exact HxG. }
    assert (HxD' : xm # (D2 & z ~ committed)).
    { rewrite dom_push. apply notin_union_l.
      - apply notin_singleton_l. exact (not_eq_sym Hzxm).
      - exact HxD. }
    assert (Hbinds' : binds ym committed (D1 & (D2 & z ~ committed))).
    { rewrite concat_assoc.
      eapply LibEnv.binds_push_neq.
      - exact Hbinds.
      - exact (not_eq_sym Hzym). }
    pose proof (Hu z HzL G1 (G2 & z ~ T) D1 (D2 & z ~ committed) xm ym Sm
                  HeqG HeqD HxG' HxD' Hfv Hpre' Hbinds') as Hres.
    rewrite map_push in Hres.
    rewrite Hru in Hres.
    repeat rewrite concat_assoc in Hres. exact Hres.
Qed.

Lemma init_commit_subst_mut :
  (forall (G:ctx) (D:init_ctx) (t:trm), G ⸴ D ⊢c t -> QcF G D t) /\
  (forall (G:ctx) (D:init_ctx) (avs:avars), G ⸴ D ⊢c avs -> QaF G D avs) /\
  (forall (G:ctx) (D:init_ctx) (l:lit), G ⸴ D ⊢c l -> QlF G D l) /\
  (forall (G:ctx) (D:init_ctx) (vs:vars) (t:trm) (i:init_typ), G ⸴ D ⸴ vs ⊢i t ∶ i -> QiF G D vs t i) /\
  (forall (G:ctx) (D:init_ctx) (vs:vars) (avs:avars) (is':inits), G ⸴ D ⸴ vs ⊢i avs :: is' -> QisF G D vs avs is').
Proof.
  apply (well_init_mut_ind
    (fun (G:ctx) (D:init_ctx) (t:trm) (_:G ⸴ D ⊢c t) => QcF G D t)
    (fun (G:ctx) (D:init_ctx) (avs:avars) (_:G ⸴ D ⊢c avs) => QaF G D avs)
    (fun (G:ctx) (D:init_ctx) (l:lit) (_:G ⸴ D ⊢c l) => QlF G D l)
    (fun (G:ctx) (D:init_ctx) (vs:vars) (t:trm) (i:init_typ) (_:G ⸴ D ⸴ vs ⊢i t ∶ i) => QiF G D vs t i)
    (fun (G:ctx) (D:init_ctx) (vs:vars) (avs:avars) (is':inits) (_:G ⸴ D ⸴ vs ⊢i avs :: is') => QisF G D vs avs is'));
  intros; unfold QcF, QaF, QlF, QiF, QisF in *;
  intros G1 G2 D1 D2 xm ym Sm HeqG HeqD HxG HxD Hfv Hpre Hbinds; subst;
  first [ solve [ eapply sc_commit_var; eauto 4 ]
        | solve [ eapply sc_commit_all_elim; eauto 4 ]
        | solve [ eapply sc_commit_new; eauto 4 ]
        | solve [ eapply sc_commit_rcd_elim; eauto 4 ]
        | solve [ eapply sc_commit_fld_asn; eauto 4 ]
        | solve [ eapply sc_commit_let; eauto 4 ]
        | solve [ eapply sc_commit_llit; eauto 4 ]
        | solve [ eapply sc_commit_avars_nil; eauto 4 ]
        | solve [ eapply sc_commit_avars_cons; eauto 4 ]
        | solve [ eapply sc_commit_all_intro; eauto 4 ]
        | solve [ eapply sc_commit_con_intro; eauto 4 ]
        | solve [ eapply si_init_var_binds; eauto 4 ]
        | solve [ eapply si_init_commit; eauto 4 ]
        | solve [ eapply si_init_new_free; eauto 4 ]
        | solve [ eapply si_init_fld_asn_ac; eauto 4 ]
        | solve [ eapply si_init_fld_asn_ff; eauto 4 ]
        | solve [ eapply si_init_let; eauto 4 ]
        | solve [ eapply si_init_llit; eauto 4 ]
        | solve [ eapply si_inits_nil; eauto 4 ]
        | solve [ eapply si_inits_cons; eauto 4 ] ].
Qed.

Corollary commit_subst : forall (G:ctx) (D:init_ctx) (t:trm), G ⸴ D ⊢c t ->
  forall G1 G2 D1 D2 xm ym Sm,
    G = G1 & xm ~ Sm & G2 ->
    D = D1 & xm ~ committed & D2 ->
    xm # G2 -> xm # D2 -> xm \notin fv_env G1 ->
    (G1 & subst_env xm ym G2 ⊢ trm_var (avar_f ym) ∶ subst_var xm ym Sm) ->
    binds ym committed (D1 & D2) ->
    G1 & subst_env xm ym G2 ⸴ D1 & D2 ⊢c subst_var xm ym t.
Proof.
  intros G D t H G1 G2 D1 D2 xm ym Sm HeqG HeqD HxG HxD Hfv Hpre Hb.
  pose proof (proj1 init_commit_subst_mut G D t H) as Hq.
  unfold QcF in Hq. exact (Hq G1 G2 D1 D2 xm ym Sm HeqG HeqD HxG HxD Hfv Hpre Hb).
Qed.

Corollary lit_commit_subst : forall (G:ctx) (D:init_ctx) (l:lit), G ⸴ D ⊢c l ->
  forall G1 G2 D1 D2 xm ym Sm,
    G = G1 & xm ~ Sm & G2 ->
    D = D1 & xm ~ committed & D2 ->
    xm # G2 -> xm # D2 -> xm \notin fv_env G1 ->
    (G1 & subst_env xm ym G2 ⊢ trm_var (avar_f ym) ∶ subst_var xm ym Sm) ->
    binds ym committed (D1 & D2) ->
    G1 & subst_env xm ym G2 ⸴ D1 & D2 ⊢c subst_var xm ym l.
Proof.
  intros G D l H G1 G2 D1 D2 xm ym Sm HeqG HeqD HxG HxD Hfv Hpre Hb.
  pose proof (proj1 (proj2 (proj2 init_commit_subst_mut)) G D l H) as Hq.
  unfold QlF in Hq. exact (Hq G1 G2 D1 D2 xm ym Sm HeqG HeqD HxG HxD Hfv Hpre Hb).
Qed.

Corollary init_subst : forall (G:ctx) (D:init_ctx) (vs:vars) (t:trm) (i:init_typ),
  G ⸴ D ⸴ vs ⊢i t ∶ i ->
  forall G1 G2 D1 D2 xm ym Sm,
    G = G1 & xm ~ Sm & G2 ->
    D = D1 & xm ~ committed & D2 ->
    xm # G2 -> xm # D2 -> xm \notin fv_env G1 ->
    (G1 & subst_env xm ym G2 ⊢ trm_var (avar_f ym) ∶ subst_var xm ym Sm) ->
    binds ym committed (D1 & D2) ->
    G1 & subst_env xm ym G2 ⸴ D1 & D2 ⸴ subst_var xm ym vs
      ⊢i subst_var xm ym t ∶ i.
Proof.
  intros G D vs t i H G1 G2 D1 D2 xm ym Sm HeqG HeqD HxG HxD Hfv Hpre Hb.
  pose proof (proj1 (proj2 (proj2 (proj2 init_commit_subst_mut))) G D vs t i H) as Hq.
  unfold QiF in Hq. exact (Hq G1 G2 D1 D2 xm ym Sm HeqG HeqD HxG HxD Hfv Hpre Hb).
Qed.

Lemma commit_all_intro_open : forall (L:fset var) (G:ctx) (D:init_ctx) (S:typ) (t:trm) (a:var),
  (forall x, x \notin L -> G & x ~ S ⸴ D & x ~ committed ⊢c open x t) ->
  G ⊢ trm_var (avar_f a) ∶ S ->
  binds a committed D ->
  G ⸴ D ⊢c open a t.
Proof.
  intros L G D S t a Hbody Ha Hb.
  destruct (@var_fresh (((L \u fv_env G) \u fv t) \u fv S)) as [x Hx].
  pose proof (notin_union_r1 Hx) as Hx1.
  pose proof (notin_union_r1 Hx1) as Hx2.
  pose proof (notin_union_r1 Hx2) as HxL.
  pose proof (notin_union_r2 Hx2) as HxG.
  pose proof (notin_union_r2 Hx1) as Hxt.
  pose proof (notin_union_r2 Hx) as HxS.
  assert (Hbodyx : G & x ~ S ⸴ D & x ~ committed ⊢c open x t) by (apply Hbody; exact HxL).
  assert (Hpre : G & subst_env x a empty ⊢ trm_var (avar_f a) ∶ subst_var x a S).
  { rewrite (@fv_subst_typ S x a HxS). rewrite map_empty. rewrite concat_empty_r. exact Ha. }
  assert (Hxempty : x # (empty:ctx)) by (rewrite (@dom_empty typ); apply notin_empty).
  assert (HxemptyD : x # (empty:init_ctx)) by (rewrite (@dom_empty init_typ); apply notin_empty).
  assert (Hb' : binds a committed (D & empty)) by (rewrite concat_empty_r; exact Hb).
  pose proof (@commit_subst (G & x ~ S) (D & x ~ committed) (open x t) Hbodyx
                G empty D empty x a S
                (eq_sym (concat_empty_r (G & x ~ S)))
                (eq_sym (concat_empty_r (D & x ~ committed)))
                Hxempty HxemptyD HxG Hpre Hb') as Hres.
  rewrite map_empty in Hres. rewrite !concat_empty_r in Hres.
  rewrite (@subst_intro_trm t x a 0 Hxt).
  exact Hres.
Qed.

Lemma ty_heap_def_binds_extends : forall (G:ctx) (d:heap_def) (D:dec),
  G ⊢ d ∶d D -> forall G', binds_extends G G' -> G' ⊢ d ∶d D.
Proof.
  intros G d D H. change (ty_heap_def G d D) in H.
  destruct H as [A T | a T | a x T Hty]; intros G' He.
  - apply ty_heap_def_typ.
  - apply ty_heap_def_trm_none.
  - eapply ty_heap_def_trm_some. eapply ty_trm_binds_extends; eassumption.
Qed.

Lemma ty_heap_defs_binds_extends : forall (G:ctx) (hds:heap_defs) (T:typ),
  G ⊢ hds ∶ T -> forall G', binds_extends G G' -> G' ⊢ hds ∶ T.
Proof.
  intros G hds T H. induction H; intros G' He.
  - eapply ty_defs_one. eapply ty_heap_def_binds_extends; eassumption.
  - eapply ty_defs_cons.
    + eapply IHty_defs; eassumption.
    + eapply ty_heap_def_binds_extends; eassumption.
    + assumption.
Qed.

Lemma heap_correspond_extend_lit : forall (G:ctx) (Sigma:heap) (x:var) (T:typ) (l:lit),
  x # Sigma -> x # G ->
  heap_correspond G Sigma ->
  G & x ~ T ⊢ l ∶ T ->
  heap_correspond (G & x ~ T) (Sigma & x ~ item_lit l).
Proof.
  intros G Sigma x T l HxS HxG [Hdom Hitem] Hlit. split.
  - rewrite !dom_push. rewrite Hdom. reflexivity.
  - intros z Hz. rewrite dom_push in Hz. rewrite in_union in Hz.
    destruct Hz as [Hz|Hz].
    + rewrite in_singleton in Hz. subst z.
      eapply ty_item_lit_s.
      * apply LibEnv.binds_push_eq.
      * apply LibEnv.binds_push_eq.
      * exact Hlit.
    + assert (Hzx : z <> x) by (intro E; subst z; exact (HxG Hz)).
      pose proof (Hitem z Hz) as Hts.
      inversion Hts; subst.
      * (* literal item *)
        eapply ty_item_lit_s.
        -- eapply LibEnv.binds_push_neq.
           ++ match goal with Hb : binds z _ G |- _ => exact Hb end.
           ++ exact Hzx.
        -- eapply LibEnv.binds_push_neq.
           ++ match goal with Hb : binds z (item_lit _) Sigma |- _ => exact Hb end.
           ++ exact Hzx.
        -- eapply ty_lit_binds_extends.
           ++ match goal with Hty : G ⊢ _ ∶ _ |- _ => exact Hty end.
           ++ apply binds_extends_push_fresh; exact HxG.
      * (* object item *)
        eapply ty_item_obj_s.
        -- eapply LibEnv.binds_push_neq.
           ++ match goal with Hb : binds z _ G |- _ => exact Hb end.
           ++ exact Hzx.
        -- eapply LibEnv.binds_push_neq.
           ++ match goal with Hb : binds z (item_obj _ _) Sigma |- _ => exact Hb end.
           ++ exact Hzx.
        -- eapply ty_heap_defs_binds_extends.
           ++ match goal with Hty : G ⊢ _ ∶ _ |- _ => exact Hty end.
           ++ apply binds_extends_push_fresh; exact HxG.
Qed.

Lemma heap_correspond_extend_obj : forall (G:ctx) (Sigma:heap) (x:var) (U:typ) (hds:heap_defs),
  x # Sigma -> x # G ->
  heap_correspond G Sigma ->
  G & x ~ typ_bnd U ⊢ hds ∶ open_rec 0 x U ->
  heap_correspond (G & x ~ typ_bnd U) (Sigma & x ~ item_obj U hds).
Proof.
  intros G Sigma x U hds HxS HxG [Hdom Hitem] Hty. split.
  - rewrite !dom_push. rewrite Hdom. reflexivity.
  - intros z Hz. rewrite dom_push in Hz. rewrite in_union in Hz.
    destruct Hz as [Hz|Hz].
    + rewrite in_singleton in Hz. subst z.
      eapply ty_item_obj_s.
      * apply LibEnv.binds_push_eq.
      * apply LibEnv.binds_push_eq.
      * exact Hty.
    + assert (Hzx : z <> x) by (intro E; subst z; exact (HxG Hz)).
      pose proof (Hitem z Hz) as Hts.
      inversion Hts; subst.
      * eapply ty_item_lit_s.
        -- eapply LibEnv.binds_push_neq.
           ++ match goal with Hb : binds z _ G |- _ => exact Hb end.
           ++ exact Hzx.
        -- eapply LibEnv.binds_push_neq.
           ++ match goal with Hb : binds z (item_lit _) Sigma |- _ => exact Hb end.
           ++ exact Hzx.
        -- eapply ty_lit_binds_extends.
           ++ match goal with Hty0 : G ⊢ _ ∶ _ |- _ => exact Hty0 end.
           ++ apply binds_extends_push_fresh; exact HxG.
      * eapply ty_item_obj_s.
        -- eapply LibEnv.binds_push_neq.
           ++ match goal with Hb : binds z _ G |- _ => exact Hb end.
           ++ exact Hzx.
        -- eapply LibEnv.binds_push_neq.
           ++ match goal with Hb : binds z (item_obj _ _) Sigma |- _ => exact Hb end.
           ++ exact Hzx.
        -- eapply ty_heap_defs_binds_extends.
           ++ match goal with Hty0 : G ⊢ _ ∶ _ |- _ => exact Hty0 end.
           ++ apply binds_extends_push_fresh; exact HxG.
Qed.

Definition rename_eff (x y:var) (e:effect) : effect := (fst e \[x -> y], snd e).

Lemma eff_trm_subst : forall (t:trm) (effs:effects),
  eff_trm t effs ->
  forall (xm ym:var), eff_trm (subst_var xm ym t) (List.map (rename_eff xm ym) effs).
Proof.
  intros t effs H. induction H; intros xm ym.
  - simpl. apply eff_ignore.
  - simpl. apply eff_fld_asn.
  - simpl. rewrite List.map_app. eapply eff_let with (L := (L \u \{xm}) \u \{ym}).
    + apply IHeff_trm.
    + intros z Hz.
      assert (HzL : z \notin L).
      { apply notin_union_r1 in Hz as Hza. apply notin_union_r1 in Hza. exact Hza. }
      assert (Hzx : z <> xm).
      { apply notin_union_r1 in Hz as Hza. apply notin_union_r2 in Hza.
        intro E; subst z; apply Hza; apply in_singleton_self. }
      assert (Hb := H1 z HzL xm ym).
      rewrite (@subst_open_fresh_trm xm ym z 0 u Hzx) in Hb.
      exact Hb.
  - simpl. eapply eff_llit with (L := (L \u \{xm}) \u \{ym}).
    intros z Hz.
    assert (HzL : z \notin L).
    { apply notin_union_r1 in Hz as Hza. apply notin_union_r1 in Hza. exact Hza. }
    assert (Hzx : z <> xm).
    { apply notin_union_r1 in Hz as Hza. apply notin_union_r2 in Hza.
      intro E; subst z; apply Hza; apply in_singleton_self. }
    assert (Hb := H0 z HzL xm ym).
    rewrite (@subst_open_fresh_trm xm ym z 0 u Hzx) in Hb.
    exact Hb.
Qed.

Lemma in_from_list_rename : forall (xm ym:var) (effs:effects) (e:effect),
  rename_eff xm ym e = e ->
  e \in from_list effs ->
  e \in from_list (List.map (rename_eff xm ym) effs).
Proof.
  intros xm ym effs e Heq Hin.
  rewrite in_from_list in Hin. rewrite in_from_list.
  rewrite <- Heq. apply List.in_map. exact Hin.
Qed.

Lemma fv_in_values_push : forall (A:Type) (fv:A->vars) (E:env A) (x:var) (v:A),
  fv_in_values fv (E & x ~ v) = fv_in_values fv E \u fv v.
Proof.
  intros A fv E x v.
  rewrite concat_single_eq.
  unfold fv_in_values. rewrite !values_def. cbn.
  rewrite LibList.map_cons. rewrite LibList.fold_right_cons.
  rewrite union_comm. reflexivity.
Qed.

Lemma fv_env_push_ctx : forall (G:ctx) (x:var) (T:typ),
  fv_env (G & x ~ T) = fv_env G \u fv T.
Proof. intros. apply (@fv_in_values_push typ fv G x T). Qed.

Lemma notin_fv_env_push : forall (G:ctx) (x:var) (T:typ) (y:var),
  y \notin fv_env G -> y \notin fv T -> y \notin fv_env (G & x ~ T).
Proof.
  intros. rewrite fv_env_push_ctx. apply notin_union_l; assumption.
Qed.

Lemma binds_extends_push_perm : forall (A:Set) (G:env A) (x x0:var) (T T0:A),
  x0 \notin dom G -> x \notin dom G -> x0 <> x ->
  binds_extends (G & x0 ~ T0) (G & x ~ T & x0 ~ T0).
Proof.
  intros A G x x0 T T0 Hx0G HxG Hne z v Hz.
  destruct (classic (z = x0)) as [Heq|Hneq].
  - subst z. apply LibEnv.binds_push_eq_inv in Hz. subst v. apply LibEnv.binds_push_eq.
  - eapply LibEnv.binds_push_neq; [|exact Hneq].
    eapply LibEnv.binds_concat_left.
    + eapply LibEnv.binds_push_neq_inv; [exact Hz|exact Hneq].
    + intro E. rewrite LibEnv.dom_single in E. rewrite in_singleton in E. subst z.
      assert (Hb : binds x v G) by (eapply LibEnv.binds_push_neq_inv; [exact Hz|exact Hneq]).
      exact (HxG (@binds_in_dom A G x v Hb)).
Qed.

Lemma ty_lit_open_rename : forall (L:fset var) (G:ctx) (T U:typ) (t:trm) (x:var),
  x \notin dom G ->
  (forall x0, x0 \notin L -> G & x0 ~ T ⊢ open x0 t ∶ U) ->
  G & x ~ T ⊢ open x t ∶ U.
Proof.
  intros L G T U t x HxG Hpre.
  destruct (@var_fresh ((((((L \u dom G) \u fv_env G) \u fv t) \u fv T) \u fv U) \u \{x})) as [x0 Hx0].
  pose proof (notin_union_r1 Hx0) as Hx1.
  pose proof (notin_union_r1 Hx1) as Hx2.
  pose proof (notin_union_r1 Hx2) as Hx3.
  pose proof (notin_union_r1 Hx3) as Hx4.
  pose proof (notin_union_r1 Hx4) as Hx5.
  pose proof (notin_union_r1 Hx5) as Hx0L.
  pose proof (notin_union_r2 Hx5) as Hx0dom.
  pose proof (notin_union_r2 Hx4) as Hx0fv.
  pose proof (notin_union_r2 Hx3) as Hx0t.
  pose proof (notin_union_r2 Hx2) as Hx0T.
  pose proof (notin_union_r2 Hx1) as Hx0U.
  pose proof (notin_union_r2 Hx0) as Hx0x.
  assert (Hne : x0 <> x) by (exact (@notin_singleton_r x0 x Hx0x)).
  assert (Hprem : G & x0 ~ T ⊢ open x0 t ∶ U) by (apply Hpre; exact Hx0L).
  assert (Hperm : binds_extends (G & x0 ~ T) ((G & x ~ T) & x0 ~ T))
    by (eapply binds_extends_push_perm; [exact Hx0dom|exact HxG|exact Hne]).
  pose proof (@ty_trm_binds_extends (G & x0 ~ T) (open x0 t) U Hprem
                ((G & x ~ T) & x0 ~ T) Hperm) as Hweaken.
  assert (Hty' : (G & x ~ T) & x0 ~ T & empty ⊢ open x0 t ∶ U).
  { rewrite concat_empty_r. exact Hweaken. }
  assert (Hfv : x0 \notin fv_env (G & x ~ T))
    by (apply (@notin_fv_env_push G x T x0 Hx0fv Hx0T)).
  assert (Hxempty : x0 # (empty:ctx)) by (rewrite (@dom_empty typ); apply notin_empty).
  assert (HpreS : (G & x ~ T) & subst_env x0 x empty ⊢ trm_var (avar_f x) ∶ subst_var x0 x T).
  { rewrite map_empty. rewrite concat_empty_r.
    rewrite (@fv_subst_typ T x0 x Hx0T). apply ty_var. apply LibEnv.binds_push_eq. }
  pose proof (@ty_trm_subst (G & x ~ T) empty x0 x T (open x0 t) U
                Hty' Hxempty Hfv HpreS) as Hres.
  rewrite map_empty in Hres. rewrite concat_empty_r in Hres.
  rewrite (@fv_subst_typ U x0 x Hx0U) in Hres.
  rewrite (@subst_intro_trm t x0 x 0 Hx0t).
  exact Hres.
Qed.

Lemma ty_all_open_rename : forall (L:fset var) (G:ctx) (T U:typ) (t:trm) (x:var),
  x \notin dom G ->
  (forall x0, x0 \notin L -> G & x0 ~ T ⊢ open x0 t ∶ open x0 U) ->
  G & x ~ T ⊢ open x t ∶ open x U.
Proof.
  intros L G T U t x HxG Hpre.
  destruct (@var_fresh ((((((L \u dom G) \u fv_env G) \u fv t) \u fv T) \u fv U) \u \{x})) as [x0 Hx0].
  pose proof (notin_union_r1 Hx0) as Hx1.
  pose proof (notin_union_r1 Hx1) as Hx2.
  pose proof (notin_union_r1 Hx2) as Hx3.
  pose proof (notin_union_r1 Hx3) as Hx4.
  pose proof (notin_union_r1 Hx4) as Hx5.
  pose proof (notin_union_r1 Hx5) as Hx0L.
  pose proof (notin_union_r2 Hx5) as Hx0dom.
  pose proof (notin_union_r2 Hx4) as Hx0fv.
  pose proof (notin_union_r2 Hx3) as Hx0t.
  pose proof (notin_union_r2 Hx2) as Hx0T.
  pose proof (notin_union_r2 Hx1) as Hx0U.
  pose proof (notin_union_r2 Hx0) as Hx0x.
  assert (Hne : x0 <> x) by (exact (@notin_singleton_r x0 x Hx0x)).
  assert (Hprem : G & x0 ~ T ⊢ open x0 t ∶ open x0 U) by (apply Hpre; exact Hx0L).
  assert (Hperm : binds_extends (G & x0 ~ T) ((G & x ~ T) & x0 ~ T))
    by (eapply binds_extends_push_perm; [exact Hx0dom|exact HxG|exact Hne]).
  pose proof (@ty_trm_binds_extends (G & x0 ~ T) (open x0 t) (open x0 U) Hprem
                ((G & x ~ T) & x0 ~ T) Hperm) as Hweaken.
  assert (Hty' : (G & x ~ T) & x0 ~ T & empty ⊢ open x0 t ∶ open x0 U).
  { rewrite concat_empty_r. exact Hweaken. }
  assert (Hfv : x0 \notin fv_env (G & x ~ T))
    by (apply (@notin_fv_env_push G x T x0 Hx0fv Hx0T)).
  assert (Hxempty : x0 # (empty:ctx)) by (rewrite (@dom_empty typ); apply notin_empty).
  assert (HpreS : (G & x ~ T) & subst_env x0 x empty ⊢ trm_var (avar_f x) ∶ subst_var x0 x T).
  { rewrite map_empty. rewrite concat_empty_r.
    rewrite (@fv_subst_typ T x0 x Hx0T). apply ty_var. apply LibEnv.binds_push_eq. }
  pose proof (@ty_trm_subst (G & x ~ T) empty x0 x T (open x0 t) (open x0 U)
                Hty' Hxempty Hfv HpreS) as Hres.
  rewrite map_empty in Hres. rewrite concat_empty_r in Hres.
  rewrite (@subst_intro_trm t x0 x 0 Hx0t).
  rewrite (@subst_intro_typ U x0 x 0 Hx0U).
  exact Hres.
Qed.

Lemma commit_open_rename : forall (L:fset var) (G:ctx) (D:init_ctx) (T:typ) (t:trm) (x:var),
  x \notin dom G -> x \notin dom D ->
  binds x committed D ->
  (forall x0, x0 \notin L -> G & x0 ~ T ⸴ D & x0 ~ committed ⊢c open x0 t) ->
  G & x ~ T ⸴ D & x ~ committed ⊢c open x t.
Proof.
  intros L G D T t x HxG HxD Hxb Hpre.
  destruct (@var_fresh (((((((L \u dom G) \u fv_env G) \u fv t) \u fv T) \u dom D) \u \{x}))) as [x0 Hx0].
  pose proof (notin_union_r1 Hx0) as Hx1.
  pose proof (notin_union_r1 Hx1) as Hx2.
  pose proof (notin_union_r1 Hx2) as Hx3.
  pose proof (notin_union_r1 Hx3) as Hx4.
  pose proof (notin_union_r1 Hx4) as Hx5.
  pose proof (notin_union_r1 Hx5) as Hx0L.
  pose proof (notin_union_r2 Hx5) as Hx0domG.
  pose proof (notin_union_r2 Hx4) as Hx0fvG.
  pose proof (notin_union_r2 Hx3) as Hx0t.
  pose proof (notin_union_r2 Hx2) as Hx0T.
  pose proof (notin_union_r2 Hx1) as Hx0domD.
  pose proof (notin_union_r2 Hx0) as Hx0x.
  assert (Hne : x0 <> x) by (exact (@notin_singleton_r x0 x Hx0x)).
  assert (Hprem : G & x0 ~ T ⸴ D & x0 ~ committed ⊢c open x0 t) by (apply Hpre; exact Hx0L).
  assert (HpermG : binds_extends (G & x0 ~ T) ((G & x ~ T) & x0 ~ T))
    by (eapply binds_extends_push_perm; [exact Hx0domG|exact HxG|exact Hne]).
  assert (HpermD : binds_extends (D & x0 ~ committed) ((D & x ~ committed) & x0 ~ committed))
    by (eapply (@binds_extends_push_perm init_typ); [exact Hx0domD|exact HxD|exact Hne]).
  pose proof (@commit_binds_extends (G & x0 ~ T) (D & x0 ~ committed) (open x0 t) Hprem
                ((G & x ~ T) & x0 ~ T) ((D & x ~ committed) & x0 ~ committed)
                (\{}:vars) (\{}:vars) HpermG HpermD (@vs_subset_refl (\{}:vars))) as Hbody.
  assert (Hfv : x0 \notin fv_env (G & x ~ T))
    by (apply (@notin_fv_env_push G x T x0 Hx0fvG Hx0T)).
  assert (HxemptyG : x0 # (empty:ctx)) by (rewrite (@dom_empty typ); apply notin_empty).
  assert (HxemptyD : x0 # (empty:init_ctx)) by (rewrite (@dom_empty init_typ); apply notin_empty).
  assert (HpreS : (G & x ~ T) & subst_env x0 x empty ⊢ trm_var (avar_f x) ∶ subst_var x0 x T).
  { rewrite map_empty. rewrite concat_empty_r.
    rewrite (@fv_subst_typ T x0 x Hx0T). apply ty_var. apply LibEnv.binds_push_eq. }
  assert (Hbinds : binds x committed ((D & x ~ committed) & empty)).
  { rewrite concat_empty_r. apply LibEnv.binds_push_eq. }
  pose proof (@commit_subst ((G & x ~ T) & x0 ~ T) ((D & x ~ committed) & x0 ~ committed)
                (open x0 t) Hbody (G & x ~ T) empty (D & x ~ committed) empty x0 x T
                (eq_sym (concat_empty_r ((G & x ~ T) & x0 ~ T)))
                (eq_sym (concat_empty_r ((D & x ~ committed) & x0 ~ committed)))
                HxemptyG HxemptyD Hfv HpreS Hbinds) as Hres.
  rewrite map_empty in Hres. rewrite !concat_empty_r in Hres.
  rewrite (@subst_intro_trm t x0 x 0 Hx0t).
  exact Hres.
Qed.

Lemma init_open_rename_committed : forall (L:fset var) (G:ctx) (D:init_ctx) (vs:vars)
    (T:typ) (t:trm) (x:var) (i:init_typ),
  x \notin dom G -> x \notin dom D ->
  binds x committed D ->
  (forall x0, x0 \notin L -> G & x0 ~ T ⸴ D & x0 ~ committed ⸴ vs ⊢i open x0 t ∶ i) ->
  G & x ~ T ⸴ D & x ~ committed ⸴ vs ⊢i open x t ∶ i.
Proof.
  intros L G D vs T t x i HxG HxD Hxb Hpre.
  destruct (@var_fresh (((((((L \u dom G) \u fv_env G) \u fv t) \u fv T) \u dom D) \u vs) \u \{x})) as [x0 Hx0].
  pose proof (notin_union_r1 Hx0) as Hx1.
  pose proof (notin_union_r1 Hx1) as Hx2.
  pose proof (notin_union_r1 Hx2) as Hx3.
  pose proof (notin_union_r1 Hx3) as Hx4.
  pose proof (notin_union_r1 Hx4) as Hx5.
  pose proof (notin_union_r1 Hx5) as Hx6.
  pose proof (notin_union_r1 Hx6) as Hx0L.
  pose proof (notin_union_r2 Hx6) as Hx0domG.
  pose proof (notin_union_r2 Hx5) as Hx0fvG.
  pose proof (notin_union_r2 Hx4) as Hx0t.
  pose proof (notin_union_r2 Hx3) as Hx0T.
  pose proof (notin_union_r2 Hx2) as Hx0domD.
  pose proof (notin_union_r2 Hx1) as Hx0vs.
  pose proof (notin_union_r2 Hx0) as Hx0x.
  assert (Hne : x0 <> x) by (exact (@notin_singleton_r x0 x Hx0x)).
  assert (Hprem : G & x0 ~ T ⸴ D & x0 ~ committed ⸴ vs ⊢i open x0 t ∶ i)
    by (apply Hpre; exact Hx0L).
  assert (HpermG : binds_extends (G & x0 ~ T) ((G & x ~ T) & x0 ~ T))
    by (eapply binds_extends_push_perm; [exact Hx0domG|exact HxG|exact Hne]).
  assert (HpermD : binds_extends (D & x0 ~ committed) ((D & x ~ committed) & x0 ~ committed))
    by (eapply (@binds_extends_push_perm init_typ); [exact Hx0domD|exact HxD|exact Hne]).
  pose proof (@init_binds_extends (G & x0 ~ T) (D & x0 ~ committed) vs (open x0 t) i Hprem
                ((G & x ~ T) & x0 ~ T) ((D & x ~ committed) & x0 ~ committed) vs
                HpermG HpermD (@vs_subset_refl vs)) as Hbody.
  assert (Hfv : x0 \notin fv_env (G & x ~ T))
    by (apply (@notin_fv_env_push G x T x0 Hx0fvG Hx0T)).
  assert (HxemptyG : x0 # (empty:ctx)) by (rewrite (@dom_empty typ); apply notin_empty).
  assert (HxemptyD : x0 # (empty:init_ctx)) by (rewrite (@dom_empty init_typ); apply notin_empty).
  assert (HpreS : (G & x ~ T) & subst_env x0 x empty ⊢ trm_var (avar_f x) ∶ subst_var x0 x T).
  { rewrite map_empty. rewrite concat_empty_r.
    rewrite (@fv_subst_typ T x0 x Hx0T). apply ty_var. apply LibEnv.binds_push_eq. }
  assert (Hbinds : binds x committed ((D & x ~ committed) & empty)).
  { rewrite concat_empty_r. apply LibEnv.binds_push_eq. }
  pose proof (@init_subst ((G & x ~ T) & x0 ~ T) ((D & x ~ committed) & x0 ~ committed)
                vs (open x0 t) i Hbody
                (G & x ~ T) empty (D & x ~ committed) empty x0 x T
                (eq_sym (concat_empty_r ((G & x ~ T) & x0 ~ T)))
                (eq_sym (concat_empty_r ((D & x ~ committed) & x0 ~ committed)))
                HxemptyG HxemptyD Hfv HpreS Hbinds) as Hres.
  rewrite map_empty in Hres. rewrite !concat_empty_r in Hres.
  assert (Hvs : subst_var x0 x vs = vs)
    by (apply (@vars_subst_notin vs x0 x Hx0vs)).
  rewrite <- Hvs.
  rewrite (@subst_intro_trm t x0 x 0 Hx0t).
  exact Hres.
Qed.

Lemma init_var_split : forall (D1 D2:init_ctx) (xm:var) (ib:init_typ),
  xm # D2 -> binds xm ib (D1 & xm ~ ib & D2).
Proof.
  intros D1 D2 xm ib Hnot.
  eapply LibEnv.binds_concat_left.
  - apply LibEnv.binds_push_eq.
  - exact Hnot.
Qed.

Lemma init_var_subst_gen : forall (D1 D2:init_ctx) (vs:vars) (xm ym x:var) (ib i:init_typ),
  xm # D2 ->
  binds ym ib (D1 & D2) ->
  init_var (D1 & xm ~ ib & D2) vs x i ->
  init_var (D1 & D2) (subst_var xm ym vs) (x \[xm -> ym]) i.
Proof.
  intros D1 D2 vs xm ym x ib i HxD Hbinds Hin.
  remember (D1 & xm ~ ib & D2) as Delta eqn:Heq.
  induction Hin.
  - (* commit *)
    subst Delta.
    destruct (classic (x = xm)) as [->|Hne].
    + rewrite (@subst_if_eq xm ym). apply init_var_commit.
      assert (Hc : binds xm ib (D1 & xm ~ ib & D2)) by (eapply init_var_split; exact HxD).
      pose proof (@LibEnv.binds_functional init_typ xm committed ib
                    (D1 & xm ~ ib & D2) H Hc) as Heqib.
      subst ib. exact Hbinds.
    + rewrite (@subst_if_neq xm ym x Hne). apply init_var_commit.
      eapply (@binds_drop_middle init_typ D1 D2 xm x committed ib);
        [exact Hne|exact H].
  - (* free *)
    subst Delta.
    destruct (classic (x = xm)) as [->|Hne].
    + rewrite (@subst_if_eq xm ym). apply init_var_free.
      * eapply in_vars_subst_self. exact H.
      * assert (Hc : binds xm ib (D1 & xm ~ ib & D2)) by (eapply init_var_split; exact HxD).
        pose proof (@LibEnv.binds_functional init_typ xm free ib
                      (D1 & xm ~ ib & D2) H0 Hc) as Heqib.
        subst ib. exact Hbinds.
    + rewrite (@subst_if_neq xm ym x Hne). apply init_var_free.
      * eapply (@in_vars_subst vs xm ym x); [exact H|exact Hne].
      * eapply (@binds_drop_middle init_typ D1 D2 xm x free ib);
          [exact Hne|exact H0].
  - (* unspec *)
    subst Delta.
    destruct (classic (x = xm)) as [->|Hne].
    + rewrite (@subst_if_eq xm ym). apply init_var_unspec.
      * eapply in_vars_subst_self. exact H.
      * assert (Hc : binds xm ib (D1 & xm ~ ib & D2)) by (eapply init_var_split; exact HxD).
        pose proof (@LibEnv.binds_functional init_typ xm unspecified ib
                      (D1 & xm ~ ib & D2) H0 Hc) as Heqib.
        subst ib. exact Hbinds.
    + rewrite (@subst_if_neq xm ym x Hne). apply init_var_unspec.
      * eapply (@in_vars_subst vs xm ym x); [exact H|exact Hne].
      * eapply (@binds_drop_middle init_typ D1 D2 xm x unspecified ib);
          [exact Hne|exact H0].
  - (* sub *)
    eapply init_var_sub.
    + apply IHHin. exact Heq.
    + exact H.
Qed.

Lemma committed_heap_defs_extend : forall (D:init_ctx) (hds:heap_defs) (x:var),
  x \notin dom D ->
  committed_heap_defs D hds ->
  committed_heap_defs (D & x ~ committed) hds.
Proof.
  intros D hds x HxD H. induction H.
  - apply committed_heap_defs_nil.
  - apply committed_heap_defs_cons; [exact (IHcommitted_heap_defs HxD)|].
    inversion H0; subst.
    + apply committed_heap_def_typ.
    + apply committed_heap_def_trm.
      match goal with Hy : @binds ?A ?y committed Delta |- _ =>
        assert (Hne : y <> x) by
          (intro Exy; subst y; apply HxD; eapply binds_in_dom; exact Hy);
        eapply LibEnv.binds_push_neq; [exact Hy|exact Hne] end.
Qed.

Lemma free_heap_defs_extend : forall (D:init_ctx) (E:eff_ctx) (y:var) (hds:heap_defs) (x:var),
  free_heap_defs D E y hds ->
  x \notin dom D -> x \notin dom E ->
  free_heap_defs (D & x ~ committed) E y hds.
Proof.
  intros D E y hds x [Hb [Hbe Hwp]] HxD HxE. split; [|split].
  - assert (Hne : y <> x).
    { intro Exy; subst y.
      assert (HyE : x \in dom E) by (eapply binds_in_dom; eexact Hbe).
      exact (HxE HyE). }
    eapply LibEnv.binds_push_neq; [exact Hb|exact Hne].
  - exact Hbe.
  - intros z Hz. destruct (Hwp z Hz) as [Hc|[HzE Hf]].
    + assert (Hzx : z <> x).
      { intro Ezx; subst z; exact (HxD (@binds_in_dom init_typ D x committed Hc)). }
      left. eapply LibEnv.binds_push_neq; [exact Hc|exact Hzx].
    + assert (Hzx : z <> x) by (intro Ezx; subst z; exact (HxE HzE)).
      right. split; [exact HzE|].
      eapply LibEnv.binds_push_neq; [exact Hf|exact Hzx].
Qed.

Lemma free_heap_item_extend : forall (D:init_ctx) (E:eff_ctx) (y:var) (itm:item) (x:var),
  free_heap_item D E y itm ->
  x \notin dom D -> x \notin dom E ->
  free_heap_item (D & x ~ committed) E y itm.
Proof.
  intros D E y itm x H HxD HxE. inversion H; subst.
  apply free_heap_obj. eapply free_heap_defs_extend; eassumption.
Qed.

Lemma free_sub_heaps_dom_in : forall (G:ctx) (D:init_ctx) (Sigma:heap) (Es:list eff_ctx),
  free_sub_heaps G D Sigma Es ->
  forall E, List.In E Es -> forall x, x \in dom E -> x \in dom Sigma.
Proof.
  intros G D Sigma Es H. induction H; intros E0 Hin x Hx.
  - inversion Hin.
  - destruct Hin as [->|Hin].
    + unfold free_sub_heap in H0.
      destruct (dom_binds_exists Hx) as [effs Hb].
      destruct (H0 x effs Hb) as [_ [itm [HbS _]]].
      eapply binds_in_dom. eexact HbS.
    + eapply IHfree_sub_heaps; eassumption.
Qed.

Lemma committed_heap_defs_binds_extends : forall (D:init_ctx) (hds:heap_defs),
  committed_heap_defs D hds ->
  forall D', binds_extends D D' -> committed_heap_defs D' hds.
Proof.
  intros D hds H. induction H; intros D' He.
  - apply committed_heap_defs_nil.
  - apply committed_heap_defs_cons.
    + eapply IHcommitted_heap_defs; exact He.
    + inversion H0; subst.
      * apply committed_heap_def_typ.
      * apply committed_heap_def_trm.
        eapply He. eassumption.
Qed.

Lemma committed_heap_item_binds_extends : forall (G:ctx) (D:init_ctx) (itm:item),
  committed_heap_item G D itm ->
  forall G' D', binds_extends G G' -> binds_extends D D' ->
    committed_heap_item G' D' itm.
Proof.
  intros G D itm H. induction H; intros G' D' HeG HeD.
  - eapply committed_heap_lit.
    refine (@commit_lit_binds_extends Gamma Delta l H G' D' (\{}:vars) (\{}:vars) HeG HeD _).
    apply vs_subset_refl.
  - eapply committed_heap_obj.
    eapply committed_heap_defs_binds_extends; eassumption.
Qed.

Lemma well_committed_heap_extend_lit : forall (G:ctx) (D:init_ctx) (S:heap)
  (x:var) (T:typ) (l:lit),
  well_committed_heap G D S -> x # G -> x # D -> x # S ->
  G ⸴ D ⊢c l ->
  well_committed_heap (G & x ~ T) (D & x ~ committed) (S & x ~ item_lit l).
Proof.
  intros G D S x T l [HG [HD Hitem]] HxG HxD HxS Hc. split; [|split].
  - rewrite !dom_push. rewrite HG. reflexivity.
  - rewrite !dom_push. rewrite HD. reflexivity.
  - intros y itm Hy Hi.
    destruct (classic (y = x)) as [->|Hne].
    + apply binds_push_eq_inv in Hi. subst itm.
      refine (committed_heap_lit (Gamma:=G & x ~ T) (Delta:=D & x ~ committed) (l:=l) _).
      refine (@commit_lit_binds_extends G D l Hc
                (G & x ~ T) (D & x ~ committed) (\{}:vars) (\{}:vars) _ _ _).
      * apply binds_extends_push_fresh. exact HxG.
      * apply binds_extends_push_fresh. exact HxD.
      * apply vs_subset_refl.
    + assert (HyD : binds y committed D) by (eapply binds_push_neq_inv; [exact Hy|exact Hne]).
      assert (HiS : binds y itm S) by (eapply binds_push_neq_inv; [exact Hi|exact Hne]).
      eapply committed_heap_item_binds_extends; [eapply Hitem; [exact HyD|exact HiS]| |].
      * apply binds_extends_push_fresh. exact HxG.
      * apply binds_extends_push_fresh. exact HxD.
Qed.

Lemma free_sub_heap_notin_dom : forall (E:eff_ctx) (S:heap) (D:init_ctx),
  free_sub_heap E S D -> forall x, x # S -> x \notin dom E.
Proof.
  intros E S D H x HxS HxE.
  destruct (dom_binds_exists HxE) as [effs Hb].
  unfold free_sub_heap in H.
  destruct (H x effs Hb) as [_ Hex].
  destruct Hex as [itm [HbS Hfi]].
  apply HxS. eapply binds_in_dom. eexact HbS.
Qed.

Lemma free_sub_heap_extend : forall (E:eff_ctx) (S:heap) (D:init_ctx),
  free_sub_heap E S D ->
  forall (x:var) (itm:item), x # S -> x # D -> x \notin dom E ->
    free_sub_heap E (S & x ~ itm) (D & x ~ committed).
Proof.
  intros E S D H x itm HxS HxD HxE y effs Hy.
  unfold free_sub_heap in H.
  destruct (H y effs Hy) as [Hfresh [itm0 [HbS Hfi]]].
  split; [exact Hfresh|].
  exists itm0. split.
  - assert (Hne : y <> x).
    { intro E0; subst y. exact (HxE (binds_in_dom Hy)). }
    eapply binds_push_neq; [exact HbS|exact Hne].
  - eapply free_heap_item_extend; eassumption.
Qed.

Lemma free_sub_heaps_extend_lit : forall (G:ctx) (D:init_ctx) (S:heap) (Es:list eff_ctx)
  (x:var) (T:typ) (l:lit),
  free_sub_heaps G D S Es -> x # G -> x # D -> x # S ->
  G ⸴ D ⊢c l ->
  free_sub_heaps (G & x ~ T) (D & x ~ committed) (S & x ~ item_lit l) Es.
Proof.
  intros G D S Es x T l H. induction H; intros HxG HxD HxS Hc.
  - apply free_sub_heaps_nil.
    eapply well_committed_heap_extend_lit; eassumption.
  - apply free_sub_heaps_cons.
    + exact H.
    + eapply free_sub_heap_extend; [exact H0|exact HxS|exact HxD|].
      eapply free_sub_heap_notin_dom; eassumption.
    + eapply IHfree_sub_heaps; eassumption.
Qed.

Lemma inert_typ_open_rec : forall (T:typ) (n:nat) (u:var),
  inert_typ T -> inert_typ (open_rec n u T).
Proof.
  intros T n u H. inversion H; subst.
  - apply inert_typ_all.
  - eapply inert_typ_con. eapply record_type_open. eassumption.
  - eapply inert_typ_bnd. eapply record_type_open. eassumption.
Qed.

Lemma inert_typ_open : forall (T:typ) (u:var),
  inert_typ T -> inert_typ (open u T).
Proof. intros. eapply inert_typ_open_rec. exact H. Qed.

Lemma inert_typ_open_rec_vars : forall (T:typ) (k:nat) (ys:list var),
  inert_typ T -> inert_typ (open_rec_vars k ys T).
Proof.
  intros T k ys. revert T k. induction ys; intros T k H.
  - cbn. exact H.
  - cbn. eapply IHys. eapply inert_typ_open_rec. exact H.
Qed.

Lemma inert_typ_open_vars : forall (T:typ) (ys:list var),
  inert_typ T -> inert_typ (open_vars ys T).
Proof. intros. eapply inert_typ_open_rec_vars. exact H. Qed.

Lemma record_typ_open_rec_vars : forall (T:typ) (k:nat) (ys:list var) (ls:fset label),
  record_typ T ls -> record_typ (open_rec_vars k ys T) ls.
Proof.
  intros T k ys ls Hrt. revert T k Hrt.
  induction ys; intros T k Hrt.
  - cbn. exact Hrt.
  - cbn. eapply IHys. eapply record_typ_open. exact Hrt.
Qed.

Lemma record_type_open_rec_vars : forall (T:typ) (k:nat) (ys:list var),
  record_type T -> record_type (open_rec_vars k ys T).
Proof.
  intros T k ys [ls Hrt]. exists ls. eapply record_typ_open_rec_vars. exact Hrt.
Qed.

Lemma record_type_open_vars : forall (T:typ) (ys:list var),
  record_type T -> record_type (open_vars ys T).
Proof. intros. eapply record_type_open_rec_vars. exact H. Qed.

Lemma inert_inits_push_committed : forall (D:init_ctx) (x:var),
  inert_inits D -> inert_inits (D & x ~ committed).
Proof.
  intros D x H y i Hy. unfold inert_inits in *.
  destruct (classic (y = x)) as [->|Hne].
  - apply binds_push_eq_inv in Hy. subst i. right. reflexivity.
  - eapply H. eapply binds_push_neq_inv; eassumption.
Qed.

Lemma inert_inits_push_free : forall (D:init_ctx) (x:var),
  inert_inits D -> inert_inits (D & x ~ free).
Proof.
  intros D x H y i Hy. unfold inert_inits in *.
  destruct (classic (y = x)) as [->|Hne].
  - apply binds_push_eq_inv in Hy. subst i. left. reflexivity.
  - eapply H. eapply binds_push_neq_inv; eassumption.
Qed.

Lemma inert_push : forall (G:ctx) (x:var) (T:typ),
  inert G -> inert_typ T -> x # G -> inert (G & x ~ T).
Proof. intros. eapply inert_all; eassumption. Qed.

Unset Implicit Arguments.

Lemma open_rec_avar_inj : forall (n:nat) (u:var) (a1 a2:avar),
  u \notin fv a1 -> u \notin fv a2 ->
  open_rec n u a1 = open_rec n u a2 -> a1 = a2.
Proof.
  intros n u a1 a2 H1 H2 H.
  destruct a1 as [n1|y1]; destruct a2 as [n2|y2]; simpl in *.
  - destruct (Nat.eq_dec n1 n) as [->|E1];
      destruct (Nat.eq_dec n2 n) as [->|E2].
    + rewrite (If_l (P:=n = n) _ _ eq_refl) in H.
      inversion H. reflexivity.
    + rewrite (If_l (P:=n = n) _ _ eq_refl) in H.
      rewrite (If_r (P:=n = n2) _ _ (fun E => E2 (eq_sym E))) in H.
      discriminate.
    + rewrite (If_r (P:=n = n1) _ _ (fun E => E1 (eq_sym E))) in H.
      rewrite (If_l (P:=n = n) _ _ eq_refl) in H.
      discriminate.
    + rewrite (If_r (P:=n = n1) _ _ (fun E => E1 (eq_sym E))) in H.
      rewrite (If_r (P:=n = n2) _ _ (fun E => E2 (eq_sym E))) in H.
      inversion H. reflexivity.
  - destruct (Nat.eq_dec n1 n) as [->|E1].
    + rewrite (If_l (P:=n = n) _ _ eq_refl) in H.
      inversion H; subst.
      exfalso. apply H2. rewrite in_singleton. reflexivity.
    + rewrite (If_r (P:=n = n1) _ _ (fun E => E1 (eq_sym E))) in H.
      discriminate.
  - destruct (Nat.eq_dec n2 n) as [->|E2].
    + rewrite (If_l (P:=n = n) _ _ eq_refl) in H.
      inversion H; subst.
      exfalso. apply H1. rewrite in_singleton. reflexivity.
    + rewrite (If_r (P:=n = n2) _ _ (fun E => E2 (eq_sym E))) in H.
      discriminate.
  - inversion H. reflexivity.
Qed.

Lemma open_rec_inj_mut :
  (forall (T:typ), forall (n:nat) (u:var) (T2:typ),
      u \notin fv T -> u \notin fv T2 ->
      open_rec n u T = open_rec n u T2 -> T = T2) /\
  (forall (Ts:typs), forall (n:nat) (u:var) (Ts2:typs),
      u \notin fv_typs Ts -> u \notin fv_typs Ts2 ->
      open_rec n u Ts = open_rec n u Ts2 -> Ts = Ts2) /\
  (forall (D:dec), forall (n:nat) (u:var) (D2:dec),
      u \notin fv_dec D -> u \notin fv_dec D2 ->
      open_rec n u D = open_rec n u D2 -> D = D2).
Proof.
  apply (typ_mutind
    (fun T => forall (n:nat) (u:var) (T2:typ),
        u \notin fv T -> u \notin fv T2 ->
        open_rec n u T = open_rec n u T2 -> T = T2)
    (fun Ts => forall (n:nat) (u:var) (Ts2:typs),
        u \notin fv_typs Ts -> u \notin fv_typs Ts2 ->
        open_rec n u Ts = open_rec n u Ts2 -> Ts = Ts2)
    (fun D => forall (n:nat) (u:var) (D2:dec),
        u \notin fv_dec D -> u \notin fv_dec D2 ->
        open_rec n u D = open_rec n u D2 -> D = D2)).
  - intros n u T2 H1 H2 H. destruct T2; simpl in H, H1, H2; try discriminate; reflexivity.
  - intros n u T2 H1 H2 H. destruct T2; simpl in H, H1, H2; try discriminate; reflexivity.
  - intros d IH n u T2 H1 H2 H. destruct T2; simpl in H, H1, H2; try discriminate.
    injection H as Hd. f_equal. eapply (IH n u); [exact H1|exact H2|exact Hd].
  - intros t IHt t0 IHt0 n u T2 H1 H2 H.
    destruct T2; simpl in H, H1, H2; try discriminate.
    injection H as H1' H2'. f_equal.
    + eapply (IHt n u); [| |exact H1'].
      * intro K. apply H1. rewrite in_union. left. exact K.
      * intro K. apply H2. rewrite in_union. left. exact K.
    + eapply (IHt0 n u); [| |exact H2'].
      * intro K. apply H1. rewrite in_union. right. exact K.
      * intro K. apply H2. rewrite in_union. right. exact K.
  - intros a A n u T2 H1 H2 H. destruct T2; simpl in H, H1, H2; try discriminate.
    injection H as Ha HA. subst. f_equal.
    eapply open_rec_avar_inj; eassumption.
  - intros t IH n u T2 H1 H2 H. destruct T2; simpl in H, H1, H2; try discriminate.
    injection H as H'. f_equal. eapply (IH (S n) u); [exact H1|exact H2|exact H'].
  - intros t IHt t0 IHt0 n u T2 H1 H2 H. destruct T2; simpl in H, H1, H2; try discriminate.
    injection H as H1' H2'. f_equal.
    + eapply (IHt n u); [| |exact H1'].
      * intro K. apply H1. rewrite in_union. left. exact K.
      * intro K. apply H2. rewrite in_union. left. exact K.
    + eapply (IHt0 (S n) u); [| |exact H2'].
      * intro K. apply H1. rewrite in_union. right. exact K.
      * intro K. apply H2. rewrite in_union. right. exact K.
  - intros Ts IHts is' T IHt n u T2 H1 H2 H. destruct T2; simpl in H, H1, H2; try discriminate.
    injection H as Hts His HT. subst.
    assert (HeqTs : Ts = t).
    { eapply (IHts n u); [| |exact Hts].
      - intro K. apply H1. rewrite in_union. left. exact K.
      - intro K. apply H2. rewrite in_union. left. exact K. }
    subst t. f_equal.
    eapply (IHt (S (length_s Ts) + n) u);
      [ intro K; apply H1; rewrite in_union; right; exact K
      | intro K; apply H2; rewrite in_union; right; exact K
      | exact HT ].
  - intros n u Ts2 H1 H2 H. destruct Ts2; simpl in H, H1, H2; try discriminate; reflexivity.
  - intros t IHt ts IHts n u Ts2 H1 H2 H. destruct Ts2; simpl in H, H1, H2; try discriminate.
    injection H as H1' H2'. f_equal.
    + eapply (IHt n u); [| |exact H1'].
      * intro K. apply H1. rewrite in_union. left. exact K.
      * intro K. apply H2. rewrite in_union. left. exact K.
    + eapply (IHts n u); [| |exact H2'].
      * intro K. apply H1. rewrite in_union. right. exact K.
      * intro K. apply H2. rewrite in_union. right. exact K.
  - intros A t IHt t0 IHt0 n u D2 H1 H2 H. destruct D2; simpl in H, H1, H2; try discriminate.
    injection H as HA H1' H2'. subst. f_equal.
    + eapply (IHt n u); [| |exact H1'].
      * intro K. apply H1. rewrite in_union. left. exact K.
      * intro K. apply H2. rewrite in_union. left. exact K.
    + eapply (IHt0 n u); [| |exact H2'].
      * intro K. apply H1. rewrite in_union. right. exact K.
      * intro K. apply H2. rewrite in_union. right. exact K.
  - intros a t IHt t0 IHt0 n u D2 H1 H2 H. destruct D2; simpl in H, H1, H2; try discriminate.
    injection H as Ha H1' H2'. subst. f_equal.
    + eapply (IHt n u); [| |exact H1'].
      * intro K. apply H1. rewrite in_union. left. exact K.
      * intro K. apply H2. rewrite in_union. left. exact K.
    + eapply (IHt0 n u); [| |exact H2'].
      * intro K. apply H1. rewrite in_union. right. exact K.
      * intro K. apply H2. rewrite in_union. right; exact K.
Qed.

Corollary open_rec_typ_inj : forall (n:nat) (u:var) (T1 T2:typ),
  u \notin fv T1 -> u \notin fv T2 ->
  open_rec n u T1 = open_rec n u T2 -> T1 = T2.
Proof. intros. eapply (proj1 open_rec_inj_mut); eassumption. Qed.

Lemma record_dec_open_rec_inv : forall (n:nat) (u:var) (D:dec),
  u \notin fv D -> record_dec (open_rec n u D) -> record_dec D.
Proof.
  intros n u D Hf H. destruct D as [A T1 T2|a T1 T2]; simpl in H; simpl in Hf.
  - inversion H; subst.
    assert (Heq : T1 = T2).
    { eapply open_rec_typ_inj.
      - intro K. apply Hf. rewrite in_union. left. exact K.
      - intro K. apply Hf. rewrite in_union. right. exact K.
      - eassumption. }
    subst. apply rd_typ.
  - inversion H; subst.
    assert (Heq : T1 = T2).
    { eapply open_rec_typ_inj.
      - intro K. apply Hf. rewrite in_union. left. exact K.
      - intro K. apply Hf. rewrite in_union. right. exact K.
      - eassumption. }
    subst. apply rd_trm.
Qed.

Lemma record_typ_open_rec_inv_mut :
  (forall (T:typ), forall (n:nat) (u:var) (ls:fset label),
      u \notin fv T -> record_typ (open_rec n u T) ls -> record_typ T ls) /\
  (forall (Ts:typs), True) /\ (forall (D:dec), True).
Proof.
  apply typ_mutind.
  - intros n u ls Hf Hrt. simpl in Hrt. inversion Hrt.
  - intros n u ls Hf Hrt. simpl in Hrt. inversion Hrt.
  - intros d IH n u ls Hf Hrt. simpl in Hf, Hrt.
    destruct (record_typ_rcd_inv Hrt) as [Hrd Hls].
    assert (HrdD : record_dec d) by (eapply record_dec_open_rec_inv; eassumption).
    rewrite Hls, label_of_open_dec. apply rt_one; [exact HrdD|reflexivity].
  - intros t IHt t0 IHt0 n u ls Hf Hrt. simpl in Hf, Hrt.
    destruct (record_typ_and_inv Hrt) as [ls' [D [Hrt1 [HeqU [Hrd [Hnin Hls]]]]]].
    destruct t0 as [| |D2|T2 U2|a2 A2|T2|T2 U2|Ts2 is2 T2]; simpl in HeqU; try discriminate.
    injection HeqU as HeqD. simpl in Hf.
    assert (HrdD : record_dec D2).
    { refine (@record_dec_open_rec_inv n u D2 _ _).
      - intro K. apply Hf. rewrite in_union. right. exact K.
      - change (record_dec (open_rec_dec n u D2)). rewrite HeqD. exact Hrd. }
    rewrite Hls, <- HeqD, label_of_open_dec.
    apply rt_cons; [|exact HrdD|reflexivity|].
    + eapply IHt; [|exact Hrt1].
      intro K. apply Hf. rewrite in_union. left. exact K.
    + rewrite <- HeqD, label_of_open_dec in Hnin. exact Hnin.
  - intros a A n u ls Hf Hrt. simpl in Hrt. inversion Hrt.
  - intros t IH n u ls Hf Hrt. simpl in Hrt. inversion Hrt.
  - intros t IHt t0 IHt0 n u ls Hf Hrt. simpl in Hrt. inversion Hrt.
  - intros Ts IHts is' T IHt n u ls Hf Hrt. simpl in Hrt. inversion Hrt.
  - intros. exact I.
  - intros. exact I.
  - intros. exact I.
  - intros. exact I.
Qed.

Corollary record_typ_open_rec_inv : forall (T:typ) (n:nat) (u:var) (ls:fset label),
  u \notin fv T -> record_typ (open_rec n u T) ls -> record_typ T ls.
Proof. intros. eapply (proj1 record_typ_open_rec_inv_mut); eassumption. Qed.

Corollary record_type_open_rec_inv : forall (T:typ) (n:nat) (u:var),
  u \notin fv T -> record_type (open_rec n u T) -> record_type T.
Proof.
  intros T n u Hf [ls Hrt]. exists ls. eapply record_typ_open_rec_inv; eassumption.
Qed.

Lemma fv_open_rec_avar_subset : forall (n:nat) (u:var) (a:avar) (z:var),
  z \in fv (open_rec n u a) -> z \in fv a \/ z = u.
Proof.
  intros n u a z H. destruct a as [i|y]; simpl in *.
  - destruct (Nat.eq_dec n i) as [E|E].
    + rewrite (If_l (P:=n = i) _ _ E) in H. simpl in H. right.
      rewrite in_singleton in H. exact H.
    + rewrite (If_r (P:=n = i) _ _ E) in H. left. exact H.
  - left. exact H.
Qed.

Lemma fv_open_rec_subset_mut :
  (forall (T:typ) (n:nat) (u z:var),
      z \in fv (open_rec n u T) -> z \in fv T \/ z = u) /\
  (forall (Ts:typs) (n:nat) (u z:var),
      z \in fv_typs (open_rec n u Ts) -> z \in fv_typs Ts \/ z = u) /\
  (forall (D:dec) (n:nat) (u z:var),
      z \in fv_dec (open_rec n u D) -> z \in fv_dec D \/ z = u).
Proof.
  apply typ_mutind.
  - intros n u z H. simpl in H. rewrite in_empty in H. destruct H.
  - intros n u z H. simpl in H. rewrite in_empty in H. destruct H.
  - intros d IH n u z H. simpl in H. simpl. destruct (IH n u z H) as [K|K]; [left|right]; exact K.
  - intros t IHt t0 IHt0 n u z H. simpl in H. simpl.
    rewrite in_union in H. rewrite in_union. destruct H as [H|H].
    + destruct (IHt n u z H) as [K|K]; [left; left|right]; exact K.
    + destruct (IHt0 n u z H) as [K|K]; [left; right|right]; exact K.
  - intros a A n u z H. simpl in H. simpl.
    destruct (fv_open_rec_avar_subset n u a z H) as [K|K]; [left|right]; exact K.
  - intros t IH n u z H. simpl in H. simpl.
    destruct (IH (S n) u z H) as [K|K]; [left|right]; exact K.
  - intros t IHt t0 IHt0 n u z H. simpl in H. simpl.
    rewrite in_union in H. rewrite in_union. destruct H as [H|H].
    + destruct (IHt n u z H) as [K|K]; [left; left|right]; exact K.
    + destruct (IHt0 (S n) u z H) as [K|K]; [left; right|right]; exact K.
  - intros Ts IHts is' T IHt n u z H. simpl in H. simpl.
    rewrite in_union in H. rewrite in_union. destruct H as [H|H].
    + destruct (IHts n u z H) as [K|K]; [left; left|right]; exact K.
    + destruct (IHt (S (length_s Ts) + n) u z H) as [K|K]; [left; right|right]; exact K.
  - intros n u z H. simpl in H. rewrite in_empty in H. destruct H.
  - intros t IHt ts IHts n u z H. simpl in H. simpl.
    rewrite in_union in H. rewrite in_union. destruct H as [H|H].
    + destruct (IHt n u z H) as [K|K]; [left; left|right]; exact K.
    + destruct (IHts n u z H) as [K|K]; [left; right|right]; exact K.
  - intros A t IHt t0 IHt0 n u z H. simpl in H. simpl.
    rewrite in_union in H. rewrite in_union. destruct H as [H|H].
    + destruct (IHt n u z H) as [K|K]; [left; left|right]; exact K.
    + destruct (IHt0 n u z H) as [K|K]; [left; right|right]; exact K.
  - intros a t IHt t0 IHt0 n u z H. simpl in H. simpl.
    rewrite in_union in H. rewrite in_union. destruct H as [H|H].
    + destruct (IHt n u z H) as [K|K]; [left; left|right]; exact K.
    + destruct (IHt0 n u z H) as [K|K]; [left; right|right]; exact K.
Qed.

Corollary fv_open_rec_typ_fresh : forall (T:typ) (n:nat) (u:var) (z:var),
  z \notin fv T -> z <> u -> z \notin fv (open_rec n u T).
Proof.
  intros T n u z Hf Hne K.
  destruct (proj1 fv_open_rec_subset_mut T n u z K) as [Hin|Heq]; eauto.
Qed.

Lemma fresh_NoDup : forall (L:vars) (n:nat) (xs:list var),
  fresh L n xs -> NoDup xs.
Proof.
  intros L n xs. revert L n. induction xs; intros L n Hf.
  - apply NoDup_nil.
  - destruct n as [|n']; [cbn in Hf; contradiction|].
    cbn in Hf. destruct Hf as [HxL Htail].
    apply NoDup_cons.
    + intro Hin.
      assert (Hinx : a \in from_list xs) by (rewrite in_from_list; exact Hin).
      assert (Hnot : a \notin L \u \{a}).
      { eapply fresh_from_list_notin; [exact Htail|exact Hinx]. }
      apply Hnot. rewrite in_union. right. rewrite in_singleton. reflexivity.
    + eapply IHxs. exact Htail.
Qed.

Lemma fresh_add_notin : forall (L:vars) (n:nat) (xs:list var) (x:var),
  fresh L n xs -> x \notin from_list xs -> fresh (L \u \{x}) n xs.
Proof.
  intros L n xs. revert L n. induction xs; intros L n x Hf Hnot.
  - destruct n; [cbn; exact I|cbn in Hf; contradiction].
  - destruct n as [|n']; [cbn in Hf; contradiction|].
    cbn in Hf. destruct Hf as [HyL Htail].
    assert (Hxyn : x <> a).
    { intro E. subst x. apply Hnot. rewrite in_from_list. left. reflexivity. }
    cbn. split.
    + intro K. rewrite in_union in K. destruct K as [K|K].
      * apply HyL. exact K.
      * rewrite in_singleton in K. subst a. apply Hxyn. reflexivity.
    + replace ((L \u \{x}) \u \{a}) with ((L \u \{a}) \u \{x}).
      * eapply IHxs.
        -- exact Htail.
        -- intro K. apply Hnot. rewrite in_from_list. right.
           rewrite in_from_list in K. exact K.
      * apply fset_extens.
        -- intros z Hz. repeat rewrite in_union in Hz.
           repeat rewrite in_union. rewrite !in_singleton in *. tauto.
        -- intros z Hz. repeat rewrite in_union in Hz.
           repeat rewrite in_union. rewrite !in_singleton in *. tauto.
Qed.

Lemma record_type_open_rec_vars_inv : forall (T:typ) (k:nat) (ys:list var),
  NoDup ys ->
  (forall y, y \in from_list ys -> y \notin fv T) ->
  record_type (open_rec_vars k ys T) -> record_type T.
Proof.
  intros T k ys. revert T k. induction ys; intros T k Hnd Hf Hrt.
  - cbn in Hrt. exact Hrt.
  - simpl in Hrt.
    eapply record_type_open_rec_inv.
    + apply Hf. rewrite from_list_cons. rewrite in_union. left.
      rewrite in_singleton. reflexivity.
    + apply NoDup_cons_iff in Hnd. destruct Hnd as [Hnotin Hnd'].
      apply (IHys (open_rec k a T) (S k)).
      * exact Hnd'.
      * intros z Hz. eapply fv_open_rec_typ_fresh.
        -- apply Hf. rewrite from_list_cons. rewrite in_union. right. exact Hz.
        -- intro Ez. subst z.
           apply Hnotin. rewrite in_from_list in Hz. exact Hz.
      * exact Hrt.
Qed.

Lemma lit_typ_inert : forall (G:ctx) (l:lit) (T:typ),
  G ⊢ l ∶ T -> inert_typ T.
Proof.
  intros G l T H. inversion H; subst.
  - apply inert_typ_all.
  - eapply inert_typ_con.
    set (L0 := L \u fv T0).
    destruct (@var_freshes L0 (length_s Ts)) as [ys Hys].
    destruct (@var_fresh (L0 \u from_list ys)) as [x Hx].
    assert (Hx_ys : x \notin from_list ys) by (eapply notin_union_r2; exact Hx).
    assert (Hx_rest : x \notin L0) by (eapply notin_union_r1; exact Hx).
    assert (HxL : x \notin L) by (eapply notin_union_r1; exact Hx_rest).
    assert (Hxfv : x \notin fv T0) by (eapply notin_union_r2; exact Hx_rest).
    assert (HysL : fresh L (length_s Ts) ys) by (eapply fresh_union_r1; exact Hys).
    assert (Hysfv : fresh (fv T0) (length_s Ts) ys) by (eapply fresh_union_r2; exact Hys).
    assert (Hys_nd : NoDup ys) by (eapply fresh_NoDup; exact Hys).
    assert (Hys_notin : forall y, y \in from_list ys -> y \notin fv T0).
    { intros y Hy. eapply fresh_from_list_notin; [exact Hysfv|exact Hy]. }
    assert (Hlen : List.length ys = length_s Ts).
    { rewrite List_length_LibList_length. symmetry. eapply fresh_length. exact Hys. }
    assert (Hfresh_L : fresh L (List.length ys) ys)
      by (eapply fresh_resize; [exact HysL|exact Hlen]).
    assert (Hfresh_Lx : fresh (L \u \{x}) (List.length ys) ys)
      by (eapply fresh_add_notin; [exact Hfresh_L|exact Hx_ys]).
    assert (Hfresh_cons : fresh L (S (length ys)) (cons x ys)).
    { simpl. split; assumption. }
    assert (Hds_ty : exists Gx, Gx ⊢ open_vars (cons x ys) ds ∶ open_vars (cons x ys) T0).
    { eexists. eapply H0; [exact Hlen|exact Hfresh_cons]. }
    destruct Hds_ty as [Gx Hds_ty].
    assert (Hrt_opened : record_type (open_vars (cons x ys) T0)).
    { eapply ty_defs_def_record_type. exact Hds_ty. }
    eapply (@record_type_open_rec_vars_inv T0 0 (cons x ys)).
    + apply NoDup_cons; [rewrite <- in_from_list; exact Hx_ys|exact Hys_nd].
    + intros z Hz. rewrite from_list_cons in Hz. rewrite in_union in Hz.
      destruct Hz as [Hz|Hz].
      * rewrite in_singleton in Hz. subst z. exact Hxfv.
      * eapply Hys_notin; exact Hz.
    + exact Hrt_opened.
Qed.

Lemma free_sub_heaps_wch : forall (G:ctx) (D:init_ctx) (S:heap) (Es:list eff_ctx),
  free_sub_heaps G D S Es -> well_committed_heap G D S.
Proof. intros G D S Es H. induction H; [exact H|apply IHfree_sub_heaps]. Qed.

Lemma init_open_rename_committed_keep : forall (L:fset var) (G:ctx) (D:init_ctx) (vs:vars)
    (T:typ) (t:trm) (x:var) (i:init_typ),
  x \notin dom G -> x \notin dom D ->
  (forall x0, x0 \notin L -> G & x0 ~ T ⸴ D & x0 ~ committed ⸴ vs ⊢i open x0 t ∶ i) ->
  G & x ~ T ⸴ D & x ~ committed ⸴ vs ⊢i open x t ∶ i.
Proof.
  intros L G D vs T t x i HxG HxD Hpre.
  destruct (@var_fresh (((((((L \u dom G) \u fv_env G) \u fv t) \u fv T) \u dom D) \u vs) \u \{x})) as [x0 Hx0].
  pose proof (notin_union_r1 Hx0) as Hx1.
  pose proof (notin_union_r1 Hx1) as Hx2.
  pose proof (notin_union_r1 Hx2) as Hx3.
  pose proof (notin_union_r1 Hx3) as Hx4.
  pose proof (notin_union_r1 Hx4) as Hx5.
  pose proof (notin_union_r1 Hx5) as Hx6.
  pose proof (notin_union_r1 Hx6) as Hx0L.
  pose proof (notin_union_r2 Hx6) as Hx0domG.
  pose proof (notin_union_r2 Hx5) as Hx0fvG.
  pose proof (notin_union_r2 Hx4) as Hx0t.
  pose proof (notin_union_r2 Hx3) as Hx0T.
  pose proof (notin_union_r2 Hx2) as Hx0domD.
  pose proof (notin_union_r2 Hx1) as Hx0vs.
  pose proof (notin_union_r2 Hx0) as Hx0x.
  assert (Hne : x0 <> x) by (exact (@notin_singleton_r x0 x Hx0x)).
  assert (Hprem : G & x0 ~ T ⸴ D & x0 ~ committed ⸴ vs ⊢i open x0 t ∶ i)
    by (apply Hpre; exact Hx0L).
  assert (Hx0_xG : x0 \notin dom G) by exact Hx0domG.
  assert (Hx0_xD : x0 \notin dom D) by exact Hx0domD.
  (* weaken with the extra x bindings, pushed after x0 *)
  assert (Hx_notG0 : x \notin dom (G & x0 ~ T)).
  { rewrite dom_push. intro K. rewrite in_union in K. destruct K as [K|K].
    - rewrite in_singleton in K. exact (Hne (eq_sym K)).
    - exact (HxG K). }
  assert (Hx_notD0 : x \notin dom (D & x0 ~ committed)).
  { rewrite dom_push. intro K. rewrite in_union in K. destruct K as [K|K].
    - rewrite in_singleton in K. exact (Hne (eq_sym K)).
    - exact (HxD K). }
  assert (HextG : binds_extends (G & x0 ~ T) ((G & x0 ~ T) & x ~ T))
    by (apply binds_extends_push_fresh; exact Hx_notG0).
  assert (HextD : binds_extends (D & x0 ~ committed) ((D & x0 ~ committed) & x ~ committed))
    by (apply binds_extends_push_fresh; exact Hx_notD0).
  pose proof (@init_binds_extends (G & x0 ~ T) (D & x0 ~ committed) vs (open x0 t) i Hprem
                ((G & x0 ~ T) & x ~ T) ((D & x0 ~ committed) & x ~ committed) vs
                HextG HextD (@vs_subset_refl vs)) as Hbody.
  (* prepare the init_subst arguments *)
  assert (Hx0_G2 : x0 # (x ~ T : ctx)).
  { rewrite dom_single. intro K. rewrite in_singleton in K. exact (Hne K). }
  assert (Hx0_D2 : x0 # (x ~ committed : init_ctx)).
  { rewrite dom_single. intro K. rewrite in_singleton in K. exact (Hne K). }
  assert (HsubstT : subst_var x0 x T = T).
  { apply (@fv_subst_typ T x0 x Hx0T). }
  assert (HpreS : (G & subst_env x0 x (x ~ T)) ⊢ trm_var (avar_f x) ∶ subst_var x0 x T).
  { apply ty_var. rewrite map_single. apply binds_push_eq. }
  assert (Hbinds : binds x committed (D & (x ~ committed : init_ctx))).
  { apply binds_push_eq. }
  pose proof (@init_subst ((G & x0 ~ T) & x ~ T) ((D & x0 ~ committed) & x ~ committed)
                vs (open x0 t) i Hbody
                G (x ~ T : ctx) D (x ~ committed : init_ctx) x0 x T
                eq_refl eq_refl
                Hx0_G2 Hx0_D2 Hx0fvG HpreS Hbinds) as Hres.
  rewrite map_single in Hres.
  rewrite HsubstT in Hres.
  assert (H0 : subst_var x0 x vs = vs) by (apply (@vars_subst_notin vs x0 x Hx0vs)).
  rewrite H0 in Hres.
  rewrite <- (@subst_intro_trm t x0 x 0 Hx0t) in Hres.
  exact Hres.
Qed.

Lemma init_trm_lit_commit_lit : forall (G:ctx) (D:init_ctx) (vs:vars)
  (T:typ) (l:lit) (t:trm) (i:init_typ),
  G ⸴ D ⸴ vs ⊢i trm_lit T l t ∶ i -> G ⸴ D ⊢c l.
Proof.
  intros G D vs T l t i H. inversion H; subst; try discriminate.
  - inversion H0; subst. eassumption.
  - eassumption.
Qed.

Definition eff_vars (effs:effects) : vars := from_list (List.map (fun e => fst e) effs).

Lemma eff_vars_notin : forall (effs:effects) (z:var),
  z \notin eff_vars effs -> forall e, List.In e effs -> fst e <> z.
Proof.
  intros effs z H e Hin E.
  apply H. unfold eff_vars. rewrite in_from_list.
  rewrite <- E. apply List.in_map. exact Hin.
Qed.

Lemma rename_eff_map_id : forall (x y:var) (effs:effects),
  (forall e, List.In e effs -> fst e <> x) ->
  List.map (rename_eff x y) effs = effs.
Proof.
  intros x y effs H. induction effs as [|e effs IH].
  - simpl. reflexivity.
  - destruct e as [v l]. simpl in *.
    assert (Hfe : v <> x) by (apply (H (v,l)); left; reflexivity).
    unfold rename_eff. simpl.
    rewrite (@subst_if_neq x y v Hfe).
    f_equal. apply IH. intros e0 H0. apply H. right. exact H0.
Qed.

Lemma eff_trm_llit_open : forall (L:fset var) (t:trm) (effs:effects),
  (forall z, z \notin L -> eff_trm (open z t) effs) ->
  forall x, eff_trm (open x t) effs.
Proof.
  intros L t effs H x.
  destruct (@var_fresh ((L \u fv t \u eff_vars effs) \u \{x})) as [z Hz].
  pose proof (notin_union_r1 Hz) as Hz1.
  pose proof (notin_union_r2 Hz) as Hzx.
  pose proof (notin_union_r1 Hz1) as HzL.
  pose proof (notin_union_r2 Hz1) as Hzfveff.
  pose proof (notin_union_r1 Hzfveff) as Hzfv.
  pose proof (notin_union_r2 Hzfveff) as Hzeff.
  pose proof (H z HzL) as Hzpre.
  rewrite (@subst_intro_trm t z x 0 Hzfv).
  pose proof (@eff_trm_subst (open z t) effs Hzpre z x) as Hsub.
  rewrite (rename_eff_map_id z x effs (eff_vars_notin effs z Hzeff)) in Hsub.
  exact Hsub.
Qed.


Lemma ty_trm_lit_inv : forall (G:ctx) (T:typ) (l:lit) (t:trm) (U:typ),
  G ⊢ trm_lit T l t ∶ U ->
  exists (L:fset var) (U0:typ),
    G ⊢ l ∶ T /\
    (forall x0, x0 \notin L -> G & x0 ~ T ⊢ open x0 t ∶ U0) /\
    G ⊢ U0 <: U.
Proof.
  intros G T l t U H. remember (trm_lit T l t) as tm eqn:Heq.
  induction H; try discriminate Heq.
  - (* ty_llit *) inversion Heq; subst.
    exists L, U. split; [|split]; [exact H|exact H0|apply subtyp_refl].
  - (* ty_sub *) apply IHty_trm in Heq.
    destruct Heq as [L [U0 [Hlit [Hbody Hsub]]]].
    exists L, U0. split; [|split]; [exact Hlit|exact Hbody|].
    eapply subtyp_trans; eassumption.
Qed.

Lemma commit_open_rename_keep : forall (L:fset var) (G:ctx) (D:init_ctx)
    (T:typ) (t:trm) (x:var),
  x \notin dom G -> x \notin dom D ->
  (forall x0, x0 \notin L -> G & x0 ~ T ⸴ D & x0 ~ committed ⊢c open x0 t) ->
  G & x ~ T ⸴ D & x ~ committed ⊢c open x t.
Proof.
  intros L G D T t x HxG HxD Hpre.
  destruct (@var_fresh ((((((L \u dom G) \u fv_env G) \u fv t) \u fv T) \u dom D) \u \{x})) as [x0 Hx0].
  pose proof (notin_union_r1 Hx0) as Hx1.
  pose proof (notin_union_r1 Hx1) as Hx2.
  pose proof (notin_union_r1 Hx2) as Hx3.
  pose proof (notin_union_r1 Hx3) as Hx4.
  pose proof (notin_union_r1 Hx4) as Hx5.
  pose proof (notin_union_r1 Hx5) as Hx0L.
  pose proof (notin_union_r2 Hx5) as Hx0domG.
  pose proof (notin_union_r2 Hx4) as Hx0fvG.
  pose proof (notin_union_r2 Hx3) as Hx0t.
  pose proof (notin_union_r2 Hx2) as Hx0T.
  pose proof (notin_union_r2 Hx1) as Hx0domD.
  pose proof (notin_union_r2 Hx0) as Hx0x.
  assert (Hne : x0 <> x) by (exact (@notin_singleton_r x0 x Hx0x)).
  assert (Hprem : G & x0 ~ T ⸴ D & x0 ~ committed ⊢c open x0 t)
    by (apply Hpre; exact Hx0L).
  assert (Hx_notG0 : x \notin dom (G & x0 ~ T)).
  { rewrite dom_push. intro K. rewrite in_union in K. destruct K as [K|K].
    - rewrite in_singleton in K. exact (Hne (eq_sym K)).
    - exact (HxG K). }
  assert (Hx_notD0 : x \notin dom (D & x0 ~ committed)).
  { rewrite dom_push. intro K. rewrite in_union in K. destruct K as [K|K].
    - rewrite in_singleton in K. exact (Hne (eq_sym K)).
    - exact (HxD K). }
  assert (HextG : binds_extends (G & x0 ~ T) ((G & x0 ~ T) & x ~ T))
    by (apply binds_extends_push_fresh; exact Hx_notG0).
  assert (HextD : binds_extends (D & x0 ~ committed) ((D & x0 ~ committed) & x ~ committed))
    by (apply binds_extends_push_fresh; exact Hx_notD0).
  pose proof (@commit_binds_extends (G & x0 ~ T) (D & x0 ~ committed) (open x0 t) Hprem
                ((G & x0 ~ T) & x ~ T) ((D & x0 ~ committed) & x ~ committed) \{} \{}
                HextG HextD (@vs_subset_refl \{})) as Hbody.
  assert (Hx0_G2 : x0 # (x ~ T : ctx)).
  { rewrite dom_single. intro K. rewrite in_singleton in K. exact (Hne K). }
  assert (Hx0_D2 : x0 # (x ~ committed : init_ctx)).
  { rewrite dom_single. intro K. rewrite in_singleton in K. exact (Hne K). }
  assert (HsubstT : subst_var x0 x T = T).
  { apply (@fv_subst_typ T x0 x Hx0T). }
  assert (HpreS : (G & subst_env x0 x (x ~ T)) ⊢ trm_var (avar_f x) ∶ subst_var x0 x T).
  { apply ty_var. rewrite map_single. apply binds_push_eq. }
  assert (Hbinds : binds x committed (D & (x ~ committed : init_ctx))).
  { apply binds_push_eq. }
  pose proof (@commit_subst ((G & x0 ~ T) & x ~ T) ((D & x0 ~ committed) & x ~ committed)
                (open x0 t) Hbody
                G (x ~ T : ctx) D (x ~ committed : init_ctx) x0 x T
                eq_refl eq_refl Hx0_G2 Hx0_D2 Hx0fvG HpreS Hbinds) as Hres.
  rewrite map_single in Hres.
  rewrite HsubstT in Hres.
  rewrite <- (@subst_intro_trm t x0 x 0 Hx0t) in Hres.
  exact Hres.
Qed.

Lemma init_trm_lit_open : forall (G:ctx) (D:init_ctx) (vs:vars)
    (T:typ) (l:lit) (t:trm) (i:init_typ) (x:var),
  x \notin dom G -> x \notin dom D ->
  G ⸴ D ⸴ vs ⊢i trm_lit T l t ∶ i ->
  G & x ~ T ⸴ D & x ~ committed ⸴ vs ⊢i open x t ∶ i.
Proof.
  intros G D vs T l t i x HxG HxD H. inversion H; subst; try discriminate.
  - (* init_commit *) inversion H0; subst.
    eapply init_commit.
    eapply commit_open_rename_keep; [exact HxG|exact HxD|exact H7].
  - (* init_llit *)
    eapply init_open_rename_committed_keep; [exact HxG|exact HxD|exact H8].
Qed.

Lemma eff_trm_lit_open : forall (T:typ) (l:lit) (t:trm) (effs:effects) (x:var),
  eff_trm (trm_lit T l t) effs -> eff_trm (open x t) effs.
Proof.
  intros T l t effs x H. inversion H; subst; try discriminate.
  - apply eff_ignore.
  - eapply eff_trm_llit_open; exact H4.
Qed.

Lemma ty_config_inv_s : forall (G:ctx) (D:init_ctx) (Es:list eff_ctx) (effss:list effects)
    (t:trm) (s:stack) (Sigma:heap) (U:typ),
  ty_config G D Es effss (t ; s ; Sigma) U ->
  exists ℰ ℰs T i effs effs' effss0,
    Es = ℰ :: ℰs /\
    effss = ((effs' ++ effs) :: effss0)%list /\
    inert G /\
    inert_inits D /\
    heap_correspond G Sigma /\
    free_sub_heaps G D Sigma (ℰ :: ℰs) /\
    ty_stack G D (ℰ :: ℰs) s T i (effs :: effss0) U /\
    G ⊢ t ∶ T /\
    ⊢e t ∶ effs' /\
    G ⸴ D ⸴ dom ℰ ⊢i t ∶ i /\
    eff_ctx_corr (ℰ :: ℰs) (List.app effs' effs :: effss0).
Proof.
  intros G D Es effss t s Sigma U H. inversion H; subst.
  eexists ℰ, ℰs, T, i, effs, effs', effss0. repeat split; try reflexivity; try eassumption;
    try (exact (proj1 H5)); try (exact (proj2 H5)).
Qed.

Lemma ty_config_red_let_lit : forall (G:ctx) (D:init_ctx) (Es:list eff_ctx)
  (effss:list effects) (Fs:stack) (i0:init_typ) (effsS:list effects)
  (Sigma:heap) (U TL:typ) (l:lit) (t:trm) (x:var),
  ty_config G D Es effss (trm_lit TL l t ; Fs ; Sigma) U ->
  x # Sigma ->
  exists G' D' Es' effss',
    ty_config (G & G') D' Es' effss' (open x t ; Fs ; Sigma & x ~ (item_lit l)) U.
Proof.
  intros G D Es effss Fs i0 effsS Sigma U TL l t x Hcfg HxS.
  destruct (ty_config_inv_s G D Es effss (trm_lit TL l t) Fs Sigma U Hcfg) as
    (ℰ & ℰs & Ts & ii & effsH & effs' & effss0 &
     HeqEs & Heqeff & Hinert & Hinits & Hhc & Hfs & Hstack & Hty & Heff & Hinit & Hcorr).
  destruct (ty_trm_lit_inv G TL l t Ts Hty) as (L & U0 & Hlit & Hbody & Hsub).
  pose proof (free_sub_heaps_wch G D Sigma (ℰ::ℰs) Hfs) as Hwc.
  destruct Hwc as [HG [HD _]].
  assert (HxG : x # G) by (intro K; apply HxS; rewrite <- HD, <- HG; exact K).
  assert (HxD : x # D) by (intro K; apply HxS; rewrite <- HD; exact K).
  assert (Hlit' : G & x ~ TL ⊢ l ∶ TL).
  { eapply ty_lit_binds_extends; [exact Hlit|apply binds_extends_push_fresh; exact HxG]. }
  assert (Hcomm : G ⸴ D ⊢c l) by (exact (init_trm_lit_commit_lit G D (dom ℰ) TL l t ii Hinit)).
  assert (Hinert' : inert (G & x ~ TL)).
  { eapply inert_all; [exact Hinert|eapply lit_typ_inert; exact Hlit|exact HxG]. }
  assert (Hinits' : inert_inits (D & x ~ committed)).
  { exact (@inert_inits_push_committed D x Hinits). }
  assert (Hhc' : heap_correspond (G & x ~ TL) (Sigma & x ~ item_lit l)).
  { eapply heap_correspond_extend_lit; eassumption. }
  assert (Hfs' : free_sub_heaps (G & x ~ TL) (D & x ~ committed)
                   (Sigma & x ~ item_lit l) (ℰ :: ℰs)).
  { eapply free_sub_heaps_extend_lit; eassumption. }
  assert (Hstack' : ty_stack (G & x ~ TL) (D & x ~ committed) (ℰ :: ℰs)
                       Fs Ts ii (effsH :: effss0) U).
  { eapply ty_stack_weaken_GD; [exact Hstack|apply binds_extends_push_fresh; exact HxG|
                                apply binds_extends_push_fresh; exact HxD]. }
  assert (Hbody' : G & x ~ TL ⊢ open x t ∶ U0).
  { eapply ty_lit_open_rename; [exact HxG|exact Hbody]. }
  assert (Hsub' : G & x ~ TL ⊢ U0 <: Ts).
  { eapply subtyp_binds_extends; [exact Hsub|apply binds_extends_push_fresh; exact HxG]. }
  assert (Hty' : G & x ~ TL ⊢ open x t ∶ Ts).
  { eapply ty_sub; [exact Hbody'|exact Hsub']. }
  assert (Heff' : eff_trm (open x t) effs').
  { eapply eff_trm_lit_open. exact Heff. }
  assert (Hinit' : G & x ~ TL ⸴ D & x ~ committed ⸴ dom ℰ ⊢i open x t ∶ ii).
  { eapply init_trm_lit_open; eassumption. }
  exists (x ~ TL : ctx), (D & x ~ committed : init_ctx), (ℰ :: ℰs),
    ((List.app effs' effsH :: effss0)%list).
  eapply ty_config_c; eassumption.
Qed.

Lemma ty_trm_let_inv : forall (G:ctx) (T:typ) (s t:trm) (U:typ),
  G ⊢ trm_let T s t ∶ U ->
  exists (L:fset var) (U0:typ),
    G ⊢ s ∶ T /\
    (forall x0, x0 \notin L -> G & x0 ~ T ⊢ open x0 t ∶ U0) /\
    G ⊢ U0 <: U.
Proof.
  intros G T s t U H. remember (trm_let T s t) as tm eqn:Heq.
  induction H; try discriminate Heq.
  - (* ty_let *) inversion Heq; subst.
    exists L, U. split; [|split]; [exact H|exact H0|apply subtyp_refl].
  - (* ty_sub *) apply IHty_trm in Heq.
    destruct Heq as [L [U0 [Hs [Hbody Hsub]]]].
    exists L, U0. split; [|split]; [exact Hs|exact Hbody|].
    eapply subtyp_trans; eassumption.
Qed.

Lemma eff_trm_let_inv : forall (T:typ) (s t:trm) (effs:effects),
  eff_trm (trm_let T s t) effs ->
  exists (L:fset var) (eff1 eff2:effects),
    effs = (eff1 ++ eff2)%list /\
    eff_trm s eff1 /\
    (forall x0, x0 \notin L -> eff_trm (open x0 t) eff2).
Proof.
  intros T s t effs H. inversion H; subst; try discriminate.
  - exists (\{}:vars), (nil:effects), (nil:effects). split; [reflexivity|split].
    + apply eff_ignore.
    + intros x0 Hx0. apply eff_ignore.
  - exists L, eff1, eff2. split; [reflexivity|split]; assumption.
Qed.

Lemma init_trm_let_inv : forall (G:ctx) (D:init_ctx) (vs:vars)
    (T:typ) (s t:trm) (i:init_typ),
  G ⸴ D ⸴ vs ⊢i trm_let T s t ∶ i ->
  exists (L:fset var) (is:init_typ),
    G ⸴ D ⸴ vs ⊢i s ∶ is /\
    (forall x0, x0 \notin L -> G & x0 ~ T ⸴ D & x0 ~ is ⸴ (vs \u \{x0}) ⊢i open x0 t ∶ i).
Proof.
  intros G D vs T s t i H. inversion H; subst; try discriminate.
  - (* init_commit *) inversion H0; subst.
    exists L, committed. split.
    + eapply init_commit. exact H5.
    + intros x0 Hx0. apply init_commit. eapply H7; exact Hx0.
  - (* init_let *) exists L, i0. split; [exact H7|exact H8].
Qed.

Lemma ty_config_red_let_sta : forall (G:ctx) (D:init_ctx) (Es:list eff_ctx)
  (effss:list effects) (Fs:stack) (i0:init_typ) (effsS:list effects)
  (Sigma:heap) (U TL:typ) (s t:trm),
  ty_config G D Es effss (trm_let TL s t ; Fs ; Sigma) U ->
  exists G' D' Es' effss',
    ty_config (G & G') D' Es' effss' (s ; (frame_let t :: Fs)%list ; Sigma) U.
Proof.
  intros G D Es effss Fs i0 effsS Sigma U TL s t Hcfg.
  destruct (ty_config_inv_s G D Es effss (trm_let TL s t) Fs Sigma U Hcfg) as
    (ℰ & ℰs & Ts & ii & effsH & effs' & effss0 &
     HeqEs & Heqeff & Hinert & Hinits & Hhc & Hfs & Hstack & Hty & Heff & Hinit & Hcorr).
  destruct (ty_trm_let_inv G TL s t Ts Hty) as (L & U0 & Hty_s & Hbody_ty & Hsub).
  destruct (eff_trm_let_inv TL s t effs' Heff) as (Le & eff1 & eff2 & Heqeffs & Heff_s & Hbody_eff).
  destruct (init_trm_let_inv G D (dom ℰ) TL s t ii Hinit) as (Li & is & Hinit_s & Hbody_init).
  rewrite Heqeffs in Hcorr.
  rewrite <- List.app_assoc in Hcorr.
  assert (Hstack' : ty_stack G D (ℰ :: ℰs) (frame_let t :: Fs)%list TL is
                     (((eff2 ++ effsH)%list) :: effss0) U).
  { eapply ty_stack_let with (L := L \u Le \u Li \u dom G)
      (T := Ts) (i' := ii) (effs := effsH) (effss := effss0)
      (effs' := eff2) (t := t) (S := TL) (i := is).
    - exact Hstack.
    - intros x0 Hx0.
      assert (HxL : x0 \notin L) by (intro K; apply Hx0; repeat rewrite in_union; tauto).
      assert (HxG0 : x0 # G) by (intro K; apply Hx0; repeat rewrite in_union; tauto).
      eapply ty_sub.
      + eapply Hbody_ty; exact HxL.
      + eapply subtyp_binds_extends; [exact Hsub|apply binds_extends_push_fresh; exact HxG0].
    - intros x0 Hx0.
      assert (HxLi : x0 \notin Li) by (intro K; apply Hx0; repeat rewrite in_union; tauto).
      eapply Hbody_init; exact HxLi.
    - intros x0 Hx0.
      assert (HxLe : x0 \notin Le) by (intro K; apply Hx0; repeat rewrite in_union; tauto).
      eapply Hbody_eff; exact HxLe.
  }
  exists (empty:ctx), D, (ℰ :: ℰs), (((eff1 ++ (eff2 ++ effsH))%list) :: effss0).
  rewrite concat_empty_r.
  eapply ty_config_c; eassumption.
Qed.

Lemma progress_trm_var : forall (G:ctx) (D:init_ctx) (Es:list eff_ctx)
  (effss:list effects) (Fs:stack) (Sigma:heap) (U:typ) (y:var),
  ty_config G D Es effss (trm_var (avar_f y) ; Fs ; Sigma) U ->
  answer (trm_var (avar_f y) ; Fs ; Sigma) \/
  exists s' Sigma' t', (trm_var (avar_f y) ; Fs ; Sigma) ↦ (t' ; s' ; Sigma').
Proof.
  intros G D Es effss Fs Sigma U y Hcfg.
  destruct Fs as [|f Fs].
  - left. apply nf_loc.
  - destruct f as [t|z].
    + right. exists Fs, Sigma, (open y t). apply red_let_var.
    + right. exists Fs, Sigma, (trm_var (avar_f z)). apply red_return.
Qed.

Lemma progress_trm_let : forall (G:ctx) (D:init_ctx) (Es:list eff_ctx)
  (effss:list effects) (Fs:stack) (Sigma:heap) (U:typ) (TL:typ) (s t:trm),
  ty_config G D Es effss (trm_let TL s t ; Fs ; Sigma) U ->
  answer (trm_let TL s t ; Fs ; Sigma) \/
  exists s' Sigma' t', (trm_let TL s t ; Fs ; Sigma) ↦ (t' ; s' ; Sigma').
Proof.
  intros. right. exists (frame_let t :: Fs)%list, Sigma, s. apply red_let_sta.
Qed.

Lemma progress_trm_lit : forall (G:ctx) (D:init_ctx) (Es:list eff_ctx)
  (effss:list effects) (Fs:stack) (Sigma:heap) (U TL:typ) (l:lit) (t:trm),
  ty_config G D Es effss (trm_lit TL l t ; Fs ; Sigma) U ->
  answer (trm_lit TL l t ; Fs ; Sigma) \/
  exists s' Sigma' t', (trm_lit TL l t ; Fs ; Sigma) ↦ (t' ; s' ; Sigma').
Proof.
  intros. right.
  destruct (@var_fresh (dom Sigma)) as [x Hx].
  exists Fs, (Sigma & x ~ item_lit l), (open x t).
  eapply red_let_lit. exact Hx.
Qed.

Lemma ty_config_pop_ret_free : forall (G:ctx) (D:init_ctx) (ℰ:eff_ctx) (ℰs:list eff_ctx)
  (Fs:stack) (Sigma:heap) (U Ttail:typ) (x:var) (effs:effects) (effssTail:list effects),
  inert G ->
  inert_inits D ->
  heap_correspond G Sigma ->
  free_sub_heaps G D Sigma (ℰ :: ℰs) ->
  ty_stack G D (ℰ :: ℰs) Fs Ttail free ((effs :: effssTail)%list) U ->
  G ⊢ trm_var (avar_f x) ∶ Ttail ->
  G ⸴ D ⸴ dom ℰ ⊢i trm_var (avar_f x) ∶ free ->
  eff_ctx_corr (ℰ :: ℰs) ((effs :: effssTail)%list) ->
  exists G' D' Es' effss',
    ty_config (G & G') D' Es' effss' (trm_var (avar_f x) ; Fs ; Sigma) U.
Proof.
  intros G D ℰ ℰs Fs Sigma U Ttail x effs effssTail
         Hinert Hinits Hhc Hfs Hstack Hty Hinit Hcorr.
  exists (empty:ctx), D, (ℰ :: ℰs), ((effs :: effssTail)%list).
  rewrite concat_empty_r.
  eapply (@ty_config_c G D Sigma ℰ ℰs Fs (trm_var (avar_f x)) Ttail free U nil effs effssTail).
  - exact Hinert.
  - exact Hinits.
  - exact Hhc.
  - exact Hfs.
  - exact Hstack.
  - exact Hty.
  - apply eff_ignore.
  - exact Hinit.
  - exact Hcorr.
Qed.

Lemma ty_trm_open_any : forall (L:fset var) (G:ctx) (S T:typ) (t:trm) (y:var),
  (forall x0, x0 \notin L -> G & x0 ~ S ⊢ open x0 t ∶ T) ->
  G ⊢ trm_var (avar_f y) ∶ S ->
  G ⊢ open y t ∶ T.
Proof.
  intros L G S T t y Hbody Hty.
  destruct (@var_fresh ((((((L \u dom G) \u fv_env G) \u fv t) \u fv S) \u fv T) \u \{y})) as [x0 Hx0].
  pose proof (notin_union_r1 Hx0) as Hx1.
  pose proof (notin_union_r1 Hx1) as Hx2.
  pose proof (notin_union_r1 Hx2) as Hx3.
  pose proof (notin_union_r1 Hx3) as Hx4.
  pose proof (notin_union_r1 Hx4) as Hx5.
  pose proof (notin_union_r1 Hx5) as HxL.
  pose proof (notin_union_r2 Hx5) as Hxdom.
  pose proof (notin_union_r2 Hx4) as Hxfvenv.
  pose proof (notin_union_r2 Hx3) as Hxt.
  pose proof (notin_union_r2 Hx2) as HxS.
  pose proof (notin_union_r2 Hx1) as HxT.
  pose proof (notin_union_r2 Hx0) as Hxy.
  assert (Hxempty : x0 # (empty:ctx)) by (rewrite (@dom_empty typ); apply notin_empty).
  assert (Hprem : G & x0 ~ S ⊢ open x0 t ∶ T) by (apply Hbody; exact HxL).
  assert (Hprem' : G & x0 ~ S & empty ⊢ open x0 t ∶ T)
    by (rewrite concat_empty_r; exact Hprem).
  assert (Hpre : (G & subst_env x0 y (empty:ctx)) ⊢ trm_var (avar_f y) ∶ subst_var x0 y S).
  { rewrite map_empty. rewrite concat_empty_r.
    rewrite (@fv_subst_typ S x0 y HxS). exact Hty. }
  pose proof (@ty_trm_subst G (empty:ctx) x0 y S (open x0 t) T Hprem' Hxempty Hxfvenv Hpre) as Hres.
  rewrite map_empty in Hres. rewrite concat_empty_r in Hres.
  rewrite (@fv_subst_typ T x0 y HxT) in Hres.
  rewrite <- (@subst_intro_trm t x0 y 0 Hxt) in Hres.
  exact Hres.
Qed.

Lemma init_typing_vs_weaken_mut :
  (forall (G:ctx) (D:init_ctx) (t:trm), G ⸴ D ⊢c t -> True) /\
  (forall (G:ctx) (D:init_ctx) (avs:avars), G ⸴ D ⊢c avs -> True) /\
  (forall (G:ctx) (D:init_ctx) (l:lit), G ⸴ D ⊢c l -> True) /\
  (forall (G:ctx) (D:init_ctx) (vs:vars) (t:trm) (i:init_typ),
      G ⸴ D ⸴ vs ⊢i t ∶ i ->
      forall vs', vs_subset vs vs' -> G ⸴ D ⸴ vs' ⊢i t ∶ i) /\
  (forall (G:ctx) (D:init_ctx) (vs:vars) (avs:avars) (is':inits),
      G ⸴ D ⸴ vs ⊢i avs :: is' ->
      forall vs', vs_subset vs vs' -> G ⸴ D ⸴ vs' ⊢i avs :: is').
Proof.
  apply well_init_mut_ind; intros.
  - exact I.
  - exact I.
  - exact I.
  - exact I.
  - exact I.
  - exact I.
  - exact I.
  - exact I.
  - exact I.
  - exact I.
  - exact I.
  - (* init_var_binds *) eapply init_var_binds.
    eapply init_var_transfer; [eapply binds_extends_refl|exact H|exact i0].
  - (* init_commit *) eapply init_commit. exact c.
  - (* init_new_free *) eapply init_new_free; [exact c|exact t|eapply H0; exact H1].
  - (* init_fld_asn_ac *) eapply init_fld_asn_ac; [eapply H; exact H1|eapply H0; exact H1].
  - (* init_fld_asn_ff *) eapply init_fld_asn_ff; [eapply H; exact H1|eapply H0; exact H1].
  - (* init_let *) eapply init_let with (L:=L).
    + eapply H; exact H1.
    + intros x Hx. eapply H0; [exact Hx|apply vs_subset_remove; exact H1].
  - (* init_llit *) eapply init_llit with (L:=L).
    + exact c.
    + intros x Hx. eapply H0; [exact Hx|exact H1].
  - (* inits_nil *) apply well_inits_nil.
  - (* inits_cons *) eapply well_inits_cons; [eapply H; exact H1|eapply H0; exact H1].
Qed.

Corollary init_typing_vs_weaken : forall (G:ctx) (D:init_ctx) (vs vs':vars) (t:trm) (i:init_typ),
  vs_subset vs vs' -> G ⸴ D ⸴ vs ⊢i t ∶ i -> G ⸴ D ⸴ vs' ⊢i t ∶ i.
Proof.
  intros. eapply (proj1 (proj2 (proj2 (proj2 init_typing_vs_weaken_mut)))); eassumption.
Qed.

Lemma init_var_remove_committed : forall (D:init_ctx) (vs:vars) (x:var) (i:init_typ) (y:var),
  binds y committed D -> init_var D vs x i -> init_var D (vs \- \{y}) x i.
Proof.
  intros D vs x i y Hb H. induction H.
  - apply init_var_commit. exact H.
  - apply init_var_free.
    + rewrite FsetImpl.in_remove. split; [exact H|].
      intro E. rewrite in_singleton in E. rewrite E in H0.
      pose proof (@LibEnv.binds_functional init_typ y free committed Delta H0 Hb) as E2.
      discriminate E2.
    + exact H0.
  - apply init_var_unspec.
    + rewrite FsetImpl.in_remove. split; [exact H|].
      intro E. rewrite in_singleton in E. rewrite E in H0.
      pose proof (@LibEnv.binds_functional init_typ y unspecified committed Delta H0 Hb) as E2.
      discriminate E2.
    + exact H0.
  - eapply init_var_sub; [eapply IHinit_var; exact Hb|exact H0].
Qed.

Lemma vs_remove_union_subset : forall (vs:vars) (x y:var),
  vs_subset ((vs \u \{x}) \- \{y}) ((vs \- \{y}) \u \{x}).
Proof.
  intros vs x y z Hz.
  rewrite FsetImpl.in_remove in Hz. destruct Hz as [Hz Hne].
  rewrite in_union in Hz. rewrite in_union.
  destruct Hz as [Hz|Hz].
  - left. rewrite FsetImpl.in_remove. split; assumption.
  - right. exact Hz.
Qed.


Lemma init_typing_vs_remove_committed_mut (y:var) :
  (forall (G:ctx) (D:init_ctx) (t:trm), G ⸴ D ⊢c t -> True) /\
  (forall (G:ctx) (D:init_ctx) (avs:avars), G ⸴ D ⊢c avs -> True) /\
  (forall (G:ctx) (D:init_ctx) (l:lit), G ⸴ D ⊢c l -> True) /\
  (forall (G:ctx) (D:init_ctx) (vs:vars) (t:trm) (i:init_typ),
      G ⸴ D ⸴ vs ⊢i t ∶ i ->
      binds y committed D -> G ⸴ D ⸴ (vs \- \{y}) ⊢i t ∶ i) /\
  (forall (G:ctx) (D:init_ctx) (vs:vars) (avs:avars) (is':inits),
      G ⸴ D ⸴ vs ⊢i avs :: is' ->
      binds y committed D -> G ⸴ D ⸴ (vs \- \{y}) ⊢i avs :: is').
Proof.
  apply well_init_mut_ind; intros.
  - exact I.
  - exact I.
  - exact I.
  - exact I.
  - exact I.
  - exact I.
  - exact I.
  - exact I.
  - exact I.
  - exact I.
  - exact I.
  - (* init_var_binds *) eapply init_var_binds.
    eapply init_var_remove_committed; [exact H|exact i0].
  - (* init_commit *) eapply init_commit. exact c.
  - (* init_new_free *) eapply init_new_free; [exact c|exact t|eapply H0; exact H1].
  - (* init_fld_asn_ac *) eapply init_fld_asn_ac; [eapply H; exact H1|eapply H0; exact H1].
  - (* init_fld_asn_ff *) eapply init_fld_asn_ff; [eapply H; exact H1|eapply H0; exact H1].
  - (* init_let *) eapply init_let with (L := L \u \{y}).
    + eapply H; exact H1.
    + intros x Hx.
      assert (HxL : x \notin L) by (eapply notin_union_r1; exact Hx).
      assert (Hxy : x \notin \{y}) by (eapply notin_union_r2; exact Hx).
      assert (Hb' : binds y committed (Delta & x ~ i)).
      { eapply LibEnv.binds_push_neq; [exact H1|].
        intro E. apply Hxy. rewrite in_singleton. symmetry. exact E. }
      eapply init_typing_vs_weaken.
      * apply vs_remove_union_subset.
      * eapply H0; [exact HxL|exact Hb'].
  - (* init_llit *) eapply init_llit with (L := L \u \{y}).
    + exact c.
    + intros x Hx.
      assert (HxL : x \notin L) by (eapply notin_union_r1; exact Hx).
      assert (Hxy : x \notin \{y}) by (eapply notin_union_r2; exact Hx).
      assert (Hb' : binds y committed (Delta & x ~ committed)).
      { eapply LibEnv.binds_push_neq; [exact H1|].
        intro E. apply Hxy. rewrite in_singleton. symmetry. exact E. }
      eapply H0; [exact HxL|exact Hb'].
  - (* inits_nil *) apply well_inits_nil.
  - (* inits_cons *) eapply well_inits_cons; [eapply H; exact H1|eapply H0; exact H1].
Qed.

Corollary init_typing_vs_remove_committed : forall (G:ctx) (D:init_ctx) (vs:vars)
  (t:trm) (i:init_typ) (y:var),
  binds y committed D -> G ⸴ D ⸴ vs ⊢i t ∶ i -> G ⸴ D ⸴ (vs \- \{y}) ⊢i t ∶ i.
Proof.
  intros. eapply (proj1 (proj2 (proj2 (proj2 (init_typing_vs_remove_committed_mut y))))); eassumption.
Qed.

Lemma subst_var_union_self : forall (vs:vars) (x0 y:var),
  x0 \notin vs -> subst_var x0 y (vs \u \{x0}) = vs \u \{y}.
Proof.
  intros vs x0 y Hx0.
  unfold subst_var, VarsSubstVar. cbn.
  assert (Hin : x0 \in vs \u \{x0}) by (rewrite in_union; right; rewrite in_singleton; reflexivity).
  rewrite (If_l (P:=x0 \in vs \u \{x0}) _ _ Hin).
  apply fset_extens.
  - intros z Hz.
    rewrite !in_union in Hz. rewrite FsetImpl.in_remove in Hz.
    rewrite in_union in Hz. rewrite !in_singleton in Hz.
    destruct Hz as [[[Hz|Hz] Hne]|Hy].
    + rewrite in_union. left. exact Hz.
    + exfalso. apply Hne. rewrite in_singleton. exact Hz.
    + rewrite in_union. right. rewrite in_singleton. exact Hy.
  - intros z Hz.
    rewrite in_union in Hz. rewrite in_union.
    rewrite FsetImpl.in_remove.
    destruct Hz as [Hz|Hy].
    + left. split.
      * rewrite in_union. left. exact Hz.
      * intro E. rewrite in_singleton in E. subst z. exact (Hx0 Hz).
    + right. exact Hy.
Qed.

Lemma vs_remove_subset : forall (vs:vars) (y:var), vs_subset (vs \- \{y}) vs.
Proof.
  intros vs y z Hz. rewrite FsetImpl.in_remove in Hz. exact (proj1 Hz).
Qed.

Lemma init_open_committed_any : forall (L:fset var) (G:ctx) (D:init_ctx) (vs:vars)
  (T:typ) (t:trm) (i':init_typ) (y:var),
  binds y committed D ->
  G ⊢ trm_var (avar_f y) ∶ T ->
  (forall x0, x0 \notin L -> G & x0 ~ T ⸴ D & x0 ~ committed ⸴ (vs \u \{x0}) ⊢i open x0 t ∶ i') ->
  G ⸴ D ⸴ vs ⊢i open y t ∶ i'.
Proof.
  intros L G D vs T t i' y Hb Hty Hbody.
  destruct (@var_fresh (((((((L \u dom G) \u fv_env G) \u fv t) \u fv T) \u dom D) \u vs) \u \{y})) as [x0 Hx0].
  pose proof (notin_union_r1 Hx0) as Hx1.
  pose proof (notin_union_r1 Hx1) as Hx2.
  pose proof (notin_union_r1 Hx2) as Hx3.
  pose proof (notin_union_r1 Hx3) as Hx4.
  pose proof (notin_union_r1 Hx4) as Hx5.
  pose proof (notin_union_r1 Hx5) as Hx6.
  pose proof (notin_union_r1 Hx6) as HxL.
  pose proof (notin_union_r2 Hx6) as HxdomG.
  pose proof (notin_union_r2 Hx5) as Hxfvenv.
  pose proof (notin_union_r2 Hx4) as Hxt.
  pose proof (notin_union_r2 Hx3) as HxT.
  pose proof (notin_union_r2 Hx2) as HxdomD.
  pose proof (notin_union_r2 Hx1) as Hxvs.
  pose proof (notin_union_r2 Hx0) as Hxy.
  assert (HxemptyG : x0 # (empty:ctx)) by (rewrite (@dom_empty typ); apply notin_empty).
  assert (HxemptyD : x0 # (empty:init_ctx)) by (rewrite (@dom_empty init_typ); apply notin_empty).
  assert (Hbody0 : G & x0 ~ T ⸴ D & x0 ~ committed ⸴ (vs \u \{x0}) ⊢i open x0 t ∶ i')
    by (apply Hbody; exact HxL).
  assert (Hbody0' : G & x0 ~ T & empty ⸴ D & x0 ~ committed & empty ⸴ (vs \u \{x0}) ⊢i open x0 t ∶ i').
  { rewrite concat_empty_r. rewrite concat_empty_r. exact Hbody0. }
  assert (HpreS : (G & subst_env x0 y (empty:ctx)) ⊢ trm_var (avar_f y) ∶ subst_var x0 y T).
  { rewrite map_empty. rewrite concat_empty_r.
    rewrite (@fv_subst_typ T x0 y HxT). exact Hty. }
  assert (Hb' : binds y committed (D & empty)) by (rewrite concat_empty_r; exact Hb).
  pose proof (@init_subst (G & x0 ~ T & empty) (D & x0 ~ committed & empty)
                (vs \u \{x0}) (open x0 t) i' Hbody0'
                G (empty:ctx) D (empty:init_ctx) x0 y T
                eq_refl eq_refl HxemptyG HxemptyD Hxfvenv HpreS Hb') as Hres.
  rewrite map_empty in Hres. rewrite concat_empty_r in Hres.
  assert (Hvs : subst_var x0 y (vs \u \{x0}) = vs \u \{y})
    by (apply subst_var_union_self; exact Hxvs).
  assert (Hres2 : G ⸴ D ⸴ (vs \u \{y}) ⊢i open y t ∶ i').
  { rewrite (@subst_intro_trm t x0 y 0 Hxt).
    rewrite <- Hvs.
    rewrite <- (@concat_empty_r init_typ D).
    exact Hres. }
  assert (Hrm : G ⸴ D ⸴ ((vs \u \{y}) \- \{y}) ⊢i open y t ∶ i').
  { eapply init_typing_vs_remove_committed; [exact Hb|exact Hres2]. }
  eapply init_typing_vs_weaken with (vs := ((vs \u \{y}) \- \{y})).
  - intros z Hz. rewrite FsetImpl.in_remove in Hz.
    destruct Hz as [Hin Hne]. rewrite in_union in Hin.
    destruct Hin as [Hin|Hin]; [exact Hin|].
    exfalso. apply Hne. exact Hin.
  - exact Hrm.
Qed.

Lemma ty_config_let_var_committed : forall (L:fset var) (G:ctx) (D:init_ctx)
  (ℰ:eff_ctx) (ℰs:list eff_ctx) (Fs:stack) (Sigma:heap) (U S T2:typ)
  (i':init_typ) (effs_frame effs_tail:effects) (effss_tail:list effects)
  (t:trm) (y:var),
  inert G -> inert_inits D -> heap_correspond G Sigma ->
  free_sub_heaps G D Sigma (ℰ :: ℰs) ->
  ty_stack G D (ℰ :: ℰs) Fs T2 i' ((effs_tail :: effss_tail)%list) U ->
  G ⊢ trm_var (avar_f y) ∶ S ->
  (forall x0, x0 \notin L -> G & x0 ~ S ⊢ open x0 t ∶ T2) ->
  (forall x0, x0 \notin L ->
     G & x0 ~ S ⸴ D & x0 ~ committed ⸴ (dom ℰ \u \{x0}) ⊢i open x0 t ∶ i') ->
  (forall x0, x0 \notin L -> eff_trm (open x0 t) effs_frame) ->
  binds y committed D ->
  eff_ctx_corr (ℰ :: ℰs) (((effs_frame ++ effs_tail)%list :: effss_tail)%list) ->
  exists G' D' Es' effss',
    ty_config (G & G') D' Es' effss' (open y t ; Fs ; Sigma) U.
Proof.
  intros L G D ℰ ℰs Fs Sigma U S T2 i' effs_frame effs_tail effss_tail t y
         Hinert Hinits Hhc Hfs Hstack Hty Hbody_ty Hbody_init Hbody_eff Hb Hcorr.
  assert (Hty' : G ⊢ open y t ∶ T2).
  { eapply ty_trm_open_any; [exact Hbody_ty|exact Hty]. }
  assert (Heff' : eff_trm (open y t) effs_frame).
  { eapply eff_trm_llit_open; exact Hbody_eff. }
  assert (Hinit' : G ⸴ D ⸴ dom ℰ ⊢i open y t ∶ i').
  { eapply init_open_committed_any; [exact Hb|exact Hty|exact Hbody_init]. }
  exists (empty:ctx), D, (ℰ :: ℰs),
    (((effs_frame ++ effs_tail)%list :: effss_tail)%list).
  rewrite concat_empty_r.
  eapply (@ty_config_c G D Sigma ℰ ℰs Fs (open y t) T2 i' U effs_frame effs_tail effss_tail).
  - exact Hinert.
  - exact Hinits.
  - exact Hhc.
  - exact Hfs.
  - exact Hstack.
  - exact Hty'.
  - exact Heff'.
  - exact Hinit'.
  - exact Hcorr.
Qed.

Lemma init_var_committed_binds : forall (D:init_ctx) (vs:vars) (x:var),
  init_var D vs x committed -> binds x committed D.
Proof.
  intros D vs x H. remember committed as i eqn:Heq. induction H; subst.
  - exact H.
  - inversion H0; subst; discriminate.
  - inversion H0; subst; discriminate.
  - inversion H0; subst. apply IHinit_var. reflexivity.
Qed.

Lemma init_typing_var_committed_binds : forall (G:ctx) (D:init_ctx) (vs:vars) (x:var),
  G ⸴ D ⸴ vs ⊢i trm_var (avar_f x) ∶ committed -> binds x committed D.
Proof.
  intros G D vs x H. inversion H; subst; try discriminate.
  - eapply init_var_committed_binds. exact H4.
  - inversion H0; subst; try discriminate. exact H4.
Qed.

Lemma init_var_subst_gen_param : forall (D1 D2:init_ctx) (vs:vars) (xm ym x:var) (ib it ix:init_typ),
  xm # D2 ->
  binds ym it (D1 & D2) ->
  init_sub it ib ->
  init_var (D1 & xm ~ ib & D2) vs x ix ->
  init_var (D1 & D2) (subst_var xm ym vs) (x \[xm -> ym]) ix.
Proof.
  intros D1 D2 vs xm ym x ib it ix HxD Hbinds Hsub Hin.
  remember (D1 & xm ~ ib & D2) as Delta eqn:Heq.
  induction Hin.
  - (* commit *) subst Delta.
    destruct (classic (x = xm)) as [->|Hne].
    + rewrite (@subst_if_eq xm ym). apply init_var_commit.
      assert (Hsrc : binds xm ib (D1 & xm ~ ib & D2)) by (eapply init_var_split; exact HxD).
      pose proof (@LibEnv.binds_functional init_typ xm ib committed (D1 & xm ~ ib & D2)
                    (@init_var_split D1 D2 xm ib HxD) H) as Hbi.
      subst ib.
      assert (Hit : it = committed).
      { inversion Hsub; subst; reflexivity. }
      subst it. exact Hbinds.
    + rewrite (@subst_if_neq xm ym x Hne). apply init_var_commit.
      eapply (@binds_drop_middle init_typ D1 D2 xm x committed ib);
        [exact Hne|exact H].
  - (* free *) subst Delta.
    destruct (classic (x = xm)) as [->|Hne].
    + rewrite (@subst_if_eq xm ym). apply init_var_free.
      * eapply in_vars_subst_self. exact H.
      * assert (Hsrc : binds xm ib (D1 & xm ~ ib & D2)) by (eapply init_var_split; exact HxD).
        pose proof (@LibEnv.binds_functional init_typ xm ib free (D1 & xm ~ ib & D2)
                      (@init_var_split D1 D2 xm ib HxD) H0) as Hbi.
        subst ib.
        assert (Hit : it = free) by (inversion Hsub; subst; reflexivity).
        subst it. exact Hbinds.
    + rewrite (@subst_if_neq xm ym x Hne). apply init_var_free.
      * eapply (@in_vars_subst vs xm ym x); [exact H|exact Hne].
      * eapply (@binds_drop_middle init_typ D1 D2 xm x free ib);
          [exact Hne|exact H0].
  - (* unspec *) subst Delta.
    destruct (classic (x = xm)) as [->|Hne].
    + rewrite (@subst_if_eq xm ym).
      assert (Hsrc : binds xm ib (D1 & xm ~ ib & D2)) by (eapply init_var_split; exact HxD).
      pose proof (@LibEnv.binds_functional init_typ xm ib unspecified (D1 & xm ~ ib & D2)
                    (@init_var_split D1 D2 xm ib HxD) H0) as Hbi.
      subst ib.
      inversion Hsub; subst.
      * apply init_var_unspec. { eapply in_vars_subst_self. exact H. } { exact Hbinds. }
      * eapply init_var_sub. { apply init_var_commit. exact Hbinds. } { apply init_sub_comm_unspec. }
      * eapply init_var_sub. { apply init_var_free. { eapply in_vars_subst_self. exact H. } { exact Hbinds. } }
        apply init_sub_free_unspec.
    + rewrite (@subst_if_neq xm ym x Hne). apply init_var_unspec.
      * eapply (@in_vars_subst vs xm ym x); [exact H|exact Hne].
      * eapply (@binds_drop_middle init_typ D1 D2 xm x unspecified ib);
          [exact Hne|exact H0].
  - (* sub *) eapply init_var_sub.
    + apply IHHin. exact Heq.
    + exact H.
Qed.

Unset Implicit Arguments.

Module GenSubst.
Section Param.
Variables (ib it : init_typ).
Hypothesis Hsub : init_sub it ib.

Lemma init_var_subst_gen_param : forall (D1 D2:init_ctx) (vs:vars) (xm ym x:var) (ix:init_typ),
  xm # D2 ->
  binds ym it (D1 & D2) ->
  init_var (D1 & xm ~ ib & D2) vs x ix ->
  init_var (D1 & D2) (subst_var xm ym vs) (x \[xm -> ym]) ix.
Proof.
  intros D1 D2 vs xm ym x ix HxD Hbinds Hin.
  remember (D1 & xm ~ ib & D2) as Delta eqn:Heq.
  induction Hin.
  - (* commit *) subst Delta.
    destruct (classic (x = xm)) as [->|Hne].
    + rewrite (@subst_if_eq xm ym). apply init_var_commit.
      assert (Hsrc : binds xm ib (D1 & xm ~ ib & D2)) by (eapply init_var_split; exact HxD).
      pose proof (@LibEnv.binds_functional init_typ xm ib committed (D1 & xm ~ ib & D2)
                    (@init_var_split D1 D2 xm ib HxD) H) as Hbi.
      subst ib.
      assert (Hit : it = committed).
      { inversion Hsub; subst; reflexivity. }
      subst it. exact Hbinds.
    + rewrite (@subst_if_neq xm ym x Hne). apply init_var_commit.
      eapply (@binds_drop_middle init_typ D1 D2 xm x committed ib);
        [exact Hne|exact H].
  - (* free *) subst Delta.
    destruct (classic (x = xm)) as [->|Hne].
    + rewrite (@subst_if_eq xm ym). apply init_var_free.
      * eapply in_vars_subst_self. exact H.
      * assert (Hsrc : binds xm ib (D1 & xm ~ ib & D2)) by (eapply init_var_split; exact HxD).
        pose proof (@LibEnv.binds_functional init_typ xm ib free (D1 & xm ~ ib & D2)
                      (@init_var_split D1 D2 xm ib HxD) H0) as Hbi.
        subst ib.
        assert (Hit : it = free) by (inversion Hsub; subst; reflexivity).
        subst it. exact Hbinds.
    + rewrite (@subst_if_neq xm ym x Hne). apply init_var_free.
      * eapply (@in_vars_subst vs xm ym x); [exact H|exact Hne].
      * eapply (@binds_drop_middle init_typ D1 D2 xm x free ib);
          [exact Hne|exact H0].
  - (* unspec *) subst Delta.
    destruct (classic (x = xm)) as [->|Hne].
    + rewrite (@subst_if_eq xm ym).
      assert (Hsrc : binds xm ib (D1 & xm ~ ib & D2)) by (eapply init_var_split; exact HxD).
      pose proof (@LibEnv.binds_functional init_typ xm ib unspecified (D1 & xm ~ ib & D2)
                    (@init_var_split D1 D2 xm ib HxD) H0) as Hbi.
      subst ib.
      inversion Hsub; subst.
      * apply init_var_unspec. { eapply in_vars_subst_self. exact H. } { exact Hbinds. }
      * eapply init_var_sub. { apply init_var_commit. exact Hbinds. } { apply init_sub_comm_unspec. }
      * eapply init_var_sub. { apply init_var_free. { eapply in_vars_subst_self. exact H. } { exact Hbinds. } }
        apply init_sub_free_unspec.
    + rewrite (@subst_if_neq xm ym x Hne). apply init_var_unspec.
      * eapply (@in_vars_subst vs xm ym x); [exact H|exact Hne].
      * eapply (@binds_drop_middle init_typ D1 D2 xm x unspecified ib);
          [exact Hne|exact H0].
  - (* sub *) eapply init_var_sub.
    + apply IHHin. exact Heq.
    + exact H.
Qed.

Definition QcF (G:ctx) (D:init_ctx) (t:trm) : Prop :=
  forall G1 G2 D1 D2 xm ym Sm,
    G = G1 & xm ~ Sm & G2 ->
    D = D1 & xm ~ ib & D2 ->
    xm # G2 -> xm # D2 -> xm \notin fv_env G1 ->
    (G1 & subst_env xm ym G2 ⊢ trm_var (avar_f ym) ∶ subst_var xm ym Sm) ->
    binds ym it (D1 & D2) ->
    G1 & subst_env xm ym G2 ⸴ D1 & D2 ⊢c subst_var xm ym t.

Definition QaF (G:ctx) (D:init_ctx) (avs:avars) : Prop :=
  forall G1 G2 D1 D2 xm ym Sm,
    G = G1 & xm ~ Sm & G2 ->
    D = D1 & xm ~ ib & D2 ->
    xm # G2 -> xm # D2 -> xm \notin fv_env G1 ->
    (G1 & subst_env xm ym G2 ⊢ trm_var (avar_f ym) ∶ subst_var xm ym Sm) ->
    binds ym it (D1 & D2) ->
    G1 & subst_env xm ym G2 ⸴ D1 & D2 ⊢c subst_var xm ym avs.

Definition QlF (G:ctx) (D:init_ctx) (l:lit) : Prop :=
  forall G1 G2 D1 D2 xm ym Sm,
    G = G1 & xm ~ Sm & G2 ->
    D = D1 & xm ~ ib & D2 ->
    xm # G2 -> xm # D2 -> xm \notin fv_env G1 ->
    (G1 & subst_env xm ym G2 ⊢ trm_var (avar_f ym) ∶ subst_var xm ym Sm) ->
    binds ym it (D1 & D2) ->
    G1 & subst_env xm ym G2 ⸴ D1 & D2 ⊢c subst_var xm ym l.

Definition QiF (G:ctx) (D:init_ctx) (vs:vars) (t:trm) (i:init_typ) : Prop :=
  forall G1 G2 D1 D2 xm ym Sm,
    G = G1 & xm ~ Sm & G2 ->
    D = D1 & xm ~ ib & D2 ->
    xm # G2 -> xm # D2 -> xm \notin fv_env G1 ->
    (G1 & subst_env xm ym G2 ⊢ trm_var (avar_f ym) ∶ subst_var xm ym Sm) ->
    binds ym it (D1 & D2) ->
    G1 & subst_env xm ym G2 ⸴ D1 & D2 ⸴ subst_var xm ym vs
      ⊢i subst_var xm ym t ∶ i.

Definition QisF (G:ctx) (D:init_ctx) (vs:vars) (avs:avars) (is':inits) : Prop :=
  forall G1 G2 D1 D2 xm ym Sm,
    G = G1 & xm ~ Sm & G2 ->
    D = D1 & xm ~ ib & D2 ->
    xm # G2 -> xm # D2 -> xm \notin fv_env G1 ->
    (G1 & subst_env xm ym G2 ⊢ trm_var (avar_f ym) ∶ subst_var xm ym Sm) ->
    binds ym it (D1 & D2) ->
    G1 & subst_env xm ym G2 ⸴ D1 & D2 ⸴ subst_var xm ym vs
      ⊢i subst_var xm ym avs :: is'.

Set Implicit Arguments.

(** * Helpers for the easy commit rules *)

Lemma sc_commit_var : forall (G1 G2:ctx) (D1 D2:init_ctx) (xm ym:var) (Sm:typ) (x:var),
  xm # D2 ->
  binds ym it (D1 & D2) ->
  binds x committed (D1 & xm ~ ib & D2) ->
  G1 & subst_env xm ym G2 ⸴ D1 & D2 ⊢c subst_var xm ym (trm_var (avar_f x)).
Proof.
  intros G1 G2 D1 D2 xm ym Sm x HxD Hbinds Hb.
  simpl.
  destruct (classic (x = xm)) as [->|Hne].
  - rewrite (@subst_if_eq xm ym). apply commit_var.
    assert (Hsrc : binds xm ib (D1 & xm ~ ib & D2)).
    { eapply LibEnv.binds_concat_left.
      - apply LibEnv.binds_push_eq.
      - exact HxD. }
    assert (Hi : ib = committed).
    { eapply (@LibEnv.binds_functional init_typ xm ib committed (D1 & xm ~ ib & D2)).
      - exact Hsrc.
      - exact Hb. }
    subst ib.
    assert (Hit : it = committed).
    { inversion Hsub; subst; reflexivity. }
    subst it. exact Hbinds.
  - rewrite (@subst_if_neq xm ym x Hne). apply commit_var.
    eapply (@binds_drop_middle init_typ D1 D2 xm x committed ib);
      [exact Hne|exact Hb].
Qed.

Lemma sc_commit_all_elim : forall (G1 G2:ctx) (D1 D2:init_ctx) (xm ym:var) (Sm:typ) (x z:var),
  QcF (G1 & xm ~ Sm & G2) (D1 & xm ~ ib & D2) (trm_var (avar_f x)) ->
  QcF (G1 & xm ~ Sm & G2) (D1 & xm ~ ib & D2) (trm_var (avar_f z)) ->
  xm # G2 -> xm # D2 -> xm \notin fv_env G1 ->
  (G1 & subst_env xm ym G2 ⊢ trm_var (avar_f ym) ∶ subst_var xm ym Sm) ->
  binds ym it (D1 & D2) ->
  G1 & subst_env xm ym G2 ⸴ D1 & D2
    ⊢c subst_var xm ym (trm_app (avar_f x) (avar_f z)).
Proof.
  intros G1 G2 D1 D2 xm ym Sm x z Hx Hz HxG HxD Hfv Hpre Hbinds.
  unfold QcF in Hx, Hz. simpl. eapply commit_all_elim.
  - refine (Hx G1 G2 D1 D2 xm ym Sm _ _ _ _ _ _ _);
      [reflexivity|reflexivity|exact HxG|exact HxD|exact Hfv|exact Hpre|exact Hbinds].
  - refine (Hz G1 G2 D1 D2 xm ym Sm _ _ _ _ _ _ _);
      [reflexivity|reflexivity|exact HxG|exact HxD|exact Hfv|exact Hpre|exact Hbinds].
Qed.

Lemma sc_commit_new : forall (G1 G2:ctx) (D1 D2:init_ctx) (xm ym:var) (Sm:typ)
    (x:var) (avs:avars) (Ts:typs) (is':inits) (T:typ),
  QcF (G1 & xm ~ Sm & G2) (D1 & xm ~ ib & D2) (trm_var (avar_f x)) ->
  QaF (G1 & xm ~ Sm & G2) (D1 & xm ~ ib & D2) avs ->
  (G1 & xm ~ Sm & G2 ⊢ trm_var (avar_f x) ∶ typ_con Ts is' T) ->
  all_comm_unspec is' ->
  xm # G2 -> xm # D2 -> xm \notin fv_env G1 ->
  (G1 & subst_env xm ym G2 ⊢ trm_var (avar_f ym) ∶ subst_var xm ym Sm) ->
  binds ym it (D1 & D2) ->
  G1 & subst_env xm ym G2 ⸴ D1 & D2
    ⊢c subst_var xm ym (trm_new (avar_f x) avs).
Proof.
  intros G1 G2 D1 D2 xm ym Sm x avs Ts is' T Hx Havs Hty Hacu HxG HxD Hfv Hpre Hbinds.
  unfold QcF in Hx. unfold QaF in Havs. simpl. eapply commit_new.
  - eapply Hx; [reflexivity|reflexivity|exact HxG|exact HxD|exact Hfv|exact Hpre|exact Hbinds].
  - pose proof (@ty_trm_subst G1 G2 xm ym Sm (trm_var (avar_f x))
                  (typ_con Ts is' T) Hty HxG Hfv Hpre) as Hty'.
    simpl in Hty'. exact Hty'.
  - exact Hacu.
  - refine (Havs G1 G2 D1 D2 xm ym Sm _ _ _ _ _ _ _);
      [reflexivity|reflexivity|exact HxG|exact HxD|exact Hfv|exact Hpre|exact Hbinds].
Qed.

Lemma sc_commit_rcd_elim : forall (G1 G2:ctx) (D1 D2:init_ctx) (xm ym:var) (Sm:typ)
    (x:var) (a:trm_label),
  QcF (G1 & xm ~ Sm & G2) (D1 & xm ~ ib & D2) (trm_var (avar_f x)) ->
  xm # G2 -> xm # D2 -> xm \notin fv_env G1 ->
  (G1 & subst_env xm ym G2 ⊢ trm_var (avar_f ym) ∶ subst_var xm ym Sm) ->
  binds ym it (D1 & D2) ->
  G1 & subst_env xm ym G2 ⸴ D1 & D2
    ⊢c subst_var xm ym (trm_sel (avar_f x) a).
Proof.
  intros G1 G2 D1 D2 xm ym Sm x a Hx HxG HxD Hfv Hpre Hbinds.
  unfold QcF in Hx. simpl. eapply commit_rcd_elim.
  eapply Hx; [reflexivity|reflexivity|exact HxG|exact HxD|exact Hfv|exact Hpre|exact Hbinds].
Qed.

Lemma sc_commit_fld_asn : forall (G1 G2:ctx) (D1 D2:init_ctx) (xm ym:var) (Sm:typ)
    (x y:var) (a:trm_label),
  QcF (G1 & xm ~ Sm & G2) (D1 & xm ~ ib & D2) (trm_var (avar_f x)) ->
  QcF (G1 & xm ~ Sm & G2) (D1 & xm ~ ib & D2) (trm_var (avar_f y)) ->
  xm # G2 -> xm # D2 -> xm \notin fv_env G1 ->
  (G1 & subst_env xm ym G2 ⊢ trm_var (avar_f ym) ∶ subst_var xm ym Sm) ->
  binds ym it (D1 & D2) ->
  G1 & subst_env xm ym G2 ⸴ D1 & D2
    ⊢c subst_var xm ym (trm_asn (avar_f x) a (avar_f y)).
Proof.
  intros G1 G2 D1 D2 xm ym Sm x y a Hx Hy HxG HxD Hfv Hpre Hbinds.
  unfold QcF in Hx, Hy. simpl. eapply (@commit_fld_asn _ _ _ unspecified _ _).
  - refine (Hx G1 G2 D1 D2 xm ym Sm _ _ _ _ _ _ _);
      [reflexivity|reflexivity|exact HxG|exact HxD|exact Hfv|exact Hpre|exact Hbinds].
  - refine (Hy G1 G2 D1 D2 xm ym Sm _ _ _ _ _ _ _);
      [reflexivity|reflexivity|exact HxG|exact HxD|exact Hfv|exact Hpre|exact Hbinds].
Qed.

Lemma sc_commit_avars_nil : forall (G1 G2:ctx) (D1 D2:init_ctx) (xm ym:var) (Sm:typ),
  G1 & subst_env xm ym G2 ⸴ D1 & D2 ⊢c subst_var xm ym (@nil avar).
Proof. intros. simpl. apply committed_nil. Qed.

Lemma sc_commit_avars_cons : forall (G1 G2:ctx) (D1 D2:init_ctx) (xm ym:var) (Sm:typ)
    (x:var) (avs:avars),
  QcF (G1 & xm ~ Sm & G2) (D1 & xm ~ ib & D2) (trm_var (avar_f x)) ->
  QaF (G1 & xm ~ Sm & G2) (D1 & xm ~ ib & D2) avs ->
  xm # G2 -> xm # D2 -> xm \notin fv_env G1 ->
  (G1 & subst_env xm ym G2 ⊢ trm_var (avar_f ym) ∶ subst_var xm ym Sm) ->
  binds ym it (D1 & D2) ->
  G1 & subst_env xm ym G2 ⸴ D1 & D2
    ⊢c subst_var xm ym (cons (avar_f x) avs).
Proof.
  intros G1 G2 D1 D2 xm ym Sm x avs Hx Havs HxG HxD Hfv Hpre Hbinds.
  unfold QcF in Hx. unfold QaF in Havs. simpl. eapply committed_cons.
  - refine (Hx G1 G2 D1 D2 xm ym Sm _ _ _ _ _ _ _);
      [reflexivity|reflexivity|exact HxG|exact HxD|exact Hfv|exact Hpre|exact Hbinds].
  - refine (Havs G1 G2 D1 D2 xm ym Sm _ _ _ _ _ _ _);
      [reflexivity|reflexivity|exact HxG|exact HxD|exact Hfv|exact Hpre|exact Hbinds].
Qed.

(** * Helpers for the easy init rules *)

Lemma si_init_var_binds : forall (G1 G2:ctx) (D1 D2:init_ctx) (xm ym:var) (Sm:typ)
    (vs:vars) (x:var) (i:init_typ),
  xm # D2 ->
  binds ym it (D1 & D2) ->
  init_var (D1 & xm ~ ib & D2) vs x i ->
  G1 & subst_env xm ym G2 ⸴ D1 & D2 ⸴ subst_var xm ym vs
    ⊢i subst_var xm ym (trm_var (avar_f x)) ∶ i.
Proof.
  intros G1 G2 D1 D2 xm ym Sm vs x i HxD Hbinds Hin.
  simpl. apply init_var_binds.
  eapply (@init_var_subst_gen_param D1 D2 vs xm ym x i); eassumption.
Qed.

Lemma si_init_commit : forall (G1 G2:ctx) (D1 D2:init_ctx) (xm ym:var) (Sm:typ)
    (vs:vars) (t:trm),
  QcF (G1 & xm ~ Sm & G2) (D1 & xm ~ ib & D2) t ->
  xm # G2 -> xm # D2 -> xm \notin fv_env G1 ->
  (G1 & subst_env xm ym G2 ⊢ trm_var (avar_f ym) ∶ subst_var xm ym Sm) ->
  binds ym it (D1 & D2) ->
  G1 & subst_env xm ym G2 ⸴ D1 & D2 ⸴ subst_var xm ym vs
    ⊢i subst_var xm ym t ∶ committed.
Proof.
  intros G1 G2 D1 D2 xm ym Sm vs t Ht HxG HxD Hfv Hpre Hbinds.
  unfold QcF in Ht. simpl. apply init_commit.
  refine (Ht G1 G2 D1 D2 xm ym Sm _ _ _ _ _ _ _);
    [reflexivity|reflexivity|exact HxG|exact HxD|exact Hfv|exact Hpre|exact Hbinds].
Qed.

Lemma si_init_new_free : forall (G1 G2:ctx) (D1 D2:init_ctx) (xm ym:var) (Sm:typ)
    (vs:vars) (x:var) (avs:avars) (Ts:typs) (is':inits) (T:typ),
  QcF (G1 & xm ~ Sm & G2) (D1 & xm ~ ib & D2) (trm_var (avar_f x)) ->
  QisF (G1 & xm ~ Sm & G2) (D1 & xm ~ ib & D2) vs avs is' ->
  (G1 & xm ~ Sm & G2 ⊢ trm_var (avar_f x) ∶ typ_con Ts is' T) ->
  xm # G2 -> xm # D2 -> xm \notin fv_env G1 ->
  (G1 & subst_env xm ym G2 ⊢ trm_var (avar_f ym) ∶ subst_var xm ym Sm) ->
  binds ym it (D1 & D2) ->
  G1 & subst_env xm ym G2 ⸴ D1 & D2 ⸴ subst_var xm ym vs
    ⊢i subst_var xm ym (trm_new (avar_f x) avs) ∶ free.
Proof.
  intros G1 G2 D1 D2 xm ym Sm vs x avs Ts is' T Hx Havs Hty HxG HxD Hfv Hpre Hbinds.
  unfold QcF in Hx. unfold QisF in Havs. simpl. eapply init_new_free.
  - refine (Hx G1 G2 D1 D2 xm ym Sm _ _ _ _ _ _ _);
      [reflexivity|reflexivity|exact HxG|exact HxD|exact Hfv|exact Hpre|exact Hbinds].
  - pose proof (@ty_trm_subst G1 G2 xm ym Sm (trm_var (avar_f x))
                  (typ_con Ts is' T) Hty HxG Hfv Hpre) as Hty'.
    simpl in Hty'. exact Hty'.
  - refine (Havs G1 G2 D1 D2 xm ym Sm _ _ _ _ _ _ _);
      [reflexivity|reflexivity|exact HxG|exact HxD|exact Hfv|exact Hpre|exact Hbinds].
Qed.

Lemma si_init_fld_asn_ac : forall (G1 G2:ctx) (D1 D2:init_ctx) (xm ym:var) (Sm:typ)
    (vs:vars) (x:var) (i:init_typ) (y:var) (a:trm_label),
  QiF (G1 & xm ~ Sm & G2) (D1 & xm ~ ib & D2) vs (trm_var (avar_f x)) i ->
  QiF (G1 & xm ~ Sm & G2) (D1 & xm ~ ib & D2) vs (trm_var (avar_f y)) committed ->
  xm # G2 -> xm # D2 -> xm \notin fv_env G1 ->
  (G1 & subst_env xm ym G2 ⊢ trm_var (avar_f ym) ∶ subst_var xm ym Sm) ->
  binds ym it (D1 & D2) ->
  G1 & subst_env xm ym G2 ⸴ D1 & D2 ⸴ subst_var xm ym vs
    ⊢i subst_var xm ym (trm_asn (avar_f x) a (avar_f y)) ∶ committed.
Proof.
  intros G1 G2 D1 D2 xm ym Sm vs x i y a Hx Hy HxG HxD Hfv Hpre Hbinds.
  unfold QiF in Hx, Hy. simpl. eapply init_fld_asn_ac.
  - refine (Hx G1 G2 D1 D2 xm ym Sm _ _ _ _ _ _ _);
      [reflexivity|reflexivity|exact HxG|exact HxD|exact Hfv|exact Hpre|exact Hbinds].
  - refine (Hy G1 G2 D1 D2 xm ym Sm _ _ _ _ _ _ _);
      [reflexivity|reflexivity|exact HxG|exact HxD|exact Hfv|exact Hpre|exact Hbinds].
Qed.

Lemma si_init_fld_asn_ff : forall (G1 G2:ctx) (D1 D2:init_ctx) (xm ym:var) (Sm:typ)
    (vs:vars) (x:var) (y:var) (a:trm_label),
  QiF (G1 & xm ~ Sm & G2) (D1 & xm ~ ib & D2) vs (trm_var (avar_f x)) free ->
  QiF (G1 & xm ~ Sm & G2) (D1 & xm ~ ib & D2) vs (trm_var (avar_f y)) free ->
  xm # G2 -> xm # D2 -> xm \notin fv_env G1 ->
  (G1 & subst_env xm ym G2 ⊢ trm_var (avar_f ym) ∶ subst_var xm ym Sm) ->
  binds ym it (D1 & D2) ->
  G1 & subst_env xm ym G2 ⸴ D1 & D2 ⸴ subst_var xm ym vs
    ⊢i subst_var xm ym (trm_asn (avar_f x) a (avar_f y)) ∶ free.
Proof.
  intros G1 G2 D1 D2 xm ym Sm vs x y a Hx Hy HxG HxD Hfv Hpre Hbinds.
  unfold QiF in Hx, Hy. simpl. eapply init_fld_asn_ff.
  - refine (Hx G1 G2 D1 D2 xm ym Sm _ _ _ _ _ _ _);
      [reflexivity|reflexivity|exact HxG|exact HxD|exact Hfv|exact Hpre|exact Hbinds].
  - refine (Hy G1 G2 D1 D2 xm ym Sm _ _ _ _ _ _ _);
      [reflexivity|reflexivity|exact HxG|exact HxD|exact Hfv|exact Hpre|exact Hbinds].
Qed.

Lemma si_inits_nil : forall (G1 G2:ctx) (D1 D2:init_ctx) (xm ym:var) (Sm:typ) (vs:vars),
  G1 & subst_env xm ym G2 ⸴ D1 & D2 ⸴ subst_var xm ym vs
    ⊢i subst_var xm ym (@nil avar) :: (@nil init_typ).
Proof. intros. simpl. apply well_inits_nil. Qed.

Lemma si_inits_cons : forall (G1 G2:ctx) (D1 D2:init_ctx) (xm ym:var) (Sm:typ)
    (vs:vars) (x:var) (i:init_typ) (avs:avars) (is':inits),
  QiF (G1 & xm ~ Sm & G2) (D1 & xm ~ ib & D2) vs (trm_var (avar_f x)) i ->
  QisF (G1 & xm ~ Sm & G2) (D1 & xm ~ ib & D2) vs avs is' ->
  xm # G2 -> xm # D2 -> xm \notin fv_env G1 ->
  (G1 & subst_env xm ym G2 ⊢ trm_var (avar_f ym) ∶ subst_var xm ym Sm) ->
  binds ym it (D1 & D2) ->
  G1 & subst_env xm ym G2 ⸴ D1 & D2 ⸴ subst_var xm ym vs
    ⊢i subst_var xm ym (cons (avar_f x) avs) :: (cons i is').
Proof.
  intros G1 G2 D1 D2 xm ym Sm vs x i avs is' Hx Havs HxG HxD Hfv Hpre Hbinds.
  unfold QiF in Hx. unfold QisF in Havs. simpl. eapply well_inits_cons.
  - refine (Hx G1 G2 D1 D2 xm ym Sm _ _ _ _ _ _ _);
      [reflexivity|reflexivity|exact HxG|exact HxD|exact Hfv|exact Hpre|exact Hbinds].
  - refine (Havs G1 G2 D1 D2 xm ym Sm _ _ _ _ _ _ _);
      [reflexivity|reflexivity|exact HxG|exact HxD|exact Hfv|exact Hpre|exact Hbinds].
Qed.

(** * Helper for commit_let *)

Lemma sc_commit_let : forall (L:fset var) (G1 G2:ctx) (D1 D2:init_ctx)
    (xm ym:var) (Sm:typ) (t u:trm) (T:typ),
  QcF (G1 & xm ~ Sm & G2) (D1 & xm ~ ib & D2) t ->
  (forall z, z \notin L ->
     QcF ((G1 & xm ~ Sm & G2) & z ~ T)
         ((D1 & xm ~ ib & D2) & z ~ committed)
         (open z u)) ->
  xm # G2 -> xm # D2 -> xm \notin fv_env G1 ->
  (G1 & subst_env xm ym G2 ⊢ trm_var (avar_f ym) ∶ subst_var xm ym Sm) ->
  binds ym it (D1 & D2) ->
  G1 & subst_env xm ym G2 ⸴ D1 & D2
    ⊢c subst_var xm ym (trm_let T t u).
Proof.
  intros L G1 G2 D1 D2 xm ym Sm t u T Ht Hu HxG HxD Hfv Hpre Hbinds.
  set (L' := (((L \u dom G1) \u dom G2) \u \{xm}) \u \{ym}).
  unfold QcF in Ht, Hu. simpl.
  eapply (@commit_let L' _ _ _ _ _).
  - refine (Ht G1 G2 D1 D2 xm ym Sm _ _ _ _ _ _ _);
      [reflexivity|reflexivity|exact HxG|exact HxD|exact Hfv|exact Hpre|exact Hbinds].
  - intros z Hz. unfold L' in Hz.
    assert (Hz0 : z \notin (((L \u dom G1) \u dom G2) \u \{xm})) by
      (exact (@notin_union_r1 z (((L \u dom G1) \u dom G2) \u \{xm}) \{ym} Hz)).
    assert (Hzym : z \notin \{ym}) by
      (exact (@notin_union_r2 z (((L \u dom G1) \u dom G2) \u \{xm}) \{ym} Hz)).
    assert (Hzy : z <> ym) by (exact (@notin_singleton_r z ym Hzym)).
    assert (Hz1 : z \notin (L \u dom G1) \u dom G2) by
      (exact (@notin_union_r1 z ((L \u dom G1) \u dom G2) \{xm} Hz0)).
    assert (HzL1 : z \notin L \u dom G1) by
      (exact (@notin_union_r1 z (L \u dom G1) (dom G2) Hz1)).
    assert (HzG2 : z \notin dom G2) by
      (exact (@notin_union_r2 z (L \u dom G1) (dom G2) Hz1)).
    assert (HzL : z \notin L) by
      (exact (@notin_union_r1 z L (dom G1) HzL1)).
    assert (HzG1 : z \notin dom G1) by
      (exact (@notin_union_r2 z L (dom G1) HzL1)).
    assert (Hzxm : z \notin \{xm}) by
      (exact (@notin_union_r2 z ((L \u dom G1) \u dom G2) \{xm} Hz0)).
    assert (Hzx : z <> xm) by (exact (@notin_singleton_r z xm Hzxm)).
    assert (Hru : subst_var xm ym (open_rec 0 z u) = open_rec 0 z (subst_var xm ym u))
      by (apply subst_open_fresh_trm; auto).
    assert (HeqG : ((G1 & xm ~ Sm & G2) & z ~ T) = G1 & xm ~ Sm & (G2 & z ~ T)).
    { symmetry. apply concat_assoc. }
    assert (HeqD : ((D1 & xm ~ ib & D2) & z ~ committed)
                    = D1 & xm ~ ib & (D2 & z ~ committed)).
    { symmetry. apply concat_assoc. }
    assert (Hpre' : G1 & subst_env xm ym (G2 & z ~ T)
                    ⊢ trm_var (avar_f ym) ∶ subst_var xm ym Sm).
    { rewrite map_push. rewrite concat_assoc.
      eapply ty_trm_binds_extends; [exact Hpre|].
      apply binds_extends_push_fresh.
      rewrite dom_concat. apply notin_union_l; [exact HzG1|].
      rewrite dom_subst_env. exact HzG2. }
    assert (HxG' : xm # (G2 & z ~ T)).
    { rewrite dom_push. apply notin_union_l.
      - apply notin_singleton_l. intro E; apply Hzx; symmetry; exact E.
      - exact HxG. }
    assert (HxD' : xm # (D2 & z ~ committed)).
    { rewrite dom_push. apply notin_union_l.
      - apply notin_singleton_l. intro E; apply Hzx; symmetry; exact E.
      - exact HxD. }
    repeat rewrite <- concat_assoc.
    rewrite <- map_push.
    change (G1 & subst_env xm ym (G2 & z ~ T) ⸴ D1 & (D2 & z ~ committed)
            ⊢c open_rec 0 z (subst_var xm ym u)).
    rewrite <- Hru.
    assert (Hbinds' : binds ym it (D1 & (D2 & z ~ committed))).
    { assert (Hb : binds ym it ((D1 & D2) & z ~ committed)).
      { eapply LibEnv.binds_push_neq; [exact Hbinds|].
        intro E; apply Hzy; symmetry; exact E. }
      rewrite concat_assoc. exact Hb. }
    refine (Hu z HzL G1 (G2 & z ~ T) D1 (D2 & z ~ committed) xm ym Sm
              _ _ _ _ _ _ _);
      [exact HeqG|exact HeqD|exact HxG'|exact HxD'|exact Hfv|exact Hpre'|exact Hbinds'].
Qed.

Lemma def_eff_first : forall (ds:defs) (x y:var) (a:trm_label),
  (y,a) \in from_list (def_eff x ds) -> y = x.
Proof.
  intros ds. induction ds as [|d ds IH]; intros x y a Hin.
  - cbn in Hin. exfalso. exact (in_empty_inv Hin).
  - destruct d.
    + cbn in Hin. eapply IH; eassumption.
    + cbn in Hin. rewrite from_list_cons in Hin. rewrite in_union in Hin.
      destruct Hin as [Hin|Hin].
      * rewrite in_singleton in Hin. injection Hin as Hy _. subst y. reflexivity.
      * eapply IH; eassumption.
Qed.

Lemma def_eff_no_subst : forall (ds:defs) (x xm:var) (a:trm_label),
  xm <> x -> (xm,a) \notin from_list (def_eff x ds).
Proof.
  intros ds x xm a Hne Hin.
  pose proof (@def_eff_first ds x xm a Hin) as Heq. subst xm. exfalso. apply Hne. reflexivity.
Qed.

Lemma eff_trm_subst_fresh : forall (t:trm) (effs:effects),
  eff_trm t effs ->
  forall (xm ym:var),
    (forall a, (xm,a) \notin from_list effs) ->
    eff_trm (subst_var xm ym t) effs.
Proof.
  intros t effs H. induction H; intros xm ym Hno.
  - apply eff_ignore.
  - assert (Hne : x <> xm).
    { intro E. apply (Hno a).
      rewrite <- E. rewrite from_list_cons. rewrite in_union. left. apply in_singleton_self. }
    simpl. rewrite (@subst_if_neq xm ym x Hne). apply eff_fld_asn.
  - simpl. eapply eff_let with (L := (L \u \{xm}) \u \{ym}).
    + apply IHeff_trm.
      intros a Ha. apply (Hno a). rewrite from_list_app. rewrite in_union. left. exact Ha.
    + intros z Hz.
      assert (HzL : z \notin L).
      { apply notin_union_r1 in Hz as Hza. apply notin_union_r1 in Hza. exact Hza. }
      assert (Hzx : z <> xm).
      { apply notin_union_r1 in Hz as Hza. apply notin_union_r2 in Hza.
        intro E; subst z; apply Hza; apply in_singleton_self. }
      assert (Hru : subst_var xm ym (open_rec 0 z u) = open_rec 0 z (subst_var xm ym u))
        by (apply subst_open_fresh_trm; auto).
      change (eff_trm (open_rec 0 z (subst_var xm ym u)) eff2).
      rewrite <- Hru.
      apply H1; [exact HzL|].
      intros a Ha. apply (Hno a). rewrite from_list_app. rewrite in_union. right. exact Ha.
  - simpl. eapply eff_llit with (L := (L \u \{xm}) \u \{ym}).
    intros z Hz.
    assert (HzL : z \notin L).
    { apply notin_union_r1 in Hz as Hza. apply notin_union_r1 in Hza. exact Hza. }
    assert (Hzx : z <> xm).
    { apply notin_union_r1 in Hz as Hza. apply notin_union_r2 in Hza.
      intro E; subst z; apply Hza; apply in_singleton_self. }
    assert (Hru : subst_var xm ym (open_rec 0 z u) = open_rec 0 z (subst_var xm ym u))
      by (apply subst_open_fresh_trm; auto).
    change (eff_trm (open_rec 0 z (subst_var xm ym u)) eff).
    rewrite <- Hru.
    apply H0; [exact HzL|exact Hno].
Qed.

Lemma has_effs_subst_fresh : forall (t:trm) (effs:effects) (x y:var),
  has_effs t effs ->
  (forall a, (x,a) \notin from_list effs) ->
  has_effs (subst_var x y t) effs.
Proof.
  intros t effs x y [effs' [Heff Heq]] Hno.
  exists effs'. split; [|exact Heq].
  eapply eff_trm_subst_fresh; [exact Heff|].
  intros a Ha. apply (Hno a). rewrite Heq. exact Ha.
Qed.

Lemma def_eff_subst : forall (ds:defs) (xm ym:var) (z:var),
  def_eff z (subst_var xm ym ds) = def_eff z ds.
Proof.
  intros ds. induction ds as [|d ds IH]; intros xm ym z.
  - reflexivity.
  - destruct d; cbn.
    + change (def_eff z (subst_var xm ym ds) = def_eff z ds). exact (IH xm ym z).
    + f_equal. change (def_eff z (subst_var xm ym ds) = def_eff z ds). exact (IH xm ym z).
Qed.

Lemma vars_subst_notin : forall (vs:vars) (xm ym:var),
  xm \notin vs -> subst_var xm ym vs = vs.
Proof.
  intros vs xm ym Hx. unfold subst_var, VarsSubstVar. cbn.
  rewrite (If_r (P:=xm \in vs) _ _ Hx). reflexivity.
Qed.

Lemma sc_commit_llit : forall (L:fset var) (G1 G2:ctx) (D1 D2:init_ctx)
    (xm ym:var) (Sm:typ) (l:lit) (u:trm) (T:typ),
  QlF (G1 & xm ~ Sm & G2) (D1 & xm ~ ib & D2) l ->
  (forall z, z \notin L ->
     QcF ((G1 & xm ~ Sm & G2) & z ~ T)
         ((D1 & xm ~ ib & D2) & z ~ committed)
         (open z u)) ->
  xm # G2 -> xm # D2 -> xm \notin fv_env G1 ->
  (G1 & subst_env xm ym G2 ⊢ trm_var (avar_f ym) ∶ subst_var xm ym Sm) ->
  binds ym it (D1 & D2) ->
  G1 & subst_env xm ym G2 ⸴ D1 & D2
    ⊢c subst_var xm ym (trm_lit T l u).
Proof.
  intros L G1 G2 D1 D2 xm ym Sm l u T Hl Hu HxG HxD Hfv Hpre Hbinds.
  set (L' := (((L \u dom G1) \u dom G2) \u \{xm}) \u \{ym}).
  unfold QlF in Hl. unfold QcF in Hu. simpl.
  eapply (@commit_llit L' _ _ _ _ _).
  - refine (Hl G1 G2 D1 D2 xm ym Sm _ _ _ _ _ _ _);
      [reflexivity|reflexivity|exact HxG|exact HxD|exact Hfv|exact Hpre|exact Hbinds].
  - intros z Hz. unfold L' in Hz.
    assert (Hz0 : z \notin (((L \u dom G1) \u dom G2) \u \{xm})) by
      (exact (@notin_union_r1 z (((L \u dom G1) \u dom G2) \u \{xm}) \{ym} Hz)).
    assert (Hzym : z \notin \{ym}) by
      (exact (@notin_union_r2 z (((L \u dom G1) \u dom G2) \u \{xm}) \{ym} Hz)).
    assert (Hzy : z <> ym) by (exact (@notin_singleton_r z ym Hzym)).
    assert (Hz1 : z \notin (L \u dom G1) \u dom G2) by
      (exact (@notin_union_r1 z ((L \u dom G1) \u dom G2) \{xm} Hz0)).
    assert (HzL1 : z \notin L \u dom G1) by
      (exact (@notin_union_r1 z (L \u dom G1) (dom G2) Hz1)).
    assert (HzG2 : z \notin dom G2) by
      (exact (@notin_union_r2 z (L \u dom G1) (dom G2) Hz1)).
    assert (HzL : z \notin L) by
      (exact (@notin_union_r1 z L (dom G1) HzL1)).
    assert (HzG1 : z \notin dom G1) by
      (exact (@notin_union_r2 z L (dom G1) HzL1)).
    assert (Hzxm : z \notin \{xm}) by
      (exact (@notin_union_r2 z ((L \u dom G1) \u dom G2) \{xm} Hz0)).
    assert (Hzx : z <> xm) by (exact (@notin_singleton_r z xm Hzxm)).
    assert (Hru : subst_var xm ym (open_rec 0 z u) = open_rec 0 z (subst_var xm ym u))
      by (apply subst_open_fresh_trm; auto).
    assert (HeqG : ((G1 & xm ~ Sm & G2) & z ~ T) = G1 & xm ~ Sm & (G2 & z ~ T)).
    { symmetry. apply concat_assoc. }
    assert (HeqD : ((D1 & xm ~ ib & D2) & z ~ committed)
                    = D1 & xm ~ ib & (D2 & z ~ committed)).
    { symmetry. apply concat_assoc. }
    assert (Hpre' : G1 & subst_env xm ym (G2 & z ~ T)
                    ⊢ trm_var (avar_f ym) ∶ subst_var xm ym Sm).
    { rewrite map_push. rewrite concat_assoc.
      eapply ty_trm_binds_extends; [exact Hpre|].
      apply binds_extends_push_fresh.
      rewrite dom_concat. apply notin_union_l; [exact HzG1|].
      rewrite dom_subst_env. exact HzG2. }
    assert (HxG' : xm # (G2 & z ~ T)).
    { rewrite dom_push. apply notin_union_l.
      - apply notin_singleton_l. intro E; apply Hzx; symmetry; exact E.
      - exact HxG. }
    assert (HxD' : xm # (D2 & z ~ committed)).
    { rewrite dom_push. apply notin_union_l.
      - apply notin_singleton_l. intro E; apply Hzx; symmetry; exact E.
      - exact HxD. }
    repeat rewrite <- concat_assoc.
    rewrite <- map_push.
    change (G1 & subst_env xm ym (G2 & z ~ T) ⸴ D1 & (D2 & z ~ committed)
            ⊢c open_rec 0 z (subst_var xm ym u)).
    rewrite <- Hru.
    assert (Hbinds' : binds ym it (D1 & (D2 & z ~ committed))).
    { assert (Hb : binds ym it ((D1 & D2) & z ~ committed)).
      { eapply LibEnv.binds_push_neq; [exact Hbinds|].
        intro E; apply Hzy; symmetry; exact E. }
      rewrite concat_assoc. exact Hb. }
    refine (Hu z HzL G1 (G2 & z ~ T) D1 (D2 & z ~ committed) xm ym Sm
              _ _ _ _ _ _ _);
      [exact HeqG|exact HeqD|exact HxG'|exact HxD'|exact Hfv|exact Hpre'|exact Hbinds'].
Qed.

Lemma sc_commit_all_intro : forall (L:fset var) (G1 G2:ctx) (D1 D2:init_ctx)
    (xm ym:var) (Sm:typ) (T:typ) (t:trm),
  (forall z, z \notin L ->
     QcF ((G1 & xm ~ Sm & G2) & z ~ T)
         ((D1 & xm ~ ib & D2) & z ~ committed)
         (open z t)) ->
  xm # G2 -> xm # D2 -> xm \notin fv_env G1 ->
  (G1 & subst_env xm ym G2 ⊢ trm_var (avar_f ym) ∶ subst_var xm ym Sm) ->
  binds ym it (D1 & D2) ->
  G1 & subst_env xm ym G2 ⸴ D1 & D2
    ⊢c subst_var xm ym (lit_fun T t).
Proof.
  intros L G1 G2 D1 D2 xm ym Sm T t Hu HxG HxD Hfv Hpre Hbinds.
  set (L' := (((L \u dom G1) \u dom G2) \u \{xm}) \u \{ym}).
  unfold QcF in Hu. simpl.
  eapply (@commit_all_intro L' _ _ _ _).
  intros z Hz.
  assert (Hz0 : z \notin (((L \u dom G1) \u dom G2) \u \{xm})) by
    (exact (@notin_union_r1 z (((L \u dom G1) \u dom G2) \u \{xm}) \{ym} Hz)).
  assert (Hzym : z \notin \{ym}) by
    (exact (@notin_union_r2 z (((L \u dom G1) \u dom G2) \u \{xm}) \{ym} Hz)).
  assert (Hzy : z <> ym) by (exact (@notin_singleton_r z ym Hzym)).
  assert (Hz1 : z \notin (L \u dom G1) \u dom G2) by
    (exact (@notin_union_r1 z ((L \u dom G1) \u dom G2) \{xm} Hz0)).
  assert (HzL1 : z \notin L \u dom G1) by
    (exact (@notin_union_r1 z (L \u dom G1) (dom G2) Hz1)).
  assert (HzG2 : z \notin dom G2) by
    (exact (@notin_union_r2 z (L \u dom G1) (dom G2) Hz1)).
  assert (HzL : z \notin L) by
    (exact (@notin_union_r1 z L (dom G1) HzL1)).
  assert (HzG1 : z \notin dom G1) by
    (exact (@notin_union_r2 z L (dom G1) HzL1)).
  assert (Hzxm : z \notin \{xm}) by
    (exact (@notin_union_r2 z ((L \u dom G1) \u dom G2) \{xm} Hz0)).
  assert (Hzx : z <> xm) by (exact (@notin_singleton_r z xm Hzxm)).
  assert (Hru : subst_var xm ym (open_rec 0 z t) = open_rec 0 z (subst_var xm ym t))
    by (apply subst_open_fresh_trm; auto).
  assert (HeqG : ((G1 & xm ~ Sm & G2) & z ~ T) = G1 & xm ~ Sm & (G2 & z ~ T)).
  { symmetry. apply concat_assoc. }
  assert (HeqD : ((D1 & xm ~ ib & D2) & z ~ committed)
                  = D1 & xm ~ ib & (D2 & z ~ committed)).
  { symmetry. apply concat_assoc. }
  assert (Hpre' : G1 & subst_env xm ym (G2 & z ~ T)
                  ⊢ trm_var (avar_f ym) ∶ subst_var xm ym Sm).
  { rewrite map_push. rewrite concat_assoc.
    eapply ty_trm_binds_extends; [exact Hpre|].
    apply binds_extends_push_fresh.
    rewrite dom_concat. apply notin_union_l; [exact HzG1|].
    rewrite dom_subst_env. exact HzG2. }
  assert (HxG' : xm # (G2 & z ~ T)).
  { rewrite dom_push. apply notin_union_l.
    - apply notin_singleton_l. intro E; apply Hzx; symmetry; exact E.
    - exact HxG. }
  assert (HxD' : xm # (D2 & z ~ committed)).
  { rewrite dom_push. apply notin_union_l.
    - apply notin_singleton_l. intro E; apply Hzx; symmetry; exact E.
    - exact HxD. }
  repeat rewrite <- concat_assoc.
  rewrite <- map_push.
  change (G1 & subst_env xm ym (G2 & z ~ T) ⸴ D1 & (D2 & z ~ committed)
          ⊢c open_rec 0 z (subst_var xm ym t)).
  rewrite <- Hru.
  assert (Hbinds' : binds ym it (D1 & (D2 & z ~ committed))).
  { assert (Hb : binds ym it ((D1 & D2) & z ~ committed)).
    { eapply LibEnv.binds_push_neq; [exact Hbinds|].
      intro E; apply Hzy; symmetry; exact E. }
    rewrite concat_assoc. exact Hb. }
  refine (Hu z HzL G1 (G2 & z ~ T) D1 (D2 & z ~ committed) xm ym Sm
            _ _ _ _ _ _ _);
    [exact HeqG|exact HeqD|exact HxG'|exact HxD'|exact Hfv|exact Hpre'|exact Hbinds'].
Qed.

Lemma notin_from_list_intro : forall (ys:list var) (x:var),
  (forall y, List.In y ys -> y <> x) -> x \notin from_list ys.
Proof.
  intros ys x H Hin.
  rewrite in_from_list in Hin.
  exact (H x Hin eq_refl).
Qed.

Lemma dom_ys_tolist : forall (ys:list var) (Ts:typs),
  LibList.length ys = LibList.length (to_list Ts) ->
  dom (ys ~** to_list Ts) = from_list ys.
Proof.
  intros ys Ts Hlenxy.
  rewrite (@dom_singles typ (List.rev ys) (List.rev (to_list Ts))).
  - rewrite from_list_rev. reflexivity.
  - rewrite !LibList_length_List_rev. exact Hlenxy.
Qed.

Lemma dom_ys_inits : forall (ys:list var) (is':inits),
  List.length ys = List.length is' ->
  dom (ys ~** is') = from_list ys.
Proof.
  intros ys is' Hlenxy.
  rewrite (@dom_singles init_typ (List.rev ys) (List.rev is')).
  - rewrite from_list_rev. reflexivity.
  - rewrite !LibList_length_List_rev.
    rewrite !List_length_LibList_length in Hlenxy. exact Hlenxy.
Qed.

Lemma fresh_head_L : forall (L:fset var) (G1 G2:ctx) (xm ym:var) (n:nat) (x:var) (ys:list var),
  fresh ((((L \u dom G1) \u dom G2) \u \{xm}) \u \{ym}) (S n) (cons x ys) ->
  x \notin L /\ x \notin dom G1 /\ x \notin dom G2 /\ x <> xm /\ x <> ym.
Proof.
  intros L G1 G2 xm ym n x ys Hf.
  assert (Hx1 : x \notin (((L \u dom G1) \u dom G2) \u \{xm}) \u \{ym})
    by (eapply fresh_cons_head; exact Hf).
  assert (Hx2 : x \notin ((L \u dom G1) \u dom G2) \u \{xm})
    by (exact (@notin_union_r1 x (((L \u dom G1) \u dom G2) \u \{xm}) \{ym} Hx1)).
  assert (Hx3 : x \notin (L \u dom G1) \u dom G2)
    by (exact (@notin_union_r1 x ((L \u dom G1) \u dom G2) \{xm} Hx2)).
  assert (Hx4 : x \notin L \u dom G1)
    by (exact (@notin_union_r1 x (L \u dom G1) (dom G2) Hx3)).
  assert (HxL : x \notin L) by (exact (@notin_union_r1 x L (dom G1) Hx4)).
  assert (HxG1 : x \notin dom G1) by (exact (@notin_union_r2 x L (dom G1) Hx4)).
  assert (HxG2 : x \notin dom G2) by (exact (@notin_union_r2 x (L \u dom G1) (dom G2) Hx3)).
  assert (Hxxm : x \notin \{xm}) by (exact (@notin_union_r2 x ((L \u dom G1) \u dom G2) \{xm} Hx2)).
  assert (Hxym : x \notin \{ym}) by (exact (@notin_union_r2 x ((((L \u dom G1) \u dom G2) \u \{xm})) \{ym} Hx1)).
  split; [exact HxL|]. split; [exact HxG1|]. split; [exact HxG2|]. split.
  - exact (@notin_singleton_r x xm Hxxm).
  - exact (@notin_singleton_r x ym Hxym).
Qed.

Lemma fresh_tail_L : forall (L:fset var) (G1 G2:ctx) (xm ym:var) (n:nat) (x:var) (ys:list var),
  fresh ((((L \u dom G1) \u dom G2) \u \{xm}) \u \{ym}) (S n) (cons x ys) ->
  forall y, List.In y ys ->
    y \notin L /\ y \notin dom G1 /\ y \notin dom G2 /\ y <> xm /\ y <> ym.
Proof.
  intros L G1 G2 xm ym n x ys Hf y Hy.
  set (Lb := ((((L \u dom G1) \u dom G2) \u \{xm}) \u \{ym})).
  assert (Ht : fresh (Lb \u \{x}) n ys)
    by (eapply fresh_cons_tail; exact Hf).
  assert (Hy1 : y \notin Lb \u \{x}).
  { eapply fresh_from_list_notin; [exact Ht|].
    rewrite in_from_list. exact Hy. }
  assert (Hy2 : y \notin Lb)
    by (exact (@notin_union_r1 y Lb \{x} Hy1)).
  assert (Hy3 : y \notin ((L \u dom G1) \u dom G2) \u \{xm})
    by (exact (@notin_union_r1 y (((L \u dom G1) \u dom G2) \u \{xm}) \{ym} Hy2)).
  assert (Hy4 : y \notin (L \u dom G1) \u dom G2)
    by (exact (@notin_union_r1 y ((L \u dom G1) \u dom G2) \{xm} Hy3)).
  assert (Hy5 : y \notin L \u dom G1)
    by (exact (@notin_union_r1 y (L \u dom G1) (dom G2) Hy4)).
  assert (HyL : y \notin L) by (exact (@notin_union_r1 y L (dom G1) Hy5)).
  assert (HyG1 : y \notin dom G1) by (exact (@notin_union_r2 y L (dom G1) Hy5)).
  assert (HyG2 : y \notin dom G2) by (exact (@notin_union_r2 y (L \u dom G1) (dom G2) Hy4)).
  assert (Hyxm : y \notin \{xm}) by (exact (@notin_union_r2 y ((L \u dom G1) \u dom G2) \{xm} Hy3)).
  assert (Hyym : y \notin \{ym}) by (exact (@notin_union_r2 y (((L \u dom G1) \u dom G2) \u \{xm}) \{ym} Hy2)).
  split; [exact HyL|]. split; [exact HyG1|]. split; [exact HyG2|]. split.
  - exact (@notin_singleton_r y xm Hyxm).
  - exact (@notin_singleton_r y ym Hyym).
Qed.

Lemma sc_commit_con_intro : forall (L:fset var) (G1 G2:ctx) (D1 D2:init_ctx)
    (xm ym:var) (Sm:typ) (Ts:typs) (is':inits) (T:typ) (i:init_typ) (ds:defs) (t:trm),
  List.length is' = length_s Ts ->
  (forall x ys, List.length ys = length_s Ts ->
     fresh L (S (List.length ys)) (cons x ys) ->
     has_effs (open_vars (cons x ys) t) (def_eff x ds)) ->
  (forall x ys, List.length ys = length_s Ts ->
     fresh L (S (List.length ys)) (cons x ys) ->
     QiF ((G1 & xm ~ Sm & G2) & (ys ~** to_list Ts) & (x ~ open_vars (cons x ys) T))
         ((D1 & xm ~ ib & D2) & (ys ~** is') & (x ~ free))
         ((from_list ys) \u \{x}) (open_vars (cons x ys) t) i) ->
  xm # G2 -> xm # D2 -> xm \notin fv_env G1 ->
  (G1 & subst_env xm ym G2 ⊢ trm_var (avar_f ym) ∶ subst_var xm ym Sm) ->
  binds ym it (D1 & D2) ->
  G1 & subst_env xm ym G2 ⸴ D1 & D2
    ⊢c subst_var xm ym (lit_con Ts is' T ds t).
Proof.
  intros L G1 G2 D1 D2 xm ym Sm Ts is' T i ds t Hlenis Heff Hinit HxG HxD Hfv Hpre Hbinds.
  set (L' := (((L \u dom G1) \u dom G2) \u \{xm}) \u \{ym}).
  unfold QiF in Hinit. simpl.
  eapply (@commit_con_intro L' _ _ _ _ _ i _ _).
  - rewrite length_s_subst_typs. exact Hlenis.
  - intros x ys Hlenxy Hf.
    rewrite length_s_subst_typs in Hlenxy.
    destruct (@fresh_head_L L G1 G2 xm ym (List.length ys) x ys Hf) as [HxL [HxG1 [HxG2 [Hxxm Hxym]]]].
    assert (Hf1 : fresh (((L \u dom G1) \u dom G2) \u \{xm}) (S (List.length ys)) (cons x ys))
      by (exact (@fresh_union_r1 (cons x ys) (((L \u dom G1) \u dom G2) \u \{xm}) \{ym} (S (List.length ys)) Hf)).
    assert (Hf2 : fresh ((L \u dom G1) \u dom G2) (S (List.length ys)) (cons x ys))
      by (exact (@fresh_union_r1 (cons x ys) ((L \u dom G1) \u dom G2) \{xm} (S (List.length ys)) Hf1)).
    assert (Hf3 : fresh (L \u dom G1) (S (List.length ys)) (cons x ys))
      by (exact (@fresh_union_r1 (cons x ys) (L \u dom G1) (dom G2) (S (List.length ys)) Hf2)).
    assert (HfL : fresh L (S (List.length ys)) (cons x ys))
      by (exact (@fresh_union_r1 (cons x ys) L (dom G1) (S (List.length ys)) Hf3)).
    pose proof (Heff x ys Hlenxy HfL) as Heffxy.
    assert (Htrw : subst_var xm ym (open_vars (cons x ys) t) = open_vars (cons x ys) (subst_var xm ym t)).
    { rewrite subst_open_rec_vars_trm. rewrite map_ren_id.
      - reflexivity.
      - intros z Hz. unfold L' in Hz. destruct Hz as [->|Hz].
        + exact Hxxm.
        + destruct (@fresh_tail_L L G1 G2 xm ym (List.length ys) x ys Hf z Hz) as [_ [_ [_ [Hzxm _]]]]. exact Hzxm. }
    assert (Heffsub : has_effs (subst_var xm ym (open_vars (cons x ys) t)) (def_eff x ds)).
    { eapply has_effs_subst_fresh; [exact Heffxy|].
      intros a Ha. exact (@def_eff_no_subst ds x xm a (not_eq_sym Hxxm) Ha). }
    rewrite Htrw in Heffsub. rewrite <- (@def_eff_subst ds xm ym x) in Heffsub. exact Heffsub.
  - intros x ys Hlenxy Hf.
    rewrite length_s_subst_typs in Hlenxy.
    destruct (@fresh_head_L L G1 G2 xm ym (List.length ys) x ys Hf) as [HxL [HxG1 [HxG2 [Hxxm Hxym]]]].
    assert (Hf1 : fresh (((L \u dom G1) \u dom G2) \u \{xm}) (S (List.length ys)) (cons x ys))
      by (exact (@fresh_union_r1 (cons x ys) (((L \u dom G1) \u dom G2) \u \{xm}) \{ym} (S (List.length ys)) Hf)).
    assert (Hf2 : fresh ((L \u dom G1) \u dom G2) (S (List.length ys)) (cons x ys))
      by (exact (@fresh_union_r1 (cons x ys) ((L \u dom G1) \u dom G2) \{xm} (S (List.length ys)) Hf1)).
    assert (Hf3 : fresh (L \u dom G1) (S (List.length ys)) (cons x ys))
      by (exact (@fresh_union_r1 (cons x ys) (L \u dom G1) (dom G2) (S (List.length ys)) Hf2)).
    assert (HfL : fresh L (S (List.length ys)) (cons x ys))
      by (exact (@fresh_union_r1 (cons x ys) L (dom G1) (S (List.length ys)) Hf3)).
    pose proof (Hinit x ys Hlenxy HfL) as HIH.
    assert (HlenL : LibList.length ys = LibList.length (to_list Ts)).
    { unfold length_s in Hlenxy. change (List.length ys = List.length (to_list Ts)) in Hlenxy.
      rewrite !List_length_LibList_length in Hlenxy. exact Hlenxy. }
    assert (HlenI : List.length ys = List.length is').
    { rewrite <- Hlenis in Hlenxy. exact Hlenxy. }
    assert (Htrw : subst_var xm ym (open_vars (cons x ys) t) = open_vars (cons x ys) (subst_var xm ym t)).
    { rewrite subst_open_rec_vars_trm. rewrite map_ren_id.
      - reflexivity.
      - intros z Hz. unfold L' in Hz. destruct Hz as [->|Hz].
        + exact Hxxm.
        + destruct (@fresh_tail_L L G1 G2 xm ym (List.length ys) x ys Hf z Hz) as [_ [_ [_ [Hzxm _]]]]. exact Hzxm. }
    assert (HTrwT : subst_var xm ym (open_vars (cons x ys) T) = open_vars (cons x ys) (subst_var xm ym T)).
    { rewrite subst_open_rec_vars_typ. rewrite map_ren_id.
      - reflexivity.
      - intros z Hz. unfold L' in Hz. destruct Hz as [->|Hz].
        + exact Hxxm.
        + destruct (@fresh_tail_L L G1 G2 xm ym (List.length ys) x ys Hf z Hz) as [_ [_ [_ [Hzxm _]]]]. exact Hzxm. }
    assert (HnotxmYs : xm \notin from_list ys).
    { apply notin_from_list_intro. intros z Hz.
      destruct (@fresh_tail_L L G1 G2 xm ym (List.length ys) x ys Hf z Hz) as [_ [_ [_ [Hzxm _]]]]. exact Hzxm. }
    assert (HnotymYs : ym \notin from_list ys).
    { apply notin_from_list_intro. intros z Hz.
      destruct (@fresh_tail_L L G1 G2 xm ym (List.length ys) x ys Hf z Hz) as [_ [_ [_ [_ Hzyn]]]]. exact Hzyn. }
    assert (HxG' : xm # ((G2 & (ys ~** to_list Ts)) & (x ~ open_vars (cons x ys) T))).
    { rewrite !dom_concat, !dom_single. apply notin_union_l.
      - apply notin_union_l.
        + exact HxG.
        + rewrite (@dom_ys_tolist ys Ts HlenL). exact HnotxmYs.
      - apply notin_singleton_l. exact (not_eq_sym Hxxm). }
    assert (HxD' : xm # ((D2 & (ys ~** is')) & (x ~ free))).
    { rewrite !dom_concat, !dom_single. apply notin_union_l.
      - apply notin_union_l.
        + exact HxD.
        + rewrite (@dom_ys_inits ys is' HlenI). exact HnotxmYs.
      - apply notin_singleton_l. exact (not_eq_sym Hxxm). }
    assert (Hpre' : G1 & subst_env xm ym ((G2 & (ys ~** to_list Ts)) & (x ~ open_vars (cons x ys) T))
                    ⊢ trm_var (avar_f ym) ∶ subst_var xm ym Sm).
    { rewrite map_concat. rewrite map_single. rewrite map_concat.
      rewrite (subst_env_singles xm ym ys Ts HlenL).
      eapply ty_trm_binds_extends; [exact Hpre|].
      rewrite <- concat_assoc. rewrite concat_assoc.
      eapply binds_extends_push_env_fresh.
      intros z Hz. unfold L' in Hz. rewrite !dom_concat, !dom_single in Hz. rewrite in_union in Hz.
      destruct Hz as [Hz|Hz].
      - assert (HL2 : LibList.length ys = LibList.length (to_list (subst_var xm ym Ts))).
        { change (LibList.length ys = LibList.length (to_list (subst_typs xm ym Ts))).
          rewrite length_to_list_subst. exact HlenL. }
        rewrite (@dom_ys_tolist ys (subst_var xm ym Ts) HL2) in Hz.
        destruct (@fresh_tail_L L G1 G2 xm ym (List.length ys) x ys Hf z
                    (proj1 (@in_from_list var z ys) Hz)) as [HzL [HzG1 [HzG2 _]]].
        rewrite !dom_concat, dom_map. apply notin_union_l; assumption.
      - rewrite in_singleton in Hz. subst z.
        rewrite !dom_concat, dom_map. apply notin_union_l; assumption. }
    assert (Hbinds' : binds ym it (D1 & ((D2 & (ys ~** is')) & (x ~ free)))).
    { repeat rewrite concat_assoc.
      eapply LibEnv.binds_push_neq.
      - eapply LibEnv.binds_concat_left.
        + exact Hbinds.
        + rewrite (@dom_ys_inits ys is' HlenI). exact HnotymYs.
      - exact (not_eq_sym Hxym). }
    assert (HeqG : ((G1 & xm ~ Sm & G2) & (ys ~** to_list Ts)) & (x ~ open_vars (cons x ys) T)
                 = G1 & xm ~ Sm & ((G2 & (ys ~** to_list Ts)) & (x ~ open_vars (cons x ys) T))).
    { repeat rewrite concat_assoc. reflexivity. }
    assert (HeqD : ((D1 & xm ~ ib & D2) & (ys ~** is')) & (x ~ free)
                 = D1 & xm ~ ib & ((D2 & (ys ~** is')) & (x ~ free))).
    { repeat rewrite concat_assoc. reflexivity. }
    pose proof (HIH G1 ((G2 & (ys ~** to_list Ts)) & (x ~ open_vars (cons x ys) T))
                  D1 ((D2 & (ys ~** is')) & (x ~ free)) xm ym Sm
                  HeqG HeqD HxG' HxD' Hfv Hpre' Hbinds') as Hres.
    rewrite map_concat in Hres. rewrite map_single in Hres. rewrite map_concat in Hres.
    rewrite (subst_env_singles xm ym ys Ts HlenL) in Hres.
    rewrite HTrwT in Hres. rewrite Htrw in Hres.
    assert (Hvs : subst_var xm ym ((from_list ys) \u \{x}) = (from_list ys) \u \{x}).
    { apply (@vars_subst_notin ((from_list ys) \u \{x}) xm ym).
      apply notin_union_l.
      - exact HnotxmYs.
      - apply notin_singleton_l. exact (not_eq_sym Hxxm). }
    repeat rewrite concat_assoc in Hres.
    rewrite <- Hvs.
    exact Hres.
Qed.

Lemma notin_L_prime : forall (L:fset var) (G1 G2:ctx) (xm ym z:var),
  z \notin (((L \u dom G1) \u dom G2) \u \{xm}) \u \{ym} ->
  z \notin L /\ z \notin dom G1 /\ z \notin dom G2 /\ z <> xm /\ z <> ym.
Proof.
  intros L G1 G2 xm ym z Hz.
  assert (Hz1 : z \notin ((L \u dom G1) \u dom G2) \u \{xm})
    by (exact (@notin_union_r1 z (((L \u dom G1) \u dom G2) \u \{xm}) \{ym} Hz)).
  assert (Hz2 : z \notin (L \u dom G1) \u dom G2)
    by (exact (@notin_union_r1 z ((L \u dom G1) \u dom G2) \{xm} Hz1)).
  assert (Hz3 : z \notin L \u dom G1)
    by (exact (@notin_union_r1 z (L \u dom G1) (dom G2) Hz2)).
  assert (HzL : z \notin L) by (exact (@notin_union_r1 z L (dom G1) Hz3)).
  assert (HzG1 : z \notin dom G1) by (exact (@notin_union_r2 z L (dom G1) Hz3)).
  assert (HzG2 : z \notin dom G2) by (exact (@notin_union_r2 z (L \u dom G1) (dom G2) Hz2)).
  assert (Hzxm : z \notin \{xm}) by (exact (@notin_union_r2 z ((L \u dom G1) \u dom G2) \{xm} Hz1)).
  assert (Hzym : z \notin \{ym}) by (exact (@notin_union_r2 z (((L \u dom G1) \u dom G2) \u \{xm}) \{ym} Hz)).
  split; [exact HzL|]. split; [exact HzG1|]. split; [exact HzG2|]. split.
  - exact (@notin_singleton_r z xm Hzxm).
  - exact (@notin_singleton_r z ym Hzym).
Qed.

Lemma si_init_let : forall (L:fset var) (G1 G2:ctx) (D1 D2:init_ctx)
    (xm ym:var) (Sm:typ) (vs:vars) (t u:trm) (T:typ) (i i':init_typ),
  QiF (G1 & xm ~ Sm & G2) (D1 & xm ~ ib & D2) vs t i ->
  (forall z, z \notin L ->
     QiF ((G1 & xm ~ Sm & G2) & z ~ T)
         ((D1 & xm ~ ib & D2) & z ~ i)
         (vs \u \{z}) (open z u) i') ->
  xm # G2 -> xm # D2 -> xm \notin fv_env G1 ->
  (G1 & subst_env xm ym G2 ⊢ trm_var (avar_f ym) ∶ subst_var xm ym Sm) ->
  binds ym it (D1 & D2) ->
  G1 & subst_env xm ym G2 ⸴ D1 & D2 ⸴ subst_var xm ym vs
    ⊢i subst_var xm ym (trm_let T t u) ∶ i'.
Proof.
  intros L G1 G2 D1 D2 xm ym Sm vs t u T i i' Ht Hu HxG HxD Hfv Hpre Hbinds.
  set (L' := (((L \u dom G1) \u dom G2) \u \{xm}) \u \{ym}).
  unfold QiF in Ht, Hu. simpl.
  eapply (@init_let L' _ _ _ _ _ _ i _).
  - refine (Ht G1 G2 D1 D2 xm ym Sm _ _ _ _ _ _ _);
      [reflexivity|reflexivity|exact HxG|exact HxD|exact Hfv|exact Hpre|exact Hbinds].
  - intros z Hz. unfold L' in Hz.
    destruct (@notin_L_prime L G1 G2 xm ym z Hz) as [HzL [HzG1 [HzG2 [Hzxm Hzym]]]].
    assert (Hzx : z <> xm) by exact Hzxm.
    assert (Hru : subst_var xm ym (open_rec 0 z u) = open_rec 0 z (subst_var xm ym u))
      by (apply subst_open_fresh_trm; auto).
    assert (HeqG : ((G1 & xm ~ Sm & G2) & z ~ T) = G1 & xm ~ Sm & (G2 & z ~ T)).
    { symmetry. apply concat_assoc. }
    assert (HeqD : ((D1 & xm ~ ib & D2) & z ~ i)
                    = D1 & xm ~ ib & (D2 & z ~ i)).
    { symmetry. apply concat_assoc. }
    assert (Hpre' : G1 & subst_env xm ym (G2 & z ~ T)
                    ⊢ trm_var (avar_f ym) ∶ subst_var xm ym Sm).
    { rewrite map_push. rewrite concat_assoc.
      eapply ty_trm_binds_extends; [exact Hpre|].
      apply binds_extends_push_fresh.
      rewrite dom_concat. apply notin_union_l; [exact HzG1|].
      rewrite dom_subst_env. exact HzG2. }
    assert (HxG' : xm # (G2 & z ~ T)).
    { rewrite dom_push. apply notin_union_l.
      - apply notin_singleton_l. exact (not_eq_sym Hzxm).
      - exact HxG. }
    assert (HxD' : xm # (D2 & z ~ i)).
    { rewrite dom_push. apply notin_union_l.
      - apply notin_singleton_l. exact (not_eq_sym Hzxm).
      - exact HxD. }
    assert (Hbinds' : binds ym it (D1 & (D2 & z ~ i))).
    { rewrite concat_assoc.
      eapply LibEnv.binds_push_neq.
      - exact Hbinds.
      - exact (not_eq_sym Hzym). }
    pose proof (Hu z HzL G1 (G2 & z ~ T) D1 (D2 & z ~ i) xm ym Sm
                  HeqG HeqD HxG' HxD' Hfv Hpre' Hbinds') as Hres.
    rewrite map_push in Hres.
    rewrite Hru in Hres.
    assert (Hvs : subst_var xm ym (vs \u \{z}) = (subst_var xm ym vs) \u \{z})
      by (apply (@subst_vars_union_singleton vs xm ym z Hzx)).
    repeat rewrite concat_assoc in Hres.
    rewrite <- Hvs. exact Hres.
Qed.

Lemma si_init_llit : forall (L:fset var) (G1 G2:ctx) (D1 D2:init_ctx)
    (xm ym:var) (Sm:typ) (vs:vars) (l:lit) (u:trm) (T:typ) (i:init_typ),
  QlF (G1 & xm ~ Sm & G2) (D1 & xm ~ ib & D2) l ->
  (forall z, z \notin L ->
     QiF ((G1 & xm ~ Sm & G2) & z ~ T)
         ((D1 & xm ~ ib & D2) & z ~ committed)
         vs (open z u) i) ->
  xm # G2 -> xm # D2 -> xm \notin fv_env G1 ->
  (G1 & subst_env xm ym G2 ⊢ trm_var (avar_f ym) ∶ subst_var xm ym Sm) ->
  binds ym it (D1 & D2) ->
  G1 & subst_env xm ym G2 ⸴ D1 & D2 ⸴ subst_var xm ym vs
    ⊢i subst_var xm ym (trm_lit T l u) ∶ i.
Proof.
  intros L G1 G2 D1 D2 xm ym Sm vs l u T i Hl Hu HxG HxD Hfv Hpre Hbinds.
  set (L' := (((L \u dom G1) \u dom G2) \u \{xm}) \u \{ym}).
  unfold QlF in Hl. unfold QiF in Hu. simpl.
  eapply (@init_llit L' _ _ _ _ _ _).
  - refine (Hl G1 G2 D1 D2 xm ym Sm _ _ _ _ _ _ _);
      [reflexivity|reflexivity|exact HxG|exact HxD|exact Hfv|exact Hpre|exact Hbinds].
  - intros z Hz. unfold L' in Hz.
    destruct (@notin_L_prime L G1 G2 xm ym z Hz) as [HzL [HzG1 [HzG2 [Hzxm Hzym]]]].
    assert (Hzx : z <> xm) by exact Hzxm.
    assert (Hru : subst_var xm ym (open_rec 0 z u) = open_rec 0 z (subst_var xm ym u))
      by (apply subst_open_fresh_trm; auto).
    assert (HeqG : ((G1 & xm ~ Sm & G2) & z ~ T) = G1 & xm ~ Sm & (G2 & z ~ T)).
    { symmetry. apply concat_assoc. }
    assert (HeqD : ((D1 & xm ~ ib & D2) & z ~ committed)
                    = D1 & xm ~ ib & (D2 & z ~ committed)).
    { symmetry. apply concat_assoc. }
    assert (Hpre' : G1 & subst_env xm ym (G2 & z ~ T)
                    ⊢ trm_var (avar_f ym) ∶ subst_var xm ym Sm).
    { rewrite map_push. rewrite concat_assoc.
      eapply ty_trm_binds_extends; [exact Hpre|].
      apply binds_extends_push_fresh.
      rewrite dom_concat. apply notin_union_l; [exact HzG1|].
      rewrite dom_subst_env. exact HzG2. }
    assert (HxG' : xm # (G2 & z ~ T)).
    { rewrite dom_push. apply notin_union_l.
      - apply notin_singleton_l. exact (not_eq_sym Hzxm).
      - exact HxG. }
    assert (HxD' : xm # (D2 & z ~ committed)).
    { rewrite dom_push. apply notin_union_l.
      - apply notin_singleton_l. exact (not_eq_sym Hzxm).
      - exact HxD. }
    assert (Hbinds' : binds ym it (D1 & (D2 & z ~ committed))).
    { rewrite concat_assoc.
      eapply LibEnv.binds_push_neq.
      - exact Hbinds.
      - exact (not_eq_sym Hzym). }
    pose proof (Hu z HzL G1 (G2 & z ~ T) D1 (D2 & z ~ committed) xm ym Sm
                  HeqG HeqD HxG' HxD' Hfv Hpre' Hbinds') as Hres.
    rewrite map_push in Hres.
    rewrite Hru in Hres.
    repeat rewrite concat_assoc in Hres. exact Hres.
Qed.

Lemma init_commit_subst_mut :
  (forall (G:ctx) (D:init_ctx) (t:trm), G ⸴ D ⊢c t -> QcF G D t) /\
  (forall (G:ctx) (D:init_ctx) (avs:avars), G ⸴ D ⊢c avs -> QaF G D avs) /\
  (forall (G:ctx) (D:init_ctx) (l:lit), G ⸴ D ⊢c l -> QlF G D l) /\
  (forall (G:ctx) (D:init_ctx) (vs:vars) (t:trm) (i:init_typ), G ⸴ D ⸴ vs ⊢i t ∶ i -> QiF G D vs t i) /\
  (forall (G:ctx) (D:init_ctx) (vs:vars) (avs:avars) (is':inits), G ⸴ D ⸴ vs ⊢i avs :: is' -> QisF G D vs avs is').
Proof.
  apply (well_init_mut_ind
    (fun (G:ctx) (D:init_ctx) (t:trm) (_:G ⸴ D ⊢c t) => QcF G D t)
    (fun (G:ctx) (D:init_ctx) (avs:avars) (_:G ⸴ D ⊢c avs) => QaF G D avs)
    (fun (G:ctx) (D:init_ctx) (l:lit) (_:G ⸴ D ⊢c l) => QlF G D l)
    (fun (G:ctx) (D:init_ctx) (vs:vars) (t:trm) (i:init_typ) (_:G ⸴ D ⸴ vs ⊢i t ∶ i) => QiF G D vs t i)
    (fun (G:ctx) (D:init_ctx) (vs:vars) (avs:avars) (is':inits) (_:G ⸴ D ⸴ vs ⊢i avs :: is') => QisF G D vs avs is'));
  intros; unfold QcF, QaF, QlF, QiF, QisF in *;
  intros G1 G2 D1 D2 xm ym Sm HeqG HeqD HxG HxD Hfv Hpre Hbinds; subst;
  first [ solve [ eapply sc_commit_var; eauto 4 ]
        | solve [ eapply sc_commit_all_elim; eauto 4 ]
        | solve [ eapply sc_commit_new; eauto 4 ]
        | solve [ eapply sc_commit_rcd_elim; eauto 4 ]
        | solve [ eapply sc_commit_fld_asn; eauto 4 ]
        | solve [ eapply sc_commit_let; eauto 4 ]
        | solve [ eapply sc_commit_llit; eauto 4 ]
        | solve [ eapply sc_commit_avars_nil; eauto 4 ]
        | solve [ eapply sc_commit_avars_cons; eauto 4 ]
        | solve [ eapply sc_commit_all_intro; eauto 4 ]
        | solve [ eapply sc_commit_con_intro; eauto 4 ]
        | solve [ eapply si_init_var_binds; eauto 4 ]
        | solve [ eapply si_init_commit; eauto 4 ]
        | solve [ eapply si_init_new_free; eauto 4 ]
        | solve [ eapply si_init_fld_asn_ac; eauto 4 ]
        | solve [ eapply si_init_fld_asn_ff; eauto 4 ]
        | solve [ eapply si_init_let; eauto 4 ]
        | solve [ eapply si_init_llit; eauto 4 ]
        | solve [ eapply si_inits_nil; eauto 4 ]
        | solve [ eapply si_inits_cons; eauto 4 ] ].
Qed.

Corollary commit_subst : forall (G:ctx) (D:init_ctx) (t:trm), G ⸴ D ⊢c t ->
  forall G1 G2 D1 D2 xm ym Sm,
    G = G1 & xm ~ Sm & G2 ->
    D = D1 & xm ~ ib & D2 ->
    xm # G2 -> xm # D2 -> xm \notin fv_env G1 ->
    (G1 & subst_env xm ym G2 ⊢ trm_var (avar_f ym) ∶ subst_var xm ym Sm) ->
    binds ym it (D1 & D2) ->
    G1 & subst_env xm ym G2 ⸴ D1 & D2 ⊢c subst_var xm ym t.
Proof.
  intros G D t H G1 G2 D1 D2 xm ym Sm HeqG HeqD HxG HxD Hfv Hpre Hb.
  pose proof (proj1 init_commit_subst_mut G D t H) as Hq.
  unfold QcF in Hq. exact (Hq G1 G2 D1 D2 xm ym Sm HeqG HeqD HxG HxD Hfv Hpre Hb).
Qed.

Corollary lit_commit_subst : forall (G:ctx) (D:init_ctx) (l:lit), G ⸴ D ⊢c l ->
  forall G1 G2 D1 D2 xm ym Sm,
    G = G1 & xm ~ Sm & G2 ->
    D = D1 & xm ~ ib & D2 ->
    xm # G2 -> xm # D2 -> xm \notin fv_env G1 ->
    (G1 & subst_env xm ym G2 ⊢ trm_var (avar_f ym) ∶ subst_var xm ym Sm) ->
    binds ym it (D1 & D2) ->
    G1 & subst_env xm ym G2 ⸴ D1 & D2 ⊢c subst_var xm ym l.
Proof.
  intros G D l H G1 G2 D1 D2 xm ym Sm HeqG HeqD HxG HxD Hfv Hpre Hb.
  pose proof (proj1 (proj2 (proj2 init_commit_subst_mut)) G D l H) as Hq.
  unfold QlF in Hq. exact (Hq G1 G2 D1 D2 xm ym Sm HeqG HeqD HxG HxD Hfv Hpre Hb).
Qed.

Corollary init_subst : forall (G:ctx) (D:init_ctx) (vs:vars) (t:trm) (i:init_typ),
  G ⸴ D ⸴ vs ⊢i t ∶ i ->
  forall G1 G2 D1 D2 xm ym Sm,
    G = G1 & xm ~ Sm & G2 ->
    D = D1 & xm ~ ib & D2 ->
    xm # G2 -> xm # D2 -> xm \notin fv_env G1 ->
    (G1 & subst_env xm ym G2 ⊢ trm_var (avar_f ym) ∶ subst_var xm ym Sm) ->
    binds ym it (D1 & D2) ->
    G1 & subst_env xm ym G2 ⸴ D1 & D2 ⸴ subst_var xm ym vs
      ⊢i subst_var xm ym t ∶ i.
Proof.
  intros G D vs t i H G1 G2 D1 D2 xm ym Sm HeqG HeqD HxG HxD Hfv Hpre Hb.
  pose proof (proj1 (proj2 (proj2 (proj2 init_commit_subst_mut))) G D vs t i H) as Hq.
  unfold QiF in Hq. exact (Hq G1 G2 D1 D2 xm ym Sm HeqG HeqD HxG HxD Hfv Hpre Hb).
Qed.


End Param.
End GenSubst.


Unset Implicit Arguments.

Lemma init_sub_trans : forall (a b c:init_typ),
  init_sub a b -> init_sub b c -> init_sub a c.
Proof.
  intros a b c H1 H2. inversion H1; subst; inversion H2; subst;
    auto using init_sub_refl, init_sub_comm_unspec, init_sub_free_unspec.
Qed.

Lemma init_var_status_binds : forall (D:init_ctx) (vs:vars) (y:var) (i:init_typ),
  init_var D vs y i ->
  exists i0, binds y i0 D /\ init_sub i0 i /\ (y \in vs \/ i0 = committed).
Proof.
  intros D vs y i H. induction H.
  - exists committed. split; [exact H|split]; [apply init_sub_refl|right; reflexivity].
  - exists free. split; [exact H0|split]; [apply init_sub_refl|left; exact H].
  - exists unspecified. split; [exact H0|split]; [apply init_sub_refl|left; exact H].
  - destruct IHinit_var as [i0 [Hb [Hsub Hcase]]].
    exists i0. split; [exact Hb|split]; [|exact Hcase].
    eapply init_sub_trans; eassumption.
Qed.

Lemma init_typing_var_status : forall (G:ctx) (D:init_ctx) (vs:vars) (y:var) (i:init_typ),
  G ⸴ D ⸴ vs ⊢i trm_var (avar_f y) ∶ i ->
  exists i0, binds y i0 D /\ init_sub i0 i /\ (y \in vs \/ i0 = committed).
Proof.
  intros G D vs y i H. inversion H; subst; try discriminate.
  - eapply init_var_status_binds. exact H4.
  - assert (Hb : binds y committed D) by (eapply init_typing_var_committed_binds; exact H).
    exists committed. split; [exact Hb|split]; [apply init_sub_refl|right; reflexivity].
Qed.

Lemma vs_union_id : forall (vs:vars) (y:var), y \in vs -> vs \u \{y} = vs.
Proof.
  intros vs y Hy. apply fset_extens.
  - intros z Hz. rewrite in_union in Hz. destruct Hz as [Hz|Hz].
    + exact Hz.
    + rewrite in_singleton in Hz. subst z. exact Hy.
  - intros z Hz. rewrite in_union. left. exact Hz.
Qed.

Lemma init_open_any_status : forall (L:fset var) (G:ctx) (D:init_ctx) (vs:vars)
  (S:typ) (t:trm) (i' i:init_typ) (y:var),
  (forall x0, x0 \notin L ->
     G & x0 ~ S ⸴ D & x0 ~ i ⸴ (vs \u \{x0}) ⊢i open x0 t ∶ i') ->
  G ⊢ trm_var (avar_f y) ∶ S ->
  G ⸴ D ⸴ vs ⊢i trm_var (avar_f y) ∶ i ->
  G ⸴ D ⸴ vs ⊢i open y t ∶ i'.
Proof.
  intros L G D vs S t i' i y Hbody Hty Hinit.
  destruct (@init_typing_var_status G D vs y i Hinit) as [i0 [Hbinds [Hsub Hcase]]].
  destruct (@var_fresh (((((((L \u dom G) \u fv_env G) \u fv t) \u fv S) \u dom D) \u vs) \u \{y})) as [x0 Hx0].
  pose proof (notin_union_r1 Hx0) as Hx1.
  pose proof (notin_union_r1 Hx1) as Hx2.
  pose proof (notin_union_r1 Hx2) as Hx3.
  pose proof (notin_union_r1 Hx3) as Hx4.
  pose proof (notin_union_r1 Hx4) as Hx5.
  pose proof (notin_union_r1 Hx5) as Hx6.
  pose proof (notin_union_r1 Hx6) as HxL.
  pose proof (notin_union_r2 Hx6) as HxdomG.
  pose proof (notin_union_r2 Hx5) as Hxfvenv.
  pose proof (notin_union_r2 Hx4) as Hxt.
  pose proof (notin_union_r2 Hx3) as HxS.
  pose proof (notin_union_r2 Hx2) as HxdomD.
  pose proof (notin_union_r2 Hx1) as Hxvs.
  pose proof (notin_union_r2 Hx0) as Hxy.
  assert (HxemptyG : x0 # (empty:ctx)) by (rewrite (@dom_empty typ); apply notin_empty).
  assert (HxemptyD : x0 # (empty:init_ctx)) by (rewrite (@dom_empty init_typ); apply notin_empty).
  assert (Hbody0 : G & x0 ~ S ⸴ D & x0 ~ i ⸴ (vs \u \{x0}) ⊢i open x0 t ∶ i')
    by (apply Hbody; exact HxL).
  assert (Hbody0' : G & x0 ~ S & empty ⸴ D & x0 ~ i & empty ⸴ (vs \u \{x0}) ⊢i open x0 t ∶ i').
  { rewrite concat_empty_r. rewrite concat_empty_r. exact Hbody0. }
  assert (HpreS : (G & subst_env x0 y (empty:ctx)) ⊢ trm_var (avar_f y) ∶ subst_var x0 y S).
  { rewrite map_empty. rewrite concat_empty_r.
    rewrite (@fv_subst_typ S x0 y HxS). exact Hty. }
  assert (Hb' : binds y i0 (D & empty)) by (rewrite concat_empty_r; exact Hbinds).
  pose proof (@GenSubst.init_subst i i0 Hsub
                (G & x0 ~ S & empty) (D & x0 ~ i & empty)
                (vs \u \{x0}) (open x0 t) i' Hbody0'
                G (empty:ctx) D (empty:init_ctx) x0 y S
                eq_refl eq_refl HxemptyG HxemptyD Hxfvenv HpreS Hb') as Hres.
  rewrite (@map_empty typ typ (subst_var x0 y)) in Hres.
  rewrite (@concat_empty_r typ G) in Hres.
  rewrite (@concat_empty_r init_typ D) in Hres.
  assert (Hvs : subst_var x0 y (vs \u \{x0}) = vs \u \{y})
    by (apply subst_var_union_self; exact Hxvs).
  assert (Hres2 : G ⸴ D ⸴ (vs \u \{y}) ⊢i open y t ∶ i').
  { rewrite (@subst_intro_trm t x0 y 0 Hxt).
    rewrite <- Hvs.
    exact Hres. }
  destruct Hcase as [Hy|Hcomm].
  - rewrite <- (@vs_union_id vs y Hy). exact Hres2.
  - subst i0.
    assert (Hrm : G ⸴ D ⸴ ((vs \u \{y}) \- \{y}) ⊢i open y t ∶ i').
    { eapply init_typing_vs_remove_committed; [exact Hbinds|exact Hres2]. }
    eapply init_typing_vs_weaken with (vs := ((vs \u \{y}) \- \{y})).
    + intros z Hz. rewrite FsetImpl.in_remove in Hz. destruct Hz as [Hin Hne].
      rewrite in_union in Hin. destruct Hin as [Hin|Hin]; [exact Hin|].
      exfalso. apply Hne. exact Hin.
    + exact Hrm.
Qed.

Lemma ty_config_let_var_any : forall (L:fset var) (G:ctx) (D:init_ctx)
  (ℰ:eff_ctx) (ℰs:list eff_ctx) (Fs:stack) (Sigma:heap) (U S T2:typ)
  (i i':init_typ) (effs_frame effs_tail:effects) (effss_tail:list effects)
  (t:trm) (y:var),
  inert G -> inert_inits D -> heap_correspond G Sigma ->
  free_sub_heaps G D Sigma (ℰ :: ℰs) ->
  ty_stack G D (ℰ :: ℰs) Fs T2 i' ((effs_tail :: effss_tail)%list) U ->
  G ⊢ trm_var (avar_f y) ∶ S ->
  G ⸴ D ⸴ dom ℰ ⊢i trm_var (avar_f y) ∶ i ->
  (forall x0, x0 \notin L -> G & x0 ~ S ⊢ open x0 t ∶ T2) ->
  (forall x0, x0 \notin L ->
     G & x0 ~ S ⸴ D & x0 ~ i ⸴ (dom ℰ \u \{x0}) ⊢i open x0 t ∶ i') ->
  (forall x0, x0 \notin L -> eff_trm (open x0 t) effs_frame) ->
  eff_ctx_corr (ℰ :: ℰs) (((effs_frame ++ effs_tail)%list :: effss_tail)%list) ->
  exists G' D' Es' effss',
    ty_config (G & G') D' Es' effss' (open y t ; Fs ; Sigma) U.
Proof.
  intros L G D ℰ ℰs Fs Sigma U S T2 i i' effs_frame effs_tail effss_tail t y
         Hinert Hinits Hhc Hfs Hstack Hty Hinit Hbody_ty Hbody_init Hbody_eff Hcorr.
  assert (Hty' : G ⊢ open y t ∶ T2).
  { eapply ty_trm_open_any; [exact Hbody_ty|exact Hty]. }
  assert (Heff' : eff_trm (open y t) effs_frame).
  { eapply eff_trm_llit_open; exact Hbody_eff. }
  assert (Hinit' : G ⸴ D ⸴ dom ℰ ⊢i open y t ∶ i').
  { eapply init_open_any_status; [exact Hbody_init|exact Hty|exact Hinit]. }
  exists (empty:ctx), D, (ℰ :: ℰs),
    (((effs_frame ++ effs_tail)%list :: effss_tail)%list).
  rewrite concat_empty_r.
  eapply (@ty_config_c G D Sigma ℰ ℰs Fs (open y t) T2 i' U effs_frame effs_tail effss_tail).
  - exact Hinert.
  - exact Hinits.
  - exact Hhc.
  - exact Hfs.
  - exact Hstack.
  - exact Hty'.
  - exact Heff'.
  - exact Hinit'.
  - exact Hcorr.
Qed.

Lemma eff_trm_var_nil : forall (a:avar) (effs:effects),
  eff_trm (trm_var a) effs -> effs = nil.
Proof.
  intros a effs H. inversion H; subst; try discriminate.
  - reflexivity.
Qed.

Lemma ty_config_red_let_var : forall (G:ctx) (D:init_ctx) (Es:list eff_ctx)
  (effss:list effects) (Fs:stack) (Sigma:heap) (U:typ) (t:trm) (y:var),
  ty_config G D Es effss (trm_var (avar_f y) ; (frame_let t :: Fs)%list ; Sigma) U ->
  exists G' D' Es' effss',
    ty_config (G & G') D' Es' effss' (open y t ; Fs ; Sigma) U.
Proof.
  intros G D Es effss Fs Sigma U t y Hcfg.
  destruct (@ty_config_inv_s G D Es effss (trm_var (avar_f y))
              ((frame_let t :: Fs)%list) Sigma U Hcfg) as
    (ℰ & ℰs & Ts & ii & effsH & effs' & effss0 &
     HeqEs & HeqEffs & Hinert & Hinits & Hhc & Hfs & Hstack & Hty & Heff & Hinit & Hcorr).
  destruct (ty_stack_let_inv Hstack) as
    (ℰ0 & ℰs0 & L & T2 & i' & effs0 & effss_tail & effs_frame &
     HeqEs' & HeqEffs' & Hstack_tail & Hbody_ty & Hbody_init & Hbody_eff).
  inversion HeqEs'; subst.
  injection HeqEffs' as HeqH HeqT. subst effsH effss0.
  assert (Heffnil : effs' = nil) by (eapply eff_trm_var_nil; exact Heff).
  subst effs'.
  cbn in Hcorr.
  eapply (ty_config_let_var_any L G D ℰ0 ℰs0 Fs Sigma U Ts T2 ii i'
            effs_frame effs0 effss_tail t y);
    eassumption.
Qed.


Unset Implicit Arguments.

Definition commit_ctx (E:eff_ctx) : init_ctx := EnvOps.map (fun (_:effects) => committed) E.

Lemma commit_ctx_dom : forall (E:eff_ctx), dom (commit_ctx E) = dom E.
Proof. intros. unfold commit_ctx. apply dom_map. Qed.

Lemma binds_commit_ctx_in : forall (E:eff_ctx) (x:var),
  x \in dom E -> binds x committed (commit_ctx E).
Proof.
  intros E x Hx. destruct (dom_binds_exists Hx) as [v Hb].
  unfold commit_ctx. exact (@binds_map effects init_typ x v (fun _ => committed) E Hb).
Qed.

Lemma binds_commit_ctx_notin : forall (E:eff_ctx) (x:var) (v:init_typ),
  x \notin dom E -> ~ binds x v (commit_ctx E).
Proof.
  intros E x v Hx Hb. apply Hx. rewrite <- commit_ctx_dom.
  eapply binds_in_dom; exact Hb.
Qed.

Section Strengthen.
Variables (D:init_ctx) (ℰ:eff_ctx).
Definition Dstr := D & commit_ctx ℰ.

Hypothesis Hfree_ℰ : forall x, x \in dom ℰ -> binds x free D.




Lemma binds_str_in : forall (E:init_ctx) (x:var),
  (forall y, y \in dom E -> y \notin dom ℰ) ->
  x \in dom ℰ -> binds x committed (Dstr & E).
Proof.
  intros E x Hdisj Hx.
  assert (HxE : x \notin dom E) by (intro K; exact (Hdisj x K Hx)).
  apply LibEnv.binds_concat_left with (E2:=E).
  - unfold Dstr. apply LibEnv.binds_concat_right.
    apply binds_commit_ctx_in. exact Hx.
  - exact HxE.
Qed.

Lemma binds_str_out : forall (E:init_ctx) (x:var) (v:init_typ),
  (forall y, y \in dom E -> y \notin dom ℰ) ->
  x \notin dom ℰ ->
  binds x v (D & E) -> binds x v (Dstr & E).
Proof.
  intros E x v Hdisj Hx Hb.
  destruct (classic (x \in dom E)) as [HinE|HnotinE].
  - assert (HbE : binds x v E).
    { destruct (@LibEnv.binds_concat_inv' init_typ x v D E Hb) as [[HxE _]|HbE].
      - exfalso. exact (HxE HinE).
      - exact HbE. }
    apply LibEnv.binds_concat_right. exact HbE.
  - assert (HbD : binds x v D) by (eapply LibEnv.binds_concat_left_inv; [exact Hb|exact HnotinE]).
    apply LibEnv.binds_concat_left with (E2:=E).
    + unfold Dstr. apply LibEnv.binds_concat_left with (E2:=commit_ctx ℰ).
      * exact HbD.
      * rewrite commit_ctx_dom. exact Hx.
    + exact HnotinE.
Qed.

Lemma init_var_transfer_commit : forall (E:init_ctx) (vs:vars) (x:var) (i:init_typ),
  (forall y, y \in dom E -> y \notin dom ℰ) ->
  (forall y, y \in dom ℰ -> y \notin vs) ->
  init_var (D & E) vs x i -> init_var (Dstr & E) vs x i.
Proof.
  intros E vs x i Hdisj Hvs H. remember (D & E) as Delta eqn:Heq.
  induction H.
  - (* commit *) subst Delta. apply init_var_commit.
    destruct (classic (x \in dom ℰ)) as [Hx|Hx].
    + exfalso.
      assert (HxE : x \notin dom E) by (intro K; exact (Hdisj x K Hx)).
      assert (HbD : binds x committed D) by (eapply LibEnv.binds_concat_left_inv; [exact H|exact HxE]).
      pose proof (Hfree_ℰ x Hx) as Hf.
      pose proof (@LibEnv.binds_functional init_typ x committed free D HbD Hf) as E0.
      discriminate E0.
    + eapply binds_str_out; [exact Hdisj|exact Hx|exact H].
  - (* free *) subst Delta. apply init_var_free.
    + exact H.
    + destruct (classic (x \in dom ℰ)) as [Hx|Hx].
      * exfalso. exact (Hvs x Hx H).
      * eapply binds_str_out; [exact Hdisj|exact Hx|exact H0].
  - (* unspec *) subst Delta. apply init_var_unspec.
    + exact H.
    + destruct (classic (x \in dom ℰ)) as [Hx|Hx].
      * exfalso. exact (Hvs x Hx H).
      * eapply binds_str_out; [exact Hdisj|exact Hx|exact H0].
  - (* sub *) eapply init_var_sub; [apply IHinit_var; [exact Hvs|exact Heq]|exact H0].
Qed.

End Strengthen.


Unset Implicit Arguments.

Section Mut.
Variables (D:init_ctx) (ℰ:eff_ctx).
Let Dstr := D & commit_ctx ℰ.

Hypothesis Hfree_ℰ : forall x, x \in dom ℰ -> binds x free D.

(* Disjointness is preserved when extending E with a single binder whose
   variable is not in the effect context. *)
Lemma disj_push : forall (E:init_ctx) (z:var) (v:init_typ),
  (forall y, y \in dom E -> y \notin dom ℰ) ->
  z \notin dom ℰ ->
  (forall y, y \in dom (E & z ~ v) -> y \notin dom ℰ).
Proof.
  intros E z v Hdisj Hz y Hy.
  rewrite dom_concat in Hy. rewrite in_union in Hy.
  destruct Hy as [Hy|Hy].
  - apply Hdisj. exact Hy.
  - rewrite dom_single in Hy. rewrite in_singleton in Hy. subst y. exact Hz.
Qed.

(* Disjointness for the binder block used by commit_con_intro. *)
Lemma disj_con : forall (E:init_ctx) (L:fset var) (n:nat) (x:var)
  (ys:list var) (is':inits),
  List.length ys = List.length is' ->
  fresh (L \u dom ℰ) (S n) (x :: ys) ->
  (forall y, y \in dom E -> y \notin dom ℰ) ->
  (forall y, y \in dom (E & (ys ~** is') & (x ~ free)) -> y \notin dom ℰ).
Proof.
  intros E L n x ys is' Hlen Hfresh Hdisj y Hy.
  rewrite dom_concat in Hy. rewrite in_union in Hy.
  destruct Hy as [Hy|Hy].
  - rewrite dom_concat in Hy. rewrite in_union in Hy.
    destruct Hy as [HyE|HyY].
    + apply Hdisj. exact HyE.
    + rewrite (@dom_ys_inits ys is' Hlen) in HyY.
      assert (Hnot : y \notin L \u dom ℰ).
      { eapply fresh_from_list_notin; [exact Hfresh|].
        rewrite from_list_cons. rewrite in_union. right. exact HyY. }
      exact (@notin_union_r2 y L (dom ℰ) Hnot).
  - rewrite dom_single in Hy. rewrite in_singleton in Hy. subst y.
    assert (Hnot : x \notin L \u dom ℰ) by (eapply fresh_cons_head; exact Hfresh).
    exact (@notin_union_r2 x L (dom ℰ) Hnot).
Qed.

(* All fresh variables introduced by commit_con_intro avoid dom ℰ, hence
   every variable of dom ℰ avoids the variable set of the init rule. *)
Lemma vs_con : forall (L:fset var) (n:nat) (x:var) (ys:list var),
  fresh (L \u dom ℰ) (S n) (x :: ys) ->
  (forall y, y \in dom ℰ -> y \notin (from_list ys) \u \{x}).
Proof.
  intros L n x ys Hfresh y Hy Hyin.
  rewrite in_union in Hyin. destruct Hyin as [Hyin|Hyin].
  - assert (Hnot : y \notin L \u dom ℰ).
    { eapply fresh_from_list_notin; [exact Hfresh|].
      rewrite from_list_cons. rewrite in_union. right. exact Hyin. }
    exact (@notin_union_r2 y L (dom ℰ) Hnot Hy).
  - rewrite in_singleton in Hyin. subst y.
    assert (Hnot : x \notin L \u dom ℰ) by (eapply fresh_cons_head; exact Hfresh).
    exact (@notin_union_r2 x L (dom ℰ) Hnot Hy).
Qed.

Lemma init_commit_strengthen_mut :
  (forall (G:ctx) (D0:init_ctx) (t:trm), G ⸴ D0 ⊢c t ->
     forall E, D0 = D & E ->
       (forall y, y \in dom E -> y \notin dom ℰ) ->
       G ⸴ (Dstr & E) ⊢c t) /\
  (forall (G:ctx) (D0:init_ctx) (avs:avars), G ⸴ D0 ⊢c avs ->
     forall E, D0 = D & E ->
       (forall y, y \in dom E -> y \notin dom ℰ) ->
       G ⸴ (Dstr & E) ⊢c avs) /\
  (forall (G:ctx) (D0:init_ctx) (l:lit), G ⸴ D0 ⊢c l ->
     forall E, D0 = D & E ->
       (forall y, y \in dom E -> y \notin dom ℰ) ->
       G ⸴ (Dstr & E) ⊢c l) /\
  (forall (G:ctx) (D0:init_ctx) (vs:vars) (t:trm) (i:init_typ),
     G ⸴ D0 ⸴ vs ⊢i t ∶ i ->
     forall E, D0 = D & E ->
       (forall y, y \in dom E -> y \notin dom ℰ) ->
       (forall y, y \in dom ℰ -> y \notin vs) ->
       G ⸴ (Dstr & E) ⸴ vs ⊢i t ∶ i) /\
  (forall (G:ctx) (D0:init_ctx) (vs:vars) (avs:avars) (is':inits),
     G ⸴ D0 ⸴ vs ⊢i avs :: is' ->
     forall E, D0 = D & E ->
       (forall y, y \in dom E -> y \notin dom ℰ) ->
       (forall y, y \in dom ℰ -> y \notin vs) ->
       G ⸴ (Dstr & E) ⸴ vs ⊢i avs :: is').
Proof.
  apply (well_init_mut_ind
    (fun (G:ctx) (D0:init_ctx) (t:trm) (_:G ⸴ D0 ⊢c t) =>
       forall E, D0 = D & E ->
         (forall y, y \in dom E -> y \notin dom ℰ) ->
         G ⸴ (Dstr & E) ⊢c t)
    (fun (G:ctx) (D0:init_ctx) (avs:avars) (_:G ⸴ D0 ⊢c avs) =>
       forall E, D0 = D & E ->
         (forall y, y \in dom E -> y \notin dom ℰ) ->
         G ⸴ (Dstr & E) ⊢c avs)
    (fun (G:ctx) (D0:init_ctx) (l:lit) (_:G ⸴ D0 ⊢c l) =>
       forall E, D0 = D & E ->
         (forall y, y \in dom E -> y \notin dom ℰ) ->
         G ⸴ (Dstr & E) ⊢c l)
    (fun (G:ctx) (D0:init_ctx) (vs:vars) (t:trm) (i:init_typ)
         (_:G ⸴ D0 ⸴ vs ⊢i t ∶ i) =>
       forall E, D0 = D & E ->
         (forall y, y \in dom E -> y \notin dom ℰ) ->
         (forall y, y \in dom ℰ -> y \notin vs) ->
         G ⸴ (Dstr & E) ⸴ vs ⊢i t ∶ i)
    (fun (G:ctx) (D0:init_ctx) (vs:vars) (avs:avars) (is':inits)
         (_:G ⸴ D0 ⸴ vs ⊢i avs :: is') =>
       forall E, D0 = D & E ->
         (forall y, y \in dom E -> y \notin dom ℰ) ->
         (forall y, y \in dom ℰ -> y \notin vs) ->
         G ⸴ (Dstr & E) ⸴ vs ⊢i avs :: is')).
  - (* commit_var *)
    intros Gamma Delta x b E Heq Hdisj. subst Delta.
    apply commit_var.
    destruct (classic (x \in dom ℰ)) as [Hx|Hx].
    + exfalso.
      assert (HxE : x \notin dom E) by (intro K; exact (Hdisj x K Hx)).
      assert (HbD : binds x committed D)
        by (eapply LibEnv.binds_concat_left_inv; [exact b|exact HxE]).
      pose proof (Hfree_ℰ x Hx) as Hf.
      pose proof (@LibEnv.binds_functional init_typ x committed free D HbD Hf) as E0.
      discriminate E0.
    + eapply binds_str_out; [exact Hdisj|exact Hx|exact b].
  - (* commit_all_elim *)
    intros Gamma Delta x z c IHx c0 IHz E Heq Hdisj. subst Delta.
    apply commit_all_elim.
    + apply IHx; [reflexivity|exact Hdisj].
    + apply IHz; [reflexivity|exact Hdisj].
  - (* commit_new *)
    intros Gamma Delta x avs Ts is' T c IHx t a c0 IHa E Heq Hdisj. subst Delta.
    eapply commit_new.
    + apply IHx; [reflexivity|exact Hdisj].
    + exact t.
    + exact a.
    + apply IHa; [reflexivity|exact Hdisj].
  - (* commit_rcd_elim *)
    intros Gamma Delta x a c IHx E Heq Hdisj. subst Delta.
    apply commit_rcd_elim.
    apply IHx; [reflexivity|exact Hdisj].
  - (* commit_fld_asn *)
    intros Gamma Delta x i y a c IHx c0 IHy E Heq Hdisj. subst Delta.
    eapply (@commit_fld_asn Gamma (Dstr & E) x i y a).
    + apply IHx; [reflexivity|exact Hdisj].
    + apply IHy; [reflexivity|exact Hdisj].
  - (* commit_let *)
    intros L Gamma Delta t u T c IHt c0 IHbody E Heq Hdisj. subst Delta.
    eapply commit_let with (L := L \u dom ℰ).
    + apply IHt; [reflexivity|exact Hdisj].
    + intros x Hx.
      assert (HxL : x \notin L) by (eapply notin_union_r1; exact Hx).
      assert (HxE : x \notin dom ℰ) by (exact (@notin_union_r2 x L (dom ℰ) Hx)).
      assert (Hdisj' : forall y, y \in dom (E & x ~ committed) -> y \notin dom ℰ).
      { eapply disj_push; [exact Hdisj|exact HxE]. }
      specialize (IHbody x HxL (E & x ~ committed)
                    (eq_sym (@concat_assoc init_typ D E (x ~ committed))) Hdisj').
      rewrite concat_assoc in IHbody. exact IHbody.
  - (* commit_llit *)
    intros L Gamma Delta l u T c IHl c0 IHbody E Heq Hdisj. subst Delta.
    eapply commit_llit with (L := L \u dom ℰ).
    + apply IHl; [reflexivity|exact Hdisj].
    + intros x Hx.
      assert (HxL : x \notin L) by (eapply notin_union_r1; exact Hx).
      assert (HxE : x \notin dom ℰ) by (exact (@notin_union_r2 x L (dom ℰ) Hx)).
      assert (Hdisj' : forall y, y \in dom (E & x ~ committed) -> y \notin dom ℰ).
      { eapply disj_push; [exact Hdisj|exact HxE]. }
      specialize (IHbody x HxL (E & x ~ committed)
                    (eq_sym (@concat_assoc init_typ D E (x ~ committed))) Hdisj').
      rewrite concat_assoc in IHbody. exact IHbody.
  - (* committed_nil *)
    intros Gamma Delta E Heq Hdisj. subst Delta.
    apply committed_nil.
  - (* committed_cons *)
    intros Gamma Delta x avs c IHx c0 IHa E Heq Hdisj. subst Delta.
    apply committed_cons.
    + apply IHx; [reflexivity|exact Hdisj].
    + apply IHa; [reflexivity|exact Hdisj].
  - (* commit_all_intro *)
    intros L Gamma Delta T t c IHbody E Heq Hdisj. subst Delta.
    eapply commit_all_intro with (L := L \u dom ℰ).
    intros x Hx.
    assert (HxL : x \notin L) by (eapply notin_union_r1; exact Hx).
    assert (HxE : x \notin dom ℰ) by (eapply notin_union_r2; exact Hx).
    assert (Hdisj' : forall y, y \in dom (E & x ~ committed) -> y \notin dom ℰ).
    { eapply disj_push; [exact Hdisj|exact HxE]. }
    specialize (IHbody x HxL (E & x ~ committed)
                  (eq_sym (@concat_assoc init_typ D E (x ~ committed))) Hdisj').
    rewrite concat_assoc in IHbody. exact IHbody.
  - (* commit_con_intro *)
    intros L Gamma Delta Ts is' T i ds t e h i0 IHbody E Heq Hdisj. subst Delta.
    eapply commit_con_intro with (L := L \u dom ℰ).
    + exact e.
    + intros x ys Hlen Hfresh.
      apply h; [exact Hlen|].
      eapply fresh_union_r1; exact Hfresh.
    + intros x ys Hlen Hfresh.
      assert (HlenI : List.length ys = List.length is').
      { rewrite Hlen. rewrite <- e. reflexivity. }
      assert (HfL : fresh L (S (List.length ys)) (x :: ys)).
      { eapply fresh_union_r1; exact Hfresh. }
      assert (Hdisj' : forall y, y \in dom (E & (ys ~** is') & (x ~ free)) ->
                                y \notin dom ℰ).
      { eapply disj_con; [exact HlenI|exact Hfresh|exact Hdisj]. }
      assert (Hvs' : forall y, y \in dom ℰ -> y \notin (from_list ys) \u \{x}).
      { eapply vs_con; exact Hfresh. }
      assert (Heq' : ((D & E) & (ys ~** is') & (x ~ free)) =
                     D & (E & (ys ~** is') & (x ~ free))).
      { repeat rewrite concat_assoc. reflexivity. }
      specialize (IHbody x ys Hlen HfL (E & (ys ~** is') & (x ~ free)) Heq' Hdisj' Hvs').
      repeat rewrite concat_assoc in IHbody. exact IHbody.
  - (* init_var_binds *)
    intros Gamma Delta vs x i i0 E Heq Hdisj Hvs. subst Delta.
    apply init_var_binds.
    exact (@init_var_transfer_commit D ℰ Hfree_ℰ E vs x i Hdisj Hvs i0).
  - (* init_commit *)
    intros Gamma Delta t vs c IHt E Heq Hdisj Hvs. subst Delta.
    apply init_commit.
    apply IHt; [reflexivity|exact Hdisj].
  - (* init_new_free *)
    intros Gamma Delta vs x avs Ts is' T c IHx t iav IHa E Heq Hdisj Hvs. subst Delta.
    eapply init_new_free.
    + apply IHx; [reflexivity|exact Hdisj].
    + exact t.
    + apply IHa; [reflexivity|exact Hdisj|exact Hvs].
  - (* init_fld_asn_ac *)
    intros Gamma Delta vs x i y a i0 IHx i1 IHy E Heq Hdisj Hvs. subst Delta.
    eapply init_fld_asn_ac.
    + apply IHx; [reflexivity|exact Hdisj|exact Hvs].
    + apply IHy; [reflexivity|exact Hdisj|exact Hvs].
  - (* init_fld_asn_ff *)
    intros Gamma Delta vs x y a i IHx i0 IHy E Heq Hdisj Hvs. subst Delta.
    eapply init_fld_asn_ff.
    + apply IHx; [reflexivity|exact Hdisj|exact Hvs].
    + apply IHy; [reflexivity|exact Hdisj|exact Hvs].
  - (* init_let *)
    intros L Gamma Delta vs t u T i i' i0 IHt i1 IHbody E Heq Hdisj Hvs. subst Delta.
    eapply init_let with (L := L \u dom ℰ).
    + apply IHt; [reflexivity|exact Hdisj|exact Hvs].
    + intros x Hx.
      assert (HxL : x \notin L) by (eapply notin_union_r1; exact Hx).
      assert (HxE : x \notin dom ℰ) by (exact (@notin_union_r2 x L (dom ℰ) Hx)).
      assert (Hdisj' : forall y, y \in dom (E & x ~ i) -> y \notin dom ℰ).
      { eapply disj_push; [exact Hdisj|exact HxE]. }
      assert (Hvs' : forall y, y \in dom ℰ -> y \notin vs \u \{x}).
      { intros y Hy Hyin. rewrite in_union in Hyin.
        destruct Hyin as [Hyvs|Hyx].
        - exact (Hvs y Hy Hyvs).
        - rewrite in_singleton in Hyx. subst y. exact (HxE Hy). }
      specialize (IHbody x HxL (E & x ~ i)
                    (eq_sym (@concat_assoc init_typ D E (x ~ i))) Hdisj' Hvs').
      rewrite concat_assoc in IHbody. exact IHbody.
  - (* init_llit *)
    intros L Gamma Delta vs l u T i c IHl i0 IHbody E Heq Hdisj Hvs. subst Delta.
    eapply init_llit with (L := L \u dom ℰ).
    + apply IHl; [reflexivity|exact Hdisj].
    + intros x Hx.
      assert (HxL : x \notin L) by (eapply notin_union_r1; exact Hx).
      assert (HxE : x \notin dom ℰ) by (exact (@notin_union_r2 x L (dom ℰ) Hx)).
      assert (Hdisj' : forall y, y \in dom (E & x ~ committed) -> y \notin dom ℰ).
      { eapply disj_push; [exact Hdisj|exact HxE]. }
      specialize (IHbody x HxL (E & x ~ committed)
                    (eq_sym (@concat_assoc init_typ D E (x ~ committed))) Hdisj' Hvs).
      rewrite concat_assoc in IHbody. exact IHbody.
  - (* well_inits_nil *)
    intros Gamma Delta vs E Heq Hdisj Hvs. subst Delta.
    apply well_inits_nil.
  - (* well_inits_cons *)
    intros Gamma Delta vs x i avs is' i0 IHx iav IHa E Heq Hdisj Hvs. subst Delta.
    eapply well_inits_cons.
    + apply IHx; [reflexivity|exact Hdisj|exact Hvs].
    + apply IHa; [reflexivity|exact Hdisj|exact Hvs].
Qed.

End Mut.


Unset Implicit Arguments.

Lemma free_sub_heap_binds_free : forall (ℰ:eff_ctx) (Sigma:heap) (D:init_ctx) (y:var),
  free_sub_heap ℰ Sigma D -> y \in dom ℰ -> binds y free D.
Proof.
  intros ℰ Sigma D y H Hy.
  destruct (dom_binds_exists Hy) as [effs Hb].
  unfold free_sub_heap in H.
  destruct (H y effs Hb) as [_ [itm [HbS Hfi]]].
  inversion Hfi; subst.
  match goal with Hfd : free_heap_defs D ℰ y ?hds |- _ =>
    unfold free_heap_defs in Hfd; destruct Hfd as [Hfree _]; exact Hfree end.
Qed.

Lemma inert_inits_commit_ctx : forall (D:init_ctx) (ℰ:eff_ctx),
  inert_inits D -> inert_inits (D & commit_ctx ℰ).
Proof.
  intros D ℰ H y i Hy. unfold inert_inits in *.
  destruct (classic (y \in dom ℰ)) as [Hin|Hout].
  - right.
    assert (Hc : binds y committed (D & commit_ctx ℰ))
      by (apply LibEnv.binds_concat_right; apply binds_commit_ctx_in; exact Hin).
    pose proof (@LibEnv.binds_functional init_typ y i committed (D & commit_ctx ℰ) Hy Hc) as E.
    exact E.
  - assert (HyD : binds y i D).
    { eapply LibEnv.binds_concat_left_inv; [exact Hy|].
      rewrite commit_ctx_dom. exact Hout. }
    destruct (H y i HyD) as [E0|E0]; [left|right]; exact E0.
Qed.

Lemma init_var_free_mem : forall (D:init_ctx) (vs:vars) (x:var),
  init_var D vs x free -> x \in vs.
Proof.
  intros D vs x H. remember free as i eqn:Heq. induction H; subst.
  - discriminate Heq.
  - exact H.
  - discriminate Heq.
  - assert (Hi : i' = free) by (inversion H0; reflexivity). apply IHinit_var. exact Hi.
Qed.

Lemma init_typing_var_free_mem : forall (G:ctx) (D:init_ctx) (vs:vars) (x:var),
  G ⸴ D ⸴ vs ⊢i trm_var (avar_f x) ∶ free -> x \in vs.
Proof.
  intros G D vs x H. inversion H; subst; try discriminate.
  - eapply init_var_free_mem. exact H4.
Qed.



(* ==== StrHeap ==== *)


(* ------------------------------------------------------------------ *)
(* 1. Helpers for all_notin / list_dom_union                           *)
(* ------------------------------------------------------------------ *)

Lemma all_notin_head : forall (ℰ E:eff_ctx) (Es:list eff_ctx),
  all_notin (dom ℰ) (list_dom_union (E :: Es)) ->
  all_notin (dom ℰ) (dom E).
Proof.
  intros ℰ E Es H x Hx Hy.
  apply (H x Hx). simpl. rewrite in_union. left. exact Hy.
Qed.

Lemma all_notin_tail : forall (ℰ E:eff_ctx) (Es:list eff_ctx),
  all_notin (dom ℰ) (list_dom_union (E :: Es)) ->
  all_notin (dom ℰ) (list_dom_union Es).
Proof.
  intros ℰ E Es H x Hx Hy.
  apply (H x Hx). simpl. rewrite in_union. right. exact Hy.
Qed.

(* Symmetric form of disjointness: a member of the second set avoids the
   first one. *)
Lemma notin_dom_of_all_notin : forall (ℰ E:eff_ctx),
  all_notin (dom ℰ) (dom E) ->
  forall x, x \in dom E -> x \notin dom ℰ.
Proof.
  intros ℰ E H x Hx HxE. exact (H x HxE Hx).
Qed.

(* ------------------------------------------------------------------ *)
(* Convenient strengthen wrappers around StrMut's projections           *)
(* ------------------------------------------------------------------ *)

(* init typing, pushed extra context E, source context D & E *)
Lemma init_trm_strengthen_push : forall (D:init_ctx) (ℰ:eff_ctx),
  (forall x, x \in dom ℰ -> binds x free D) ->
  forall (G:ctx) (E:init_ctx) (vs:vars) (t:trm) (i:init_typ),
  G ⸴ (D & E) ⸴ vs ⊢i t ∶ i ->
  (forall y, y \in dom E -> y # ℰ) ->
  (forall y, y \in dom ℰ -> y \notin vs) ->
  G ⸴ ((D & commit_ctx ℰ) & E) ⸴ vs ⊢i t ∶ i.
Proof.
  intros D ℰ Hfree G E vs t i H Hdisj Hvs.
  exact (proj1 (proj2 (proj2 (proj2 (@init_commit_strengthen_mut D ℰ Hfree))))
           G (D & E) vs t i H E eq_refl Hdisj Hvs).
Qed.

(* init typing, no extra context (E = empty), source context D *)
Lemma init_trm_strengthen_empty : forall (D:init_ctx) (ℰ:eff_ctx),
  (forall x, x \in dom ℰ -> binds x free D) ->
  forall (G:ctx) (vs:vars) (t:trm) (i:init_typ),
  G ⸴ D ⸴ vs ⊢i t ∶ i ->
  (forall y, y \in dom ℰ -> y \notin vs) ->
  G ⸴ (D & commit_ctx ℰ) ⸴ vs ⊢i t ∶ i.
Proof.
  intros D ℰ Hfree G vs t i H Hvs.
  assert (Hdisj : forall y, y \in dom (empty:init_ctx) -> y # ℰ).
  { intros y Hy. rewrite dom_empty in Hy. rewrite in_empty in Hy. destruct Hy. }
  pose proof (proj1 (proj2 (proj2 (proj2 (@init_commit_strengthen_mut D ℰ Hfree))))
                G D vs t i H (empty:init_ctx) (eq_sym (concat_empty_r D))
                Hdisj Hvs) as Hres.
  rewrite concat_empty_r in Hres. exact Hres.
Qed.

(* commit typing of literals, no extra context, source context D *)
Lemma commit_lit_strengthen_empty : forall (D:init_ctx) (ℰ:eff_ctx),
  (forall x, x \in dom ℰ -> binds x free D) ->
  forall (G:ctx) (l:lit),
  G ⸴ D ⊢c l ->
  G ⸴ (D & commit_ctx ℰ) ⊢c l.
Proof.
  intros D ℰ Hfree G l H.
  assert (Hdisj : forall y, y \in dom (empty:init_ctx) -> y # ℰ).
  { intros y Hy. rewrite dom_empty in Hy. rewrite in_empty in Hy. destruct Hy. }
  pose proof (proj1 (proj2 (proj2 (@init_commit_strengthen_mut D ℰ Hfree)))
                G D l H (empty:init_ctx) (eq_sym (concat_empty_r D)) Hdisj) as Hres.
  rewrite concat_empty_r in Hres. exact Hres.
Qed.

(* commit typing of terms, no extra context, source context D *)
Lemma commit_trm_strengthen_empty : forall (D:init_ctx) (ℰ:eff_ctx),
  (forall x, x \in dom ℰ -> binds x free D) ->
  forall (G:ctx) (t:trm),
  G ⸴ D ⊢c t ->
  G ⸴ (D & commit_ctx ℰ) ⊢c t.
Proof.
  intros D ℰ Hfree G t H.
  assert (Hdisj : forall y, y \in dom (empty:init_ctx) -> y # ℰ).
  { intros y Hy. rewrite dom_empty in Hy. rewrite in_empty in Hy. destruct Hy. }
  pose proof (proj1 (@init_commit_strengthen_mut D ℰ Hfree)
                G D t H (empty:init_ctx) (eq_sym (concat_empty_r D)) Hdisj) as Hres.
  rewrite concat_empty_r in Hres. exact Hres.
Qed.

(* ------------------------------------------------------------------ *)
(* 2. Strengthening of stack typing                                    *)
(* ------------------------------------------------------------------ *)

Lemma ty_stack_strengthen : forall (G:ctx) (D:init_ctx) (ℰ:eff_ctx)
  (Es:list eff_ctx) (Fs:stack) (T:typ) (i:init_typ) (effs:list effects) (U:typ),
  (forall x, x \in dom ℰ -> binds x free D) ->
  all_notin (dom ℰ) (list_dom_union Es) ->
  ty_stack G D Es Fs T i effs U ->
  ty_stack G (D & commit_ctx ℰ) Es Fs T i effs U.
Proof.
  intros G D ℰ Es Fs T i effs U Hfree Hnotin H.
  revert Hfree Hnotin.
  induction H; intros Hfree Hnotin.
  - (* ty_stack_nil *)
    apply ty_stack_nil. exact H.
  - (* ty_stack_let *)
    eapply ty_stack_let with (L := L \u dom ℰ).
    + apply IHty_stack; [exact Hfree|exact Hnotin].
    + intros y Hy. apply H0. apply (notin_union_r1 Hy).
    + intros y Hy.
      assert (HyL : y \notin L) by (apply (notin_union_r1 Hy)).
      assert (HyE : y \notin dom ℰ) by (apply (notin_union_r2 Hy)).
      assert (Hdisj : forall z, z \in dom (y ~ i) -> z # ℰ).
      { intros z Hz. rewrite dom_single in Hz. rewrite in_singleton in Hz.
        subst z. exact HyE. }
      assert (Hhead : all_notin (dom ℰ) (dom ℰ0)) by (exact (all_notin_head ℰ ℰ0 ℰs Hnotin)).
      assert (Hvs : forall z, z \in dom ℰ -> z \notin (dom ℰ0 \u \{y})).
      { intros z Hz. apply notin_union_l.
        - exact (Hhead z Hz).
        - intro K. rewrite in_singleton in K. subst z. exact (HyE Hz). }
      refine (init_trm_strengthen_push Delta ℰ Hfree (Gamma & y ~ S) (y ~ i) (dom ℰ0 \u \{y}) (open y t) i' (H1 y HyL) Hdisj Hvs).
    + intros y Hy. apply H2. apply (notin_union_r1 Hy).
  - (* ty_stack_ret_free *)
    eapply ty_stack_ret_free with (T := T).
    + apply IHty_stack; [exact Hfree|exact Hnotin].
    + exact H0.
    + assert (Hvs : forall z, z \in dom ℰ -> z \notin dom ℰ0).
      { exact (all_notin_head ℰ ℰ0 ℰs Hnotin). }
      refine (init_trm_strengthen_empty Delta ℰ Hfree Gamma (dom ℰ0) (trm_var (avar_f x)) free H1 Hvs).
  - (* ty_stack_ret_committed *)
    eapply ty_stack_ret_committed with (T := T).
    + apply IHty_stack; [exact Hfree|exact (all_notin_tail ℰ ℰ0 ℰs Hnotin)].
    + exact H0.
    + assert (Hvs : forall z, z \in dom ℰ -> z \notin dom ℰ0).
      { exact (all_notin_head ℰ ℰ0 ℰs Hnotin). }
      refine (init_trm_strengthen_empty Delta ℰ Hfree Gamma (dom ℰ0) (trm_var (avar_f x)) free H1 Hvs).
Qed.

(* ------------------------------------------------------------------ *)
(* 3. Strengthening of free_sub_heap                                   *)
(* ------------------------------------------------------------------ *)

Lemma free_sub_heap_strengthen : forall (ℰ0:eff_ctx) (Sigma:heap)
  (D:init_ctx) (ℰ:eff_ctx),
  (forall x, x \in dom ℰ -> binds x free D) ->
  all_notin (dom ℰ) (dom ℰ0) ->
  free_sub_heap ℰ0 Sigma D ->
  free_sub_heap ℰ0 Sigma (D & commit_ctx ℰ).
Proof.
  intros ℰ0 Sigma D ℰ Hfree Hnot Hfs.
  unfold free_sub_heap in *.
  intros x effs Hb.
  destruct (Hfs x effs Hb) as [Hfresh [itm [HbSigma Hitem]]].
  split; [exact Hfresh|].
  exists itm. split; [exact HbSigma|].
  inversion Hitem; subst.
  apply free_heap_obj.
  match goal with Hf : free_heap_defs D ℰ0 x ?hds |- _ =>
    unfold free_heap_defs in Hf; destruct Hf as [Hby [Hbe Hwp]] end.
  unfold free_heap_defs. split; [|split].
  - (* binds x free (D & commit_ctx ℰ) *)
    assert (Hx0 : x \in dom ℰ0) by (eapply binds_in_dom; eexact Hbe).
    assert (HxE : x \notin dom ℰ) by (exact (notin_dom_of_all_notin ℰ ℰ0 Hnot x Hx0)).
    eapply binds_concat_left; [exact Hby|].
    rewrite commit_ctx_dom. exact HxE.
  - exact Hbe.
  - intros z Hz. destruct (Hwp z Hz) as [Hcomm | [HzE Hzfree]].
    + left. destruct (classic (z \in dom ℰ)) as [HzE|HzE].
      * exfalso. pose proof (Hfree z HzE) as Hf.
        pose proof (@binds_functional init_typ z committed free D Hcomm Hf) as E0.
        discriminate E0.
      * eapply binds_concat_left; [exact Hcomm|].
        rewrite commit_ctx_dom. exact HzE.
    + right. split; [exact HzE|].
      assert (Hz0 : z \notin dom ℰ) by (exact (notin_dom_of_all_notin ℰ ℰ0 Hnot z HzE)).
      eapply binds_concat_left; [exact Hzfree|].
      rewrite commit_ctx_dom. exact Hz0.
Qed.

(* ------------------------------------------------------------------ *)
(* 4. Committed status of well-pointed variables                       *)
(* ------------------------------------------------------------------ *)

Lemma well_pointed_committed_str : forall (D:init_ctx) (ℰ:eff_ctx) (y:var),
  (forall x, x \in dom ℰ -> binds x free D) ->
  well_pointed D ℰ y ->
  binds y committed (D & commit_ctx ℰ).
Proof.
  intros D ℰ y Hfree Hwp.
  destruct Hwp as [Hcomm | [HyE HfreeD]].
  - destruct (classic (y \in dom ℰ)) as [HyE|HyE].
    + exfalso. pose proof (Hfree y HyE) as Hf.
      pose proof (@binds_functional init_typ y committed free D Hcomm Hf) as E0.
      discriminate E0.
    + eapply binds_concat_left; [exact Hcomm|].
      rewrite commit_ctx_dom. exact HyE.
  - apply binds_concat_right. apply (binds_commit_ctx_in ℰ y HyE).
Qed.

(* ------------------------------------------------------------------ *)
(* 5. Committed heap definitions                                       *)
(*                                                                     *)
(* NOTE: the statement "free_heap_defs -> committed_heap_defs" is      *)
(* FALSE as formulated, because free_heap_defs permits heap_def_trm    *)
(* entries carrying None, while committed_heap_def has no constructor  *)
(* for those (a machine-checked counterexample is given at the end of  *)
(* this file).  The provable version therefore carries the explicit    *)
(* no-None invariant [all_some_hds].                                   *)
(* ------------------------------------------------------------------ *)

Fixpoint all_some_hds (hds:heap_defs) : Prop :=
  match hds with
  | nil => True
  | heap_def_typ _ _ :: hds => all_some_hds hds
  | heap_def_trm _ (Some _) :: hds => all_some_hds hds
  | heap_def_trm _ None :: _ => False
  end.

Lemma free_heap_defs_committed_some : forall (D:init_ctx) (ℰ:eff_ctx)
  (y:var) (hds:heap_defs),
  (forall x, x \in dom ℰ -> binds x free D) ->
  all_some_hds hds ->
  free_heap_defs D ℰ y hds ->
  committed_heap_defs (D & commit_ctx ℰ) hds.
Proof.
  intros D ℰ y hds. induction hds as [| hd hds IH].
  - intros Hfree Hsome Hfd. apply committed_heap_defs_nil.
  - intros Hfree Hsome Hfd. destruct hd as [A T| a o].
    + (* heap_def_typ *)
      simpl in Hsome.
      apply committed_heap_defs_cons.
      * apply IH; [exact Hfree|exact Hsome|exact Hfd].
      * apply committed_heap_def_typ.
    + destruct o as [z|].
      * (* heap_def_trm a (Some z) *)
        simpl in Hsome.
        apply committed_heap_defs_cons.
        -- apply IH; [exact Hfree|exact Hsome|].
           unfold free_heap_defs in Hfd |- *.
           destruct Hfd as [Hby [Hbe Hwp]]. split; [exact Hby|split].
           ++ exact Hbe.
           ++ intros w Hw. apply Hwp. simpl. rewrite in_union. right. exact Hw.
        -- apply committed_heap_def_trm.
           apply well_pointed_committed_str; [exact Hfree|].
           unfold free_heap_defs in Hfd. destruct Hfd as [_ [_ Hwp]].
           apply Hwp. simpl. rewrite in_union. left. rewrite in_singleton. reflexivity.
      * (* heap_def_trm a None : excluded by all_some_hds *)
        simpl in Hsome. destruct Hsome.
Qed.

(* Transfer of committed heap definitions to D & commit_ctx ℰ. *)
Lemma committed_heap_def_transfer_str : forall (D:init_ctx) (ℰ:eff_ctx)
  (hd:heap_def),
  (forall x, x \in dom ℰ -> binds x free D) ->
  committed_heap_def D hd ->
  committed_heap_def (D & commit_ctx ℰ) hd.
Proof.
  intros D ℰ hd Hfree H. inversion H; subst.
  - apply committed_heap_def_typ.
  - apply committed_heap_def_trm.
    match goal with Hb : binds ?x committed D |- _ =>
      destruct (classic (x \in dom ℰ)) as [Hx|Hx];
      [ exfalso; pose proof (Hfree x Hx) as Hf;
        pose proof (@binds_functional init_typ x committed free D Hb Hf) as E0;
        discriminate E0
      | eapply binds_concat_left; [exact Hb|];
        rewrite commit_ctx_dom; exact Hx ]
    end.
Qed.

Lemma committed_heap_defs_str : forall (D:init_ctx) (ℰ:eff_ctx)
  (hds:heap_defs),
  (forall x, x \in dom ℰ -> binds x free D) ->
  committed_heap_defs D hds ->
  committed_heap_defs (D & commit_ctx ℰ) hds.
Proof.
  intros D ℰ hds Hfree H. induction H.
  - apply committed_heap_defs_nil.
  - apply committed_heap_defs_cons.
    + apply IHcommitted_heap_defs. exact Hfree.
    + apply committed_heap_def_transfer_str; [exact Hfree|exact H0].
Qed.

Lemma committed_heap_item_str : forall (G:ctx) (D:init_ctx) (ℰ:eff_ctx)
  (itm:item),
  (forall x, x \in dom ℰ -> binds x free D) ->
  committed_heap_item G D itm ->
  committed_heap_item G (D & commit_ctx ℰ) itm.
Proof.
  intros G D ℰ itm Hfree H. inversion H; subst.
  - apply committed_heap_lit.
    refine (commit_lit_strengthen_empty D ℰ Hfree G l H0).
  - apply committed_heap_obj.
    apply committed_heap_defs_str; [exact Hfree|exact H0].
Qed.

(* ------------------------------------------------------------------ *)
(* 6. Strengthening of well_committed_heap                             *)
(*                                                                     *)
(* Again, the unrestricted statement is false for the same reason;     *)
(* the provable version assumes that the heap items of all variables   *)
(* of dom ℰ have no None entries.                                      *)
(* ------------------------------------------------------------------ *)

Lemma well_committed_heap_strengthen_some : forall (G:ctx) (D:init_ctx)
  (Sigma:heap) (ℰ:eff_ctx),
  (forall x, x \in dom ℰ -> binds x free D) ->
  free_sub_heap ℰ Sigma D ->
  (forall z T hds, z \in dom ℰ -> binds z (item_obj T hds) Sigma -> all_some_hds hds) ->
  well_committed_heap G D Sigma ->
  well_committed_heap G (D & commit_ctx ℰ) Sigma.
Proof.
  intros G D Sigma ℰ Hfree Hfs Hsome [HG [HD Hitem]].
  assert (Hsub : dom ℰ \c dom D).
  { intros x Hx. eapply binds_in_dom. apply Hfree. exact Hx. }
  assert (Hunion : dom D \u dom ℰ = dom D).
  { apply fset_extens.
    - intros x Hx. rewrite in_union in Hx. destruct Hx as [Hx|Hx].
      + exact Hx.
      + exact (Hsub x Hx).
    - intros x Hx. rewrite in_union. left. exact Hx. }
  assert (Hdom : dom (D & commit_ctx ℰ) = dom D).
  { rewrite dom_concat. rewrite commit_ctx_dom. exact Hunion. }
  split; [|split].
  - rewrite HG. symmetry. exact Hdom.
  - rewrite Hdom. exact HD.
  - intros z itm Hz Hzi.
    destruct (classic (z \in dom ℰ)) as [HzE|HzE].
    + (* z \in dom ℰ : its heap item comes from free_sub_heap *)
      assert (Hzfree : binds z free D) by (apply Hfree; exact HzE).
      destruct (dom_binds_exists HzE) as [effs Heffs].
      unfold free_sub_heap in Hfs.
      destruct (Hfs z effs Heffs) as [_ [itm0 [HzSigma Hfi]]].
      assert (Heqitm : itm0 = itm) by (eapply binds_functional; [exact HzSigma|exact Hzi]).
      subst itm0.
      inversion Hfi; subst.
      apply committed_heap_obj.
      refine (free_heap_defs_committed_some D ℰ z hds Hfree _ H).
      eapply Hsome; [exact HzE| eexact Hzi].
    + (* z \notin dom ℰ : transfer the old committed item *)
      assert (HzD : binds z committed D).
      { eapply binds_concat_left_inv; [exact Hz|].
        rewrite commit_ctx_dom. exact HzE. }
      apply (committed_heap_item_str G D ℰ itm Hfree).
      apply (Hitem z itm HzD Hzi).
Qed.

(* ------------------------------------------------------------------ *)
(* 7. Strengthening of free_sub_heaps                                  *)
(* ------------------------------------------------------------------ *)

Lemma free_sub_heaps_strengthen_some : forall (G:ctx) (D:init_ctx)
  (ℰ:eff_ctx) (Sigma:heap) (Es:list eff_ctx),
  (forall x, x \in dom ℰ -> binds x free D) ->
  free_sub_heap ℰ Sigma D ->
  (forall z T hds, z \in dom ℰ -> binds z (item_obj T hds) Sigma -> all_some_hds hds) ->
  all_notin (dom ℰ) (list_dom_union Es) ->
  free_sub_heaps G D Sigma Es ->
  free_sub_heaps G (D & commit_ctx ℰ) Sigma Es.
Proof.
  intros G D ℰ Sigma Es Hfree Hfs Hsome Hnot H.
  revert Hnot.
  induction H; intros Hnot.
  - (* nil *)
    apply free_sub_heaps_nil.
    eapply well_committed_heap_strengthen_some;
      [exact Hfree|exact Hfs|exact Hsome|exact H].
  - (* cons *)
    apply free_sub_heaps_cons.
    + exact H.
    + eapply free_sub_heap_strengthen.
      * exact Hfree.
      * exact (all_notin_head ℰ ℰ0 ℰs Hnot).
      * exact H0.
    + apply IHfree_sub_heaps.
      * exact Hfree.
      * exact Hfs.
      * exact Hsome.
      * exact (all_notin_tail ℰ ℰ0 ℰs Hnot).
Qed.

(* ------------------------------------------------------------------ *)
(* Machine-checked counterexample showing why the unrestricted        *)
(* statements of items 5-7 cannot hold: free_heap_defs accepts         *)
(* [heap_def_trm a None], while committed_heap_def has no such         *)
(* constructor.                                                        *)
(* ------------------------------------------------------------------ *)

Lemma none_hd_not_committed : forall (D:init_ctx) (a:trm_label),
  ~ committed_heap_def D (heap_def_trm a None).
Proof. intros D a H. inversion H. Qed.

Lemma none_hds_not_committed : forall (D:init_ctx) (a:trm_label),
  ~ committed_heap_defs D (heap_def_trm a None :: nil).
Proof.
  intros D a H. inversion H; subst.
  match goal with Hc : committed_heap_def _ (heap_def_trm _ None) |- _ =>
    exact (none_hd_not_committed _ _ Hc) end.
Qed.

Lemma free_heap_defs_none_counterexample : forall (y:var) (a:trm_label) (T:typ),
  free_heap_defs ((empty:init_ctx) & y ~ free)
                ((empty:eff_ctx) & y ~ ((y,a)::nil)) y
                (heap_def_trm a None :: nil) /\
  ~ committed_heap_defs
      (((empty:init_ctx) & y ~ free) &
        commit_ctx ((empty:eff_ctx) & y ~ ((y,a)::nil)))
      (heap_def_trm a None :: nil).
Proof.
  intros y a T. split.
  - unfold free_heap_defs. split; [|split].
    + apply binds_push_eq.
    + simpl. apply binds_push_eq.
    + intros x Hx. simpl in Hx. rewrite in_empty in Hx. destruct Hx.
  - apply none_hds_not_committed.
Qed.

(* The exact statement of item 5 is refutable: instantiating the
   universally quantified hypothesis at the counterexample above yields
   a contradiction. *)
Lemma free_heap_defs_committed_refuted : forall (y:var) (a:trm_label) (T:typ),
  ~ (forall (D:init_ctx) (ℰ:eff_ctx) (y0:var) (hds:heap_defs),
        (forall x, x \in dom ℰ -> binds x free D) ->
        free_heap_defs D ℰ y0 hds ->
        committed_heap_defs (D & commit_ctx ℰ) hds).
Proof.
  intros y a T Hex.
  destruct (free_heap_defs_none_counterexample y a T) as [Hfd Hn].
  apply Hn.
  apply (Hex ((empty:init_ctx) & y ~ free)
             ((empty:eff_ctx) & y ~ ((y,a)::nil)) y
             (heap_def_trm a None :: nil)).
  - intros x Hx.
    rewrite dom_concat in Hx. rewrite dom_empty in Hx.
    rewrite union_empty_l in Hx. rewrite dom_single in Hx.
    rewrite in_singleton in Hx. subst x. apply binds_push_eq.
  - exact Hfd.
Qed.

(* The exact statement of item 6 is refutable as well: take a heap that
   binds y to an object with a None heap definition, and an effect
   context binding y.  The hypotheses all hold, but after committing the
   effect context y becomes committed and the item would have to be a
   committed heap item, which is impossible. *)
Lemma well_committed_heap_strengthen_refuted :
  forall (y:var) (a:trm_label) (T:typ),
  ~ (forall (G:ctx) (D:init_ctx) (Sigma:heap) (ℰ:eff_ctx),
        (forall x, x \in dom ℰ -> binds x free D) ->
        free_sub_heap ℰ Sigma D ->
        well_committed_heap G D Sigma ->
        well_committed_heap G (D & commit_ctx ℰ) Sigma).
Proof.
  intros y a T Hex.
  destruct (free_heap_defs_none_counterexample y a T) as [Hfd Hnc].
  set (D0 := (empty:init_ctx) & y ~ free).
  set (E0 := (empty:eff_ctx) & y ~ ((y,a)::nil)).
  set (S0 := (empty:heap) & y ~ item_obj T (heap_def_trm a None :: nil)).
  set (G0 := (empty:ctx) & y ~ T).
  assert (Hfree0 : forall x, x \in dom E0 -> binds x free D0).
  { intros x Hx. unfold E0 in Hx. unfold D0.
    rewrite dom_concat in Hx. rewrite dom_empty in Hx.
    rewrite union_empty_l in Hx. rewrite dom_single in Hx.
    rewrite in_singleton in Hx. subst x. apply binds_push_eq. }
  assert (Hfs0 : free_sub_heap E0 S0 D0).
  { unfold free_sub_heap. intros x effs Hb.
    unfold E0 in Hb.
    apply binds_push_inv in Hb.
    destruct Hb as [[Hxy Heffs]|[Hne Hbe]].
    - subst x. subst effs. split.
      + intros y0 a0 Hy0. rewrite from_list_cons in Hy0.
        rewrite in_union in Hy0. destruct Hy0 as [Hy0|Hy0].
        * rewrite in_singleton in Hy0. inversion Hy0. subst. reflexivity.
        * rewrite from_list_nil in Hy0. rewrite in_empty in Hy0. destruct Hy0.
      + exists (item_obj T (heap_def_trm a None :: nil)). split.
        * unfold S0. apply binds_push_eq.
        * apply free_heap_obj. exact Hfd.
    - destruct (binds_empty_inv Hbe). }
  assert (Hwc0 : well_committed_heap G0 D0 S0).
  { split; [|split].
    - unfold G0, D0. repeat rewrite dom_concat. repeat rewrite dom_empty.
      repeat rewrite union_empty_l. repeat rewrite dom_single. reflexivity.
    - unfold D0, S0. repeat rewrite dom_concat. repeat rewrite dom_empty.
      repeat rewrite union_empty_l. repeat rewrite dom_single. reflexivity.
    - intros x itm Hc _. unfold D0 in Hc.
      apply binds_push_inv in Hc.
      destruct Hc as [[Hxy Hcv]|[Hne Hc0]].
      + subst x. discriminate Hcv.
      + destruct (binds_empty_inv Hc0). }
  assert (Hbad : ~ well_committed_heap G0 (D0 & commit_ctx E0) S0).
  { intro Hwc. destruct Hwc as [_ [_ Hitem]].
    assert (Hcy : binds y committed (D0 & commit_ctx E0)).
    { apply binds_concat_right. apply binds_commit_ctx_in.
      unfold E0. rewrite dom_concat, dom_empty, union_empty_l, dom_single.
      rewrite in_singleton. reflexivity. }
    assert (Hys : binds y (item_obj T (heap_def_trm a None :: nil)) S0).
    { unfold S0. apply binds_push_eq. }
    pose proof (Hitem y (item_obj T (heap_def_trm a None :: nil)) Hcy Hys) as Hci.
    inversion Hci; subst.
    match goal with Hcd : committed_heap_defs _ (heap_def_trm a None :: nil) |- _ =>
      exact (none_hds_not_committed _ _ Hcd) end. }
  exact (Hbad (Hex G0 D0 S0 E0 Hfree0 Hfs0 Hwc0)).
Qed.

(* Concrete failure of well-committedness after committing: the heap
   binds y to an object whose definitions contain a None entry, and the
   committed context binds y.  This is the core of the refutations of
   items 6 and 7. *)
Lemma none_item_not_well_committed : forall (y:var) (a:trm_label) (T:typ),
  ~ well_committed_heap ((empty:ctx) & y ~ T)
      (((empty:init_ctx) & y ~ free) &
        commit_ctx ((empty:eff_ctx) & y ~ ((y,a)::nil)))
      ((empty:heap) & y ~ item_obj T (heap_def_trm a None :: nil)).
Proof.
  intros y a T Hwc. destruct Hwc as [_ [_ Hitem]].
  assert (Hcy : binds y committed
      (((empty:init_ctx) & y ~ free) &
        commit_ctx ((empty:eff_ctx) & y ~ ((y,a)::nil)))).
  { apply binds_concat_right. apply binds_commit_ctx_in.
    rewrite dom_concat, dom_empty, union_empty_l, dom_single.
    rewrite in_singleton. reflexivity. }
  assert (Hys : binds y (item_obj T (heap_def_trm a None :: nil))
      ((empty:heap) & y ~ item_obj T (heap_def_trm a None :: nil))).
  { apply binds_push_eq. }
  pose proof (Hitem y _ Hcy Hys) as Hci.
  inversion Hci; subst.
  match goal with Hcd : committed_heap_defs _ (heap_def_trm a None :: nil) |- _ =>
    exact (none_hds_not_committed _ _ Hcd) end.
Qed.

(* The exact statement of item 7 is refutable: take Es = [empty] and the
   same heap as above.  Every hypothesis holds, but the conclusion
   contains free_sub_heaps ... nil, hence well_committed_heap at the
   committed context, which is impossible. *)
Lemma free_sub_heaps_strengthen_refuted :
  forall (y:var) (a:trm_label) (T:typ),
  ~ (forall (G:ctx) (D:init_ctx) (ℰ:eff_ctx) (Sigma:heap) (Es:list eff_ctx),
        (forall x, x \in dom ℰ -> binds x free D) ->
        free_sub_heap ℰ Sigma D ->
        all_notin (dom ℰ) (list_dom_union Es) ->
        free_sub_heaps G D Sigma Es ->
        free_sub_heaps G (D & commit_ctx ℰ) Sigma Es).
Proof.
  intros y a T Hex.
  destruct (free_heap_defs_none_counterexample y a T) as [Hfd Hnc].
  set (D0 := (empty:init_ctx) & y ~ free).
  set (E0 := (empty:eff_ctx) & y ~ ((y,a)::nil)).
  set (S0 := (empty:heap) & y ~ item_obj T (heap_def_trm a None :: nil)).
  set (G0 := (empty:ctx) & y ~ T).
  assert (Hfree0 : forall x, x \in dom E0 -> binds x free D0).
  { intros x Hx. unfold E0 in Hx. unfold D0.
    rewrite dom_concat in Hx. rewrite dom_empty in Hx.
    rewrite union_empty_l in Hx. rewrite dom_single in Hx.
    rewrite in_singleton in Hx. subst x. apply binds_push_eq. }
  assert (Hfs0 : free_sub_heap E0 S0 D0).
  { unfold free_sub_heap. intros x effs Hb.
    unfold E0 in Hb.
    apply binds_push_inv in Hb.
    destruct Hb as [[Hxy Heffs]|[Hne Hbe]].
    - subst x. subst effs. split.
      + intros y0 a0 Hy0. rewrite from_list_cons in Hy0.
        rewrite in_union in Hy0. destruct Hy0 as [Hy0|Hy0].
        * rewrite in_singleton in Hy0. inversion Hy0. subst. reflexivity.
        * rewrite from_list_nil in Hy0. rewrite in_empty in Hy0. destruct Hy0.
      + exists (item_obj T (heap_def_trm a None :: nil)). split.
        * unfold S0. apply binds_push_eq.
        * apply free_heap_obj. exact Hfd.
    - destruct (binds_empty_inv Hbe). }
  assert (Hwc0 : well_committed_heap G0 D0 S0).
  { split; [|split].
    - unfold G0, D0. repeat rewrite dom_concat. repeat rewrite dom_empty.
      repeat rewrite union_empty_l. repeat rewrite dom_single. reflexivity.
    - unfold D0, S0. repeat rewrite dom_concat. repeat rewrite dom_empty.
      repeat rewrite union_empty_l. repeat rewrite dom_single. reflexivity.
    - intros x itm Hc _. unfold D0 in Hc.
      apply binds_push_inv in Hc.
      destruct Hc as [[Hxy Hcv]|[Hne Hc0]].
      + subst x. discriminate Hcv.
      + destruct (binds_empty_inv Hc0). }
  assert (Hnot0 : all_notin (dom E0)
            (list_dom_union ((empty:eff_ctx)::nil))).
  { intros x Hx Hy. simpl in Hy. rewrite dom_empty in Hy.
    rewrite union_empty_l in Hy. rewrite in_empty in Hy. destruct Hy. }
  assert (Hfsh0 : free_sub_heaps G0 D0 S0 ((empty:eff_ctx)::nil)).
  { apply free_sub_heaps_cons.
    - intros x Hx _. rewrite dom_empty in Hx. rewrite in_empty in Hx. destruct Hx.
    - unfold free_sub_heap. intros x effs Hb. destruct (binds_empty_inv Hb).
    - apply free_sub_heaps_nil. exact Hwc0. }
  assert (Hbad : ~ free_sub_heaps G0 (D0 & commit_ctx E0) S0
                     ((empty:eff_ctx)::nil)).
  { intro H. inversion H; subst.
    match goal with Ht : free_sub_heaps _ _ _ nil |- _ =>
      inversion Ht; subst;
      match goal with Hwc : well_committed_heap ?G ?D ?S |- _ =>
        exact (none_item_not_well_committed y a T Hwc) end
    end. }
  exact (Hbad (Hex G0 D0 E0 S0 ((empty:eff_ctx)::nil)
                    Hfree0 Hfs0 Hnot0 Hfsh0)).
Qed.

(* ==== RH ==== *)


Lemma all_some_hds_of_effs_empty : forall (z:var) (hds:heap_defs),
  (forall e, e \in from_list (heap_defs_effs z hds) -> False) ->
  all_some_hds hds.
Proof.
  intros z hds. induction hds as [|d hds IH]; intros Hempty.
  - simpl. exact I.
  - destruct d as [a T|a o].
    + simpl. apply IH. intros e He. apply (Hempty e). simpl. exact He.
    + destruct o as [y|].
      * simpl. apply IH. intros e He. apply (Hempty e). simpl. exact He.
      * exfalso. apply (Hempty (z,a)).
        simpl. rewrite from_list_cons. rewrite in_union. left.
        rewrite in_singleton. reflexivity.
Qed.

Lemma nil_eff_all_some : forall (ℰ:eff_ctx) (Sigma:heap) (D:init_ctx),
  free_sub_heap ℰ Sigma D ->
  eff_ctx_corr_one ℰ nil ->
  forall (z:var) (T:typ) (hds:heap_defs),
    z \in dom ℰ -> binds z (item_obj T hds) Sigma -> all_some_hds hds.
Proof.
  intros ℰ Sigma D Hfs Hone z T hds Hz Hiz.
  destruct (dom_binds_exists Hz) as [effs Hb].
  unfold free_sub_heap in Hfs.
  destruct (Hfs z effs Hb) as [_ [itm [HbS Hfi]]].
  assert (Heqitm : itm = item_obj T hds)
    by (eapply (@LibEnv.binds_functional item z itm (item_obj T hds) Sigma); eassumption).
  subst itm.
  inversion Hfi; subst.
  match goal with Hfd : free_heap_defs D ℰ z ?hds0 |- _ =>
    unfold free_heap_defs in Hfd; destruct Hfd as [_ [Hbe _]];
    assert (Heffs : heap_defs_effs z hds0 = effs)
      by (eapply (@LibEnv.binds_functional effects z (heap_defs_effs z hds0) effs ℰ); eassumption)
  end.
  assert (Hnil : forall e, e \in from_list (heap_defs_effs z hds) -> False).
  { intros e He. rewrite Heffs in He.
    exact (in_empty_inv (Hone z effs Hb e He)). }
  eapply all_some_hds_of_effs_empty. exact Hnil.
Qed.

(* ==== RetC ==== *)


Lemma free_sub_heaps_cons_inv3 : forall (G:ctx) (D:init_ctx) (Sigma:heap)
  (ℰ:eff_ctx) (ℰs:list eff_ctx),
  free_sub_heaps G D Sigma (ℰ :: ℰs) ->
  all_notin (dom ℰ) (list_dom_union ℰs) /\
  free_sub_heap ℰ Sigma D /\
  free_sub_heaps G D Sigma ℰs.
Proof.
  intros G D Sigma ℰ ℰs H. inversion H; subst.
  split; [|split]; eassumption.
Qed.

Lemma ty_config_red_return : forall (G:ctx) (D:init_ctx) (Es:list eff_ctx)
  (effss:list effects) (Fs:stack) (Sigma:heap) (U:typ) (t:trm) (y x:var),
  ty_config G D Es effss (trm_var (avar_f y) ; (frame_ret x :: Fs)%list ; Sigma) U ->
  exists G' D' Es' effss',
    ty_config (G & G') D' Es' effss' (trm_var (avar_f x) ; Fs ; Sigma) U.
Proof.
  intros G D Es effss Fs Sigma U t y x Hcfg.
  destruct (@ty_config_inv_s G D Es effss (trm_var (avar_f y))
              ((frame_ret x :: Fs)%list) Sigma U Hcfg) as
    (ℰ & ℰs & Ts & ii & effsH & effs' & effss0 &
     HeqEs & HeqEffs & Hinert & Hinits & Hhc & Hfs & Hstack & Hty & Heff & Hinit & Hcorr).
  destruct (@ty_stack_ret_inv G D (ℰ :: ℰs) x Fs Ts ii (effsH :: effss0) U Hstack) as
    [ (ℰ0 & ℰs0 & T & effs0 & effssF &
        HeqEs0 & HeqEffs0 & Hstack_free & HxT & Hxinit)
    | (ℰ0 & ℰs0 & T & effssC &
        HeqEs0 & HeqEffs0 & Hstack_tail & HxT & Hxinit) ].
  - (* free branch *)
    inversion HeqEs0; subst.
    injection HeqEffs0 as HeffH Heffss. subst effsH effss0.
    assert (Heffnil : effs' = nil) by (eapply eff_trm_var_nil; exact Heff).
    subst effs'.
    cbn in Hcorr.
    eapply (@ty_config_pop_ret_free G D ℰ0 ℰs0 Fs Sigma U T x effs0 effssF);
      eassumption.
  - (* committed branch *)
    inversion HeqEs0; subst.
    injection HeqEffs0 as HeffH Heffss. subst effsH effss0.
    assert (Heffnil : effs' = nil) by (eapply eff_trm_var_nil; exact Heff).
    subst effs'.
    cbn in Hcorr.
    assert (Hcorr_cons : eff_ctx_corr (ℰ0 :: ℰs0) (nil :: effssC)) by exact Hcorr.
    destruct (@eff_ctx_corr_cons_inv ℰ0 ℰs0 nil effssC Hcorr_cons) as [Hcorr_tail Hone].
    destruct (@free_sub_heaps_cons_inv3 G D Sigma ℰ0 ℰs0 Hfs) as [Hnot [Hfree_sub Hfs_tail]].
    assert (Hfreeℰ0 : forall z, z \in dom ℰ0 -> binds z free D).
    { intros z Hz. exact (@free_sub_heap_binds_free ℰ0 Sigma D z Hfree_sub Hz). }
    assert (Hallsome : forall z T0 hds, z \in dom ℰ0 ->
                        binds z (item_obj T0 hds) Sigma -> all_some_hds hds).
    { intros z T0 hds Hz Hb. exact (@nil_eff_all_some ℰ0 Sigma D Hfree_sub Hone z T0 hds Hz Hb). }
    assert (Hstack' : ty_stack G (D & commit_ctx ℰ0) ℰs0 Fs T committed effssC U).
    { eapply (@ty_stack_strengthen G D ℰ0 ℰs0 Fs T committed effssC U);
        [exact Hfreeℰ0|exact Hnot|exact Hstack_tail]. }
    assert (Hfs' : free_sub_heaps G (D & commit_ctx ℰ0) Sigma ℰs0).
    { eapply (@free_sub_heaps_strengthen_some G D ℰ0 Sigma ℰs0);
        [exact Hfreeℰ0|exact Hfree_sub|exact Hallsome|exact Hnot|exact Hfs_tail]. }
    assert (Hinits' : inert_inits (D & commit_ctx ℰ0))
      by (exact (@inert_inits_commit_ctx D ℰ0 Hinits)).
    assert (Hxmem : x \in dom ℰ0) by (exact (@init_typing_var_free_mem G D (dom ℰ0) x Hxinit)).
    assert (Hxb : binds x committed (D & commit_ctx ℰ0))
      by (apply LibEnv.binds_concat_right; exact (@binds_commit_ctx_in ℰ0 x Hxmem)).
    destruct ℰs0 as [|ℰ1 ℰs'].
    + inversion Hstack'.
    + destruct effssC as [|effs1 effss'].
      * inversion Hstack'.
      * exists (empty:ctx), (D & commit_ctx ℰ0), (ℰ1 :: ℰs'), (effs1 :: effss').
        rewrite concat_empty_r.
        eapply (@ty_config_c G (D & commit_ctx ℰ0) Sigma ℰ1 ℰs' Fs
                  (trm_var (avar_f x)) T committed U nil effs1 effss').
        -- exact Hinert.
        -- exact Hinits'.
        -- exact Hhc.
        -- exact Hfs'.
        -- exact Hstack'.
        -- exact HxT.
        -- apply eff_ignore.
        -- eapply init_var_binds. apply init_var_commit. exact Hxb.
        -- exact Hcorr_tail.
Qed.


(* ==== AsnAux ==== *)


Lemma get_labeld_list_some_in : forall (A:Set) `{LabelOf A} (l:label) (ds:list A) (d:A),
  get_labeld_list l ds = Some d -> List.In d ds.
Proof.
  intros A LA l ds. induction ds as [|a ds IH]; intros d H.
  - simpl in H. discriminate H.
  - simpl in H. destruct (classic (label_of a = l)) as [E|NE].
    + rewrite (If_l (P:=label_of a = l) _ _ E) in H.
      injection H as Heq. subst d. apply List.in_eq.
    + rewrite (If_r (P:=label_of a = l) _ _ NE) in H.
      apply List.in_cons. eapply IH; exact H.
Qed.

Lemma committed_heap_defs_in : forall (D:init_ctx) (hds:heap_defs) (d:heap_def),
  committed_heap_defs D hds -> List.In d hds -> committed_heap_def D d.
Proof.
  intros D hds d H. induction H; intros Hin.
  - inversion Hin.
  - destruct Hin as [Heq|Hin].
    + subst d. assumption.
    + eapply IHcommitted_heap_defs; exact Hin.
Qed.

Lemma committed_heap_def_trm_some_binds : forall (D:init_ctx) (a:trm_label) (y:var),
  committed_heap_def D (heap_def_trm a (Some y)) -> binds y committed D.
Proof. intros D a y H. inversion H; subst; assumption. Qed.

Lemma committed_heap_def_trm_none_false : forall (D:init_ctx) (a:trm_label),
  committed_heap_def D (heap_def_trm a None) -> False.
Proof. intros D a H. inversion H. Qed.

(* Effects: an effect-context inclusion survives dropping a prefix whose
   variables are not bound in the effect context. *)
Lemma eff_ctx_corr_one_suffix : forall (E:eff_ctx) (Sigma:heap) (D:init_ctx)
  (effs' effs:effects),
  eff_ctx_corr_one E (effs' ++ effs) ->
  free_sub_heap E Sigma D ->
  (forall e, List.In e effs' -> fst e \notin dom E) ->
  eff_ctx_corr_one E effs.
Proof.
  intros E Sigma D effs' effs Hcorr Hfree Hnodom x effs0 Hb e He.
  destruct e as [z l].
  assert (Hin : (z,l) \in from_list (effs' ++ effs)).
  { exact (Hcorr x effs0 Hb (z,l) He). }
  rewrite from_list_app in Hin. rewrite in_union in Hin.
  destruct Hin as [Hin|Hin].
  - exfalso.
    pose proof (proj1 (Hfree x effs0 Hb) z l He) as Hz.
    assert (Hdom : x \in dom E) by (eapply binds_in_dom; exact Hb).
    apply (Hnodom (z,l) (proj1 (@in_from_list effect (z,l) effs') Hin)). rewrite Hz. exact Hdom.
  - exact Hin.
Qed.

(* Typing inversion for selection. *)
Lemma ty_sel_inv_gen : forall (G:ctx) (t:trm) (T:typ),
  G ⊢ t ∶ T ->
  forall (x:var) (a:trm_label), t = trm_sel (avar_f x) a ->
  exists S T0, G ⊢ trm_var (avar_f x) ∶ typ_rcd (dec_trm a S T0) /\ G ⊢ T0 <: T.
Proof.
  intros G t T H.
  induction H; intros x0 a0 Heq; try discriminate Heq.
  - injection Heq as Hx Ha. subst x0 a0.
    exists S, T. split; [assumption|apply subtyp_refl].
  - subst.
    destruct (IHty_trm x0 a0 eq_refl) as [S [T1 [Hx Hsub]]].
    exists S, T1. split; [exact Hx|]. eapply subtyp_trans; [exact Hsub|exact H0].
Qed.

Lemma ty_sel_inv : forall (G:ctx) (x:var) (a:trm_label) (T:typ),
  G ⊢ trm_sel (avar_f x) a ∶ T ->
  exists S T0, G ⊢ trm_var (avar_f x) ∶ typ_rcd (dec_trm a S T0) /\ G ⊢ T0 <: T.
Proof. intros. eapply ty_sel_inv_gen; [exact H|reflexivity]. Qed.

(* Typing inversion for assignment. *)
Lemma ty_asn_inv_gen : forall (G:ctx) (t:trm) (T:typ),
  G ⊢ t ∶ T ->
  forall (x y:var) (a:trm_label), t = trm_asn (avar_f x) a (avar_f y) ->
  exists S T0, G ⊢ trm_var (avar_f x) ∶ typ_rcd (dec_trm a S T0) /\
               G ⊢ trm_var (avar_f y) ∶ S /\ G ⊢ T0 <: T.
Proof.
  intros G t T H.
  induction H; intros x0 y0 a0 Heq; try discriminate Heq.
  - injection Heq as Hx Ha Hy. subst x0 y0 a0.
    exists S, T. split; [exact H|]. split; [exact H0|apply subtyp_refl].
  - subst.
    destruct (IHty_trm x0 y0 a0 eq_refl) as [S [T1 [Hx [Hy Hsub]]]].
    exists S, T1. split; [exact Hx|]. split; [exact Hy|].
    eapply subtyp_trans; [exact Hsub|exact H0].
Qed.

Lemma ty_asn_inv : forall (G:ctx) (x:var) (a:trm_label) (y:var) (T:typ),
  G ⊢ trm_asn (avar_f x) a (avar_f y) ∶ T ->
  exists S T0, G ⊢ trm_var (avar_f x) ∶ typ_rcd (dec_trm a S T0) /\
               G ⊢ trm_var (avar_f y) ∶ S /\ G ⊢ T0 <: T.
Proof. intros. eapply ty_asn_inv_gen; [exact H|reflexivity]. Qed.

(* Initialization status facts for the reduction of selection/assignment. *)
Lemma init_typing_sel_committed : forall (G:ctx) (D:init_ctx) (vs:vars)
  (x:var) (a:trm_label) (i:init_typ),
  G ⸴ D ⸴ vs ⊢i trm_sel (avar_f x) a ∶ i ->
  i = committed /\ binds x committed D.
Proof.
  intros G D vs x a i H.
  destruct (@init_sel_commit G D vs x a i H) as [Heq Hc]. subst i.
  split; [reflexivity|].
  eapply commit_sel_binds; exact Hc.
Qed.

Lemma init_typing_asn_status : forall (G:ctx) (D:init_ctx) (vs:vars)
  (x y:var) (a:trm_label) (i:init_typ),
  G ⸴ D ⸴ vs ⊢i trm_asn (avar_f x) a (avar_f y) ∶ i ->
  (i = committed /\ binds y committed D) \/
  (i = free /\ y \in vs).
Proof.
  intros G D vs x y a i H.
  change (well_init G D vs (trm_asn (avar_f x) a (avar_f y)) i) in H.
  inversion H; subst.
  - (* init_commit *) left. split; [reflexivity|].
    inversion H0; subst. eapply commit_var_binds. eassumption.
  - (* init_fld_asn_ac *) left. split; [reflexivity|].
    eapply init_typing_var_committed_binds; exact H8.
  - (* init_fld_asn_ff *) right. split; [reflexivity|].
    eapply @init_typing_var_free_mem with (G:=G) (D:=D) (vs:=vs) (x:=y).
    exact H8.
Qed.


(* ==== HeapAsn ==== *)


Lemma committed_heap_defs_update : forall (D:init_ctx) (hds hds':heap_defs) (a:trm_label) (y:var),
  committed_heap_defs D hds ->
  defs_update hds a y hds' ->
  binds y committed D ->
  committed_heap_defs D hds'.
Proof.
  intros D hds hds' a y Hc Hu Hy. revert Hc. induction Hu; intros Hc.
  - inversion Hc; subst.
    eapply (@committed_heap_defs_cons D (heap_def_trm a (Some x)) hds).
    + exact H2.
    + eapply committed_heap_def_trm. change (binds x committed D). exact Hy.
  - inversion Hc; subst.
    eapply (@committed_heap_defs_cons D d hds').
    + eapply IHHu; [exact Hy|exact H2].
    + exact H3.
Qed.

Lemma free_sub_heap_asn_update : forall (E:eff_ctx) (Sigma Sigma':heap) (D:init_ctx)
  (x:var) (a:trm_label) (y:var),
  free_sub_heap E Sigma D ->
  heap_update Sigma x a y Sigma' ->
  binds x committed D ->
  free_sub_heap E Sigma' D.
Proof.
  intros E Sigma Sigma' D x a y Hfree Hup Hxcomm.
  destruct Hup as (T & hds & hds' & S1 & S2 & Heq & Hfresh & Hdu & Heq').
  subst Sigma Sigma'.
  intros z effs Hb. destruct (Hfree z effs Hb) as [Hsame Hrest].
  destruct Hrest as [itm [Hbinds Hitem]].
  assert (Hne : z <> x).
  { intro E0. subst z.
    inversion Hitem; subst.
    match goal with
    | Hf : free_heap_defs D E x ?hds0 |- _ =>
      destruct Hf as [Hbzfree _]
    end.
    pose proof (@LibEnv.binds_functional init_typ x free committed D Hbzfree Hxcomm) as Heqfc.
    discriminate Heqfc. }
  split.
  - exact Hsame.
  - exists itm. split.
    + eapply (@binds_replace item S1 S2 x z
                 (item_obj T hds) (item_obj T hds') itm);
      [exact Hne|exact Hbinds].
    + exact Hitem.
Qed.

Lemma well_committed_heap_asn_update : forall (G:ctx) (D:init_ctx)
  (Sigma Sigma':heap) (x:var) (a:trm_label) (y:var),
  well_committed_heap G D Sigma ->
  heap_update Sigma x a y Sigma' ->
  binds x committed D ->
  binds y committed D ->
  well_committed_heap G D Sigma'.
Proof.
  intros G D Sigma Sigma' x a y Hwc Hup Hxcomm Hycomm.
  destruct Hwc as [HdomG [HdomD Hitem]].
  destruct Hup as (T & hds & hds' & S1 & S2 & Heq & Hfresh & Hdu & Heq').
  subst Sigma Sigma'.
  split; [exact HdomG|]. split.
  - rewrite HdomD. rewrite !LibEnv.dom_concat, !LibEnv.dom_single. reflexivity.
  - intros z itm Hzcomm Hbinds.
    destruct (classic (z = x)) as [->|Hne].
    + assert (Hcanon : binds x (item_obj T hds')
                      (S1 & x ~ item_obj T hds' & S2)).
      { eapply LibEnv.binds_concat_left.
        - apply LibEnv.binds_push_eq.
        - exact Hfresh. }
      assert (Heqitm : itm = item_obj T hds')
        by (eapply LibEnv.binds_functional; [exact Hbinds|exact Hcanon]).
      subst itm.
      assert (Hcanon_old : binds x (item_obj T hds)
                          (S1 & x ~ item_obj T hds & S2)).
      { eapply LibEnv.binds_concat_left.
        - apply LibEnv.binds_push_eq.
        - exact Hfresh. }
      pose proof (Hitem x (item_obj T hds) Hzcomm Hcanon_old) as Hci.
      pose proof (committed_heap_item_obj_inv Hci) as Hcdefs.
      eapply committed_heap_obj. eapply committed_heap_defs_update; eassumption.
    + assert (Hbinds_old : binds z itm (S1 & x ~ item_obj T hds & S2)).
      { eapply (@binds_replace item S1 S2 x z
                   (item_obj T hds') (item_obj T hds) itm);
          [exact Hne|exact Hbinds]. }
      exact (Hitem z itm Hzcomm Hbinds_old).
Qed.

Lemma free_sub_heaps_asn_update : forall (G:ctx) (D:init_ctx) (Sigma Sigma':heap)
  (Es:list eff_ctx) (x:var) (a:trm_label) (y:var),
  free_sub_heaps G D Sigma Es ->
  heap_update Sigma x a y Sigma' ->
  binds x committed D ->
  binds y committed D ->
  free_sub_heaps G D Sigma' Es.
Proof.
  intros G D Sigma Sigma' Es x a y Hfs Hup Hxcomm Hycomm.
  induction Hfs.
  - eapply free_sub_heaps_nil.
    eapply well_committed_heap_asn_update; eassumption.
  - eapply free_sub_heaps_cons.
    + exact H.
    + eapply free_sub_heap_asn_update; eassumption.
    + eapply IHHfs; assumption.
Qed.

(* ==== SelPrep ==== *)


Lemma eff_trm_sel_nil : forall (x:var) (a:trm_label) (effs:effects),
  ⊢e trm_sel (avar_f x) a ∶ effs -> effs = nil.
Proof.
  intros x a effs H. inversion H; subst; reflexivity.
Qed.

Lemma ty_heap_def_trm_some_inv : forall (G:ctx) (a:trm_label) (y:var) (D:dec),
  G ⊢ heap_def_trm a (Some y) ∶d D ->
  exists Tf, D = dec_trm a Tf Tf /\ G ⊢ trm_var (avar_f y) ∶ Tf.
Proof.
  intros G a y D H. change (ty_heap_def G (heap_def_trm a (Some y)) D) in H.
  inversion H; subst. eexists. split; [reflexivity|assumption].
Qed.

Lemma labels_has_heap_in : forall (hds:heap_defs) (d:heap_def),
  labels_has hds d -> List.In d hds.
Proof.
  intros hds d H. unfold labels_has in H.
  eapply (@get_labeld_list_some_in heap_def HeapDefLabelOf (label_of d) hds d).
  exact H.
Qed.

Lemma heap_def_typing_rh : forall (G:ctx) (hds:heap_defs) (T:typ)
  (a:trm_label) (y:var),
  G ⊢ hds ∶ T ->
  List.In (heap_def_trm a (Some y)) hds ->
  exists Tf, record_has T (dec_trm a Tf Tf) /\ G ⊢ trm_var (avar_f y) ∶ Tf.
Proof.
  intros G hds T a y Hhds Hin.
  destruct (@ty_heap_defs_correspond G hds T Hhds) as (ls & Hrt & Hfwd & Hbwd).
  destruct (Hfwd (heap_def_trm a (Some y)) Hin) as [D [Hrh Hdty]].
  destruct (@ty_heap_def_trm_some_inv G a y D Hdty) as [Tf [Heq Hy]].
  subst D. exists Tf. split; assumption.
Qed.

Lemma heap_def_typing_rh_any : forall (G:ctx) (hds:heap_defs) (T:typ)
  (a:trm_label) (y:var),
  G ⊢ hds ∶ T ->
  List.In (heap_def_trm a (Some y)) hds ->
  exists Tf, record_has T (dec_trm a Tf Tf) /\ G ⊢ trm_var (avar_f y) ∶ Tf.
Proof. exact heap_def_typing_rh. Qed.

(* ==== LitInv ==== *)


Lemma ty_lit_all_inv : forall (G:ctx) (l:lit) (S U:typ),
  G ⊢ l ∶ typ_all S U ->
  exists T t, l = lit_fun T t.
Proof.
  intros G l S U H. change (ty_lit G l (typ_all S U)) in H.
  inversion H; subst; try discriminate; eexists _, _; reflexivity.
Qed.

Lemma ty_lit_con_inv : forall (G:ctx) (l:lit) (Ts:typs) (is':inits) (T:typ),
  G ⊢ l ∶ typ_con Ts is' T ->
  exists ds t, l = lit_con Ts is' T ds t.
Proof.
  intros G l Ts is' T H. change (ty_lit G l (typ_con Ts is' T)) in H.
  inversion H; subst; try discriminate; eexists _, _; reflexivity.
Qed.

Lemma ty_lit_fun_shape : forall (G:ctx) (l:lit) (S U:typ),
  G ⊢ l ∶ typ_all S U ->
  exists T t, l = lit_fun T t.
Proof. exact ty_lit_all_inv. Qed.

Lemma ty_avars_length : forall (G:ctx) (avs:avars) (Ts:typs),
  G ⊢ avs :: Ts -> List.length avs = length_s Ts.
Proof.
  intros G avs Ts H. change (ty_avars G avs Ts) in H.
  induction H; simpl.
  - reflexivity.
  - f_equal. exact IHty_avars.
Qed.

Lemma ty_avars_types_of_avars : forall (G:ctx) (xs:list var) (avs:avars) (Ts:typs),
  vars_of_avars xs avs ->
  G ⊢ avs :: Ts ->
  exists Ts', Ts = Ts'.
Proof. intros. eexists. reflexivity. Qed.

Lemma ty_lit_shape : forall (G:ctx) (l:lit) (T:typ),
  G ⊢ l ∶ T ->
  (exists S U, T = typ_all S U) \/
  (exists Ts is' X, T = typ_con Ts is' X).
Proof.
  intros G l T H. change (ty_lit G l T) in H. induction H.
  - left. eexists _, _. reflexivity.
  - right. eexists _, _, _. reflexivity.
Qed.


Require Import Lia.
(* ==== LitInv additions ==== *)
Lemma heap_correspond_lit_shape : forall (G:ctx) (Sigma:heap) (x:var) (l:lit),
  heap_correspond G Sigma ->
  binds x (item_lit l) Sigma ->
  (exists T S U, binds x T G /\ T = typ_all S U) \/
  (exists T Ts is' X, binds x T G /\ T = typ_con Ts is' X).
Proof.
  intros G Sigma x l Hhc Hb.
  destruct (@heap_correspond_lit G Sigma x l Hhc Hb) as [T [HbG Hty]].
  destruct (@ty_lit_shape G l T Hty) as [[S [U Heq]]|[Ts [is' [X Heq]]]].
  - left. exists T, S, U. split; [exact HbG|exact Heq].
  - right. exists T, Ts, is', X. split; [exact HbG|exact Heq].
Qed.

Lemma vars_of_avars_det : forall (xs ys:list var) (avs:avars),
  vars_of_avars xs avs -> vars_of_avars ys avs -> xs = ys.
Proof.
  intros xs ys avs H. revert ys. induction H; intros ys H2.
  - inversion H2. reflexivity.
  - inversion H2; subst. f_equal. eapply IHvars_of_avars. eassumption.
Qed.

Lemma ty_lit_fun_type_inv : forall (G:ctx) (Tf:typ) (tf:trm) (V:typ),
  G ⊢ lit_fun Tf tf ∶ V ->
  exists Uf, V = typ_all Tf Uf.
Proof.
  intros G Tf tf V H. change (ty_lit G (lit_fun Tf tf) V) in H.
  inversion H; subst; eexists; reflexivity.
Qed.

Lemma ty_lit_con_type_inv : forall (G:ctx) (Ts:typs) (is':inits) (T:typ)
  (ds:defs) (t:trm) (V:typ),
  G ⊢ lit_con Ts is' T ds t ∶ V ->
  V = typ_con Ts is' T.
Proof.
  intros G Ts is' T ds t V H. change (ty_lit G (lit_con Ts is' T ds t) V) in H.
  inversion H; subst; reflexivity.
Qed.

(* ==== AppPrep ==== *)


Lemma subtyp_all_inst : forall (L:fset var) (G:ctx) (S2 U1 U2:typ) (z:var),
  (forall x, x \notin L -> G & x ~ S2 ⊢ open x U1 <: open x U2) ->
  G ⊢ trm_var (avar_f z) ∶ S2 ->
  G ⊢ open z U1 <: open z U2.
Proof.
  intros L G S2 U1 U2 z Hbody Hz.
  destruct (@var_fresh ((((((L \u fv_env G) \u fv U1) \u fv U2) \u fv S2) \u \{z}))) as [x Hx].
  pose proof (notin_union_r1 Hx) as Hx1.
  pose proof (notin_union_r1 Hx1) as Hx2.
  pose proof (notin_union_r1 Hx2) as Hx3.
  pose proof (notin_union_r1 Hx3) as Hx4.
  pose proof (notin_union_r1 Hx4) as Hx5.
  pose proof Hx5 as HxL.
  pose proof (notin_union_r2 Hx4) as HxG.
  pose proof (notin_union_r2 Hx3) as HxU1.
  pose proof (notin_union_r2 Hx2) as HxU2.
  pose proof (notin_union_r2 Hx1) as HxS2.
  pose proof (notin_union_r2 Hx1) as Hxz.
  assert (Hbodyx : G & x ~ S2 ⊢ open x U1 <: open x U2) by (apply Hbody; exact HxL).
  assert (Hbodyx' : G & x ~ S2 & empty ⊢ open x U1 <: open x U2)
    by (rewrite concat_empty_r; exact Hbodyx).
  assert (Hpre : G & subst_env x z empty ⊢ trm_var (avar_f z) ∶ subst_var x z S2).
  { rewrite (@fv_subst_typ S2 x z HxS2). rewrite map_empty. rewrite concat_empty_r. exact Hz. }
  assert (Hxempty : x # (empty:ctx)) by (rewrite (@dom_empty typ); apply notin_empty).
  pose proof (@subtyp_subst G empty x z S2 (open x U1) (open x U2)
                Hbodyx' Hxempty HxG Hpre) as Hsub.
  rewrite map_empty in Hsub. rewrite concat_empty_r in Hsub.
  rewrite <- (@subst_intro_typ U1 x z 0 HxU1) in Hsub.
  rewrite <- (@subst_intro_typ U2 x z 0 HxU2) in Hsub.
  exact Hsub.
Qed.

Lemma ty_app_inv_gen : forall (G:ctx) (t:trm) (T:typ),
  G ⊢ t ∶ T ->
  forall (f z:var), t = trm_app (avar_f f) (avar_f z) ->
  exists S U, G ⊢ trm_var (avar_f f) ∶ typ_all S U /\
              G ⊢ trm_var (avar_f z) ∶ S /\ G ⊢ open z U <: T.
Proof.
  intros G t T H. induction H; intros f0 z0 Heq; try discriminate Heq.
  - injection Heq as Hf Hz. subst f0 z0.
    exists S, T. split; [exact H|]. split; [exact H0|apply subtyp_refl].
  - subst.
    destruct (IHty_trm f0 z0 eq_refl) as [Sa [Ua [Hf [Hz Hsub]]]].
    exists Sa, Ua. split; [exact Hf|]. split; [exact Hz|].
    eapply subtyp_trans; [exact Hsub|exact H0].
Qed.

Lemma ty_app_inv : forall (G:ctx) (f z:var) (T:typ),
  G ⊢ trm_app (avar_f f) (avar_f z) ∶ T ->
  exists S U, G ⊢ trm_var (avar_f f) ∶ typ_all S U /\
              G ⊢ trm_var (avar_f z) ∶ S /\ G ⊢ open z U <: T.
Proof. intros. eapply ty_app_inv_gen; [exact H|reflexivity]. Qed.

Lemma ty_new_inv_gen : forall (G:ctx) (t:trm) (T:typ),
  G ⊢ t ∶ T ->
  forall (f:var) (avs:avars), t = trm_new (avar_f f) avs ->
  exists Ts is' X xs,
    G ⊢ trm_var (avar_f f) ∶ typ_con Ts is' X /\
    G ⊢ avs :: Ts /\ vars_of_avars xs avs /\
    G ⊢ typ_bnd (open_rec_vars 1 xs X) <: T.
Proof.
  intros G t T H. induction H; intros f0 avs0 Heq; try discriminate Heq.
  - injection Heq as Hf Havs. subst f0 avs0.
    exists Ts, is', T, xs. split; [exact H|]. split; [exact H0|]. split; [exact H1|apply subtyp_refl].
  - subst.
    destruct (IHty_trm f0 avs0 eq_refl) as [Ts [is' [X [xs [Hf [Havs [Hvars Hsub]]]]]]].
    exists Ts, is', X, xs. split; [exact Hf|]. split; [exact Havs|]. split; [exact Hvars|].
    eapply subtyp_trans; [exact Hsub|exact H0].
Qed.

Lemma ty_new_inv : forall (G:ctx) (f:var) (avs:avars) (T:typ),
  G ⊢ trm_new (avar_f f) avs ∶ T ->
  exists Ts is' X xs,
    G ⊢ trm_var (avar_f f) ∶ typ_con Ts is' X /\
    G ⊢ avs :: Ts /\ vars_of_avars xs avs /\
    G ⊢ typ_bnd (open_rec_vars 1 xs X) <: T.
Proof. intros. eapply ty_new_inv_gen; [exact H|reflexivity]. Qed.

Lemma eff_trm_app_nil : forall (f z:var) (effs:effects),
  ⊢e trm_app (avar_f f) (avar_f z) ∶ effs -> effs = nil.
Proof. intros. inversion H; subst; reflexivity. Qed.

Lemma eff_trm_new_nil : forall (f:var) (avs:avars) (effs:effects),
  ⊢e trm_new (avar_f f) avs ∶ effs -> effs = nil.
Proof. intros. inversion H; subst; reflexivity. Qed.

Lemma ty_lit_fun_body : forall (G:ctx) (Tf Uf:typ) (tf:trm),
  G ⊢ lit_fun Tf tf ∶ typ_all Tf Uf ->
  exists L, forall x, x \notin L -> G & x ~ Tf ⊢ open x tf ∶ open x Uf.
Proof.
  intros G Tf Uf tf H. change (ty_lit G (lit_fun Tf tf) (typ_all Tf Uf)) in H.
  inversion H; subst. eexists. eassumption.
Qed.

Lemma commit_lit_fun_body : forall (G:ctx) (D:init_ctx) (Tf:typ) (tf:trm),
  G ⸴ D ⊢c lit_fun Tf tf ->
  exists L, forall x, x \notin L -> G & x ~ Tf ⸴ D & x ~ committed ⊢c open x tf.
Proof.
  intros G D Tf tf H. change (well_committed_lit G D (lit_fun Tf tf)) in H.
  inversion H; subst. eexists. eassumption.
Qed.

(* ==== HeapSplit ==== *)


Lemma binds_split_fresh : forall (A:Type) (E:env A) (x:var) (v:A),
  binds x v E -> exists E1 E2, E = E1 & x ~ v & E2 /\ x # E2.
Proof.
  intros A E. remember (LibList.length E) as n eqn:Hn.
  revert E Hn. induction n as [|n IH]; intros E Hn x v Hb.
  - destruct (env_case E) as [Heq|(y & w & E' & Heq)].
    + rewrite Heq in Hb. unfold binds in Hb. rewrite LibEnv.get_empty in Hb.
      discriminate Hb.
    + rewrite Heq in Hn. rewrite concat_def in Hn. rewrite single_def in Hn.
      rewrite LibList.length_app in Hn.
      rewrite LibList.length_cons in Hn. rewrite LibList.length_nil in Hn.
      cbn in Hn. exfalso. lia.
  - destruct (env_case E) as [Heq|(y & w & E' & Heq)].
    + rewrite Heq in Hb. unfold binds in Hb. rewrite LibEnv.get_empty in Hb.
      discriminate Hb.
    + rewrite Heq in Hb. rewrite Heq in Hn.
      destruct (LibEnv.binds_push_inv Hb) as [[Hx Hv]|Hneq].
      * subst x v. exists E', (empty:env A). split.
        -- rewrite Heq. rewrite concat_empty_r. reflexivity.
        -- rewrite (@dom_empty A). apply notin_empty.
      * destruct Hneq as [Hne HbE'].
        assert (Hlen : LibList.length E' = n).
        { rewrite concat_def in Hn. rewrite single_def in Hn.
          rewrite LibList.length_app in Hn.
          rewrite LibList.length_cons in Hn. rewrite LibList.length_nil in Hn.
          cbn in Hn. lia. }
        destruct (IH E' (eq_sym Hlen) x v HbE') as [E1 [E2 [HeqE Hfresh]]].
        exists E1, (E2 & y ~ w). split.
        -- rewrite Heq. rewrite HeqE. rewrite <- concat_assoc. reflexivity.
        -- intro Hz. rewrite dom_push in Hz. rewrite in_union in Hz.
           destruct Hz as [Hz|Hz].
           ++ rewrite in_singleton in Hz. exact (Hne Hz).
           ++ exact (Hfresh Hz).
Qed.

(* ==== NoBavar ==== *)


Lemma ty_var_b_false_gen : forall (G:ctx) (t:trm) (T:typ),
  G ⊢ t ∶ T ->
  forall (n:nat), t = trm_var (avar_b n) -> False.
Proof.
  intros G t T H. induction H; intros n E; try discriminate E.
  - eapply IHty_trm. exact E.
Qed.

Lemma ty_sel_b_false_gen : forall (G:ctx) (t:trm) (T:typ),
  G ⊢ t ∶ T ->
  forall (n:nat) (a:trm_label), t = trm_sel (avar_b n) a -> False.
Proof.
  intros G t T H. induction H; intros n0 a0 E; try discriminate E.
  - eapply IHty_trm. exact E.
Qed.

Lemma ty_asn_bx_false_gen : forall (G:ctx) (t:trm) (T:typ),
  G ⊢ t ∶ T ->
  forall (n:nat) (a:trm_label) (z:avar), t = trm_asn (avar_b n) a z -> False.
Proof.
  intros G t T H. induction H; intros n0 a0 z0 E; try discriminate E.
  - eapply IHty_trm. exact E.
Qed.

Lemma ty_asn_bz_false_gen : forall (G:ctx) (t:trm) (T:typ),
  G ⊢ t ∶ T ->
  forall (x:avar) (a:trm_label) (n:nat), t = trm_asn x a (avar_b n) -> False.
Proof.
  intros G t T H. induction H; intros x0 a0 n0 E; try discriminate E.
  - eapply IHty_trm. exact E.
Qed.

Lemma ty_app_bf_false_gen : forall (G:ctx) (t:trm) (T:typ),
  G ⊢ t ∶ T ->
  forall (n:nat) (z:avar), t = trm_app (avar_b n) z -> False.
Proof.
  intros G t T H. induction H; intros n0 z0 E; try discriminate E.
  - eapply IHty_trm. exact E.
Qed.

Lemma ty_app_bz_false_gen : forall (G:ctx) (t:trm) (T:typ),
  G ⊢ t ∶ T ->
  forall (f:avar) (n:nat), t = trm_app f (avar_b n) -> False.
Proof.
  intros G t T H. induction H; intros f0 n0 E; try discriminate E.
  - eapply IHty_trm. exact E.
Qed.

Lemma ty_new_bf_false_gen : forall (G:ctx) (t:trm) (T:typ),
  G ⊢ t ∶ T ->
  forall (n:nat) (avs:avars), t = trm_new (avar_b n) avs -> False.
Proof.
  intros G t T H. induction H; intros n0 avs0 E; try discriminate E.
  - eapply IHty_trm. exact E.
Qed.

Corollary ty_var_b_false : forall (G:ctx) (n:nat) (T:typ),
  G ⊢ trm_var (avar_b n) ∶ T -> False.
Proof. intros. eapply ty_var_b_false_gen; [exact H|reflexivity]. Qed.

Corollary ty_sel_b_false : forall (G:ctx) (n:nat) (a:trm_label) (T:typ),
  G ⊢ trm_sel (avar_b n) a ∶ T -> False.
Proof. intros. eapply ty_sel_b_false_gen; [exact H|reflexivity]. Qed.

Corollary ty_asn_bx_false : forall (G:ctx) (n:nat) (a:trm_label) (z:avar) (T:typ),
  G ⊢ trm_asn (avar_b n) a z ∶ T -> False.
Proof. intros. eapply ty_asn_bx_false_gen; [exact H|reflexivity]. Qed.

Corollary ty_asn_bz_false : forall (G:ctx) (x:avar) (a:trm_label) (n:nat) (T:typ),
  G ⊢ trm_asn x a (avar_b n) ∶ T -> False.
Proof. intros. eapply ty_asn_bz_false_gen; [exact H|reflexivity]. Qed.

Corollary ty_app_bf_false : forall (G:ctx) (n:nat) (z:avar) (T:typ),
  G ⊢ trm_app (avar_b n) z ∶ T -> False.
Proof. intros. eapply ty_app_bf_false_gen; [exact H|reflexivity]. Qed.

Corollary ty_app_bz_false : forall (G:ctx) (f:avar) (n:nat) (T:typ),
  G ⊢ trm_app f (avar_b n) ∶ T -> False.
Proof. intros. eapply ty_app_bz_false_gen; [exact H|reflexivity]. Qed.

Corollary ty_new_bf_false : forall (G:ctx) (n:nat) (avs:avars) (T:typ),
  G ⊢ trm_new (avar_b n) avs ∶ T -> False.
Proof. intros. eapply ty_new_bf_false_gen; [exact H|reflexivity]. Qed.


(* ==== VarDom ==== *)


Lemma ty_var_dom_gen : forall (G:ctx) (t:trm) (T:typ),
  G ⊢ t ∶ T ->
  forall (x0:var), t = trm_var (avar_f x0) -> x0 \in dom G.
Proof.
  intros G t T H. induction H; intros x0 E; try discriminate E.
  - injection E as Hxy. subst.
    exact (@binds_in_dom typ G x0 T H).
  - eapply IHty_trm. exact E.
  - eapply IHty_trm. exact E.
  - eapply IHty_trm. exact E.
  - eapply IHty_trm. exact E.
Qed.

Lemma ty_var_dom : forall (G:ctx) (x:var) (T:typ),
  G ⊢ trm_var (avar_f x) ∶ T -> x \in dom G.
Proof. intros. eapply ty_var_dom_gen; [exact H|reflexivity]. Qed.

From Stdlib Require Import ClassicalDescription.
(* ==== AsnHelpers ==== *)

(* ------------------------------------------------------------------ *)
(* Basic initialization facts                                           *)
(* ------------------------------------------------------------------ *)

Lemma init_var_free_binds : forall (D:init_ctx) (vs:vars) (x:var),
  init_var D vs x free -> binds x free D.
Proof.
  intros D vs x H. remember free as i eqn:Heq. induction H; subst.
  - discriminate Heq.
  - exact H0.
  - discriminate Heq.
  - inversion H0; subst. apply IHinit_var. reflexivity.
Qed.

Lemma init_typing_var_free_binds : forall (G:ctx) (D:init_ctx) (vs:vars) (x:var),
  G ⸴ D ⸴ vs ⊢i trm_var (avar_f x) ∶ free -> binds x free D.
Proof.
  intros G D vs x H. change (well_init G D vs (trm_var (avar_f x)) free) in H.
  inversion H; subst; try discriminate.
  eapply init_var_free_binds. eassumption.
Qed.

Lemma init_typing_var_bind_mem : forall (G:ctx) (D:init_ctx) (vs:vars)
  (x:var) (i:init_typ),
  G ⸴ D ⸴ vs ⊢i trm_var (avar_f x) ∶ i ->
  binds x free D -> x \in vs.
Proof.
  intros G D vs x i H Hf.
  destruct (@init_typing_var_status G D vs x i H) as [i0 [Hb [Hsub Hcase]]].
  assert (Heq : i0 = free) by (eapply LibEnv.binds_functional; eassumption).
  subst i0.
  destruct Hcase as [Hin|Hc]; [exact Hin|].
  inversion Hc.
Qed.

Lemma free_sub_heaps_binds_free : forall (G:ctx) (D:init_ctx) (Sigma:heap)
  (Es:list eff_ctx) (E:eff_ctx),
  free_sub_heaps G D Sigma Es ->
  List.In E Es ->
  forall x, x \in dom E -> binds x free D.
Proof.
  intros G D Sigma Es. induction Es as [|E0 Es IH];
    intros E Hfs Hin x Hx.
  - inversion Hfs; subst. inversion Hin.
  - inversion Hfs as [|G0 D0 S0 E1 Es1 Hall Hfree Htail]; subst.
    destruct Hin as [->|Hin].
    + eapply free_sub_heap_binds_free; [exact Hfree|exact Hx].
    + eapply IH; [exact Htail|exact Hin|exact Hx].
Qed.

(* ------------------------------------------------------------------ *)
(* Environment / point-to helpers                                       *)
(* ------------------------------------------------------------------ *)

Lemma dom_push_in : forall (A:Type) (E:env A) (x:var) (v:A),
  x \in dom E -> dom (E & x ~ v) = dom E.
Proof.
  intros A E x v Hin. rewrite dom_push.
  apply fset_extens.
  - intros z Hz. rewrite in_union in Hz. destruct Hz as [Hz|Hz].
    + rewrite in_singleton in Hz. subst z. exact Hin.
    + exact Hz.
  - intros z Hz. rewrite in_union. right. exact Hz.
Qed.

Lemma well_pointed_dom_eq : forall (D:init_ctx) (E E':eff_ctx) (z:var),
  dom E' = dom E -> well_pointed D E z -> well_pointed D E' z.
Proof.
  intros D E E' z Heq H.
  destruct H as [Hc|[Hin Hf]].
  - left. exact Hc.
  - right. split.
    + rewrite Heq. exact Hin.
    + exact Hf.
Qed.

(* ------------------------------------------------------------------ *)
(* heap_defs_effs and defs_update                                       *)
(* ------------------------------------------------------------------ *)

Lemma heap_defs_effs_update_in : forall (hds hds':heap_defs)
  (a:trm_label) (y:var),
  defs_update hds a y hds' ->
  forall (x:var) (e:effect),
    List.In e (heap_defs_effs x hds') ->
    List.In e (heap_defs_effs x hds).
Proof.
  intros hds hds' a y H. induction H; intros z e Hin; simpl in *.
  - destruct o.
    + exact Hin.
    + right. exact Hin.
  - destruct d as [A T|m o]; simpl in *.
    + apply IHdefs_update. exact Hin.
    + destruct o.
      * apply IHdefs_update. exact Hin.
      * destruct Hin as [Heq|Hin].
        -- left. exact Heq.
        -- right. apply IHdefs_update. exact Hin.
Qed.

Lemma heap_defs_effs_in_inv : forall (x:var) (l:trm_label) (hds:heap_defs),
  List.In (x,l) (heap_defs_effs x hds) ->
  List.In (heap_def_trm l None) hds.
Proof.
  intros x l hds. induction hds as [|d hds IH]; simpl.
  - intro H. inversion H.
  - destruct d as [A T|m o]; simpl.
    + intro H. apply List.in_cons. apply IH. exact H.
    + destruct o.
      * intro H. apply List.in_cons. apply IH. exact H.
      * intro H. destruct H as [Heq|Hin].
        -- injection Heq as Hl. subst l. apply List.in_eq.
        -- apply List.in_cons. apply IH. exact Hin.
Qed.

Lemma defs_update_some_in : forall (hds hds':heap_defs)
  (a:trm_label) (y:var),
  defs_update hds a y hds' ->
  List.In (heap_def_trm a (Some y)) hds'.
Proof.
  intros hds hds' a y H. induction H.
  - apply List.in_eq.
  - apply List.in_cons. exact IHdefs_update.
Qed.

Lemma defs_update_not_none : forall (hds hds':heap_defs)
  (a:trm_label) (y:var),
  defs_update hds a y hds' ->
  (forall d1 d2, List.In d1 hds' -> List.In d2 hds' ->
    label_of d1 = label_of d2 -> d1 = d2) ->
  ~ List.In (heap_def_trm a None) hds'.
Proof.
  intros hds hds' a y Hup Huniq Hnone.
  assert (Hsome : List.In (heap_def_trm a (Some y)) hds')
    by (eapply defs_update_some_in; exact Hup).
  pose proof (Huniq _ _ Hsome Hnone eq_refl) as Heq.
  inversion Heq.
Qed.

Lemma heap_defs_points_to_update : forall (hds hds':heap_defs)
  (a:trm_label) (y:var),
  defs_update hds a y hds' ->
  forall z, z \in heap_defs_points_to hds' ->
    z = y \/ z \in heap_defs_points_to hds.
Proof.
  intros hds hds' a y H. induction H; intros z Hz; simpl in *.
  - destruct o as [z0|].
    + rewrite in_union in Hz. destruct Hz as [Hz|Hz].
      * left. rewrite in_singleton in Hz. exact Hz.
      * right. rewrite in_union. right. exact Hz.
    + rewrite in_union in Hz. destruct Hz as [Hz|Hz].
      * left. rewrite in_singleton in Hz. exact Hz.
      * right. exact Hz.
  - destruct d as [A T|m o]; simpl in *.
    + destruct (IHdefs_update z Hz) as [->|Hz2].
      * left. reflexivity.
      * right. exact Hz2.
    + destruct o as [z0|].
      * rewrite in_union in Hz. destruct Hz as [Hz|Hz].
        -- right. rewrite in_union. left. exact Hz.
        -- destruct (IHdefs_update z Hz) as [->|Hz2].
           ++ left. reflexivity.
           ++ right. rewrite in_union. right. exact Hz2.
      * destruct (IHdefs_update z Hz) as [->|Hz2].
        -- left. reflexivity.
        -- right. exact Hz2.
Qed.

(* ------------------------------------------------------------------ *)
(* Updating a free subheap                                             *)
(* ------------------------------------------------------------------ *)

Lemma free_sub_heap_update_notin : forall (E:eff_ctx) (D:init_ctx)
  (Sigma:heap) (x:var) (a:trm_label) (y:var) (UB:typ)
  (hds hds':heap_defs) (S1 S2:heap),
  free_sub_heap E Sigma D ->
  Sigma = S1 & x ~ item_obj UB hds & S2 ->
  x # S2 ->
  defs_update hds a y hds' ->
  x \notin dom E ->
  free_sub_heap E (S1 & x ~ item_obj UB hds' & S2) D.
Proof.
  intros E D Sigma x a y UB hds hds' S1 S2 Hfree Heq Hfresh Hdu HxE.
  subst Sigma. intros z effs Hz.
  destruct (Hfree z effs Hz) as [Hfr [itm [HbS Hfi]]].
  assert (Hne : z <> x).
  { intro Ez. subst z. eapply HxE. eapply binds_in_dom. exact Hz. }
  split; [exact Hfr|].
  exists itm. split.
  - eapply (@binds_replace item S1 S2 x z
               (item_obj UB hds) (item_obj UB hds') itm);
      [exact Hne|exact HbS].
  - exact Hfi.
Qed.

Lemma free_sub_heap_update_x : forall (E:eff_ctx) (D:init_ctx)
  (Sigma:heap) (x:var) (a:trm_label) (y:var) (UB:typ)
  (hds hds':heap_defs) (S1 S2:heap),
  free_sub_heap E Sigma D ->
  binds x (item_obj UB hds) Sigma ->
  Sigma = S1 & x ~ item_obj UB hds & S2 ->
  x # S2 ->
  defs_update hds a y hds' ->
  x \in dom E ->
  well_pointed D (E & x ~ heap_defs_effs x hds') y ->
  free_sub_heap (E & x ~ heap_defs_effs x hds')
    (S1 & x ~ item_obj UB hds' & S2) D.
Proof.
  intros E D Sigma x a y UB hds hds' S1 S2 Hfree Hbinds Heq Hfresh Hdu HxE Hwpy.
  subst Sigma.
  destruct (dom_binds_exists HxE) as [e0 Hb0].
  destruct (Hfree x e0 Hb0) as [Hfr0 [itm0 [Hb0S Hfi0]]].
  assert (Hitm : itm0 = item_obj UB hds)
    by (eapply LibEnv.binds_functional; eassumption).
  subst itm0. inversion Hfi0; subst.
  match goal with
  | Hfd : free_heap_defs _ _ _ _ |- _ =>
      unfold free_heap_defs in Hfd;
      destruct Hfd as [Hbxf [Hbe0 Hwp0]]
  end.
  assert (Heffeq : e0 = heap_defs_effs x hds)
    by (eapply LibEnv.binds_functional; eassumption).
  subst e0.
  assert (HdomE' : dom (E & x ~ heap_defs_effs x hds') = dom E)
    by (apply dom_push_in; exact HxE).
  intros z effs Hz.
  destruct (LibEnv.binds_push_inv Hz) as [[Heqz Heqe]|[Hne Hzb]].
  - subst z effs. split.
    + intros z0 l Hl. apply (Hfr0 z0 l).
      rewrite in_from_list. rewrite in_from_list in Hl.
      eapply heap_defs_effs_update_in; eassumption.
    + exists (item_obj UB hds'). split.
      * eapply LibEnv.binds_middle_eq. exact Hfresh.
      * eapply free_heap_obj. split; [exact Hbxf|split].
        -- apply LibEnv.binds_push_eq.
        -- intros z0 Hz0.
           destruct (@heap_defs_points_to_update hds hds' a y Hdu z0 Hz0)
             as [->|Hz0old].
           ++ exact Hwpy.
           ++ eapply well_pointed_dom_eq; [exact HdomE'|].
              eapply Hwp0. exact Hz0old.
  - destruct (Hfree z effs Hzb) as [Hfr [itm [HbS Hfi]]].
    split; [exact Hfr|].
    exists itm. split.
    + eapply (@binds_replace item S1 S2 x z
                 (item_obj UB hds) (item_obj UB hds') itm);
        [exact Hne|exact HbS].
    + inversion Hfi; subst.
      match goal with
      | Hfd : free_heap_defs _ _ _ _ |- _ =>
          unfold free_heap_defs in Hfd;
          destruct Hfd as [Hzf [Hze Hwp]]
      end.
      eapply free_heap_obj. split; [exact Hzf|split].
      * eapply LibEnv.binds_push_neq; [exact Hze|exact Hne].
      * intros z0 Hz0.
        eapply well_pointed_dom_eq; [exact HdomE'|].
        eapply Hwp. exact Hz0.
Qed.

Lemma well_committed_heap_update : forall (G:ctx) (D:init_ctx)
  (Sigma:heap) (x:var) (a:trm_label) (y:var) (UB:typ)
  (hds hds':heap_defs) (S1 S2:heap),
  well_committed_heap G D Sigma ->
  Sigma = S1 & x ~ item_obj UB hds & S2 ->
  x # S2 ->
  defs_update hds a y hds' ->
  (binds x committed D -> binds y committed D) ->
  well_committed_heap G D (S1 & x ~ item_obj UB hds' & S2).
Proof.
  intros G D Sigma x a y UB hds hds' S1 S2 Hwc Heq Hfresh Hdu Hcond.
  subst Sigma. destruct Hwc as [HG [HD Hitem]]. split; [exact HG|]. split.
  - rewrite HD. rewrite !LibEnv.dom_concat, !LibEnv.dom_single. reflexivity.
  - intros z itm Hzcomm Hbinds.
    destruct (classic (z = x)) as [->|Hne].
    + assert (Hyc : binds x committed D) by exact Hzcomm.
      assert (Hycomm : binds y committed D) by (apply Hcond; exact Hyc).
      assert (Hbinds_new : binds x (item_obj UB hds')
                            (S1 & x ~ item_obj UB hds' & S2))
        by (eapply LibEnv.binds_middle_eq; exact Hfresh).
      assert (Heqitm : itm = item_obj UB hds')
        by (eapply LibEnv.binds_functional; eassumption).
      subst itm.
      assert (Hbinds_old : binds x (item_obj UB hds)
                            (S1 & x ~ item_obj UB hds & S2))
        by (eapply LibEnv.binds_middle_eq; exact Hfresh).
      pose proof (Hitem x (item_obj UB hds) Hyc Hbinds_old) as Hci.
      pose proof (committed_heap_item_obj_inv Hci) as Hcdefs.
      eapply committed_heap_obj.
      eapply committed_heap_defs_update; eassumption.
    + assert (Hbinds_old : binds z itm (S1 & x ~ item_obj UB hds & S2)).
      { eapply (@binds_replace item S1 S2 x z
                   (item_obj UB hds') (item_obj UB hds) itm);
          [exact Hne|exact Hbinds]. }
      exact (Hitem z itm Hzcomm Hbinds_old).
Qed.

Lemma free_sub_heaps_update_notin : forall (G:ctx) (D:init_ctx)
  (Sigma:heap) (Es:list eff_ctx) (x:var) (a:trm_label) (y:var)
  (UB:typ) (hds hds':heap_defs) (S1 S2:heap),
  free_sub_heaps G D Sigma Es ->
  x \notin list_dom_union Es ->
  (binds x committed D -> binds y committed D) ->
  Sigma = S1 & x ~ item_obj UB hds & S2 ->
  x # S2 ->
  defs_update hds a y hds' ->
  free_sub_heaps G D (S1 & x ~ item_obj UB hds' & S2) Es.
Proof.
  intros G D Sigma Es. induction Es as [|E0 Es IH];
    intros x a y UB hds hds' S1 S2 Hfs Hnotin Hcond Heq Hfresh Hdu.
  - inversion Hfs; subst. eapply free_sub_heaps_nil.
    eapply (@well_committed_heap_update G D
              (S1 & x ~ item_obj UB hds & S2) x a y UB hds hds' S1 S2).
    all: first [eassumption|reflexivity].
  - inversion Hfs as [|G0 D0 S0 E1 Es1 Hall Hfree Htail]; subst.
    assert (HxE0 : x \notin dom E0).
    { intro Hx. apply Hnotin. rewrite in_list_dom_union.
      exists E0. split; [left; reflexivity|exact Hx]. }
    assert (HxEs : x \notin list_dom_union Es).
    { intro Hx. apply Hnotin. rewrite in_list_dom_union.
      rewrite in_list_dom_union in Hx.
      destruct Hx as [E' [Hin HE']].
      exists E'. split; [right; exact Hin|exact HE']. }
    eapply free_sub_heaps_cons.
    + exact Hall.
    + eapply free_sub_heap_update_notin;
        [exact Hfree|reflexivity|exact Hfresh|exact Hdu|exact HxE0].
    + eapply IH;
        [exact Htail|exact HxEs|exact Hcond|reflexivity|exact Hfresh|exact Hdu].
Qed.

(* ------------------------------------------------------------------ *)
(* Effect-context correspondence helpers                               *)
(* ------------------------------------------------------------------ *)

Lemma eff_trm_asn_inv : forall (x y:var) (a:trm_label) (effs:effects),
  ⊢e trm_asn (avar_f x) a (avar_f y) ∶ effs ->
  effs = nil \/ effs = ((x,a) :: nil).
Proof.
  intros x y a effs H.
  change (eff_trm (trm_asn (avar_f x) a (avar_f y)) effs) in H.
  inversion H; subst; [left|right]; reflexivity.
Qed.

Lemma eff_ctx_corr_inv : forall (E:eff_ctx) (Es:list eff_ctx)
  (effs:effects) (effss:list effects),
  eff_ctx_corr (E :: Es) (effs :: effss) ->
  eff_ctx_corr Es effss /\ eff_ctx_corr_one E effs.
Proof.
  intros E Es effs effss H. inversion H; subst. split; assumption.
Qed.

Lemma eff_ctx_corr_one_update_at : forall (E:eff_ctx) (effs' effs:effects)
  (x:var) (e' e:effects),
  eff_ctx_corr_one E (effs' ++ effs) ->
  (forall z effsz, binds z effsz E ->
     forall p, p \in from_list effsz -> fst p = z) ->
  (forall p, List.In p effs' -> fst p = x) ->
  (forall p, p \in from_list e' -> p \notin from_list effs') ->
  (forall p, p \in from_list e' -> p \in from_list e) ->
  binds x e E ->
  eff_ctx_corr_one (E & x ~ e') effs.
Proof.
  intros E effs' effs x e' e Hcorr HfreshE Hfst Havoid Hsub Hbinds
    z effsz Hz p Hp.
  unfold eff_ctx_corr_one in Hcorr.
  destruct (LibEnv.binds_push_inv Hz) as [[Heqz Heqe]|[Hne Hzb]].
  - subst z effsz.
    assert (Hpold : p \in from_list e) by (apply Hsub; exact Hp).
    assert (Hin : p \in from_list (effs' ++ effs))
      by (apply (Hcorr x e); [exact Hbinds|exact Hpold]).
    rewrite from_list_app in Hin. rewrite in_union in Hin.
    destruct Hin as [Hin|Hin]; [|exact Hin].
    exfalso. eapply (Havoid p Hp). exact Hin.
  - assert (Hin : p \in from_list (effs' ++ effs))
      by (apply (Hcorr z effsz); [exact Hzb|exact Hp]).
    rewrite from_list_app in Hin. rewrite in_union in Hin.
    destruct Hin as [Hin|Hin]; [|exact Hin].
    exfalso.
    rewrite in_from_list in Hin.
    pose proof (Hfst p Hin) as Hfpx.
    pose proof (@HfreshE z effsz Hzb p Hp) as Hfpz.
    rewrite Hfpx in Hfpz. exact (Hne (eq_sym Hfpz)).
Qed.

(* ------------------------------------------------------------------ *)
(* Stack typing only depends on the domains of the effect contexts     *)
(* ------------------------------------------------------------------ *)

Definition envs_dom_eq (Es Es':list eff_ctx) : Prop :=
  List.length Es = List.length Es' /\
  forall n E E', nth_error Es n = Some E -> nth_error Es' n = Some E' ->
    dom E = dom E'.

Lemma envs_dom_eq_cons_inv : forall (E:eff_ctx) (Es:list eff_ctx)
  (E':eff_ctx) (Es':list eff_ctx),
  envs_dom_eq (E :: Es) (E' :: Es') ->
  dom E = dom E' /\ envs_dom_eq Es Es'.
Proof.
  intros E Es E' Es' [Hlen Hdom]. split.
  - exact (Hdom 0 E E' eq_refl eq_refl).
  - split.
    + simpl in Hlen. exact (eq_add_S _ _ Hlen).
    + intros n E1 E2 H1 H2. eapply Hdom with (n:=S n); simpl; eassumption.
Qed.

Lemma envs_dom_eq_zero : forall (Es Es':list eff_ctx),
  envs_dom_eq Es Es' -> List.length Es = 0 -> Es' = nil.
Proof.
  intros Es Es' [Hlen _] H0. destruct Es'; [reflexivity|].
  simpl in Hlen. rewrite H0 in Hlen. discriminate.
Qed.

Lemma envs_dom_eq_one : forall (E:eff_ctx) (Es:list eff_ctx)
  (Es':list eff_ctx),
  envs_dom_eq (E :: Es) Es' -> Es = nil -> exists E', Es' = E' :: nil.
Proof.
  intros E Es Es' [Hlen Hdom] Hnil. destruct Es' as [|E' Es''].
  - simpl in Hlen. discriminate.
  - assert (Es'' = nil) as ->.
    { destruct Es''; [reflexivity|]. simpl in Hlen. rewrite Hnil in Hlen. discriminate. }
    exists E'. reflexivity.
Qed.

Lemma ty_stack_dom_eq : forall (G:ctx) (D:init_ctx) (Es Es':list eff_ctx)
  (Fs:stack) (T:typ) (i:init_typ) (effss:list effects) (U:typ),
  envs_dom_eq Es Es' ->
  ty_stack G D Es Fs T i effss U ->
  ty_stack G D Es' Fs T i effss U.
Proof.
  intros G D Es Es' Fs T i effss U Hde H. revert Es' Hde.
  induction H; intros Es' Hde.
  - destruct Es' as [|E' Es'']; [simpl in Hde; destruct Hde as [Hlen _]; discriminate Hlen|].
    destruct Es'' as [|E2 Es2]; [|simpl in Hde; destruct Hde as [Hlen _]; discriminate Hlen].
    apply ty_stack_nil. assumption.
  - destruct Es' as [|E' Es'']; [simpl in Hde; destruct Hde as [Hlen _]; discriminate Hlen|].
    destruct (envs_dom_eq_cons_inv _ _ _ _ Hde) as [Hdomhead Hde_tail].
    eapply ty_stack_let.
    + eapply IHty_stack. exact Hde.
    + exact H0.
    + intros x Hx. rewrite <- Hdomhead. eapply H1. exact Hx.
    + exact H2.
  - destruct Es' as [|E' Es'']; [simpl in Hde; destruct Hde as [Hlen _]; discriminate Hlen|].
    destruct (envs_dom_eq_cons_inv _ _ _ _ Hde) as [Hdomhead Hde_tail].
    eapply ty_stack_ret_free.
    + eapply IHty_stack. exact Hde.
    + exact H0.
    + rewrite <- Hdomhead. exact H1.
  - destruct Es' as [|E' Es'']; [simpl in Hde; destruct Hde as [Hlen _]; discriminate Hlen|].
    destruct (envs_dom_eq_cons_inv _ _ _ _ Hde) as [Hdomhead Hde_tail].
    eapply ty_stack_ret_committed.
    + eapply IHty_stack. exact Hde_tail.
    + exact H0.
    + rewrite <- Hdomhead. exact H1.
Qed.

(* ------------------------------------------------------------------ *)
(* Updating any effect context that contains the assigned variable      *)
(* ------------------------------------------------------------------ *)

Definition ctx_upd (x:var) (e':effects) (E:eff_ctx) : eff_ctx :=
  if excluded_middle_informative (x \in dom E) then E & x ~ e' else E.

Lemma ctx_upd_in : forall (x:var) (e':effects) (E:eff_ctx),
  x \in dom E -> ctx_upd x e' E = E & x ~ e'.
Proof.
  intros x e' E H. unfold ctx_upd.
  destruct (excluded_middle_informative (x \in dom E)) as [Hx|Hx]; [reflexivity|contradiction].
Qed.

Lemma ctx_upd_notin : forall (x:var) (e':effects) (E:eff_ctx),
  x \notin dom E -> ctx_upd x e' E = E.
Proof.
  intros x e' E H. unfold ctx_upd.
  destruct (excluded_middle_informative (x \in dom E)) as [Hx|Hx]; [contradiction|reflexivity].
Qed.

Lemma dom_ctx_upd : forall (x:var) (e':effects) (E:eff_ctx),
  dom (ctx_upd x e' E) = dom E.
Proof.
  intros x e' E. unfold ctx_upd.
  destruct (excluded_middle_informative (x \in dom E)) as [Hx|Hx].
  - apply dom_push_in. exact Hx.
  - reflexivity.
Qed.

Lemma list_dom_union_map_ctx_upd : forall (Es:list eff_ctx) (x:var) (e':effects),
  list_dom_union (List.map (ctx_upd x e') Es) = list_dom_union Es.
Proof.
  induction Es as [|E Es IH]; intros x e'; simpl; [reflexivity|].
  rewrite IH, dom_ctx_upd. reflexivity.
Qed.

Lemma free_sub_heap_fresh : forall (E:eff_ctx) (Sigma:heap) (D:init_ctx),
  free_sub_heap E Sigma D ->
  forall (z:var) (effsz:effects), binds z effsz E ->
  forall p, p \in from_list effsz -> fst p = z.
Proof.
  intros E Sigma D H z effsz Hb p Hp.
  unfold free_sub_heap in H.
  destruct (H z effsz Hb) as [Hf _].
  destruct p as [y a]. simpl. apply (Hf y a Hp).
Qed.

Lemma free_sub_heaps_in_free : forall (G:ctx) (D:init_ctx) (Sigma:heap)
  (Es:list eff_ctx) (E:eff_ctx),
  free_sub_heaps G D Sigma Es -> List.In E Es ->
  free_sub_heap E Sigma D.
Proof.
  intros G D Sigma Es E H. induction H; intros Hin.
  - inversion Hin.
  - destruct Hin as [->|Hin]; [exact H0|eapply IHfree_sub_heaps; exact Hin].
Qed.

Lemma free_sub_heap_bound_effs : forall (E:eff_ctx) (Sigma:heap)
  (D:init_ctx) (x:var) (T:typ) (hds:heap_defs),
  free_sub_heap E Sigma D ->
  binds x (item_obj T hds) Sigma ->
  x \in dom E ->
  binds x (heap_defs_effs x hds) E.
Proof.
  intros E Sigma D x T hds Hfree HbS HxE.
  destruct (dom_binds_exists HxE) as [effs Hb].
  destruct (Hfree x effs Hb) as [_ [itm [HbItm Hitem]]].
  assert (Heq : itm = item_obj T hds)
    by (eapply LibEnv.binds_functional; eassumption).
  subst itm. inversion Hitem; subst.
  match goal with
  | Hfd : free_heap_defs _ _ _ _ |- _ =>
      unfold free_heap_defs in Hfd; destruct Hfd as [_ [Hbe _]]; exact Hbe
  end.
Qed.

Lemma free_sub_heaps_update_ctx : forall (G:ctx) (D:init_ctx)
  (Sigma:heap) (Es:list eff_ctx) (x:var) (a:trm_label) (y:var)
  (T:typ) (hds hds':heap_defs) (S1 S2:heap) (e':effects),
  free_sub_heaps G D Sigma Es ->
  (binds x committed D -> binds y committed D) ->
  Sigma = S1 & x ~ item_obj T hds & S2 ->
  x # S2 ->
  defs_update hds a y hds' ->
  e' = heap_defs_effs x hds' ->
  (forall E, List.In E Es -> x \in dom E ->
     well_pointed D (ctx_upd x e' E) y) ->
  free_sub_heaps G D (S1 & x ~ item_obj T hds' & S2)
    (List.map (ctx_upd x e') Es).
Proof.
  intros G D Sigma Es. induction Es as [|E Es IH];
    intros x a y T hds hds' S1 S2 e' Hfs Hcond Heq Hfresh Hdu He' Hwp.
  - inversion Hfs; subst. simpl. eapply free_sub_heaps_nil.
    eapply (@well_committed_heap_update G D
              (S1 & x ~ item_obj T hds & S2) x a y T hds hds' S1 S2).
    all: try eassumption; try reflexivity.
  - inversion Hfs as [|G0 D0 S0 E1 Es1 Hall Hfree Htail]; subst.
    simpl. eapply free_sub_heaps_cons.
    + rewrite dom_ctx_upd, list_dom_union_map_ctx_upd. exact Hall.
    + destruct (classic (x \in dom E)) as [HxE|HxE].
      * rewrite ctx_upd_in by exact HxE.
        eapply free_sub_heap_update_x.
        -- exact Hfree.
        -- eapply LibEnv.binds_middle_eq. exact Hfresh.
        -- reflexivity.
        -- exact Hfresh.
        -- exact Hdu.
        -- exact HxE.
        -- rewrite <- (ctx_upd_in x (heap_defs_effs x hds') E HxE).
           exact (Hwp E (List.in_eq _ _) HxE).
      * rewrite ctx_upd_notin by exact HxE.
        eapply free_sub_heap_update_notin.
        -- exact Hfree.
        -- reflexivity.
        -- exact Hfresh.
        -- exact Hdu.
        -- exact HxE.
    + eapply IH.
      * exact Htail.
      * exact Hcond.
      * reflexivity.
      * exact Hfresh.
      * exact Hdu.
      * reflexivity.
      * intros E' Hin Hx. eapply Hwp; [apply List.in_cons; exact Hin|exact Hx].
Qed.

(* ------------------------------------------------------------------ *)
(* Effect-context correspondence is preserved by an update             *)
(* ------------------------------------------------------------------ *)

Lemma eff_ctx_corr_one_update_sub : forall (E:eff_ctx) (effs:effects)
  (x:var) (e e':effects),
  eff_ctx_corr_one E effs ->
  binds x e E ->
  (forall p, p \in from_list e' -> p \in from_list e) ->
  eff_ctx_corr_one (ctx_upd x e' E) effs.
Proof.
  intros E effs x e e' Hcorr Hb Hsub.
  assert (HxE : x \in dom E) by (eapply binds_in_dom; exact Hb).
  rewrite ctx_upd_in by exact HxE.
  unfold eff_ctx_corr_one in *.
  intros z effsz Hz p Hp.
  destruct (LibEnv.binds_push_inv Hz) as [[Heqz Heqe]|[Hne Hzb]].
  - subst z effsz. apply (Hcorr x e Hb p). apply Hsub. exact Hp.
  - apply (Hcorr z effsz Hzb p Hp).
Qed.

Lemma eff_ctx_corr_one_ctx_upd_notin : forall (x:var) (e':effects)
  (E:eff_ctx) (effs:effects),
  x \notin dom E ->
  eff_ctx_corr_one E effs ->
  eff_ctx_corr_one (ctx_upd x e' E) effs.
Proof.
  intros x e' E effs Hx Hcorr.
  unfold eff_ctx_corr_one in *.
  intros z ez Hz p Hp.
  rewrite (ctx_upd_notin x e' E Hx) in Hz.
  exact (Hcorr z ez Hz p Hp).
Qed.

Lemma eff_ctx_corr_one_ctx_upd_at : forall (E:eff_ctx) (effs' effs:effects)
  (x:var) (e' e:effects),
  x \in dom E ->
  eff_ctx_corr_one E (effs' ++ effs) ->
  (forall z effsz, binds z effsz E ->
     forall p, p \in from_list effsz -> fst p = z) ->
  (forall p, List.In p effs' -> fst p = x) ->
  (forall p, p \in from_list e' -> p \notin from_list effs') ->
  (forall p, p \in from_list e' -> p \in from_list e) ->
  binds x e E ->
  eff_ctx_corr_one (ctx_upd x e' E) effs.
Proof.
  intros E effs' effs x e' e Hx Hcorr Hfresh Hfst Havoid Hsub Hb.
  rewrite (ctx_upd_in x e' E Hx).
  exact (eff_ctx_corr_one_update_at E effs' effs x e' e
           Hcorr Hfresh Hfst Havoid Hsub Hb).
Qed.

Lemma eff_ctx_corr_map_ctx_upd : forall (Es:list eff_ctx) (effss:list effects)
  (x:var) (e e':effects),
  eff_ctx_corr Es effss ->
  (forall E, List.In E Es -> x \in dom E -> binds x e E) ->
  (forall p, p \in from_list e' -> p \in from_list e) ->
  eff_ctx_corr (List.map (ctx_upd x e') Es) effss.
Proof.
  intros Es effss x e e' H. induction H; intros Hb Hsub.
  - simpl. apply eff_ctx_corr_nil.
  - simpl. eapply eff_ctx_corr_cons.
    + eapply IHeff_ctx_corr.
      * intros E0 Hin Hx. apply Hb. apply List.in_cons. exact Hin. exact Hx.
      * exact Hsub.
    + destruct (excluded_middle_informative (x \in dom ℰ)) as [Hx|Hx].
      * eapply eff_ctx_corr_one_update_sub;
          [exact H0| apply Hb; [apply List.in_eq|exact Hx] |exact Hsub].
      * eapply eff_ctx_corr_one_ctx_upd_notin; [exact Hx|exact H0].
Qed.

Lemma envs_dom_eq_map_ctx_upd : forall (Es:list eff_ctx) (x:var) (e:effects),
  envs_dom_eq Es (List.map (ctx_upd x e) Es).
Proof.
  intros Es x e. split.
  - rewrite List.length_map. reflexivity.
  - intros n E E' Hn Hm.
    rewrite nth_error_map in Hm.
    destruct (nth_error Es n) as [E0|] eqn:Heq; [|simpl in Hm; discriminate Hm].
    simpl in Hm. injection Hm as HE'. subst E'.
    injection Hn as HE. subst E.
    symmetry. apply dom_ctx_upd.
Qed.

(* Project the components of a configuration typing.  This is proved     *)
(* locally (not imported from Task.v) so that the development does not   *)
(* depend on the target file.                                            *)
(* A def at label [a] gives a balanced record component for [a]. *)
Lemma heap_defs_record_has_of_update : forall (G:ctx)
  (hds hds':heap_defs) (T:typ) (a:trm_label) (y:var),
  G ⊢ hds ∶ T ->
  defs_update hds a y hds' ->
  exists Tf, record_has T (dec_trm a Tf Tf).
Proof.
  intros G hds hds' T a y Hhds Hdu.
  destruct (@defs_update_label_in hds hds' a y Hdu) as [d [Hin Hlab]].
  destruct (@ty_heap_defs_correspond G hds T Hhds) as (ls & Hrt & Hfwd & Hbwd).
  destruct (Hfwd d Hin) as [D [Hrh Hdty]].
  inversion Hdty; subst.
  - simpl in Hlab. discriminate Hlab.
  - simpl in Hlab. injection Hlab as Ha0. subst a0.
    exists T0. exact Hrh.
  - simpl in Hlab. injection Hlab as Ha0. subst a0.
    exists T0. exact Hrh.
Qed.

(* ==== SelCaseParam ==== *)


Section Params.

Hypothesis Hfield : forall (G:ctx) (V:typ) (a:trm_label) (Tf S U:typ),
  inert G ->
  record_type V ->
  record_has V (dec_trm a Tf Tf) ->
  G ⊢ V <: typ_rcd (dec_trm a S U) ->
  G ⊢ Tf <: U.

Hypothesis Hroot : forall (G:ctx) (x:var) (U:typ) (D:dec),
  inert G ->
  binds x (typ_bnd U) G ->
  G ⊢ trm_var (avar_f x) ∶ typ_rcd D ->
  G ⊢ open x U <: typ_rcd D.

Lemma ty_config_red_sel : forall (G:ctx) (D:init_ctx) (Es:list eff_ctx)
  (effss:list effects) (Fs:stack) (Sigma:heap) (U:typ)
  (x:var) (a:trm_label) (y:var) (T0:typ) (hds:heap_defs),
  ty_config G D Es effss (trm_sel (avar_f x) a ; Fs ; Sigma) U ->
  binds x (item_obj T0 hds) Sigma ->
  labels_has hds (heap_def_trm a (Some y)) ->
  exists G' D' Es' effss',
    ty_config (G & G') D' Es' effss' (trm_var (avar_f y) ; Fs ; Sigma) U.
Proof.
  intros G D Es effss Fs Sigma U x a y T0 hds Hcfg Hbheap Hlab.
  destruct (@ty_config_inv_s G D Es effss (trm_sel (avar_f x) a) Fs Sigma U Hcfg) as
    (ℰ & ℰs & Ts & ii & effs & effs' & effss0 &
     HeqEs & HeqEffs & Hinert & Hinits & Hhc & Hfs & Hstack & Hty & Heff & Hinit & Hcorr).
  assert (Heffnil : effs' = nil) by (eapply eff_trm_sel_nil; exact Heff).
  subst effs'.
  cbn in Hcorr. cbn in HeqEffs.
  destruct (@ty_sel_inv G x a Ts Hty) as [S [Ts0 [Hxrec HsubT]]].
  destruct (@init_typing_sel_committed G D (dom ℰ) x a ii Hinit) as [Hi Heqxcomm].
  subst ii.
  destruct (@heap_correspond_obj G Sigma x T0 hds Hhc Hbheap) as [HxG Hhds].
  assert (Hsubopen : G ⊢ open x T0 <: typ_rcd (dec_trm a S Ts0))
    by (eapply Hroot; eassumption).
  pose proof (@labels_has_heap_in hds (heap_def_trm a (Some y)) Hlab) as Hin.
  destruct (@heap_def_typing_rh G hds (open x T0) a y Hhds Hin) as [Tf [Hrh HyTf]].
  pose proof (@ty_heap_defs_record_type G hds (open x T0) Hhds) as Hrt.
  assert (Htfsub : G ⊢ Tf <: Ts0)
    by (eapply Hfield; [exact Hinert|exact Hrt|exact Hrh|exact Hsubopen]).
  assert (HyTs : G ⊢ trm_var (avar_f y) ∶ Ts).
  { eapply ty_sub.
    - exact HyTf.
    - eapply subtyp_trans; [exact Htfsub|exact HsubT]. }
  pose proof (@free_sub_heaps_well_committed G D Sigma (ℰ :: ℰs) Hfs) as Hwc.
  pose proof (@well_committed_heap_item G D Sigma x (item_obj T0 hds) Hwc Heqxcomm Hbheap) as Hci.
  pose proof (@committed_heap_item_obj_inv G D T0 hds Hci) as Hcdefs.
  pose proof (@committed_heap_defs_in D hds (heap_def_trm a (Some y)) Hcdefs Hin) as Hcd.
  pose proof (@committed_heap_def_trm_some_binds D a y Hcd) as Hycomm.
  exists (empty:ctx), D, (ℰ :: ℰs), (effs :: effss0).
  rewrite concat_empty_r.
  eapply (@ty_config_c G D Sigma ℰ ℰs Fs (trm_var (avar_f y)) Ts committed U nil effs effss0).
  - exact Hinert.
  - exact Hinits.
  - exact Hhc.
  - exact Hfs.
  - exact Hstack.
  - exact HyTs.
  - apply eff_ignore.
  - eapply init_var_binds. apply init_var_commit. exact Hycomm.
  - exact Hcorr.
Qed.

End Params.

(* ==== AsnCase ==== *)

(* ====================================================================== *)
(* Preservation for assignment.                                           *)
(*                                                                        *)
(* Two restricted field-subtyping hypotheses are used, both guarded by    *)
(* [inert G].  The unrestricted and [record_type]-only versions are false *)
(* (see FieldSub.v / FieldSub2.v); however the actual use supplies        *)
(* [inert G] from [ty_config_inv_s], and [V = open x T] whose             *)
(* [record_type] comes from [ty_heap_defs_record_type ... Hhds].          *)
(* [Hcov] is the covariant direction and [Hcontr] the contravariant      *)
(* counterpart, needed to retype the assigned variable at the field type *)
(* read off the heap.  [Hroot] is the canonical-forms/root-subtyping     *)
(* fact for inert contexts.                                              *)
(* ====================================================================== *)

Section Params.

Hypothesis Hcov : forall (G:ctx) (V:typ) (a:trm_label) (Tf S U:typ),
  inert G ->
  record_type V ->
  record_has V (dec_trm a Tf Tf) ->
  G ⊢ V <: typ_rcd (dec_trm a S U) ->
  G ⊢ Tf <: U.

Hypothesis Hcontr : forall (G:ctx) (V:typ) (a:trm_label) (Tf S U:typ),
  inert G ->
  record_type V ->
  record_has V (dec_trm a Tf Tf) ->
  G ⊢ V <: typ_rcd (dec_trm a S U) ->
  G ⊢ S <: Tf.

Hypothesis Hroot : forall (G:ctx) (x:var) (U:typ) (D:dec),
  inert G ->
  binds x (typ_bnd U) G ->
  G ⊢ trm_var (avar_f x) ∶ typ_rcd D ->
  G ⊢ open x U <: typ_rcd D.

Lemma ty_config_red_asn : forall (G:ctx) (D:init_ctx) (Es:list eff_ctx)
  (effss:list effects) (Fs:stack) (Sigma Sigma':heap) (U:typ)
  (x:var) (a:trm_label) (y:var),
  ty_config G D Es effss (trm_asn (avar_f x) a (avar_f y) ; Fs ; Sigma) U ->
  heap_update Sigma x a y Sigma' ->
  exists G' D' Es' effss',
    ty_config (G & G') D' Es' effss' (trm_var (avar_f y) ; Fs ; Sigma') U.
Proof.
  intros G D Es effss Fs Sigma Sigma' U x a y Hcfg Hup.
  destruct Hup as (T & hds & hds' & S1 & S2 & HeqS & Hfresh & Hdu & HeqS').
  subst Sigma Sigma'.
  destruct (@ty_config_inv_s G D Es effss
              (trm_asn (avar_f x) a (avar_f y)) Fs
              (S1 & x ~ item_obj T hds & S2) U Hcfg) as
    (ℰ & ℰs & Ts & ii & effsS & effsT & effss0 &
     HeqEs & HeqEffs & Hinert & Hinits & Hhc & Hfs & Hstack & Hty & Heff & Hinit & Hcorr).
  subst Es effss.
  (* Assignment inversion. *)
  destruct (@ty_asn_inv G x a y Ts Hty) as (Sa & T0 & HxTy & HyTy & HT0sub).
  (* The heap object bound at [x]. *)
  assert (HbS : binds x (item_obj T hds)
                  (S1 & x ~ item_obj T hds & S2)).
  { eapply LibEnv.binds_middle_eq. exact Hfresh. }
  destruct (@heap_correspond_obj G (S1 & x ~ item_obj T hds & S2) x T hds
              Hhc HbS) as [HxG Hhds].
  (* Record subtyping at [x]. *)
  assert (Hsubrec : G ⊢ open x T <: typ_rcd (dec_trm a Sa T0)).
  { eapply Hroot; [exact Hinert|exact HxG|exact HxTy]. }
  (* A balanced component at label [a] exists in the old heap. *)
  destruct (@heap_defs_record_has_of_update G hds hds' (open x T) a y
              Hhds Hdu) as [Tf Hrh].
  assert (Hrec : record_type (open x T)).
  { eapply ty_heap_defs_record_type. exact Hhds. }
  assert (HSaTf : G ⊢ Sa <: Tf).
  { eapply Hcontr; [exact Hinert|exact Hrec|exact Hrh|exact Hsubrec]. }
  assert (HTfT0 : G ⊢ Tf <: T0).
  { eapply Hcov; [exact Hinert|exact Hrec|exact Hrh|exact Hsubrec]. }
  assert (HSaTs : G ⊢ Sa <: Ts).
  { eapply subtyp_trans; [exact HSaTf|].
    eapply subtyp_trans; [exact HTfT0|exact HT0sub]. }
  assert (HyTf : G ⊢ trm_var (avar_f y) ∶ Tf).
  { eapply ty_sub; [exact HyTy|exact HSaTf]. }
  assert (HyTs : G ⊢ trm_var (avar_f y) ∶ Ts).
  { eapply ty_sub; [exact HyTy|exact HSaTs]. }
  (* Retype the heap and keep heap correspondence. *)
  assert (Hhds' : G ⊢ hds' ∶ open x T).
  { eapply (@ty_heap_defs_update G hds (open x T) Hhds a y hds' Hdu Tf Hrh HyTf). }
  assert (Hhc' : heap_correspond G (S1 & x ~ item_obj T hds' & S2)).
  { eapply (@heap_correspond_update G S1 S2 x T hds hds' a y
              Hfresh Hhc Hdu Hhds'). }
  assert (Huniq : forall d1 d2, List.In d1 hds' -> List.In d2 hds' ->
                    label_of d1 = label_of d2 -> d1 = d2).
  { eapply (@ty_heap_defs_label_unique G hds' (open x T) Hhds'). }
  (* The head effect context and its tail. *)
  destruct (@free_sub_heaps_cons_inv G D (S1 & x ~ item_obj T hds & S2)
              ℰ ℰs Hfs) as [HfreeHead Htail].
  pose proof (@free_sub_heaps_all_notin G D (S1 & x ~ item_obj T hds & S2)
              ℰ ℰs Hfs) as Hall.
  (* Status of the assigned variable [y]. *)
  destruct (@init_typing_asn_status G D (dom ℰ) x y a ii Hinit)
    as [[Hii Hycomm]|[Hii Hyvs]].
  - (* [y] is committed. *)
    subst ii.
    assert (Hcond : binds x committed D -> binds y committed D)
      by (intros _; exact Hycomm).
    assert (Hwp : forall E, List.In E (ℰ :: ℰs) -> x \in dom E ->
                     well_pointed D (ctx_upd x (heap_defs_effs x hds') E) y).
    { intros E Hin HxE. left. exact Hycomm. }
    assert (HinitY : G ⸴ D ⸴ dom (ctx_upd x (heap_defs_effs x hds') ℰ)
                       ⊢i trm_var (avar_f y) ∶ committed).
    { eapply init_commit. eapply commit_var. exact Hycomm. }
    (* Free subheaps. *)
    assert (HfsNew : free_sub_heaps G D (S1 & x ~ item_obj T hds' & S2)
                       (List.map (ctx_upd x (heap_defs_effs x hds'))
                                 (ℰ :: ℰs))).
    { eapply (@free_sub_heaps_update_ctx G D
                (S1 & x ~ item_obj T hds & S2) (ℰ :: ℰs) x a y T hds hds'
                S1 S2 (heap_defs_effs x hds'));
        [exact Hfs|exact Hcond|reflexivity|exact Hfresh|exact Hdu|
         reflexivity|exact Hwp]. }
    (* Stack typing only depends on domains. *)
    assert (HstackNew : ty_stack G D
              (ctx_upd x (heap_defs_effs x hds') ℰ ::
                 List.map (ctx_upd x (heap_defs_effs x hds')) ℰs)
              Fs Ts committed (effsS :: effss0) U).
    { eapply (@ty_stack_dom_eq G D (ℰ :: ℰs)
                (ctx_upd x (heap_defs_effs x hds') ℰ ::
                   List.map (ctx_upd x (heap_defs_effs x hds')) ℰs)
                Fs Ts committed (effsS :: effss0) U).
      - change (envs_dom_eq (ℰ :: ℰs)
                  (List.map (ctx_upd x (heap_defs_effs x hds'))
                            (ℰ :: ℰs))).
        apply envs_dom_eq_map_ctx_upd.
      - exact Hstack. }
    (* Effect-context correspondence. *)
    destruct (@eff_ctx_corr_inv ℰ ℰs ((effsT ++ effsS)%list) effss0 Hcorr)
      as [HcorrTail HcorrHead].
    assert (HcorrTail' : eff_ctx_corr
              (List.map (ctx_upd x (heap_defs_effs x hds')) ℰs) effss0).
    { eapply eff_ctx_corr_map_ctx_upd.
      - exact HcorrTail.
      - intros E Hin HxE. eapply free_sub_heap_bound_effs.
        + eapply free_sub_heaps_in_free; [exact Htail|exact Hin].
        + exact HbS.
        + exact HxE.
      - intros p Hp. rewrite in_from_list in Hp |- *.
        eapply heap_defs_effs_update_in; [exact Hdu|exact Hp]. }
    assert (HcorrHead' : eff_ctx_corr_one
              (ctx_upd x (heap_defs_effs x hds') ℰ) effsS).
    { destruct (@eff_trm_asn_inv x y a effsT Heff) as [Hnil|Hcons].
      - subst effsT. simpl in HcorrHead.
        destruct (excluded_middle_informative (x \in dom ℰ)) as [HxE|HxE].
        + eapply eff_ctx_corr_one_ctx_upd_at with (effs':=nil)
            (e:=heap_defs_effs x hds).
          * exact HxE.
          * exact HcorrHead.
          * eapply free_sub_heap_fresh. exact HfreeHead.
          * intros p Hin. inversion Hin.
          * intros p Hp Hin. rewrite in_from_list in Hin. inversion Hin.
          * intros p Hp. rewrite in_from_list in Hp |- *.
            eapply heap_defs_effs_update_in; [exact Hdu|exact Hp].
          * eapply free_sub_heap_bound_effs;
              [exact HfreeHead|exact HbS|exact HxE].
        + eapply eff_ctx_corr_one_ctx_upd_notin;
            [exact HxE|exact HcorrHead].
      - subst effsT. simpl in HcorrHead.
        destruct (excluded_middle_informative (x \in dom ℰ)) as [HxE|HxE].
        + eapply eff_ctx_corr_one_ctx_upd_at
            with (effs':=((x,a)::nil)%list) (e:=heap_defs_effs x hds).
          * exact HxE.
          * exact HcorrHead.
          * eapply free_sub_heap_fresh. exact HfreeHead.
          * intros p Hin. simpl in Hin.
            destruct p as [z l]. simpl in *. destruct Hin as [Heq|[]].
            injection Heq as -> ->. reflexivity.
          * intros p Hp Hin.
            rewrite in_from_list in Hp. rewrite in_from_list in Hin.
            simpl in Hin. destruct p as [z l]. simpl in *.
            destruct Hin as [Heq|[]]. injection Heq as Hx Ha. subst z l.
            exact (@defs_update_not_none hds hds' a y Hdu Huniq
                     (@heap_defs_effs_in_inv x a hds' Hp)).
          * intros p Hp. rewrite in_from_list in Hp |- *.
            eapply heap_defs_effs_update_in; [exact Hdu|exact Hp].
          * eapply free_sub_heap_bound_effs;
              [exact HfreeHead|exact HbS|exact HxE].
        + eapply eff_ctx_corr_one_ctx_upd_notin; [exact HxE|].
          eapply (@eff_ctx_corr_one_suffix ℰ (S1 & x ~ item_obj T hds & S2)
                    D ((x, a) :: nil) effsS);
            [exact HcorrHead|exact HfreeHead|].
          intros ee Hin. simpl in Hin.
          destruct Hin as [Heq|[]]. subst ee. simpl.
          exact HxE. }
    assert (HcorrNew : eff_ctx_corr
              (ctx_upd x (heap_defs_effs x hds') ℰ ::
                 List.map (ctx_upd x (heap_defs_effs x hds')) ℰs)
              (effsS :: effss0)).
    { eapply eff_ctx_corr_cons.
      - exact HcorrTail'.
      - exact HcorrHead'. }
    (* Build the reduced configuration. *)
    exists (empty:ctx), D,
      (ctx_upd x (heap_defs_effs x hds') ℰ ::
         List.map (ctx_upd x (heap_defs_effs x hds')) ℰs),
      (effsS :: effss0).
    rewrite concat_empty_r.
    apply (@ty_config_c G D (S1 & x ~ item_obj T hds' & S2)
             (ctx_upd x (heap_defs_effs x hds') ℰ)
             (List.map (ctx_upd x (heap_defs_effs x hds')) ℰs)
             Fs (trm_var (avar_f y)) Ts committed U nil effsS effss0).
    + exact Hinert.
    + exact Hinits.
    + exact Hhc'.
    + exact HfsNew.
    + exact HstackNew.
    + exact HyTs.
    + apply eff_ignore.
    + exact HinitY.
    + exact HcorrNew.
  - (* [y] is free, hence [x] is free and belongs to the head. *)
    subst ii.
    assert (HxE : x \in dom ℰ).
    { change (well_init G D (dom ℰ)
                (trm_asn (avar_f x) a (avar_f y)) free) in Hinit.
      inversion Hinit; subst.
      match goal with
      | Hxf : G ⸴ D ⸴ dom ℰ ⊢i trm_var (avar_f x) ∶ free |- _ =>
          eapply init_typing_var_free_mem; exact Hxf
      end. }
    assert (Hxfree : binds x free D).
    { eapply free_sub_heap_binds_free; [exact HfreeHead|exact HxE]. }
    assert (Hyfree : binds y free D).
    { eapply free_sub_heap_binds_free; [exact HfreeHead|exact Hyvs]. }
    assert (Hcond : binds x committed D -> binds y committed D).
    { intro Hxc. exfalso.
      pose proof (@LibEnv.binds_functional init_typ x free committed D
                    Hxfree Hxc) as Hcontra.
      discriminate Hcontra. }
    assert (Hwp : forall E, List.In E (ℰ :: ℰs) -> x \in dom E ->
                     well_pointed D (ctx_upd x (heap_defs_effs x hds') E) y).
    { intros E Hin HxE0.
      destruct Hin as [->|Hin].
      - right. split.
        + rewrite dom_ctx_upd. exact Hyvs.
        + exact Hyfree.
      - exfalso.
        assert (HxU : x \in list_dom_union ℰs).
        { rewrite in_list_dom_union. exists E. split; [exact Hin|exact HxE0]. }
        exact (Hall x HxE HxU). }
    assert (HinitY : G ⸴ D ⸴ dom (ctx_upd x (heap_defs_effs x hds') ℰ)
                       ⊢i trm_var (avar_f y) ∶ free).
    { eapply init_var_binds. eapply init_var_free.
      - rewrite dom_ctx_upd. exact Hyvs.
      - exact Hyfree. }
    assert (HfsNew : free_sub_heaps G D (S1 & x ~ item_obj T hds' & S2)
                       (List.map (ctx_upd x (heap_defs_effs x hds'))
                                 (ℰ :: ℰs))).
    { eapply (@free_sub_heaps_update_ctx G D
                (S1 & x ~ item_obj T hds & S2) (ℰ :: ℰs) x a y T hds hds'
                S1 S2 (heap_defs_effs x hds'));
        [exact Hfs|exact Hcond|reflexivity|exact Hfresh|exact Hdu|
         reflexivity|exact Hwp]. }
    assert (HstackNew : ty_stack G D
              (ctx_upd x (heap_defs_effs x hds') ℰ ::
                 List.map (ctx_upd x (heap_defs_effs x hds')) ℰs)
              Fs Ts free (effsS :: effss0) U).
    { eapply (@ty_stack_dom_eq G D (ℰ :: ℰs)
                (ctx_upd x (heap_defs_effs x hds') ℰ ::
                   List.map (ctx_upd x (heap_defs_effs x hds')) ℰs)
                Fs Ts free (effsS :: effss0) U).
      - change (envs_dom_eq (ℰ :: ℰs)
                  (List.map (ctx_upd x (heap_defs_effs x hds'))
                            (ℰ :: ℰs))).
        apply envs_dom_eq_map_ctx_upd.
      - exact Hstack. }
    destruct (@eff_ctx_corr_inv ℰ ℰs ((effsT ++ effsS)%list) effss0 Hcorr)
      as [HcorrTail HcorrHead].
    assert (HcorrTail' : eff_ctx_corr
              (List.map (ctx_upd x (heap_defs_effs x hds')) ℰs) effss0).
    { eapply eff_ctx_corr_map_ctx_upd.
      - exact HcorrTail.
      - intros E Hin HxE0. eapply free_sub_heap_bound_effs.
        + eapply free_sub_heaps_in_free; [exact Htail|exact Hin].
        + exact HbS.
        + exact HxE0.
      - intros p Hp. rewrite in_from_list in Hp |- *.
        eapply heap_defs_effs_update_in; [exact Hdu|exact Hp]. }
    assert (HcorrHead' : eff_ctx_corr_one
              (ctx_upd x (heap_defs_effs x hds') ℰ) effsS).
    { destruct (@eff_trm_asn_inv x y a effsT Heff) as [Hnil|Hcons].
      - subst effsT. simpl in HcorrHead.
        eapply eff_ctx_corr_one_ctx_upd_at with (effs':=nil)
          (e:=heap_defs_effs x hds).
        + exact HxE.
        + exact HcorrHead.
        + eapply free_sub_heap_fresh. exact HfreeHead.
        + intros p Hin. inversion Hin.
        + intros p Hp Hin. rewrite in_from_list in Hin. inversion Hin.
        + intros p Hp. rewrite in_from_list in Hp |- *.
          eapply heap_defs_effs_update_in; [exact Hdu|exact Hp].
        + eapply free_sub_heap_bound_effs;
            [exact HfreeHead|exact HbS|exact HxE].
      - subst effsT. simpl in HcorrHead.
        eapply eff_ctx_corr_one_ctx_upd_at with (effs':=((x,a)::nil)%list)
          (e:=heap_defs_effs x hds).
        + exact HxE.
        + exact HcorrHead.
        + eapply free_sub_heap_fresh. exact HfreeHead.
        + intros p Hin. simpl in Hin.
          destruct p as [z l]. simpl in *. destruct Hin as [Heq|[]].
          injection Heq as -> ->. reflexivity.
        + intros p Hp Hin.
          rewrite in_from_list in Hp. rewrite in_from_list in Hin.
          simpl in Hin. destruct p as [z l]. simpl in *.
          destruct Hin as [Heq|[]]. injection Heq as Hx Ha. subst z l.
          exact (@defs_update_not_none hds hds' a y Hdu Huniq
                   (@heap_defs_effs_in_inv x a hds' Hp)).
        + intros p Hp. rewrite in_from_list in Hp |- *.
          eapply heap_defs_effs_update_in; [exact Hdu|exact Hp].
        + eapply free_sub_heap_bound_effs;
            [exact HfreeHead|exact HbS|exact HxE]. }
    assert (HcorrNew : eff_ctx_corr
              (ctx_upd x (heap_defs_effs x hds') ℰ ::
                 List.map (ctx_upd x (heap_defs_effs x hds')) ℰs)
              (effsS :: effss0)).
    { eapply eff_ctx_corr_cons.
      - exact HcorrTail'.
      - exact HcorrHead'. }
    exists (empty:ctx), D,
      (ctx_upd x (heap_defs_effs x hds') ℰ ::
         List.map (ctx_upd x (heap_defs_effs x hds')) ℰs),
      (effsS :: effss0).
    rewrite concat_empty_r.
    apply (@ty_config_c G D (S1 & x ~ item_obj T hds' & S2)
             (ctx_upd x (heap_defs_effs x hds') ℰ)
             (List.map (ctx_upd x (heap_defs_effs x hds')) ℰs)
             Fs (trm_var (avar_f y)) Ts free U nil effsS effss0).
    + exact Hinert.
    + exact Hinits.
    + exact Hhc'.
    + exact HfsNew.
    + exact HstackNew.
    + exact HyTs.
    + apply eff_ignore.
    + exact HinitY.
    + exact HcorrNew.
Qed.

End Params.

(* ==== AppCaseParam ==== *)


Section Params.

Hypothesis Hbind_all : forall (G:ctx) (f:var) (T0:typ) (S U:typ),
  inert G ->
  binds f T0 G ->
  inert_typ T0 ->
  G ⊢ trm_var (avar_f f) ∶ typ_all S U ->
  exists Sf Uf, T0 = typ_all Sf Uf /\
                G ⊢ typ_all Sf Uf <: typ_all S U.

Hypothesis Hall_inv : forall (G:ctx) (Sf Uf S U:typ),
  inert G ->
  G ⊢ typ_all Sf Uf <: typ_all S U ->
  exists L, G ⊢ S <: Sf /\
            (forall x, x \notin L -> G & x ~ S ⊢ open x Uf <: open x U).

Lemma ty_config_red_app : forall (G:ctx) (D:init_ctx) (Es:list eff_ctx)
  (effss:list effects) (Fs:stack) (Sigma:heap) (U:typ)
  (f z:var) (Tf:typ) (tf:trm),
  ty_config G D Es effss (trm_app (avar_f f) (avar_f z) ; Fs ; Sigma) U ->
  binds f (item_lit (lit_fun Tf tf)) Sigma ->
  exists G' D' Es' effss',
    ty_config (G & G') D' Es' effss' (open z tf ; Fs ; Sigma) U.
Proof.
  intros G D Es effss Fs Sigma U f z Tf tf Hcfg Hbitem.
  destruct (@ty_config_inv_s G D Es effss (trm_app (avar_f f) (avar_f z)) Fs Sigma U Hcfg) as
    (ℰ & ℰs & Ts & ii & effs & effs' & effss0 &
     HeqEs & HeqEffs & Hinert & Hinits & Hhc & Hfs & Hstack & Hty & Heff & Hinit & Hcorr).
  assert (Heffnil : effs' = nil) by (eapply eff_trm_app_nil; exact Heff).
  subst effs'. cbn in Hcorr. cbn in HeqEffs.
  destruct (@ty_app_inv G f z Ts Hty) as [S [Ut [Hfapp [HzS HopenSub]]]].
  destruct (@heap_correspond_lit G Sigma f (lit_fun Tf tf) Hhc Hbitem) as [T0 [HfG HlitTy]].
  assert (HinertT0 : inert_typ T0) by (eapply inert_binds_inert_typ; eassumption).
  destruct (@Hbind_all G f T0 S Ut Hinert HfG HinertT0 Hfapp)
    as [Sf [Uf [HeqT0 HsubAll]]].
  destruct (@ty_lit_fun_type_inv G Tf tf T0 HlitTy) as [Ubody HeqBody].
  assert (HeqAll : typ_all Tf Ubody = typ_all Sf Uf) by (rewrite <- HeqBody; exact HeqT0).
  injection HeqAll as HeqSf HeqUf. subst Sf Uf.
  rewrite HeqBody in HlitTy.
  assert (HbodyTy : exists L, forall x, x \notin L ->
            G & x ~ Tf ⊢ open x tf ∶ open x Ubody)
    by (eapply ty_lit_fun_body; exact HlitTy).
  destruct HbodyTy as [Lb HbodyTy].
  destruct (@Hall_inv G Tf Ubody S Ut Hinert HsubAll) as [La [HSsub HbodySub]].
  assert (HzTf : G ⊢ trm_var (avar_f z) ∶ Tf)
    by (eapply ty_sub; [exact HzS|exact HSsub]).
  assert (HopenTy : G ⊢ open z tf ∶ open z Ubody)
    by (eapply @ty_all_intro_open with (L:=Lb) (G:=G) (S:=Tf) (U:=Ubody) (t:=tf) (a:=z);
        [exact HbodyTy|exact HzTf]).
  assert (HopenSubU : G ⊢ open z Ubody <: open z Ut)
    by (eapply @subtyp_all_inst with (L:=La) (G:=G) (S2:=S) (U1:=Ubody) (U2:=Ut) (z:=z);
        [exact HbodySub|exact HzS]).
  assert (HopenUt : G ⊢ open z Ubody <: open z Ut) by exact HopenSubU.
  assert (HyTs : G ⊢ open z tf ∶ Ts).
  { eapply ty_sub; [exact HopenTy|].
    eapply subtyp_trans; [exact HopenSubU|exact HopenSub]. }
  destruct (@init_app_commit G D (dom ℰ) f z ii Hinit) as [Hi Hcapp].
  subst ii.
  destruct (@commit_app_binds G D f z Hcapp) as [Hfcomm Hzcomm].
  pose proof (@free_sub_heaps_well_committed G D Sigma (ℰ :: ℰs) Hfs) as Hwc.
  pose proof (@well_committed_heap_item G D Sigma f (item_lit (lit_fun Tf tf)) Hwc Hfcomm Hbitem) as Hci.
  pose proof (@committed_heap_item_lit_inv G D (lit_fun Tf tf) Hci) as Hclit.
  destruct (@commit_lit_fun_body G D Tf tf Hclit) as [Lc HcommitBody].
  assert (HcommitOpen : G ⸴ D ⊢c open z tf)
    by (eapply @commit_all_intro_open with (L:=Lc) (G:=G) (D:=D) (S:=Tf) (t:=tf) (a:=z);
        [exact HcommitBody|exact HzTf|exact Hzcomm]).
  exists (empty:ctx), D, (ℰ :: ℰs), (effs :: effss0).
  rewrite concat_empty_r.
  eapply (@ty_config_c G D Sigma ℰ ℰs Fs (open z tf) Ts committed U nil effs effss0).
  - exact Hinert.
  - exact Hinits.
  - exact Hhc.
  - exact Hfs.
  - exact Hstack.
  - exact HyTs.
  - apply eff_ignore.
  - eapply init_commit. exact HcommitOpen.
  - exact Hcorr.
Qed.

End Params.

(* ==== ProgressParam ==== *)


Section Params.

Hypothesis Hsel_heap : forall (G:ctx) (D:init_ctx) (Sigma:heap) (Es:list eff_ctx)
  (x:var) (a:trm_label) (S U:typ),
  inert G ->
  heap_correspond G Sigma ->
  free_sub_heaps G D Sigma Es ->
  binds x committed D ->
  G ⊢ trm_var (avar_f x) ∶ typ_rcd (dec_trm a S U) ->
  exists T hds y, binds x (item_obj T hds) Sigma /\
                  labels_has hds (heap_def_trm a (Some y)).

Hypothesis Hasn_heap : forall (G:ctx) (Sigma:heap) (x:var) (a:trm_label) (y:var) (S U:typ),
  inert G ->
  heap_correspond G Sigma ->
  G ⊢ trm_var (avar_f x) ∶ typ_rcd (dec_trm a S U) ->
  exists T hds hds', binds x (item_obj T hds) Sigma /\ defs_update hds a y hds'.

Hypothesis Happ_heap : forall (G:ctx) (Sigma:heap) (f:var) (S U:typ),
  inert G ->
  heap_correspond G Sigma ->
  G ⊢ trm_var (avar_f f) ∶ typ_all S U ->
  exists Tf tf, binds f (item_lit (lit_fun Tf tf)) Sigma.

Hypothesis Hnew_heap : forall (G:ctx) (Sigma:heap) (f:var) (Ts:typs) (is':inits) (X:typ),
  inert G ->
  heap_correspond G Sigma ->
  G ⊢ trm_var (avar_f f) ∶ typ_con Ts is' X ->
  exists Ts0 is0 X0 ds t,
    binds f (item_lit (lit_con Ts0 is0 X0 ds t)) Sigma /\
    Ts0 = Ts /\ is0 = is' /\ X0 = X.

Lemma progress_from_cases : forall (G:ctx) (D:init_ctx) (EsC:list eff_ctx)
  (EsE:list effects) (t:trm) (s:stack) (Sigma:heap) (U:typ),
  ty_config G D EsC EsE (t ; s ; Sigma) U ->
  answer (t ; s ; Sigma) \/
  exists s' Sigma' t', (t ; s ; Sigma) ↦ (t' ; s' ; Sigma').
Proof.
  intros G D EsC EsE t s Sigma U Hcfg.
  destruct t as [a | a m | a az | T t1 t2 | T l t1 | a m c | a avs].
  - (* trm_var *)
    destruct a as [n|y].
    + destruct (@ty_config_inv_s G D EsC EsE (trm_var (avar_b n)) s Sigma U Hcfg) as
        (ℰ & ℰs & Ts & ii & effs & effs' & effss0 &
         HeqEs & HeqEffs & Hinert & Hinits & Hhc & Hfs & Hstack & Hty & Heff & Hinit & Hcorr).
      exfalso. eapply ty_var_b_false; exact Hty.
    + eapply progress_trm_var; exact Hcfg.
  - (* trm_sel *)
    destruct a as [n|x].
    + destruct (@ty_config_inv_s G D EsC EsE (trm_sel (avar_b n) m) s Sigma U Hcfg) as
        (ℰ & ℰs & Ts & ii & effs & effs' & effss0 &
         HeqEs & HeqEffs & Hinert & Hinits & Hhc & Hfs & Hstack & Hty & Heff & Hinit & Hcorr).
      exfalso. eapply ty_sel_b_false; exact Hty.
    + destruct (@ty_config_inv_s G D EsC EsE (trm_sel (avar_f x) m) s Sigma U Hcfg) as
        (ℰ & ℰs & Ts & ii & effs & effs' & effss0 &
         HeqEs & HeqEffs & Hinert & Hinits & Hhc & Hfs & Hstack & Hty & Heff & Hinit & Hcorr).
      destruct (@ty_sel_inv G x m Ts Hty) as [S [T0 [Hxrec Hsub]]].
      destruct (@init_typing_sel_committed G D (dom ℰ) x m ii Hinit) as [Hi Hxcomm].
      destruct (@Hsel_heap G D Sigma (ℰ :: ℰs) x m S T0 Hinert Hhc Hfs Hxcomm Hxrec)
        as [T [hds [y [Hbinds Hlab]]]].
      right. exists s, Sigma, (trm_var (avar_f y)). eapply red_sel; eassumption.
  - (* trm_app *)
    destruct a as [n|f].
    + destruct az as [n2|z].
      * destruct (@ty_config_inv_s G D EsC EsE (trm_app (avar_b n) (avar_b n2)) s Sigma U Hcfg) as
        (ℰ & ℰs & Ts & ii & effs & effs' & effss0 &
         HeqEs & HeqEffs & Hinert & Hinits & Hhc & Hfs & Hstack & Hty & Heff & Hinit & Hcorr).
      exfalso. eapply ty_app_bf_false; exact Hty.
      * destruct (@ty_config_inv_s G D EsC EsE (trm_app (avar_b n) (avar_f z)) s Sigma U Hcfg) as
        (ℰ & ℰs & Ts & ii & effs & effs' & effss0 &
         HeqEs & HeqEffs & Hinert & Hinits & Hhc & Hfs & Hstack & Hty & Heff & Hinit & Hcorr).
      exfalso. eapply ty_app_bf_false; exact Hty.
    + destruct az as [n2|z].
      * destruct (@ty_config_inv_s G D EsC EsE (trm_app (avar_f f) (avar_b n2)) s Sigma U Hcfg) as
        (ℰ & ℰs & Ts & ii & effs & effs' & effss0 &
         HeqEs & HeqEffs & Hinert & Hinits & Hhc & Hfs & Hstack & Hty & Heff & Hinit & Hcorr).
      exfalso. eapply ty_app_bz_false; exact Hty.
      * destruct (@ty_config_inv_s G D EsC EsE (trm_app (avar_f f) (avar_f z)) s Sigma U Hcfg) as
          (ℰ & ℰs & Ts & ii & effs & effs' & effss0 &
           HeqEs & HeqEffs & Hinert & Hinits & Hhc & Hfs & Hstack & Hty & Heff & Hinit & Hcorr).
        destruct (@ty_app_inv G f z Ts Hty) as [S [Ut [Hfapp [HzS Hsub]]]].
        destruct (@Happ_heap G Sigma f S Ut Hinert Hhc Hfapp) as [Tf [tf Hbinds]].
        right. exists s, Sigma, (open z tf). eapply red_app; exact Hbinds.
  - (* trm_let *) eapply progress_trm_let; exact Hcfg.
  - (* trm_lit *) eapply progress_trm_lit; exact Hcfg.
  - (* trm_asn *)
    destruct a as [n|x].
    + destruct c as [n2|y].
      * destruct (@ty_config_inv_s G D EsC EsE (trm_asn (avar_b n) m (avar_b n2)) s Sigma U Hcfg) as
        (ℰ & ℰs & Ts & ii & effs & effs' & effss0 &
         HeqEs & HeqEffs & Hinert & Hinits & Hhc & Hfs & Hstack & Hty & Heff & Hinit & Hcorr).
      exfalso. eapply ty_asn_bx_false; exact Hty.
      * destruct (@ty_config_inv_s G D EsC EsE (trm_asn (avar_b n) m (avar_f y)) s Sigma U Hcfg) as
        (ℰ & ℰs & Ts & ii & effs & effs' & effss0 &
         HeqEs & HeqEffs & Hinert & Hinits & Hhc & Hfs & Hstack & Hty & Heff & Hinit & Hcorr).
      exfalso. eapply ty_asn_bx_false; exact Hty.
    + destruct c as [n2|y].
      * destruct (@ty_config_inv_s G D EsC EsE (trm_asn (avar_f x) m (avar_b n2)) s Sigma U Hcfg) as
        (ℰ & ℰs & Ts & ii & effs & effs' & effss0 &
         HeqEs & HeqEffs & Hinert & Hinits & Hhc & Hfs & Hstack & Hty & Heff & Hinit & Hcorr).
      exfalso. eapply ty_asn_bz_false; exact Hty.
      * destruct (@ty_config_inv_s G D EsC EsE (trm_asn (avar_f x) m (avar_f y)) s Sigma U Hcfg) as
          (ℰ & ℰs & Ts & ii & effs & effs' & effss0 &
           HeqEs & HeqEffs & Hinert & Hinits & Hhc & Hfs & Hstack & Hty & Heff & Hinit & Hcorr).
        destruct (@ty_asn_inv G x m y Ts Hty) as [S [T0 [Hxrec [HyS Hsub]]]].
        destruct (@Hasn_heap G Sigma x m y S T0 Hinert Hhc Hxrec) as [T [hds [hds' [Hbinds Hdu]]]].
        destruct (@binds_split_fresh item Sigma x (item_obj T hds) Hbinds) as [S1 [S2 [Heq Hfresh]]].
        right. exists s, (S1 & x ~ item_obj T hds' & S2), (trm_var (avar_f y)).
        eapply red_asn. unfold heap_update.
        exists T, hds, hds', S1, S2. repeat split; try assumption; try reflexivity.
  - (* trm_new *)
    destruct a as [n|f];
      try (destruct (@ty_config_inv_s G D EsC EsE (trm_new (avar_b n) avs) s Sigma U Hcfg) as
             (ℰ & ℰs & Ts & ii & effs & effs' & effss0 &
              HeqEs & HeqEffs & Hinert & Hinits & Hhc & Hfs & Hstack & Hty & Heff & Hinit & Hcorr);
           exfalso; eapply ty_new_bf_false; exact Hty).
    destruct (@ty_config_inv_s G D EsC EsE (trm_new (avar_f f) avs) s Sigma U Hcfg) as
      (ℰ & ℰs & Ts & ii & effs & effs' & effss0 &
       HeqEs & HeqEffs & Hinert & Hinits & Hhc & Hfs & Hstack & Hty & Heff & Hinit & Hcorr).
    destruct (@ty_new_inv G f avs Ts Hty) as [Tsc [isc [Xc [xs [Hfapp [Havs [Hvars Hsub]]]]]]].
    destruct (@Hnew_heap G Sigma f Tsc isc Xc Hinert Hhc Hfapp)
      as [Ts0 [is0 [X0 [ds [tb [Hbinds [HTs [His HX]]]]]]]].
    subst Ts0 is0 X0.
    assert (HlenAvs : List.length avs = length_s Tsc).
    { eapply ty_avars_length; exact Havs. }
    assert (HlenXs : List.length xs = length_s Tsc).
    { rewrite <- HlenAvs. eapply vars_of_avars_length; exact Hvars. }
    destruct (@var_fresh (dom Sigma \u fv (open_rec_vars 1 xs ds))) as [x Hx].
    pose proof (notin_union_r1 Hx) as HxSigma.
    pose proof (notin_union_r2 Hx) as Hxfv.
    right. exists (frame_ret x :: s),
      (Sigma & x ~ (item_obj (open_rec_vars 1 xs Xc)
                    (open_vars (cons x xs) (heap_defs_of_defs ds)))),
      (open_vars (cons x xs) tb).
    eapply red_new with (Ts:=Tsc) (is':=isc) (T:=Xc) (ds:=ds) (t:=tb)
                       (Sigma:=Sigma) (x:=x) (c:=f) (ys:=xs) (avs:=avs) (fs:=s).
    + exact HxSigma.
    + exact Hxfv.
    + exact Hbinds.
    + exact HlenXs.
    + exact Hvars.
Qed.

End Params.


(* ==== PreservationFinalParam ==== *)


Section Final.

Hypothesis Hfield : forall (G:ctx) (V:typ) (a:trm_label) (Tf S U:typ),
  inert G ->
  record_type V ->
  record_has V (dec_trm a Tf Tf) ->
  G ⊢ V <: typ_rcd (dec_trm a S U) ->
  G ⊢ Tf <: U.

Hypothesis Hroot : forall (G:ctx) (x:var) (U:typ) (D:dec),
  inert G ->
  binds x (typ_bnd U) G ->
  G ⊢ trm_var (avar_f x) ∶ typ_rcd D ->
  G ⊢ open x U <: typ_rcd D.

Hypothesis Hcov : forall (G:ctx) (V:typ) (a:trm_label) (Tf S U:typ),
  inert G ->
  record_type V ->
  record_has V (dec_trm a Tf Tf) ->
  G ⊢ V <: typ_rcd (dec_trm a S U) ->
  G ⊢ Tf <: U.

Hypothesis Hcontr : forall (G:ctx) (V:typ) (a:trm_label) (Tf S U:typ),
  inert G ->
  record_type V ->
  record_has V (dec_trm a Tf Tf) ->
  G ⊢ V <: typ_rcd (dec_trm a S U) ->
  G ⊢ S <: Tf.

Hypothesis Hbind_all : forall (G:ctx) (f:var) (T0:typ) (S U:typ),
  inert G ->
  binds f T0 G ->
  inert_typ T0 ->
  G ⊢ trm_var (avar_f f) ∶ typ_all S U ->
  exists Sf Uf, T0 = typ_all Sf Uf /\
                G ⊢ typ_all Sf Uf <: typ_all S U.

Hypothesis Hall_inv : forall (G:ctx) (Sf Uf S U:typ),
  inert G ->
  G ⊢ typ_all Sf Uf <: typ_all S U ->
  exists L, G ⊢ S <: Sf /\
            (forall x, x \notin L -> G & x ~ S ⊢ open x Uf <: open x U).

Hypothesis Hnew_case : forall (G:ctx) (D:init_ctx) (Es:list eff_ctx)
  (effss:list effects) (Fs:stack) (Sigma Sigma':heap) (U:typ)
  (f:var) (avs:avars) (Ts:typs) (is':inits) (X:typ) (ds:defs) (tb:trm)
  (x:var) (ys:list var),
  ty_config G D Es effss (trm_new (avar_f f) avs ; Fs ; Sigma) U ->
  binds f (item_lit (lit_con Ts is' X ds tb)) Sigma ->
  x # Sigma ->
  x \notin fv (open_rec_vars 1 ys ds) ->
  List.length ys = length_s Ts ->
  vars_of_avars ys avs ->
  Sigma' = (Sigma & x ~ (item_obj (open_rec_vars 1 ys X)
                          (open_vars (cons x ys) (heap_defs_of_defs ds)))) ->
  exists G' D' Es' effss',
    ty_config (G & G') D' Es' effss'
      (open_vars (cons x ys) tb ; (frame_ret x :: Fs)%list ; Sigma') U.

Theorem preservation_from_cases : forall (G:ctx) (D:init_ctx) (Es:list eff_ctx)
  (effss:list effects) (c c':config) (U:typ),
  ty_config G D Es effss c U ->
  c ↦ c' ->
  exists G' D' Es' effss', ty_config (G & G') D' Es' effss' c' U.
Proof.
  intros G D Es effss c c' U Hcfg Hred.
  inversion Hred; subst.
  - eapply ty_config_red_sel; eassumption.
  - eapply ty_config_red_asn; eassumption.
  - eapply ty_config_red_app; eassumption.
  - eapply (@ty_config_red_let_lit G D Es effss fs committed nil Sigma U T l t x); [exact Hcfg|exact H].
  - eapply (@Hnew_case G D Es effss fs Sigma
      (Sigma & x ~ (item_obj (open_rec_vars 1 ys T)
                    (open_vars (cons x ys) (heap_defs_of_defs ds)))) U
      c0 avs Ts is' T ds t x ys).
    + exact Hcfg.
    + exact H1.
    + exact H.
    + exact H0.
    + exact H2.
    + exact H3.
    + reflexivity.
  - eapply (@ty_config_red_return G D Es effss fs Sigma U (trm_var (avar_f x)) y x).
    exact Hcfg.
  - eapply ty_config_red_let_var; eassumption.
  - eapply (@ty_config_red_let_sta G D Es effss fs committed nil Sigma U T s t);
    exact Hcfg.
Qed.

End Final.


(* ==== DefsUpdate ==== *)


Lemma defs_update_exists_of_mem : forall (hds:heap_defs) (a:trm_label) (y:var),
  (exists o, List.In (heap_def_trm a o) hds) ->
  exists hds', defs_update hds a y hds'.
Proof.
  intros hds. induction hds as [|d hds IH]; intros a y Hmem.
  - destruct Hmem as [o Hin]. inversion Hin.
  - destruct Hmem as [o Hin]. simpl in Hin.
    destruct d as [A T|l o0].
    + destruct Hin as [Heq|Hin].
      * discriminate Heq.
      * destruct (IH a y (ex_intro _ o Hin)) as [hds' Hup].
        exists (heap_def_typ A T :: hds').
        eapply defs_update_push. exact Hup.
    + destruct (classic (l = a)) as [Heqla|Hne].
      * subst l. exists (heap_def_trm a (Some y) :: hds).
        apply defs_update_var.
      * destruct Hin as [Heq|Hin].
        -- inversion Heq; subst. exfalso. apply Hne. reflexivity.
        -- destruct (IH a y (ex_intro _ o Hin)) as [hds' Hup].
           exists (heap_def_trm l o0 :: hds').
           eapply defs_update_push. exact Hup.
Qed.

Lemma heap_update_exists : forall (Sigma:heap) (x:var) (a:trm_label) (y:var),
  (exists T hds, binds x (item_obj T hds) Sigma /\
                 (exists o, List.In (heap_def_trm a o) hds)) ->
  exists Sigma', heap_update Sigma x a y Sigma'.
Proof.
  intros Sigma x a y [T [hds [Hbinds [o Hin]]]].
  destruct (@defs_update_exists_of_mem hds a y (ex_intro _ o Hin)) as [hds' Hup].
  destruct (@binds_split_fresh item Sigma x (item_obj T hds) Hbinds) as [S1 [S2 [Heq Hfresh]]].
  exists (S1 & x ~ item_obj T hds' & S2).
  unfold heap_update. exists T, hds, hds', S1, S2.
  repeat split; try assumption; try reflexivity.
Qed.


(* ==== ExtractParam ==== *)


Section Params.

Hypothesis Hroot : forall (G:ctx) (x:var) (U:typ) (D:dec),
  inert G ->
  binds x (typ_bnd U) G ->
  G ⊢ trm_var (avar_f x) ∶ typ_rcd D ->
  G ⊢ open x U <: typ_rcd D.

Hypothesis Hbind_shape : forall (G:ctx) (x:var) (T0:typ) (D:dec),
  inert G ->
  binds x T0 G ->
  inert_typ T0 ->
  G ⊢ trm_var (avar_f x) ∶ typ_rcd D ->
  exists U, T0 = typ_bnd U.

Hypothesis Hfield_exists : forall (G:ctx) (V:typ) (a:trm_label) (S U:typ),
  inert G ->
  record_type V ->
  G ⊢ V <: typ_rcd (dec_trm a S U) ->
  exists Tf, record_has V (dec_trm a Tf Tf).

Hypothesis Hcov : forall (G:ctx) (V:typ) (a:trm_label) (Tf S U:typ),
  inert G ->
  record_type V ->
  record_has V (dec_trm a Tf Tf) ->
  G ⊢ V <: typ_rcd (dec_trm a S U) ->
  G ⊢ Tf <: U.

Hypothesis Hcontr : forall (G:ctx) (V:typ) (a:trm_label) (Tf S U:typ),
  inert G ->
  record_type V ->
  record_has V (dec_trm a Tf Tf) ->
  G ⊢ V <: typ_rcd (dec_trm a S U) ->
  G ⊢ S <: Tf.

Hypothesis Hbind_all : forall (G:ctx) (f:var) (T0:typ) (S U:typ),
  inert G ->
  binds f T0 G ->
  inert_typ T0 ->
  G ⊢ trm_var (avar_f f) ∶ typ_all S U ->
  exists Sf Uf, T0 = typ_all Sf Uf /\
                G ⊢ typ_all Sf Uf <: typ_all S U.

Hypothesis Hbind_con : forall (G:ctx) (f:var) (T0:typ) (Ts:typs) (is':inits) (X:typ),
  inert G ->
  binds f T0 G ->
  inert_typ T0 ->
  G ⊢ trm_var (avar_f f) ∶ typ_con Ts is' X ->
  T0 = typ_con Ts is' X.

Lemma heap_item_obj_of_var : forall (G:ctx) (Sigma:heap) (x:var) (T:typ) (D:dec),
  inert G ->
  heap_correspond G Sigma ->
  G ⊢ trm_var (avar_f x) ∶ T ->
  G ⊢ trm_var (avar_f x) ∶ typ_rcd D ->
  exists U hds, binds x (item_obj U hds) Sigma /\
                G ⊢ hds ∶ open x U.
Proof.
  intros G Sigma x T D Hinert Hhc Hty Hxrec.
  assert (HinG : x \in dom G) by (eapply ty_var_dom; exact Hty).
  assert (HinS : x \in dom Sigma).
  { rewrite <- (@heap_correspond_dom G Sigma Hhc). exact HinG. }
  destruct (@dom_binds_exists item Sigma x HinS) as [itm Hbinds].
  destruct itm as [U hds|l].
  - destruct (@heap_correspond_obj G Sigma x U hds Hhc Hbinds) as [HxG Hhds].
    exists U, hds. split; assumption.
  - destruct (@heap_correspond_lit G Sigma x l Hhc Hbinds) as [T0 [HbG Hlit]].
    assert (HiT0 : inert_typ T0) by (eapply inert_binds_inert_typ; eassumption).
    destruct (@Hbind_shape G x T0 D Hinert HbG HiT0 Hxrec) as [U Heq].
    pose proof (@ty_lit_shape G l T0 Hlit) as Hshape.
    destruct Hshape as [[S [U2 HeqAll]]|[Ts [is' [X HeqCon]]]].
    + rewrite HeqAll in Heq. discriminate Heq.
    + rewrite HeqCon in Heq. discriminate Heq.
Qed.

Lemma field_in_heap : forall (G:ctx) (Sigma:heap) (x:var) (U:typ) (hds:heap_defs)
  (a:trm_label) (S T0:typ),
  inert G ->
  G ⊢ hds ∶ open x U ->
  G ⊢ open x U <: typ_rcd (dec_trm a S T0) ->
  record_type (open x U) ->
  exists Tf o, record_has (open x U) (dec_trm a Tf Tf) /\
               List.In (heap_def_trm a o) hds.
Proof.
  intros G Sigma x U hds a S T0 Hinert Hhds Hsub Hrt.
  destruct (@Hfield_exists G (open x U) a S T0 Hinert Hrt Hsub) as [Tf Hrh].
  destruct (@ty_heap_defs_correspond G hds (open x U) Hhds) as (ls & Hrt' & Hfwd & Hbwd).
  destruct (Hbwd (dec_trm a Tf Tf) Hrh) as [d [Hin Hlab]].
  destruct d as [A Td|l o].
  - simpl in Hlab. discriminate Hlab.
  - exists Tf, o. split; [exact Hrh|].
    simpl in Hlab. injection Hlab as Hl. subst l. exact Hin.
Qed.

Lemma Hsel_heap_proof : forall (G:ctx) (D:init_ctx) (Sigma:heap) (Es:list eff_ctx)
  (x:var) (a:trm_label) (S U:typ),
  inert G ->
  heap_correspond G Sigma ->
  free_sub_heaps G D Sigma Es ->
  binds x committed D ->
  G ⊢ trm_var (avar_f x) ∶ typ_rcd (dec_trm a S U) ->
  exists T hds y, binds x (item_obj T hds) Sigma /\
                  labels_has hds (heap_def_trm a (Some y)).
Proof.
  intros G D Sigma Es x a S U Hinert Hhc Hfs Hxcomm Hxrec.
  destruct (@heap_item_obj_of_var G Sigma x (typ_rcd (dec_trm a S U))
              (dec_trm a S U) Hinert Hhc Hxrec Hxrec) as [T [hds [Hbinds Hhds]]].
  pose proof (@ty_heap_defs_record_type G hds (open x T) Hhds) as Hrt.
  pose proof (@heap_correspond_obj G Sigma x T hds Hhc Hbinds) as [HxG _].
  assert (Hsub : G ⊢ open x T <: typ_rcd (dec_trm a S U)) by (eapply Hroot; eassumption).
  destruct (@field_in_heap G Sigma x T hds a S U Hinert Hhds Hsub Hrt)
    as [Tf [o [Hrh Hin]]].
  assert (Hcdefs : committed_heap_defs D hds).
  { pose proof (@free_sub_heaps_well_committed G D Sigma Es Hfs) as Hwc.
    pose proof (@well_committed_heap_item G D Sigma x (item_obj T hds) Hwc Hxcomm Hbinds) as Hci.
    eapply committed_heap_item_obj_inv. exact Hci. }
  pose proof (@committed_heap_defs_in D hds (heap_def_trm a o) Hcdefs Hin) as Hcd.
  destruct o as [y|].
  - exists T, hds, y. split; [exact Hbinds|].
    eapply (@labels_has_in heap_def HeapDefLabelOf hds (heap_def_trm a (Some y))).
    + intros d1 d2 I1 I2 E. eapply (@ty_heap_defs_label_unique G hds (open x T) Hhds);
        eassumption.
    + exact Hin.
  - exfalso. eapply (@committed_heap_def_trm_none_false D a). exact Hcd.
Qed.

Lemma Hasn_heap_proof : forall (G:ctx) (Sigma:heap) (x:var) (a:trm_label) (y:var) (S U:typ),
  inert G ->
  heap_correspond G Sigma ->
  G ⊢ trm_var (avar_f x) ∶ typ_rcd (dec_trm a S U) ->
  exists T hds hds', binds x (item_obj T hds) Sigma /\ defs_update hds a y hds'.
Proof.
  intros G Sigma x a y S U Hinert Hhc Hxrec.
  destruct (@heap_item_obj_of_var G Sigma x (typ_rcd (dec_trm a S U))
              (dec_trm a S U) Hinert Hhc Hxrec Hxrec) as [T [hds [Hbinds Hhds]]].
  pose proof (@ty_heap_defs_record_type G hds (open x T) Hhds) as Hrt.
  pose proof (@heap_correspond_obj G Sigma x T hds Hhc Hbinds) as [HxG _].
  assert (Hsub : G ⊢ open x T <: typ_rcd (dec_trm a S U)) by (eapply Hroot; eassumption).
  destruct (@field_in_heap G Sigma x T hds a S U Hinert Hhds Hsub Hrt)
    as [Tf [o [Hrh Hin]]].
  destruct (@defs_update_exists_of_mem hds a y (ex_intro _ o Hin)) as [hds' Hup].
  exists T, hds, hds'. split; assumption.
Qed.

Lemma Happ_heap_proof : forall (G:ctx) (Sigma:heap) (f:var) (S U:typ),
  inert G ->
  heap_correspond G Sigma ->
  G ⊢ trm_var (avar_f f) ∶ typ_all S U ->
  exists Tf tf, binds f (item_lit (lit_fun Tf tf)) Sigma.
Proof.
  intros G Sigma f S U Hinert Hhc Hfapp.
  assert (HinG : f \in dom G) by (eapply ty_var_dom; exact Hfapp).
  assert (HinS : f \in dom Sigma).
  { rewrite <- (@heap_correspond_dom G Sigma Hhc). exact HinG. }
  destruct (@dom_binds_exists item Sigma f HinS) as [itm Hbinds].
  destruct itm as [U0 hds|l].
  - destruct (@heap_correspond_obj G Sigma f U0 hds Hhc Hbinds) as [HfG _].
    assert (Hi : inert_typ (typ_bnd U0)) by (eapply inert_binds_inert_typ; eassumption).
    destruct (@Hbind_all G f (typ_bnd U0) S U Hinert HfG Hi Hfapp)
      as [Sf [Uf [Heq _]]].
    discriminate Heq.
  - destruct (@heap_correspond_lit G Sigma f l Hhc Hbinds) as [T0 [HfG Hlit]].
    assert (Hi : inert_typ T0) by (eapply inert_binds_inert_typ; eassumption).
    destruct (@Hbind_all G f T0 S U Hinert HfG Hi Hfapp) as [Sf [Uf [Heq _]]].
    subst T0.
    destruct (@ty_lit_all_inv G l Sf Uf Hlit) as [Tf [tf Heql]].
    exists Tf, tf. subst l. exact Hbinds.
Qed.

Lemma Hnew_heap_proof : forall (G:ctx) (Sigma:heap) (f:var) (Ts:typs) (is':inits) (X:typ),
  inert G ->
  heap_correspond G Sigma ->
  G ⊢ trm_var (avar_f f) ∶ typ_con Ts is' X ->
  exists Ts0 is0 X0 ds t,
    binds f (item_lit (lit_con Ts0 is0 X0 ds t)) Sigma /\
    Ts0 = Ts /\ is0 = is' /\ X0 = X.
Proof.
  intros G Sigma f Ts is' X Hinert Hhc Hfapp.
  assert (HinG : f \in dom G) by (eapply ty_var_dom; exact Hfapp).
  assert (HinS : f \in dom Sigma).
  { rewrite <- (@heap_correspond_dom G Sigma Hhc). exact HinG. }
  destruct (@dom_binds_exists item Sigma f HinS) as [itm Hbinds].
  destruct itm as [U0 hds|l].
  - destruct (@heap_correspond_obj G Sigma f U0 hds Hhc Hbinds) as [HfG _].
    assert (Hi : inert_typ (typ_bnd U0)) by (eapply inert_binds_inert_typ; eassumption).
    pose proof (@Hbind_con G f (typ_bnd U0) Ts is' X Hinert HfG Hi Hfapp) as Heq.
    discriminate Heq.
  - destruct (@heap_correspond_lit G Sigma f l Hhc Hbinds) as [T0 [HfG Hlit]].
    assert (Hi : inert_typ T0) by (eapply inert_binds_inert_typ; eassumption).
    pose proof (@Hbind_con G f T0 Ts is' X Hinert HfG Hi Hfapp) as Heq. subst T0.
    destruct (@ty_lit_con_inv G l Ts is' X Hlit) as [ds [tb Heql]].
    exists Ts, is', X, ds, tb. split.
    + subst l. exact Hbinds.
    + split; [reflexivity|split; reflexivity].
Qed.

End Params.

(* ==== ProgressFinalParam ==== *)


Section FinalProgress.

Hypothesis Hroot : forall (G:ctx) (x:var) (U:typ) (D:dec),
  inert G ->
  binds x (typ_bnd U) G ->
  G ⊢ trm_var (avar_f x) ∶ typ_rcd D ->
  G ⊢ open x U <: typ_rcd D.

Hypothesis Hbind_shape : forall (G:ctx) (x:var) (T0:typ) (D:dec),
  inert G ->
  binds x T0 G ->
  inert_typ T0 ->
  G ⊢ trm_var (avar_f x) ∶ typ_rcd D ->
  exists U, T0 = typ_bnd U.

Hypothesis Hfield_exists : forall (G:ctx) (V:typ) (a:trm_label) (S U:typ),
  inert G ->
  record_type V ->
  G ⊢ V <: typ_rcd (dec_trm a S U) ->
  exists Tf, record_has V (dec_trm a Tf Tf).

Hypothesis Hcov : forall (G:ctx) (V:typ) (a:trm_label) (Tf S U:typ),
  inert G ->
  record_type V ->
  record_has V (dec_trm a Tf Tf) ->
  G ⊢ V <: typ_rcd (dec_trm a S U) ->
  G ⊢ Tf <: U.

Hypothesis Hcontr : forall (G:ctx) (V:typ) (a:trm_label) (Tf S U:typ),
  inert G ->
  record_type V ->
  record_has V (dec_trm a Tf Tf) ->
  G ⊢ V <: typ_rcd (dec_trm a S U) ->
  G ⊢ S <: Tf.

Hypothesis Hbind_all : forall (G:ctx) (f:var) (T0:typ) (S U:typ),
  inert G ->
  binds f T0 G ->
  inert_typ T0 ->
  G ⊢ trm_var (avar_f f) ∶ typ_all S U ->
  exists Sf Uf, T0 = typ_all Sf Uf /\
                G ⊢ typ_all Sf Uf <: typ_all S U.

Hypothesis Hbind_con : forall (G:ctx) (f:var) (T0:typ) (Ts:typs) (is':inits) (X:typ),
  inert G ->
  binds f T0 G ->
  inert_typ T0 ->
  G ⊢ trm_var (avar_f f) ∶ typ_con Ts is' X ->
  T0 = typ_con Ts is' X.

Theorem progress_from_canon : forall (G:ctx) (D:init_ctx) (EsC:list eff_ctx)
  (EsE:list effects) (t:trm) (s:stack) (Sigma:heap) (U:typ),
  ty_config G D EsC EsE (t ; s ; Sigma) U ->
  answer (t ; s ; Sigma) \/
  exists s' Sigma' t', (t ; s ; Sigma) ↦ (t' ; s' ; Sigma').
Proof.
  intros G D EsC EsE t s Sigma U Hcfg.
  eapply (@progress_from_cases
    (Hsel_heap_proof Hroot Hbind_shape Hfield_exists)
    (Hasn_heap_proof Hroot Hbind_shape Hfield_exists)
    (Happ_heap_proof Hbind_all)
    (Hnew_heap_proof Hbind_con)).
  exact Hcfg.
Qed.

End FinalProgress.

Set Implicit Arguments.

(** * Target theorems *)

Theorem preservation : forall Gamma Delta ℰs effss c c' U,
    ty_config Gamma Delta ℰs effss c U ->
    c ↦ c' ->
    exists Gamma' Delta' ℰs' effss', ty_config (Gamma & Gamma') Delta' ℰs' effss' c' U.

Theorem progress: forall Gamma Delta ℰs Es t s Sigma T,
    ty_config Gamma Delta ℰs Es (t ; s; Sigma) T ->
    answer (t; s; Sigma) \/
    exists s' Sigma' t', (t; s; Sigma) ↦ (t'; s'; Sigma').
