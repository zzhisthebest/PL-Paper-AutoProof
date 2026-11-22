Require Import AmberBase.
Require Import Metalib.Metatheory.
Require Import Program.Equality.
Require Import Lia.

Definition env_mode := list ( Mode).

Definition eqMode (a b: Mode)  : bool :=
  match a,b with
  | Pos, Pos => true
  | Neg, Neg => true
  | _,_ => false
  end.

Fixpoint amber_cov (Ea : env_amber) (Em : env_mode) (T:typ) (m:Mode) : typ :=
  match Ea, Em with
  | (X,Y)::E, m'::Em' => if (eqMode m' m) then amber_cov E Em' (subst_tt X Y T) m
                         else amber_cov E Em' T m
  | _,_ => T
  end.

(* ================================================================== *)
(* Auxiliary definitions                                              *)
(* ================================================================== *)

Lemma eqMode_refl : forall a, eqMode a a = true.
Proof. destruct a; reflexivity. Qed.

Lemma eqMode_true : forall a b, eqMode a b = true <-> a = b.
Proof.
  destruct a, b; simpl; split; intros H; try discriminate; reflexivity.
Qed.

Lemma amber_cov_nil : forall T m, amber_cov nil nil T m = T.
Proof. intros T m. reflexivity. Qed.

Lemma amber_cov_arrow : forall Ea Em A1 A2 m,
  amber_cov Ea Em (typ_arrow A1 A2) m =
  typ_arrow (amber_cov Ea Em A1 m) (amber_cov Ea Em A2 m).
Proof.
  intros Ea. induction Ea as [| [X Y] Ea IH];
    intros Em A1 A2 m.
  - destruct Em; reflexivity.
  - destruct Em as [|m' Em]; [reflexivity|].
    simpl. destruct (eqMode m' m).
    + simpl. rewrite IH. reflexivity.
    + rewrite IH. reflexivity.
Qed.

Lemma amber_cov_mu : forall Ea Em A m,
  amber_cov Ea Em (typ_mu A) m = typ_mu (amber_cov Ea Em A m).
Proof.
  intros Ea. induction Ea as [| [X Y] Ea IH]; intros Em A m.
  - destruct Em; reflexivity.
  - destruct Em as [|m' Em]; [reflexivity|].
    simpl. destruct (eqMode m' m).
    + simpl. rewrite IH. reflexivity.
    + rewrite IH. reflexivity.
Qed.

Lemma amber_cov_top : forall Ea Em m,
  amber_cov Ea Em typ_top m = typ_top.
Proof.
  intros Ea. induction Ea as [| [X Y] Ea IH]; intros Em m.
  - destruct Em; reflexivity.
  - destruct Em as [|m' Em]; [reflexivity|].
    simpl. destruct (eqMode m' m); apply IH.
Qed.

Lemma amber_cov_nat : forall Ea Em m,
  amber_cov Ea Em typ_nat m = typ_nat.
Proof.
  intros Ea. induction Ea as [| [X Y] Ea IH]; intros Em m.
  - destruct Em; reflexivity.
  - destruct Em as [|m' Em]; [reflexivity|].
    simpl. destruct (eqMode m' m); apply IH.
Qed.

Lemma amber_cov_fvar_fvar : forall Ea Em X m,
  exists Z, amber_cov Ea Em (typ_fvar X) m = typ_fvar Z.
Proof.
  intros Ea. induction Ea as [| [X Y] Ea IH]; intros Em X0 m.
  - destruct Em; simpl; eauto.
  - destruct Em as [|m' Em]; [simpl; eauto|].
    simpl. destruct (eqMode m' m).
    + destruct (X0 == X) as [Heq|Hneq].
      * subst X0. simpl. apply (IH Em Y m).
      * apply (IH Em X0 m).
    + apply (IH Em X0 m).
Qed.

(* Fresh atoms (not the first component of any pair) are left unchanged by
   the mode translation. *)
Lemma amber_cov_fvar_fresh : forall Ea Em Z m,
  (forall X Y, In (X,Y) Ea -> X <> Z) ->
  amber_cov Ea Em (typ_fvar Z) m = typ_fvar Z.
Proof.
  intros Ea. induction Ea as [| [X Y] Ea IH]; intros Em Z m H.
  - destruct Em; reflexivity.
  - destruct Em as [|m' Em]; [reflexivity|].
    simpl. destruct (eqMode m' m).
    + simpl. destruct (Z == X) as [Heq|Hneq].
      * exfalso.
        assert (Hin : In (X,Y) ((X,Y)::Ea)) by (left; reflexivity).
        exact (H X Y Hin (eq_sym Heq)).
      * apply IH. intros X' Y' Hin.
        assert (Hin2 : In (X',Y') ((X,Y)::Ea)) by (right; exact Hin).
        exact (H X' Y' Hin2).
    + apply IH. intros X' Y' Hin.
      assert (Hin2 : In (X',Y') ((X,Y)::Ea)) by (right; exact Hin).
      exact (H X' Y' Hin2).
Qed.

Lemma amber_cov_bvar : forall Ea Em n m,
  amber_cov Ea Em (typ_bvar n) m = typ_bvar n.
Proof.
  intros Ea. induction Ea as [| [X Y] Ea IH]; intros Em n m.
  - destruct Em; reflexivity.
  - destruct Em as [|m' Em]; [reflexivity|].
    simpl. destruct (eqMode m' m); apply IH.
Qed.

(* Adding a fresh pair (whose source atom is not free in the type) does
   not change the mode translation. *)
Lemma amber_cov_fresh_pair : forall W Y A,
  W \notin fv_tt A ->
  forall Ea Em m' m,
  amber_cov ((W,Y)::Ea) (m'::Em) A m = amber_cov Ea Em A m.
Proof.
  intros W Y A. induction A as [| |n|X|A IHA|A1 IH1 A2 IH2];
    intros H Ea Em m' m.
  - rewrite !amber_cov_top. reflexivity.
  - rewrite !amber_cov_nat. reflexivity.
  - rewrite !amber_cov_bvar. reflexivity.
  - simpl. destruct (eqMode m' m).
    + simpl. destruct (X == W) as [Heq|Hneq].
      * exfalso. apply H. subst X. simpl. fsetdec.
      * reflexivity.
    + reflexivity.
  - rewrite !amber_cov_mu. f_equal.
    apply IHA. intros Hx. apply H. simpl. exact Hx.
  - rewrite !amber_cov_arrow. f_equal.
    + apply IH1. intros Hx. apply H. simpl. fsetdec.
    + apply IH2. intros Hx. apply H. simpl. fsetdec.
Qed.


(* The mode translation commutes with opening.  The inserted atom is
   translated by the same environment, so the filler on the right is the
   translated atom (a type, not an atom), which is why the lemma is
   stated with open_tt_rec. *)
Lemma amber_cov_open_tt_rec : forall Ea Em A K X m,
  amber_cov Ea Em (open_tt_rec K (typ_fvar X) A) m =
  open_tt_rec K (amber_cov Ea Em (typ_fvar X) m)
                (amber_cov Ea Em A m).
Proof.
  intros Ea Em A. induction A as [| |n|x|A IHA|A1 IH1 A2 IH2];
    intros K X m; simpl.
  - rewrite amber_cov_top. simpl. reflexivity.
  - rewrite amber_cov_nat. simpl. reflexivity.
  - destruct (K === n) as [e|e]; simpl; rewrite amber_cov_bvar; simpl.
    + rewrite e. rewrite eq_dec_refl. simpl. reflexivity.
    + destruct (K === n) as [e'|e']; [exfalso; exact (e e')|reflexivity].
  - destruct (amber_cov_fvar_fvar Ea Em x m) as [Z HZ].
    rewrite HZ. simpl. reflexivity.
  - rewrite !amber_cov_mu, IHA. simpl. reflexivity.
  - rewrite !amber_cov_arrow, IH1, IH2. simpl. reflexivity.
Qed.

Lemma amber_cov_open : forall Ea Em A X m,
  amber_cov Ea Em (open_tt A (typ_fvar X)) m =
  open_tt (amber_cov Ea Em A m) (amber_cov Ea Em (typ_fvar X) m).
Proof.
  intros. unfold open_tt. apply amber_cov_open_tt_rec.
Qed.

Fixpoint bindsub_atoms (E : env) : atoms :=
  match E with
  | nil => empty
  | (X, bind_sub) :: E' => add X (bindsub_atoms E')
  | (_, bind_typ _) :: E' => bindsub_atoms E'
  end.

Lemma in_bindsub_atoms : forall E X,
  X \in bindsub_atoms E <-> binds X bind_sub E.
Proof.
  induction E as [| [Y b] E IH]; intros X; simpl.
  - unfold binds. simpl. split; intros H.
    + fsetdec.
    + contradiction.
  - destruct b; simpl.
    + unfold binds. simpl.
      rewrite add_iff. rewrite IH.
      split; intros [H|H].
      * left. inversion H. reflexivity.
      * right. assumption.
      * left. inversion H. reflexivity.
      * right. assumption.
    + unfold binds. simpl.
      rewrite IH. split; intros H.
      * right; assumption.
      * destruct H as [H|H]; auto. inversion H.
Qed.

Fixpoint ren_tt (f : atom -> atom) (T : typ) : typ :=
  match T with
  | typ_top => typ_top
  | typ_nat => typ_nat
  | typ_bvar J => typ_bvar J
  | typ_fvar X => typ_fvar (f X)
  | typ_arrow T1 T2 => typ_arrow (ren_tt f T1) (ren_tt f T2)
  | typ_mu T => typ_mu (ren_tt f T)
  end.

Lemma ren_tt_id : forall T, ren_tt (fun X => X) T = T.
Proof. induction T; simpl; congruence. Qed.

Lemma ren_tt_ext : forall f g T,
  (forall X, X \in fv_tt T -> f X = g X) ->
  ren_tt f T = ren_tt g T.
Proof.
  intros f g T; induction T as [| |n|x|T IHT|T1 IHT1 T2 IHT2]; simpl; intros H.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - f_equal. apply H. simpl. fsetdec.
  - f_equal. apply IHT. intros X HX. apply H. simpl. exact HX.
  - f_equal.
    + apply IHT1. intros X HX. apply H. simpl. fsetdec.
    + apply IHT2. intros X HX. apply H. simpl. fsetdec.
Qed.

Lemma ren_tt_ren : forall f g T,
  ren_tt f (ren_tt g T) = ren_tt (fun X => f (g X)) T.
Proof.
  intros f g T; induction T as [| |n|x|T IHT|T1 IH1 T2 IH2]; simpl; try reflexivity.
  - f_equal. exact IHT.
  - f_equal; assumption.
Qed.

Lemma ren_tt_open_rec : forall f T K X,
  ren_tt f (open_tt_rec K (typ_fvar X) T) =
  open_tt_rec K (typ_fvar (f X)) (ren_tt f T).
Proof.
  intros f T; induction T as [| |n|x|T IHT|T1 IHT1 T2 IHT2]; intros K X; simpl.
  - reflexivity.
  - reflexivity.
  - destruct (K === n); reflexivity.
  - reflexivity.
  - rewrite IHT. reflexivity.
  - rewrite IHT1, IHT2. reflexivity.
Qed.

Lemma ren_tt_open : forall f T X,
  ren_tt f (open_tt T (typ_fvar X)) = open_tt (ren_tt f T) (typ_fvar (f X)).
Proof. intros. unfold open_tt. apply ren_tt_open_rec. Qed.

(* Removing the binding of the substituted atom from the environment. *)
Lemma binds_remove : forall E1 E2 Z W,
  binds W bind_sub (E1 ++ (Z, bind_sub) :: E2) ->
  W <> Z ->
  binds W bind_sub (E1 ++ E2).
Proof.
  induction E1 as [| [A b] E1 IH]; intros E2 Z W Hb Hne;
    unfold binds in *; simpl in *.
  - destruct Hb as [Heq|Hb].
    + inversion Heq. subst. exfalso. exact (Hne eq_refl).
    + exact Hb.
  - destruct Hb as [Heq|Hb].
    + left. exact Heq.
    + right. apply (IH E2 Z W Hb Hne).
Qed.

(* ============== substitution / opening algebra ==================== *)
Lemma subst_tt_fresh : forall Z U T,
  Z \notin fv_tt T -> subst_tt Z U T = T.
Proof.
  intros Z U T. induction T as [| |n|x|T IHT|T1 IH1 T2 IH2];
    intros H; simpl.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - destruct (x == Z) as [Heq|Hneq].
    + exfalso. apply H. subst x. simpl. fsetdec.
    + reflexivity.
  - f_equal. apply IHT. exact H.
  - f_equal.
    + apply IH1. intros Hx. apply H. simpl. fsetdec.
    + apply IH2. intros Hx. apply H. simpl. fsetdec.
Qed.

(* Substituting the very atom used for opening commutes, provided that
   atom is not free in the body: the opened occurrences are replaced by U
   on both sides.  This is the identity behind the companion type. *)
Lemma subst_tt_open_same_rec : forall Z U T K,
  Z \notin fv_tt T ->
  subst_tt Z U (open_tt_rec K (typ_fvar Z) T) =
  open_tt_rec K U (subst_tt Z U T).
Proof.
  intros Z U T. induction T as [| |n|y|T IHT|T1 IH1 T2 IH2];
    intros K HZ; simpl.
  - reflexivity.
  - reflexivity.
  - destruct (K === n) as [Heq|Hneq]; simpl.
    + subst n. rewrite eq_dec_refl. reflexivity.
    + reflexivity.
  - destruct (y == Z) as [Heq|Hneq].
    + exfalso. apply HZ. subst y. simpl. fsetdec.
    + reflexivity.
  - rewrite IHT; [reflexivity|exact HZ].
  - rewrite IH1, IH2.
    + reflexivity.
    + intros Hy. apply HZ. simpl. fsetdec.
    + intros Hy. apply HZ. simpl. fsetdec.
Qed.

Lemma subst_tt_open_same : forall Z U T,
  Z \notin fv_tt T ->
  subst_tt Z U (open_tt T (typ_fvar Z)) = open_tt (subst_tt Z U T) U.
Proof.
  intros. unfold open_tt. apply subst_tt_open_same_rec. exact H.
Qed.

(* The double unfolding is the self-substitution of the opening atom. *)
Lemma open_open_subst : forall A1 W,
  W \notin fv_tt A1 ->
  open_tt A1 (open_tt A1 (typ_fvar W)) =
  subst_tt W (open_tt A1 (typ_fvar W)) (open_tt A1 (typ_fvar W)).
Proof.
  intros A1 W H.
  rewrite (subst_tt_open_same W (open_tt A1 (typ_fvar W)) A1 H).
  rewrite subst_tt_fresh; [reflexivity|exact H].
Qed.

(* ============== one-hole contexts ================================= *)
(* A syntactic one-hole context, used to state the context-indexed
   (simultaneous-body-substitution) invariant. *)
Inductive ctx : Set :=
| c_hole   : ctx
| c_top    : ctx
| c_nat    : ctx
| c_bvar   : nat -> ctx
| c_fvar   : atom -> ctx
| c_arrow  : ctx -> ctx -> ctx
| c_mu     : ctx -> ctx.

Fixpoint fill (K : ctx) (T : typ) : typ :=
  match K with
  | c_hole       => T
  | c_top        => typ_top
  | c_nat        => typ_nat
  | c_bvar n     => typ_bvar n
  | c_fvar X     => typ_fvar X
  | c_arrow K1 K2 => typ_arrow (fill K1 T) (fill K2 T)
  | c_mu K0      => typ_mu (fill K0 T)
  end.

Fixpoint ctx_fv (K : ctx) : atoms :=
  match K with
  | c_hole        => empty
  | c_top         => empty
  | c_nat         => empty
  | c_bvar _      => empty
  | c_fvar X      => {{X}}
  | c_arrow K1 K2 => union (ctx_fv K1) (ctx_fv K2)
  | c_mu K0       => ctx_fv K0
  end.

Lemma fill_subst : forall K Z U T,
  Z \notin ctx_fv K ->
  fill K (subst_tt Z U T) = subst_tt Z U (fill K T).
Proof.
  induction K as [| | |n|X|K1 IH1 K2 IH2|K0 IH];
    intros Z U T H; simpl in *.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - assert (HX : X <> Z) by (intro; subst; fsetdec).
    destruct (X == Z) as [Heq|Hneq];
      [exfalso; exact (HX Heq) | reflexivity].
  - assert (H1 : Z \notin ctx_fv K1) by fsetdec.
    assert (H2 : Z \notin ctx_fv K2) by fsetdec.
    rewrite IH1; [| exact H1]. rewrite IH2; [| exact H2].
    reflexivity.
  - rewrite IH; [reflexivity | exact H].
Qed.

Fixpoint ctx_comp (K1 K2 : ctx) : ctx :=
  match K1 with
  | c_hole        => K2
  | c_top         => c_top
  | c_nat         => c_nat
  | c_bvar n      => c_bvar n
  | c_fvar X      => c_fvar X
  | c_arrow K11 K12 => c_arrow (ctx_comp K11 K2) (ctx_comp K12 K2)
  | c_mu K10      => c_mu (ctx_comp K10 K2)
  end.

Lemma fill_ctx_comp : forall K1 K2 T,
  fill (ctx_comp K1 K2) T = fill K1 (fill K2 T).
Proof.
  induction K1 as [| | |n|X|K1 IH1 K2' IH2|K0 IH];
    intros K2 T; simpl; try reflexivity.
  - rewrite IH1, IH2. reflexivity.
  - rewrite IH. reflexivity.
Qed.

(* locally closed types *)
Fixpoint lc_rec (d : nat) (T : typ) : Prop :=
  match T with
  | typ_top => True
  | typ_nat => True
  | typ_bvar J => J < d
  | typ_fvar X => True
  | typ_arrow T1 T2 => lc_rec d T1 /\ lc_rec d T2
  | typ_mu T => lc_rec (S d) T
  end.

Definition lc_tt T := lc_rec 0 T.

Lemma lc_open_rec : forall T K X d,
  lc_rec d T -> lc_rec d (open_tt_rec K (typ_fvar X) T).
Proof.
  induction T as [| |n|x|T IHT|T1 IHT1 T2 IHT2]; intros K X d H; simpl in *.
  - exact I.
  - exact I.
  - destruct (K === n).
    + simpl. exact I.
    + simpl. exact H.
  - simpl. exact I.
  - simpl. exact (IHT (S K) X (S d) H).
  - destruct H as [H1 H2]. simpl. split.
    + exact (IHT1 K X d H1).
    + exact (IHT2 K X d H2).
Qed.

Lemma lc_open_mu_body : forall T d X,
  lc_rec (S d) T -> lc_rec d (open_tt_rec d (typ_fvar X) T).
Proof.
  induction T as [| |n|x|T IHT|T1 IHT1 T2 IHT2]; intros d X' H; simpl in *.
  - exact I.
  - exact I.
  - (* bvar *) destruct (d === n).
    + simpl. exact I.
    + simpl. unfold lt in *. lia.
  - exact I.
  - apply IHT. exact H.
  - destruct H as [H1 H2]. split.
    + exact (IHT1 d X' H1).
    + exact (IHT2 d X' H2).
Qed.



Lemma lc_open_rec_any : forall T K X, lc_rec K T -> lc_rec K (open_tt_rec K (typ_fvar X) T).
Proof.
  induction T as [| |n|x|T IHT|T1 IHT1 T2 IHT2]; intros K X' H; simpl in *.
  - exact I.
  - exact I.
  - destruct (K === n).
    + simpl. exact I.
    + exact H.
  - exact I.
  - apply IHT. exact H.
  - destruct H as [H1 H2]. split.
    + exact (IHT1 K X' H1).
    + exact (IHT2 K X' H2).
Qed.

Lemma lc_open_tt : forall T X, lc_tt T -> lc_tt (open_tt T (typ_fvar X)).
Proof.
  intros T X H. unfold lc_tt, open_tt.
  exact (lc_open_rec_any T 0 X H).
Qed.

(* Opening a locally closed type at any level is the identity. *)
Lemma lc_open_rec_id : forall T d, lc_rec d T ->
  forall K, K >= d -> forall X, open_tt_rec K (typ_fvar X) T = T.
Proof.
  intros T. induction T as [| |n|x|T IHT|T1 IH1 T2 IH2];
    intros d Hlc K HK X; simpl in *.
  - reflexivity.
  - reflexivity.
  - destruct (K === n); [|reflexivity].
    exfalso. lia.
  - reflexivity.
  - apply f_equal. apply IHT with (d := S d) (K := S K).
    + exact Hlc.
    + lia.
  - destruct Hlc as [H1 H2]. f_equal.
    + exact (IH1 d H1 K HK X).
    + exact (IH2 d H2 K HK X).
Qed.

(* Opening a locally closed type with any type at any level is the identity. *)
Lemma lc_open_any_id : forall T d, lc_rec d T ->
  forall K W, K >= d -> open_tt_rec K W T = T.
Proof.
  intros T. induction T as [| |n|x|T IHT|T1 IH1 T2 IH2];
    intros d Hlc K W HK; simpl in *.
  - reflexivity.
  - reflexivity.
  - destruct (K === n); [|reflexivity].
    exfalso. lia.
  - reflexivity.
  - apply f_equal. apply (IHT (S d) Hlc (S K) W). lia.
  - destruct Hlc as [H1 H2]. f_equal.
    + exact (IH1 d H1 K W HK).
    + exact (IH2 d H2 K W HK).
Qed.

(* Substitution commutes with opening with a type. *)
Lemma subst_tt_open_ty_rec : forall Z S C U K,
  lc_tt S ->
  subst_tt Z S (open_tt_rec K U C) =
  open_tt_rec K (subst_tt Z S U) (subst_tt Z S C).
Proof.
  intros Z S C. induction C as [| |n|y|C IHC|C1 IH1 C2 IH2];
    intros U K HS; simpl.
  - reflexivity.
  - reflexivity.
  - destruct (K === n); simpl; reflexivity.
  - destruct (y == Z) as [Heq|Hneq]; simpl.
    + subst y. simpl.
      rewrite (lc_open_any_id S 0 HS K (subst_tt Z S U) (Nat.le_0_l K)).
      reflexivity.
    + reflexivity.
  - rewrite IHC; [reflexivity | exact HS].
  - rewrite IH1, IH2; [reflexivity | exact HS | exact HS].
Qed.

(* Commuting substitution of a (fresh, distinct) atom with opening, when
   the substituted type is locally closed.  Needed for the companion
   derivation's fresh-atom step. *)
Lemma subst_tt_open_atom_lc_rec : forall W A0 C K V,
  lc_tt A0 -> V <> W ->
  subst_tt W A0 (open_tt_rec K (typ_fvar V) C) =
  open_tt_rec K (typ_fvar V) (subst_tt W A0 C).
Proof.
  intros W A0 C. induction C as [| |n|y|C IHC|C1 IH1 C2 IH2];
    intros K V Hlc HVW; simpl.
  - reflexivity.
  - reflexivity.
  - destruct (K === n); simpl.
    + destruct (V == W) as [Heq|Hneq].
      * exfalso. exact (HVW Heq).
      * reflexivity.
    + reflexivity.
  - destruct (y == W) as [Heq|Hneq]; simpl.
    + rewrite (lc_open_rec_id A0 0 Hlc K (Nat.le_0_l K) V).
      reflexivity.
    + reflexivity.
  - rewrite IHC; [reflexivity | exact Hlc | exact HVW].
  - rewrite IH1, IH2.
    + reflexivity.
    + exact Hlc. + exact HVW.
    + exact Hlc. + exact HVW.
Qed.

Lemma subst_tt_open_atom_lc : forall W A0 C V,
  lc_tt A0 -> V <> W ->
  subst_tt W A0 (open_tt C (typ_fvar V)) =
  open_tt (subst_tt W A0 C) (typ_fvar V).
Proof.
  intros. unfold open_tt. apply subst_tt_open_atom_lc_rec; assumption.
Qed.

(* The double unfolding commutes with substituting a distinct atom. *)
Lemma subst_tt_open_open_ty : forall Z S C Y,
  lc_tt S -> Y <> Z ->
  subst_tt Z S (open_tt C (open_tt C (typ_fvar Y))) =
  open_tt (subst_tt Z S C) (open_tt (subst_tt Z S C) (typ_fvar Y)).
Proof.
  intros Z S C Y HS HYZ. unfold open_tt.
  rewrite (subst_tt_open_ty_rec Z S C (open_tt_rec 0 (typ_fvar Y) C) 0 HS).
  rewrite (subst_tt_open_atom_lc_rec Z S C 0 Y HS HYZ).
  reflexivity.
Qed.

(* Inverting opening for locally closed types: if an opened body is
   locally closed, the body is closed under its binder. *)
Lemma lc_open_body_inv : forall T d X,
  lc_rec d (open_tt_rec d (typ_fvar X) T) -> lc_rec (S d) T.
Proof.
  induction T as [| |n|y|T IHT|T1 IH1 T2 IH2];
    intros d X H; simpl in *.
  - exact I.
  - exact I.
  - destruct (d === n).
    + simpl. unfold lt. lia.
    + simpl in H. unfold lt in *. lia.
  - exact I.
  - apply (IHT (S d) X). exact H.
  - destruct H as [H1 H2]. split.
    + exact (IH1 d X H1).
    + exact (IH2 d X H2).
Qed.

Lemma wf_lc : forall E A, WF E A -> lc_tt A.
Proof.
  intros E A H. induction H as
    [ E0 | E0 | X E0 Hb | E0 A1 A2 W1 IH1 W2 IH2
    | L E0 A0 p1 IH1 p2 IH2 ].
  - simpl. exact I.
  - simpl. exact I.
  - simpl. exact I.
  - simpl. split; assumption.
  - simpl.
    destruct (atom_fresh (L \u fv_tt A0)) as [X HX].
    assert (HXL : X \notin L) by fsetdec.
    exact (lc_open_body_inv A0 0 X (IH1 X HXL)).
Qed.

(* WF is monotone in the bind_sub part of the environment. *)
Lemma wf_mono : forall E A, WF E A ->
  forall E',
    (forall X, binds X bind_sub E -> binds X bind_sub E') ->
    WF E' A.
Proof.
  intros E A H. induction H as
    [ E0 | E0 | X E0 Hb | E0 A1 A2 W1 IH1 W2 IH2
    | L E0 A0 p1 IH1 p2 IH2 ]; intros E' Hle.
  - apply WF_top.
  - apply WF_nat.
  - apply WF_fvar. exact (Hle X Hb).
  - apply WF_arrow.
    + apply IH1. exact Hle.
    + apply IH2. exact Hle.
  - apply WF_rec with (L := L).
    + intros Y HY. apply (IH1 Y HY (Y ~ bind_sub ++ E')).
      intros Z HZ. unfold binds in *. simpl in *.
      destruct HZ as [Heq|HZ].
      * left. exact Heq.
      * right. exact (Hle Z HZ).
    + intros Y HY. apply (IH2 Y HY (Y ~ bind_sub ++ E')).
      intros Z HZ. unfold binds in *. simpl in *.
      destruct HZ as [Heq|HZ].
      * left. exact Heq.
      * right. exact (Hle Z HZ).
Qed.

(* WF is preserved by substituting a bind_sub atom by a well-formed type.
   The substituted binder may sit anywhere in the environment; E1 is the
   prefix introduced by nested recursion. *)
Lemma wf_subst_gen : forall E1 E2 Z C,
  WF (E1 ++ (Z, bind_sub) :: E2) C ->
  forall S, WF (E1 ++ E2) S ->
  WF (E1 ++ E2) (subst_tt Z S C).
Proof.
  intros E1 E2 Z C H.
  remember (E1 ++ (Z, bind_sub) :: E2) as Env eqn:Heq.
  revert E1 E2 Z Heq.
  induction H as
    [ Env0 | Env0 | W Env0 Hb | Env0 A1 A2 W1 IH1 W2 IH2
    | L Env0 A0 p1 IH1 p2 IH2 ];
    intros E1 E2 Z Heq S HWS.
  - simpl. apply WF_top.
  - simpl. apply WF_nat.
  - simpl. destruct (W == Z) as [HeqW|Hneq].
    + subst W. exact HWS.
    + apply WF_fvar. apply (binds_remove E1 E2 Z W).
      * subst Env0. exact Hb.
      * exact Hneq.
  - simpl. apply WF_arrow.
    + exact (IH1 E1 E2 Z Heq S HWS).
    + exact (IH2 E1 E2 Z Heq S HWS).
  - simpl.
    pose proof (wf_lc (E1++E2) S HWS) as HlcS.
    apply WF_rec with (L := L \u {{Z}}).
    + intros Y HY.
      assert (HYL : Y \notin L) by fsetdec.
      assert (HYZ : Y <> Z) by (intro; subst; fsetdec).
      change (WF (Y ~ bind_sub ++ (E1++E2))
                 (open_tt_rec 0 (typ_fvar Y) (subst_tt Z S A0))).
      rewrite <- (subst_tt_open_atom_lc_rec Z S A0 0 Y HlcS HYZ).
      apply (IH1 Y HYL ((Y, bind_sub) :: E1) E2 Z).
      * simpl. rewrite Heq. reflexivity.
      * apply (wf_mono (E1++E2) S HWS (Y ~ bind_sub ++ (E1++E2))).
        intros X HX. unfold binds in *. simpl in *. right. exact HX.
    + intros Y HY.
      assert (HYL : Y \notin L) by fsetdec.
      assert (HYZ : Y <> Z) by (intro; subst; fsetdec).
      change (WF (Y ~ bind_sub ++ (E1++E2))
                 (open_tt_rec 0
                    (open_tt_rec 0 (typ_fvar Y) (subst_tt Z S A0))
                    (subst_tt Z S A0))).
      pose proof (subst_tt_open_open_ty Z S A0 Y HlcS HYZ) as Hdbl.
      unfold open_tt in Hdbl.
      rewrite <- Hdbl.
      apply (IH2 Y HYL ((Y, bind_sub) :: E1) E2 Z).
      * simpl. rewrite Heq. reflexivity.
      * apply (wf_mono (E1++E2) S HWS (Y ~ bind_sub ++ (E1++E2))).
        intros X HX. unfold binds in *. simpl in *. right. exact HX.
Qed.

(* ============== sub implies WF on both sides ====================== *)
Lemma sub_wf : forall E A B, sub E A B -> WF E A /\ WF E B.
Proof.
  intros E A B H.
  induction H as
    [ E wfE
    | E X wfE Hb
    | E A0 wfE WFA
    | E A1 A2 B1 B2 s1 IH1 s2 IH2
    | L A1 A2 E p1 IH1 p2 IH2 ].
  - split; apply WF_nat.
  - split; apply WF_fvar; exact Hb.
  - split; [ exact WFA | apply WF_top ].
  - split; apply WF_arrow.
    + exact (proj2 IH1).
    + exact (proj1 IH2).
    + exact (proj1 IH1).
    + exact (proj2 IH2).
  - split; apply WF_rec with (L:=L).
    + intros X HX. exact (proj1 (IH1 X HX)).
    + intros X HX. exact (proj1 (IH2 X HX)).
    + intros X HX. exact (proj2 (IH1 X HX)).
    + intros X HX. exact (proj2 (IH2 X HX)).
Qed.

(* ============== inversion and transitivity of iso subtyping ======== *)
Lemma sub_wf_env : forall E A B, sub E A B -> wf_env E.
Proof.
  intros E A B H. induction H as
    [ E0 h | E0 X h _ | E0 A0 h _ | E0 A1 A2 B1 B2 s1 IH1 s2 IH2
    | L A1 A2 E0 p1 IH1 p2 IH2 ].
  - exact h.
  - exact h.
  - exact h.
  - exact IH1.
  - destruct (atom_fresh L) as [X HX]. assert (HXL : X \notin L) by fsetdec.
    specialize (IH1 X HXL). inversion IH1; subst; assumption.
Qed.

Lemma inv_top_l : forall E C, sub E typ_top C -> C = typ_top.
Proof. intros E C H. inversion H; subst; reflexivity. Qed.

Lemma inv_arrow_l : forall E A1 A2 C, sub E (typ_arrow A1 A2) C ->
  (C = typ_top /\ wf_env E /\ WF E (typ_arrow A1 A2)) \/
  (exists C1 C2, C = typ_arrow C1 C2 /\ sub E C1 A1 /\ sub E A2 C2).
Proof. intros E A1 A2 C H. inversion H; subst; eauto 10. Qed.

Lemma inv_arrow_r : forall E C B1 B2, sub E C (typ_arrow B1 B2) ->
  exists C1 C2, C = typ_arrow C1 C2 /\ sub E B1 C1 /\ sub E C2 B2.
Proof. intros E C B1 B2 H. inversion H; subst; eauto 10. Qed.

Lemma inv_mu_l : forall E A C, sub E (typ_mu A) C ->
  (C = typ_top /\ wf_env E /\ WF E (typ_mu A)) \/
  (exists L C1, C = typ_mu C1 /\
     (forall X, X \notin L -> sub (X ~ bind_sub ++ E) (open_tt A (typ_fvar X)) (open_tt C1 (typ_fvar X))) /\
     (forall X, X \notin L -> sub (X ~ bind_sub ++ E)
        (open_tt A (open_tt A (typ_fvar X))) (open_tt C1 (open_tt C1 (typ_fvar X))))).
Proof. intros E A C H. inversion H; subst; eauto 10. Qed.

Lemma inv_mu_r : forall E C B, sub E C (typ_mu B) ->
  exists L C1, C = typ_mu C1 /\
     (forall X, X \notin L -> sub (X ~ bind_sub ++ E) (open_tt C1 (typ_fvar X)) (open_tt B (typ_fvar X))) /\
     (forall X, X \notin L -> sub (X ~ bind_sub ++ E)
        (open_tt C1 (open_tt C1 (typ_fvar X))) (open_tt B (open_tt B (typ_fvar X)))).
Proof. intros E C B H. inversion H; subst; eauto 10. Qed.

Lemma sub_trans_aux : forall E A B, sub E A B ->
  (forall C, sub E B C -> sub E A C) /\
  (forall C, sub E C A -> sub E C B).
Proof.
  intros E A B H. induction H as
    [ E0 wfE | E0 X wfE Hb | E0 A0 wfE WFA
    | E0 A1 A2 B1 B2 s1 IH1 s2 IH2 | L A1 A2 E0 p1 IH1 p2 IH2 ].
  - split; intros C H2; assumption.
  - split; intros C H2; assumption.
  - split.
    + intros C H2. rewrite (inv_top_l E0 C H2). apply sa_top; assumption.
    + intros C H2. apply sa_top.
      * apply (sub_wf_env E0 C A0 H2).
      * exact (proj1 (sub_wf E0 C A0 H2)).
  - split.
    + intros C H2. destruct (inv_arrow_l E0 B1 B2 C H2) as
        [[HC [Hwf HWF]] | [D1 [D2 [HC [hdom hcod]]]]].
      * subst C. apply sa_top; [ exact Hwf | ].
        apply WF_arrow.
        -- exact (proj2 (sub_wf E0 B1 A1 s1)).
        -- exact (proj1 (sub_wf E0 A2 B2 s2)).
      * subst C. apply sa_arrow.
        -- exact (proj2 IH1 D1 hdom).
        -- exact (proj1 IH2 D2 hcod).
    + intros C H2. destruct (inv_arrow_r E0 C A1 A2 H2) as
        [C1 [C2 [HC [hdom hcod]]]].
      subst C. apply sa_arrow.
      * exact (proj1 IH1 C1 hdom).
      * exact (proj2 IH2 C2 hcod).
  - split.
    + intros C H2. destruct (inv_mu_l E0 A2 C H2) as
        [[HC [Hwf HWF]] | [L0 [C1 [HC [q1 q2]]]]].
      * subst C. apply sa_top; [ exact Hwf | ].
        apply WF_rec with (L := L).
        -- intros X HX. exact (proj1 (sub_wf (X ~ bind_sub ++ E0)
             (open_tt A1 (typ_fvar X)) (open_tt A2 (typ_fvar X)) (p1 X HX))).
        -- intros X HX. exact (proj1 (sub_wf (X ~ bind_sub ++ E0)
             (open_tt A1 (open_tt A1 (typ_fvar X)))
             (open_tt A2 (open_tt A2 (typ_fvar X))) (p2 X HX))).
      * subst C. apply sa_rec with (L := L \u L0).
        -- intros X HX.
           assert (HXL : X \notin L) by fsetdec.
           assert (HXL0 : X \notin L0) by fsetdec.
           exact (proj1 (IH1 X HXL) (open_tt C1 (typ_fvar X)) (q1 X HXL0)).
        -- intros X HX.
           assert (HXL : X \notin L) by fsetdec.
           assert (HXL0 : X \notin L0) by fsetdec.
           exact (proj1 (IH2 X HXL) (open_tt C1 (open_tt C1 (typ_fvar X))) (q2 X HXL0)).
    + intros C H2. destruct (inv_mu_r E0 C A1 H2) as
        [L0 [C1 [HC [q1 q2]]]].
      subst C. apply sa_rec with (L := L \u L0).
      * intros X HX.
        assert (HXL : X \notin L) by fsetdec.
        assert (HXL0 : X \notin L0) by fsetdec.
        exact (proj2 (IH1 X HXL) (open_tt C1 (typ_fvar X)) (q1 X HXL0)).
      * intros X HX.
        assert (HXL : X \notin L) by fsetdec.
        assert (HXL0 : X \notin L0) by fsetdec.
        exact (proj2 (IH2 X HXL) (open_tt C1 (open_tt C1 (typ_fvar X))) (q2 X HXL0)).
Qed.

Lemma sub_trans : forall E A B, sub E A B ->
  forall C, sub E B C -> sub E A C.
Proof. intros E A B H C H2. exact (proj1 (sub_trans_aux E A B H) C H2). Qed.

(* Iso subtyping is monotone in the bind_sub part of the environment. *)
Lemma sub_mono : forall E A B, sub E A B ->
  forall E', wf_env E' ->
    (forall X, binds X bind_sub E -> binds X bind_sub E') ->
    sub E' A B.
Proof.
  intros E A B H. induction H as
    [ E0 wfE
    | E0 X wfE Hb
    | E0 A0 wfE WFA
    | E0 A1 A2 B1 B2 s1 IH1 s2 IH2
    | L A1 A2 E0 p1 IH1 p2 IH2 ]; intros E' HwfE' Hle.
  - apply sa_nat. exact HwfE'.
  - apply sa_fvar. exact HwfE'. exact (Hle X Hb).
  - apply sa_top. exact HwfE'.
    apply (wf_mono E0 A0 WFA E' Hle).
  - apply sa_arrow.
    + apply IH1; assumption.
    + apply IH2; assumption.
  - apply sa_rec with (L := L \u dom E').
    + intros X HX. apply IH1.
      * fsetdec.
      * apply wf_env_sub; [ exact HwfE' | fsetdec ].
      * intros Y HY. unfold binds in *. simpl in *.
        destruct HY as [Heq|HY].
        -- left. exact Heq.
        -- right. exact (Hle Y HY).
    + intros X HX. apply IH2.
      * fsetdec.
      * apply wf_env_sub; [ exact HwfE' | fsetdec ].
      * intros Y HY. unfold binds in *. simpl in *.
        destruct HY as [Heq|HY].
        -- left. exact Heq.
        -- right. exact (Hle Y HY).
Qed.

(* fv of open *)
Lemma fv_tt_open_rec : forall T K X,
  AtomSetImpl.Subset (fv_tt (open_tt_rec K (typ_fvar X) T)) (union (fv_tt T) {{X}}).
Proof.
  induction T as [| |n|x|T IHT|T1 IHT1 T2 IHT2]; intros K X'; simpl.
  - intros z Hz. fsetdec.
  - intros z Hz. fsetdec.
  - destruct (K === n); simpl; intros z Hz; fsetdec.
  - intros z Hz. fsetdec.
  - simpl. intros z Hz. exact (IHT (S K) X' z Hz).
  - simpl. intros z Hz. apply union_iff in Hz as [Hz|Hz].
    + pose proof (IHT1 K X' _ Hz). fsetdec.
    + pose proof (IHT2 K X' _ Hz). fsetdec.
Qed.

Lemma fv_tt_open : forall T X,
  AtomSetImpl.Subset (fv_tt (open_tt T (typ_fvar X))) (union (fv_tt T) {{X}}).
Proof. intros. unfold open_tt. apply fv_tt_open_rec. Qed.

Lemma fv_tt_open_upper_rec : forall T K X,
  AtomSetImpl.Subset (fv_tt T) (fv_tt (open_tt_rec K (typ_fvar X) T)).
Proof.
  induction T as [| |n|x|T IHT|T1 IHT1 T2 IHT2]; intros K X'; simpl.
  - intros z Hz. fsetdec.
  - intros z Hz. fsetdec.
  - intros z Hz. fsetdec.
  - intros z Hz. fsetdec.
  - intros z Hz. exact (IHT (S K) X' z Hz).
  - intros z Hz. apply union_iff in Hz as [Hz|Hz].
    + pose proof (IHT1 K X' z Hz). fsetdec.
    + pose proof (IHT2 K X' z Hz). fsetdec.
Qed.

Lemma fv_tt_open_upper : forall T X,
  AtomSetImpl.Subset (fv_tt T) (fv_tt (open_tt T (typ_fvar X))).
Proof. intros. unfold open_tt. apply fv_tt_open_upper_rec. Qed.

(* ===================== domA lemmas ================================= *)
Lemma in_domA_cons : forall X Y E z,
  z \in domA ((X,Y)::E) <-> z = X \/ z = Y \/ z \in domA E.
Proof.
  intros. simpl. split; intros H; fsetdec.
Qed.

Lemma in_domA_pair_1 : forall E X Y, In (X,Y) E -> X \in domA E.
Proof.
  induction E as [| [a b] E IH]; intros X Y Hin; simpl in *.
  - contradiction.
  - destruct Hin as [Hin|Hin].
    + inversion Hin; subst. apply in_domA_cons. left. reflexivity.
    + apply in_domA_cons. right. right. exact (IH X Y Hin).
Qed.

Lemma in_domA_pair_2 : forall E X Y, In (X,Y) E -> Y \in domA E.
Proof.
  induction E as [| [a b] E IH]; intros X Y Hin; simpl in *.
  - contradiction.
  - destruct Hin as [Hin|Hin].
    + inversion Hin; subst. apply in_domA_cons. right. left. reflexivity.
    + apply in_domA_cons. right. right. exact (IH X Y Hin).
Qed.

Lemma domA_member : forall E X,
  X \in domA E -> exists Y, In (X,Y) E \/ In (Y,X) E.
Proof.
  induction E as [| [a b] E IH]; intros X H; simpl in *.
  - fsetdec.
  - apply in_domA_cons in H. destruct H as [H|[H|H]].
    + subst. exists b. left. left. reflexivity.
    + subst. exists a. right. left. reflexivity.
    + apply IH in H. destruct H as [Y [HY|HY]].
      * exists Y. left. right. exact HY.
      * exists Y. right. right. exact HY.
Qed.

(* ===================== wf_amber from lc and fv ==================== *)



Lemma sub_refl_wf : forall E A, WF E A -> wf_env E -> sub E A A.
Proof.
  intros E A H. induction H as
    [ E0 | E0 | X E0 Hb | E0 A1 A2 W1 IH1 W2 IH2
    | L E0 A0 p1 IH1 p2 IH2 ]; intro Hwf.
  - apply sa_top; [ exact Hwf | apply WF_top ].
  - apply sa_nat. exact Hwf.
  - apply sa_fvar; assumption.
  - apply sa_arrow.
    + apply IH1. exact Hwf.
    + apply IH2. exact Hwf.
  - apply sa_rec with (L := L \u dom E0).
    + intros X HX. apply IH1.
      * fsetdec.
      * apply wf_env_sub; [ exact Hwf | fsetdec ].
    + intros X HX. apply IH2.
      * fsetdec.
      * apply wf_env_sub; [ exact Hwf | fsetdec ].
Qed.

(* ============== WF renames to wf_amber ============================ *)
Lemma wf_amber_ren : forall E A, WF E A ->
  forall (f : atom -> atom) (Ea : env_amber),
  wfe_amber Ea ->
  (forall X, binds X bind_sub E -> f X \in domA Ea) ->
  AtomSetImpl.Subset (fv_tt A) (bindsub_atoms E) ->
  wf_amber Ea (ren_tt f A).
Proof.
  intros E A H. induction H as
    [ E
    | E
    | X E Hb
    | E A1 A2 WF1 IH1 WF2 IH2
    | L E A0 p1 IH1 p2 IH2 ]; intros f Ea Hwe Hcorr Hfv.
  - apply wfa_top. exact Hwe.
  - apply wfa_nat. exact Hwe.
  - simpl. pose proof (Hcorr X Hb) as Hd.
    pose proof (domA_member Ea (f X) Hd) as [Y [HY|HY]].
    + exact (wfa_fvarl Ea (f X) Y HY Hwe).
    + exact (wfa_fvarr Ea Y (f X) HY Hwe).
  - simpl. apply wfa_arrow.
    + apply IH1; auto. intros z Hz. apply Hfv. simpl. fsetdec.
    + apply IH2; auto. intros z Hz. apply Hfv. simpl. fsetdec.
  - simpl.
    apply wfa_rec with (L := domA Ea).
    intros X Y HX HY.
    destruct (atom_fresh (L \u fv_tt A0)) as [Z HZ].
    assert (HZL : Z \notin L) by (fsetdec).
    assert (HZfv : Z \notin fv_tt A0) by (fsetdec).
    assert (Hwe' : wfe_amber ((X,Y)::Ea)).
    { apply wfea_cons. exact HX. fsetdec. exact Hwe. }
    set (f' := fun W => if W == Z then X else f W).
    assert (Hcorr' : forall W, binds W bind_sub (Z ~ bind_sub ++ E) -> f' W \in domA ((X,Y)::Ea)).
    { intros W HW. unfold f'. destruct (W == Z) as [Heq|Hneq].
      - subst W. apply in_domA_cons. left. reflexivity.
      - apply in_domA_cons. right. right. apply Hcorr. unfold binds in *.
        simpl in HW. destruct HW as [HW|HW].
        + inversion HW. subst. exfalso. apply Hneq. reflexivity.
        + exact HW. }
    assert (Hfv' : AtomSetImpl.Subset (fv_tt (open_tt A0 (typ_fvar Z))) (bindsub_atoms (Z ~ bind_sub ++ E))).
    { intros w Hw. pose proof (fv_tt_open A0 Z w Hw) as Hw2.
      apply union_iff in Hw2 as [Hw2|Hw2].
      - simpl. rewrite add_iff. right. apply Hfv. exact Hw2.
      - assert (w = Z) by fsetdec. subst w. simpl. rewrite add_iff. left. reflexivity. }
    pose proof (IH1 Z HZL f' ((X,Y)::Ea) Hwe' Hcorr' Hfv') as Hwf.
    assert (Hren : ren_tt f' (open_tt A0 (typ_fvar Z)) = open_tt (ren_tt f A0) (typ_fvar X)).
    { rewrite ren_tt_open. f_equal.
      - apply ren_tt_ext. intros W HW. unfold f'.
        destruct (W == Z) as [Heq|Hneq].
        + subst W. exfalso. apply HZfv. exact HW.
        + reflexivity.
      - unfold f'. rewrite eq_dec_refl. reflexivity. }
    rewrite Hren in Hwf. exact Hwf.
Qed.
Lemma wf_fv_bindsub : forall E A, WF E A ->
  AtomSetImpl.Subset (fv_tt A) (bindsub_atoms E).
Proof.
  intros E A H. induction H as
    [ E
    | E
    | X E Hb
    | E A1 A2 WF1 IH1 WF2 IH2
    | L E A0 p1 IH1 p2 IH2 ].
  - simpl. intros x Hx. fsetdec.
  - simpl. intros x Hx. fsetdec.
  - simpl. intros x Hx.
    assert (x = X) by fsetdec.
    subst. apply in_bindsub_atoms. exact Hb.
  - simpl. intros x Hx. apply union_iff in Hx as [Hx|Hx].
    + apply IH1. exact Hx.
    + apply IH2. exact Hx.
  - simpl.
    destruct (atom_fresh (L \u fv_tt A0)) as [X HX].
    assert (HXL : X \notin L) by fsetdec.
    assert (HXfv : X \notin fv_tt A0) by fsetdec.
    intros Y HY.
    pose proof (IH1 X HXL) as Hsub.
    pose proof (fv_tt_open_upper A0 X Y HY) as HYopen.
    pose proof (Hsub Y HYopen) as HYenv.
    simpl in HYenv. rewrite add_iff in HYenv.
    destruct HYenv as [Heq|Hin].
    + exfalso. subst Y. exact (HXfv HY).
    + exact Hin.
Qed.

(* ============== per-atom origin translation ======================= *)
Definition pick (o : atom -> bool) (f g : atom -> atom) : atom -> atom :=
  fun X => if o X then f X else g X.

Definition ren_pick (o : atom -> bool) (f g : atom -> atom) (T : typ) : typ :=
  ren_tt (pick o f g) T.

Lemma ren_pick_id : forall o T,
  ren_pick o (fun X => X) (fun X => X) T = T.
Proof.
  intros o T. unfold ren_pick.
  transitivity (ren_tt (fun X => X) T).
  - apply ren_tt_ext.
    intros X HX. unfold pick. destruct (o X); reflexivity.
  - apply ren_tt_id.
Qed.

(* compatibility: for every matched atom occurrence, the origins must be
   (false,true) at negative polarity or (true,false) at positive polarity *)
Fixpoint compat (o1 o2 : atom -> bool) (pol : bool) (A B : typ) : Prop :=
  match A, B with
  | typ_fvar X, typ_fvar Y =>
      if X == Y then
        (if o1 X then (if o2 X then False else pol = true)
                   else (if o2 X then pol = false else False))
      else True
  | typ_arrow A1 A2, typ_arrow B1 B2 =>
      compat o1 o2 (negb pol) A1 B1 /\ compat o1 o2 pol A2 B2
  | typ_mu A1, typ_mu B1 => compat o1 o2 pol A1 B1
  | _,_ => True
  end.

Lemma wf_amber_ren_pick : forall E A Ea o1 f g,
  WF E A -> wfe_amber Ea ->
  (forall Z, binds Z bind_sub E -> In (f Z, g Z) Ea) ->
  AtomSetImpl.Subset (fv_tt A) (bindsub_atoms E) ->
  wf_amber Ea (ren_pick o1 f g A).
Proof.
  intros E A Ea o1 f g HWF Hwe Hcorr Hfv.
  unfold ren_pick.
  apply (wf_amber_ren E A HWF (pick o1 f g) Ea Hwe).
  - intros Z HZ. pose proof (Hcorr Z HZ) as Hin.
    pose proof (in_domA_pair_1 Ea (f Z) (g Z) Hin) as Hf.
    pose proof (in_domA_pair_2 Ea (f Z) (g Z) Hin) as Hg.
    unfold pick. destruct (o1 Z); assumption.
  - exact Hfv.
Qed.

(* ============== inversion lemmas for Amber subtyping ============== *)
Lemma sam_inv_top_l : forall E C, sub_amber E typ_top C -> C = typ_top.
Proof. intros E C H. inversion H; subst; reflexivity. Qed.

Lemma sam_inv_nat_l : forall E C,
  sub_amber E typ_nat C -> C = typ_nat \/ C = typ_top.
Proof. intros E C H. inversion H; subst; auto. Qed.

Lemma sam_inv_arrow_l : forall E A1 A2 C,
  sub_amber E (typ_arrow A1 A2) C ->
  C = typ_top \/
  (exists C1 C2, C = typ_arrow C1 C2 /\
     sub_amber E C1 A1 /\ sub_amber E A2 C2).
Proof. intros E A1 A2 C H. inversion H; subst; eauto 10. Qed.

Lemma sam_inv_arrow_r : forall E C B1 B2,
  sub_amber E C (typ_arrow B1 B2) ->
  exists C1 C2, C = typ_arrow C1 C2 /\
    sub_amber E B1 C1 /\ sub_amber E C2 B2.
Proof. intros E C B1 B2 H. inversion H; subst; eauto 10. Qed.

Lemma sam_inv_mu_l : forall E A C, sub_amber E (typ_mu A) C ->
  C = typ_top \/
  C = typ_mu A \/
  (exists B L, C = typ_mu B /\
     (forall X Y, X \notin L -> Y \notin {{X}} \u L ->
        sub_amber ((X,Y)::E) (open_tt A X) (open_tt B Y))).
Proof. intros E A C H. inversion H; subst; eauto 10. Qed.

Lemma inv_top_r : forall E A, sub E A typ_top -> wf_env E /\ WF E A.
Proof. intros E A H. inversion H; subst; auto. Qed.

Lemma inv_mu_mu : forall E A B, sub E (typ_mu A) (typ_mu B) ->
  exists L,
    (forall X, X \notin L -> sub (X ~ bind_sub ++ E) (open_tt A X) (open_tt B X)) /\
    (forall X, X \notin L -> sub (X ~ bind_sub ++ E)
       (open_tt A (open_tt A X)) (open_tt B (open_tt B X))).
Proof. intros E A B H. inversion H; subst; eauto 10. Qed.

Lemma sam_inv_top_r : forall E A,
  sub_amber E A typ_top -> wf_amber E A /\ wfe_amber E.
Proof. intros E A H. inversion H; subst; auto. Qed.

Lemma sam_inv_mu_mu : forall E A B,
  sub_amber E (typ_mu A) (typ_mu B) ->
  (A = B /\ wf_amber E (typ_mu A) /\ wfe_amber E) \/
  (exists L, forall X Y, X \notin L -> Y \notin {{X}} \u L ->
      sub_amber ((X,Y)::E) (open_tt A X) (open_tt B Y)).
Proof. intros E A B H. inversion H; subst; eauto 10. Qed.

Lemma sam_inv_mu_r : forall E C B, sub_amber E C (typ_mu B) ->
  C = typ_mu B \/
  (exists A L, C = typ_mu A /\
     (forall X Y, X \notin L -> Y \notin {{X}} \u L ->
        sub_amber ((X,Y)::E) (open_tt A X) (open_tt B Y))).
Proof. intros E C B H. inversion H; subst; eauto 10. Qed.

(* Polarity of matched occurrences of a distinguished atom.  [npol pos]
   forbids a matched occurrence at polarity [pos] (true = positive,
   false = negative); inside an arrow the domain flips the polarity. *)
Fixpoint npol (pos : bool) (Z : atom) (C D : typ) {struct C} : Prop :=
  match C, D with
  | typ_fvar X, typ_fvar Y =>
      if pos then
        (if X == Z then (if Y == Z then False else True) else True)
      else True
  | typ_arrow C1 C2, typ_arrow D1 D2 =>
      npol (negb pos) Z C1 D1 /\ npol pos Z C2 D2
  | typ_mu C0, typ_mu D0 => npol pos Z C0 D0
  | _, _ => True
  end.

Definition nn (Z : atom) (C D : typ) : Prop := npol false Z C D.
Definition np (Z : atom) (C D : typ) : Prop := npol true Z C D.

Lemma npol_sym : forall pos Z C D, npol pos Z C D <-> npol pos Z D C.
Proof.
  intros pos Z C. revert pos.
  induction C as [| |n|x|C IHC|C1 IH1 C2 IH2];
    intros pos D; destruct D as [| |m|y|D0|D1 D2]; simpl; try tauto.
  - destruct pos; [|tauto].
    destruct (x == Z) as [Hx|Hx]; destruct (y == Z) as [Hy|Hy];
      simpl; tauto.
  - apply IHC.
  - destruct (IH1 (negb pos) D1) as [Hn1 Hp1].
    destruct (IH2 pos D2) as [Hn2 Hp2].
    split; intros [H1 H2]; split.
    + apply Hn1. exact H1.
    + apply Hn2. exact H2.
    + apply Hp1. exact H1.
    + apply Hp2. exact H2.
Qed.

Lemma npol_open_rec : forall Z X, X <> Z ->
  forall pos K C D,
  (npol pos Z (open_tt_rec K (typ_fvar X) C)
            (open_tt_rec K (typ_fvar X) D)
   <-> npol pos Z C D).
Proof.
  intros Z X HXZ pos K C. revert pos K.
  induction C as [| |n|x|T IHT|T1 IHT1 T2 IHT2];
    intros pos K D; destruct D as [| |m|y|D0|D1 D2]; simpl;
    try (simpl in *;
         repeat (match goal with
                   | |- context [ if ?b then _ else _ ] => destruct b
                 end; simpl in *); tauto).
  - apply (IHT pos (S K) D0).
  - destruct (IHT1 (negb pos) K D1) as [Hn1 Hp1].
    destruct (IHT2 pos K D2) as [Hn2 Hp2].
    split; intros [A B]; split.
    + apply Hn1. exact A.
    + apply Hn2. exact B.
    + apply Hp1. exact A.
    + apply Hp2. exact B.
Qed.

Lemma compat_closed : forall A B o1 o2 pol,
  (forall X, X \notin fv_tt A) ->
  (forall X, X \notin fv_tt B) ->
  compat o1 o2 pol A B.
Proof.
  induction A as [| |n|x|T IHT|A1 IHA1 A2 IHA2];
    intros B o1 o2 pol HA HB;
    destruct B as [| |m|y|BT|B1 B2]; simpl; try tauto.
  - exfalso. apply (HA x). simpl. fsetdec.
  - apply (IHT BT o1 o2 pol).
    + intros X HX. assert (Hin : X \in fv_tt (typ_mu T)). { simpl. exact HX. }
      exact (HA X Hin).
    + intros X HX. assert (Hin : X \in fv_tt (typ_mu BT)). { simpl. exact HX. }
      exact (HB X Hin).
  - split.
    + apply (IHA1 B1 o1 o2 (negb pol)).
      * intros X HX. assert (Hin : X \in fv_tt (typ_arrow A1 A2)). { simpl. fsetdec. }
        exact (HA X Hin).
      * intros X HX. assert (Hin : X \in fv_tt (typ_arrow B1 B2)). { simpl. fsetdec. }
        exact (HB X Hin).
    + apply (IHA2 B2 o1 o2 pol).
      * intros X HX. assert (Hin : X \in fv_tt (typ_arrow A1 A2)). { simpl. fsetdec. }
        exact (HA X Hin).
      * intros X HX. assert (Hin : X \in fv_tt (typ_arrow B1 B2)). { simpl. fsetdec. }
        exact (HB X Hin).
Qed.

Lemma compat_fvar_true : forall o1 o2 X,
  compat o1 o2 true (typ_fvar X) (typ_fvar X) ->
  o1 X = true /\ o2 X = false.
Proof.
  intros o1 o2 X H. unfold compat in H. rewrite eq_dec_refl in H. simpl in H.
  destruct (o1 X); destruct (o2 X); simpl in *;
    try contradiction; try discriminate; try (split; reflexivity).
Qed.

Lemma gen_arrow_step : forall Ea o1 o2 f g A1 A2 B1 B2,
  sub_amber Ea (ren_pick o2 f g B1) (ren_pick o1 f g A1) ->
  sub_amber Ea (ren_pick o1 f g A2) (ren_pick o2 f g B2) ->
  sub_amber Ea (ren_pick o1 f g (typ_arrow A1 A2))
               (ren_pick o2 f g (typ_arrow B1 B2)).
Proof.
  intros. change (sub_amber Ea
    (typ_arrow (ren_pick o1 f g A1) (ren_pick o1 f g A2))
    (typ_arrow (ren_pick o2 f g B1) (ren_pick o2 f g B2))).
  apply sam_arrow; assumption.
Qed.

Lemma gen_mu_rec_step : forall Ea A B,
  (forall X Y, X \notin domA Ea -> Y \notin {{X}} \u domA Ea ->
     sub_amber ((X,Y)::Ea) (open_tt A X) (open_tt B Y)) ->
  sub_amber Ea (typ_mu A) (typ_mu B).
Proof.
  intros Ea A B H.
  apply sam_rec with (L := domA Ea).
  intros X Y HX HY. apply H; assumption.
Qed.

Lemma compat_flip : forall A B o1 o2 pol,
  compat o1 o2 pol A B <-> compat o2 o1 (negb pol) B A.
Proof.
  induction A as [| |n|x|T IHT|A1 IHA1 A2 IHA2];
  intros B o1 o2 pol.
  - destruct B as [| |m|y|BT|B1 B2]; simpl; tauto.
  - destruct B as [| |m|y|BT|B1 B2]; simpl; tauto.
  - destruct B as [| |m|y|BT|B1 B2]; simpl; tauto.
  - destruct B as [| |m|y|BT|B1 B2]; simpl.
    + tauto. + tauto. + tauto.
    + destruct (x == y) as [Heq|Hneq].
      * subst y. rewrite !eq_dec_refl. simpl.
        destruct (o1 x); destruct (o2 x); destruct pol; simpl; try (split; intros H); try reflexivity; try (inversion H); try discriminate; tauto; tauto.
      * destruct (y == x) as [Heq|Hneq2].
        -- subst y. exfalso. apply Hneq. reflexivity.
        -- tauto.
    + tauto. + tauto.
  - (* A = mu T *) destruct B as [| |m|y|BT|B1 B2]; simpl.
    + tauto. + tauto. + tauto. + tauto.
    + apply IHT.
    + tauto.
  - (* A = arrow *) destruct B as [| |m|y|BT|B1 B2]; simpl.
    + tauto. + tauto. + tauto. + tauto. + tauto.
    + destruct (IHA1 B1 o1 o2 (negb pol)) as [Hl Hr].
      destruct (IHA2 B2 o1 o2 pol) as [Hl2 Hr2].
      split; intros [H1 H2]; split.
      * apply Hl. exact H1.
      * apply Hl2. exact H2.
      * apply Hr. exact H1.
      * apply Hr2. exact H2.
Qed.

Lemma compat_flip_false : forall A B o1 o2,
  compat o1 o2 false A B -> compat o2 o1 true B A.
Proof. intros A B o1 o2 H. apply compat_flip. exact H. Qed.


(* ============== opening injectivity =============================== *)

Lemma open_tt_rec_inj : forall T U K X,
  X \notin fv_tt T -> X \notin fv_tt U ->
  open_tt_rec K (typ_fvar X) T = open_tt_rec K (typ_fvar X) U -> T = U.
Proof.
  induction T as [| |n|x|T IHT|T1 IHT1 T2 IHT2];
  intros U K X HT HU Heq;
  destruct U as [| |m|y|U0|U1 U2]; simpl in *;
  repeat match type of Heq with context [ if ?b then _ else _ ] => destruct b end;
  try discriminate; try reflexivity.
  - subst n. f_equal. exact e0.
  - inversion Heq. reflexivity.
  - exfalso. inversion Heq. subst y. apply HU. fsetdec.
  - exfalso. inversion Heq. subst x. apply HT. fsetdec.
  - inversion Heq. reflexivity.
  - injection Heq as Heq'. f_equal. apply IHT with (K:=S K) (X:=X).
    + exact HT.
    + exact HU.
    + exact Heq'.
  - injection Heq as E1 E2. f_equal.
    + apply IHT1 with (K:=K) (X:=X).
      * fsetdec. * fsetdec. * exact E1.
    + apply IHT2 with (K:=K) (X:=X).
      * fsetdec. * fsetdec. * exact E2.
Qed.

Lemma sub_antisym : forall E A B, sub E A B -> sub E B A -> A = B.
Proof.
  intros E A B H1. induction H1 as
    [ E0 wfE
    | E0 X wfE Hb
    | E0 A0 wfE WFA
    | E0 A1 A2 B1 B2 s1 IH1 s2 IH2
    | L A1 A2 E0 p1 IH1 p2 IH2 ]; intros H2.
  - reflexivity.
  - reflexivity.
  - inversion H2. reflexivity.
  - inversion H2. pose proof (IH1 H4) as E1a. pose proof (IH2 H6) as E2a.
    subst. reflexivity.
  - inversion H2.
    destruct (atom_fresh (L \u L0 \u fv_tt A1 \u fv_tt A2)) as [X HX].
    assert (HXL : X \notin L) by fsetdec.
    assert (HXL0 : X \notin L0) by fsetdec.
    assert (HX1 : X \notin fv_tt A1) by fsetdec.
    assert (HX2 : X \notin fv_tt A2) by fsetdec.
    pose proof (IH1 X HXL (H3 X HXL0)) as Heq.
    assert (A1 = A2).
    { apply (open_tt_rec_inj A1 A2 0 X).
      - exact HX1.
      - exact HX2.
      - unfold open_tt in Heq. exact Heq. }
    subst. reflexivity.
Qed.

(* Refl branch of the mu case of the generalized translation lemma:
   when the two renamed bodies are syntactically equal, Amber's sam_refl
   closes the mu/mu comparison, provided the body is well formed. *)
Lemma sam_refl_ren_mu : forall E A1 A2 Ea o1 o2 f g,
  wfe_amber Ea ->
  WF E (typ_mu A1) ->
  AtomSetImpl.Subset (fv_tt (typ_mu A1)) (bindsub_atoms E) ->
  (forall Z, binds Z bind_sub E -> In (f Z, g Z) Ea) ->
  ren_pick o1 f g A1 = ren_pick o2 f g A2 ->
  sub_amber Ea (ren_pick o1 f g (typ_mu A1))
               (ren_pick o2 f g (typ_mu A2)).
Proof.
  intros E A1 A2 Ea o1 o2 f g Hwe HWF Hfv Hcorr Hren.
  change (sub_amber Ea (typ_mu (ren_pick o1 f g A1))
                      (typ_mu (ren_pick o2 f g A2))).
  rewrite Hren.
  apply sam_refl.
  - exact Hwe.
  - rewrite <- Hren.
    change (wf_amber Ea (ren_pick o1 f g (typ_mu A1))).
    apply (wf_amber_ren_pick E (typ_mu A1) Ea o1 f g HWF Hwe Hcorr Hfv).
Qed.

(* The top-level reduction: the target follows from any generalized
   translation lemma of this shape.  Closed types have no free atoms, so
   the compatibility condition is vacuous and the renamings are identities. *)
Lemma amber_complete_of_gen :
  (forall E A B, sub E A B ->
     forall Ea (o1 o2 : atom -> bool) (f g : atom -> atom),
       wfe_amber Ea ->
       (forall Z, binds Z bind_sub E -> In (f Z, g Z) Ea) ->
       AtomSetImpl.Subset (fv_tt A) (bindsub_atoms E) ->
       AtomSetImpl.Subset (fv_tt B) (bindsub_atoms E) ->
       compat o1 o2 true A B ->
       sub_amber Ea (ren_pick o1 f g A) (ren_pick o2 f g B)) ->
  forall A B, sub nil A B ->
    sub_amber nil (amber_cov nil nil A Neg) (amber_cov nil nil B Pos).
Proof.
  intros Hgen A B H.
  change (sub_amber nil A B).
  assert (HsubA : AtomSetImpl.Subset (fv_tt A) (bindsub_atoms nil)).
  { apply wf_fv_bindsub.
    exact (proj1 (sub_wf (@nil (atom * binding)) A B H)). }
  assert (HsubB : AtomSetImpl.Subset (fv_tt B) (bindsub_atoms nil)).
  { apply wf_fv_bindsub.
    exact (proj2 (sub_wf (@nil (atom * binding)) A B H)). }
  assert (HclA : forall X, X \notin fv_tt A).
  { intros X HX. pose proof (HsubA X HX) as HE.
    assert (HEm : X \notin empty) by fsetdec.
    exact (HEm HE). }
  assert (HclB : forall X, X \notin fv_tt B).
  { intros X HX. pose proof (HsubB X HX) as HE.
    assert (HEm : X \notin empty) by fsetdec.
    exact (HEm HE). }
  assert (HrA : ren_pick (fun _ => true) (fun X => X) (fun X => X) A = A)
    by apply ren_pick_id.
  assert (HrB : ren_pick (fun _ => true) (fun X => X) (fun X => X) B = B)
    by apply ren_pick_id.
  assert (Hc : sub_amber nil
                 (ren_pick (fun _ => true) (fun X => X) (fun X => X) A)
                 (ren_pick (fun _ => true) (fun X => X) (fun X => X) B)).
  { apply (Hgen (@nil (atom * binding)) A B H (@nil (atom * atom))
                 (fun _ => true) (fun _ => true)
                 (fun X => X) (fun X => X)).
    - apply wfea_base.
    - intros Z HZ. unfold binds in HZ. simpl in HZ. destruct HZ.
    - exact HsubA.
    - exact HsubB.
    - apply (compat_closed A B (fun _ => true) (fun _ => true) true HclA HclB). }
  rewrite HrA in Hc. rewrite HrB in Hc. exact Hc.
Qed.



(* ===== merged Mode ===== *)

Fixpoint cov_fun (Ea : env_amber) (Em : env_mode) (m : Mode) (X : atom) : atom :=
  match Ea, Em with
  | (X0,Y)::Ea', m'::Em' =>
      if X == X0 then (if eqMode m' m then Y else X)
      else cov_fun Ea' Em' m X
  | _,_ => X
  end.

Lemma cov_fun_outside : forall Ea Em m X,
  X \notin domA Ea -> cov_fun Ea Em m X = X.
Proof.
  induction Ea as [| [X0 Y] Ea IH]; intros Em m X Hout; simpl.
  - reflexivity.
  - destruct Em as [|m' Em]; [reflexivity|].
    simpl.
    assert (HX0 : X <> X0). { intro Heq. subst X0. simpl in Hout. fsetdec. }
    destruct (X == X0) as [Heq|Hneq].
    + exfalso. exact (HX0 Heq).
    + apply IH. simpl in Hout. fsetdec.
Qed.

Lemma cov_fun_in_domA : forall Ea Em m X,
  wfe_amber Ea ->
  (exists Y, In (X,Y) Ea) ->
  cov_fun Ea Em m X \in domA Ea.
Proof.
  induction Ea as [| [X0 Y0] Ea IH]; intros Em m X Hwe Hin.
  - destruct Hin as [Y Hin]. destruct Hin.
  - simpl. destruct Em as [|m' Em].
    + destruct Hin as [Y Hin]. apply in_domA_pair_1 in Hin. exact Hin.
    + inversion Hwe as [| X1 Y1 E1 HX HY Hwe']; subst.
      destruct (X == X0) as [Heq|Hneq].
      * subst X. destruct (eqMode m' m); simpl.
        -- fsetdec.
        -- fsetdec.
      * apply in_domA_cons. right. right. apply IH; [ exact Hwe' | ].
        destruct Hin as [Y Hin]. simpl in Hin. destruct Hin as [Heq|Hin].
        -- inversion Heq; subst. exfalso. apply Hneq. reflexivity.
        -- exists Y. exact Hin.
Qed.

Lemma ren_tt_subst_fvar : forall f X Y T,
  f X = f Y ->
  ren_tt f (subst_tt X (typ_fvar Y) T) = ren_tt f T.
Proof.
  intros f X Y T Heq. induction T as [| |n|x|T0 IH|T1 IH1 T2 IH2]; simpl.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - destruct (x == X) as [Hx|Hx].
    + subst x. simpl. rewrite Heq. reflexivity.
    + simpl. reflexivity.
  - f_equal. exact IH.
  - f_equal; [exact IH1 | exact IH2].
Qed.

Lemma ren_tt_ext_fv : forall f g T,
  (forall X, X \in fv_tt T -> f X = g X) ->
  ren_tt f T = ren_tt g T.
Proof.
  intros f g T. induction T as [| |n|x|T0 IH|T1 IH1 T2 IH2]; simpl; intros H.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - simpl. f_equal. apply H. simpl. fsetdec.
  - f_equal. apply IH. intros Y HY. apply H. simpl. exact HY.
  - f_equal.
    + apply IH1. intros Y HY. apply H. simpl. fsetdec.
    + apply IH2. intros Y HY. apply H. simpl. fsetdec.
Qed.

Lemma ren_tt_subst_fvar_fun : forall f X Y T,
  ren_tt f (subst_tt X (typ_fvar Y) T)
  = ren_tt (fun Z => if Z == X then f Y else f Z) T.
Proof.
  intros f X Y T. induction T as [| |n|x|T0 IH|T1 IH1 T2 IH2]; simpl.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - destruct (x == X) as [Hx|Hx]; [subst x; reflexivity|reflexivity].
  - f_equal. exact IH.
  - f_equal; [exact IH1 | exact IH2].
Qed.

Lemma amber_cov_ren : forall Ea,
  wfe_amber Ea ->
  forall Em T m,
  amber_cov Ea Em T m = ren_tt (cov_fun Ea Em m) T.
Proof.
  induction Ea as [| [X0 Y] Ea IH]; intros Hwe Em T m.
  - destruct Em; [change (T = ren_tt (fun X => X) T); symmetry; apply ren_tt_id|].
    change (T = ren_tt (fun X => X) T). symmetry. apply ren_tt_id.
  - inversion Hwe as [| X1 Y1 E1 HX HXpart Hwe']; subst.
    destruct Em as [|m' Em].
    + change (T = ren_tt (fun X => X) T). symmetry. apply ren_tt_id.
    + simpl.
      destruct (eqMode m' m) as [Hmode|Hmode].
      * rewrite (IH Hwe' Em (subst_tt X0 (typ_fvar Y) T) m).
        set (f' := cov_fun Ea Em m).
        assert (Hf'X : f' X0 = X0).
        { unfold f'. apply cov_fun_outside. exact HX. }
        assert (Hf'Y : f' Y = Y).
        { unfold f'. apply cov_fun_outside. fsetdec. }
        rewrite ren_tt_subst_fvar_fun.
        apply ren_tt_ext_fv.
        intros Z HZ.
        destruct (Z == X0) as [Heq|Hneq].
        -- subst Z. rewrite Hf'Y. reflexivity.
        -- reflexivity.
      * rewrite (IH Hwe' Em T m).
        set (f' := cov_fun Ea Em m).
        assert (Hf'X : f' X0 = X0).
        { unfold f'. apply cov_fun_outside. exact HX. }
        apply ren_tt_ext_fv.
        intros Z HZ.
        destruct (Z == X0) as [Heq|Hneq]; [subst Z; rewrite Hf'X; reflexivity|reflexivity].
Qed.

Lemma wf_amber_cov : forall E A Ea Em m,
  wfe_amber Ea -> WF E A ->
  (forall X, binds X bind_sub E -> exists Y, In (X,Y) Ea) ->
  AtomSetImpl.Subset (fv_tt A) (bindsub_atoms E) ->
  wf_amber Ea (amber_cov Ea Em A m).
Proof.
  intros E A Ea Em m Hwe HWF Hpair Hfv.
  rewrite (amber_cov_ren Ea Hwe Em A m).
  apply (wf_amber_ren E A HWF (cov_fun Ea Em m) Ea Hwe).
  - intros X Hb. destruct (Hpair X Hb) as [Y Hin].
    apply (cov_fun_in_domA Ea Em m X Hwe). exists Y. exact Hin.
  - exact Hfv.
Qed.


Definition polar_ok (flag : bool) (m : Mode) : Prop :=
  match flag with true => m = Pos | false => m = Neg end.

Definition sideA (flag : bool) : Mode := if flag then Neg else Pos.
Definition sideB (flag : bool) : Mode := if flag then Pos else Neg.

Fixpoint mode_of (X : atom) (Ea : env_amber) (Em : env_mode) : option Mode :=
  match Ea, Em with
  | (X0,Y)::Ea', m'::Em' => if X == X0 then Some m' else mode_of X Ea' Em'
  | _,_ => None
  end.

Fixpoint modes_ok (flag : bool) (Ea : env_amber) (Em : env_mode)
                 (A B : typ) {struct A} : Prop :=
  match A, B with
  | typ_fvar X, typ_fvar Y =>
      if X == Y then
        match mode_of X Ea Em with
        | Some m => polar_ok flag m
        | None => False
        end
      else True
  | typ_arrow A1 A2, typ_arrow B1 B2 =>
      modes_ok (negb flag) Ea Em A1 B1 /\ modes_ok flag Ea Em A2 B2
  | typ_mu A1, typ_mu B1 => modes_ok flag Ea Em A1 B1
  | _,_ => True
  end.

Lemma modes_ok_closed : forall flag Ea Em A B,
  (forall X, X \notin fv_tt A) ->
  (forall X, X \notin fv_tt B) ->
  modes_ok flag Ea Em A B.
Proof.
  intros flag Ea Em A. revert flag Ea Em.
  induction A as [| |n|x|A0 IH|A1 IH1 A2 IH2];
    intros flag Ea Em B HA HB; destruct B as [| |m|y|B0|B1 B2]; simpl; try tauto.
  - exfalso. apply (HA x). simpl. fsetdec.
  - apply IH; [ exact HA | exact HB ].
  - split.
    + apply IH1.
      * intros X HX. apply (HA X). simpl. fsetdec.
      * intros X HX. apply (HB X). simpl. fsetdec.
    + apply IH2.
      * intros X HX. apply (HA X). simpl. fsetdec.
      * intros X HX. apply (HB X). simpl. fsetdec.
Qed.

Definition ModeGen : Prop :=
  forall E A B, sub E A B ->
  forall flag Ea Em,
    wfe_amber Ea ->
    (forall X, binds X bind_sub E -> exists Y, In (X,Y) Ea) ->
    modes_ok flag Ea Em A B ->
    sub_amber Ea (amber_cov Ea Em A (sideA flag))
                (amber_cov Ea Em B (sideB flag)).

Definition sa_rec_mode_hole : Prop :=
  forall E A1 A2 flag Ea Em W,
    W \notin domA Ea ->
    W \notin fv_tt A1 ->
    W \notin fv_tt A2 ->
    wfe_amber Ea ->
    (forall X, binds X bind_sub E -> exists Y, In (X,Y) Ea) ->
    sub (W ~ bind_sub ++ E) (open_tt A1 (typ_fvar W)) (open_tt A2 (typ_fvar W)) ->
    sub (W ~ bind_sub ++ E) (open_tt A1 (open_tt A1 (typ_fvar W)))
                            (open_tt A2 (open_tt A2 (typ_fvar W))) ->
    modes_ok flag Ea Em A1 A2 ->
    forall Y, Y \notin {{W}} \u domA Ea ->
      modes_ok flag ((W,Y)::Ea) ((sideB flag)::Em)
                (open_tt A1 (typ_fvar W)) (open_tt A2 (typ_fvar W)).

Lemma amber_complete_of_ModeGen :
  ModeGen ->
  forall A B, sub nil A B ->
    sub_amber nil (amber_cov nil nil A Neg) (amber_cov nil nil B Pos).
Proof.
  intros Hgen A B Hsub.
  rewrite amber_cov_nil. rewrite amber_cov_nil.
  apply (Hgen nil A B Hsub true nil nil).
  - apply wfea_base.
  - intros X HX. simpl in HX. destruct HX.
  - assert (HAcl : forall X, X \notin fv_tt A).
    { intros X HX.
      pose proof (wf_fv_bindsub nil A (proj1 (sub_wf nil A B Hsub)) X HX) as HE.
      simpl in HE. fsetdec. }
    assert (HBcl : forall X, X \notin fv_tt B).
    { intros X HX.
      pose proof (wf_fv_bindsub nil B (proj2 (sub_wf nil A B Hsub)) X HX) as HE.
      simpl in HE. fsetdec. }
    apply modes_ok_closed; assumption.
Qed.


(* ===== merged Purity ===== *)

(* ================================================================== *)
(* Environments containing only subtype bindings.                      *)
(* ================================================================== *)

Definition bindsub_only (E : env) : Prop :=
  forall (X : atom) (b : binding), In (X, b) E -> b = bind_sub.

Lemma bindsub_only_nil : bindsub_only nil.
Proof. intros X b H. simpl in H. destruct H. Qed.

Lemma bindsub_only_cons : forall E Z,
  bindsub_only E -> bindsub_only ((Z, bind_sub) :: E).
Proof.
  intros E Z H X b Hin. simpl in Hin. destruct Hin as [Heq|Hin].
  - inversion Heq. reflexivity.
  - exact (H X b Hin).
Qed.

Lemma bindsub_only_tail : forall E Z,
  bindsub_only ((Z, bind_sub) :: E) -> bindsub_only E.
Proof.
  intros E Z H X b Hin. exact (H X b (or_intror Hin)).
Qed.

(* ================================================================== *)
(* Removing an unused bind_sub from under a prefix.                    *)
(* ================================================================== *)

Lemma dom_prefix_subset : forall Δ E X,
  AtomSetImpl.Subset (dom (Δ ++ E)) (dom (Δ ++ (X, bind_sub) :: E)).
Proof.
  induction Δ as [| [Y b] Δ IH]; intros E X z Hz; simpl in *.
  - fsetdec.
  - rewrite add_iff in *. destruct Hz as [Heq|Hz].
    + left. exact Heq.
    + right. apply (IH E X z Hz).
Qed.

Lemma wf_env_remove_sub : forall Δ E X,
  bindsub_only (Δ ++ (X, bind_sub) :: E) ->
  wf_env (Δ ++ (X, bind_sub) :: E) ->
  wf_env (Δ ++ E).
Proof.
  induction Δ as [| [Y b] Δ IH]; intros E X Hbs Hwf; simpl in *.
  - inversion Hwf as [| E0 Z hwf hnot | E0 x T hwf hwfs hnot]; subst.
    exact hwf.
  - assert (Hb : b = bind_sub).
    { apply (Hbs Y b). left. reflexivity. }
    subst b.
    inversion Hwf as [| E0 Z hwf hnot | E0 x T hwf hwfs hnot]; subst.
    + apply (wf_env_sub (Δ ++ E) Y).
      * apply (IH E X).
        -- apply bindsub_only_tail in Hbs. exact Hbs.
        -- exact hwf.
      * intros HY. apply hnot. apply (dom_prefix_subset Δ E X). exact HY.
Qed.

(* ================================================================== *)
(* Free-variable facts for opening.                                    *)
(* ================================================================== *)

Lemma fv_open_tt_rec_subset : forall T K U,
  AtomSetImpl.Subset (fv_tt (open_tt_rec K U T)) (union (fv_tt T) (fv_tt U)).
Proof.
  induction T as [| |n|x|T IH|T1 IH1 T2 IH2]; intros K U z Hz; simpl in *.
  - fsetdec.
  - fsetdec.
  - destruct (K === n); simpl in Hz; fsetdec.
  - fsetdec.
  - apply IH in Hz. fsetdec.
  - apply union_iff in Hz as [Hz|Hz].
    + apply IH1 in Hz. fsetdec.
    + apply IH2 in Hz. fsetdec.
Qed.

Lemma notin_fv_open_any : forall A U X,
  X \notin fv_tt A -> X \notin fv_tt U -> X \notin fv_tt (open_tt A U).
Proof.
  intros A U X HA HU Hx.
  apply (fv_open_tt_rec_subset A 0 U X) in Hx.
  apply union_iff in Hx. destruct Hx as [Hx|Hx]; fsetdec.
Qed.

Lemma notin_fv_open_fvar : forall A Z X,
  X \notin fv_tt A -> Z <> X -> X \notin fv_tt (open_tt A (typ_fvar Z)).
Proof.
  intros A Z X HA HZ.
  apply notin_fv_open_any; [ exact HA | simpl; fsetdec ].
Qed.

Lemma notin_fv_open_double : forall A Z X,
  X \notin fv_tt A -> Z <> X ->
  X \notin fv_tt (open_tt A (open_tt A (typ_fvar Z))).
Proof.
  intros A Z X HA HZ.
  apply notin_fv_open_any.
  - exact HA.
  - apply notin_fv_open_fvar; assumption.
Qed.

(* ================================================================== *)
(* WF strengthening when an unused bind_sub is removed.                *)
(* ================================================================== *)

Lemma WF_remove_sub : forall E0 A, WF E0 A ->
  forall Δ E X, E0 = Δ ++ (X, bind_sub) :: E ->
    bindsub_only E0 -> X \notin fv_tt A -> WF (Δ ++ E) A.
Proof.
  intros E0 A H. induction H as
    [ E0 | E0 | Z E0 Hb | E0 A1 A2 w1 IH1 w2 IH2 | L E0 A0 p1 IH1 p2 IH2 ];
    intros Δ E X HE Hbs HX.
  - apply WF_top.
  - apply WF_nat.
  - assert (HZ : Z <> X).
    { intro Heq. apply HX. simpl. rewrite Heq. fsetdec. }
    apply WF_fvar. rewrite HE in Hb.
    apply (binds_remove Δ E X Z Hb HZ).
  - apply WF_arrow.
    + apply (IH1 Δ E X HE Hbs). simpl in HX. fsetdec.
    + apply (IH2 Δ E X HE Hbs). simpl in HX. fsetdec.
  - apply WF_rec with (L := L \u {{X}}).
    + intros Z HZ.
      assert (HZL : Z \notin L) by fsetdec.
      assert (HZX : Z <> X) by fsetdec.
      assert (HXo : X \notin fv_tt (open_tt A0 (typ_fvar Z))).
      { apply notin_fv_open_fvar; [ | exact HZX ].
        unfold fv_tt in HX. simpl in HX. exact HX. }
      specialize (IH1 Z HZL (Z ~ bind_sub ++ Δ) E X).
      apply IH1.
      * rewrite HE. reflexivity.
      * apply bindsub_only_cons. exact Hbs.
      * exact HXo.
    + intros Z HZ.
      assert (HZL : Z \notin L) by fsetdec.
      assert (HZX : Z <> X) by fsetdec.
      assert (HXo : X \notin fv_tt (open_tt A0 (open_tt A0 (typ_fvar Z)))).
      { apply notin_fv_open_double; [ | exact HZX ].
        unfold fv_tt in HX. simpl in HX. exact HX. }
      specialize (IH2 Z HZL (Z ~ bind_sub ++ Δ) E X).
      apply IH2.
      * rewrite HE. reflexivity.
      * apply bindsub_only_cons. exact Hbs.
      * exact HXo.
Qed.

(* ================================================================== *)
(* sub strengthening when an unused bind_sub is removed.               *)
(* ================================================================== *)

Lemma sub_remove_sub : forall E0 S T, sub E0 S T ->
  forall Δ E X, E0 = Δ ++ (X, bind_sub) :: E ->
    bindsub_only E0 -> X \notin fv_tt S -> X \notin fv_tt T ->
    sub (Δ ++ E) S T.
Proof.
  intros E0 S T H.
  induction H as
    [ E0 h
    | E0 Z h Hb
    | E0 A h HWF
    | E0 A1 A2 B1 B2 s1 IH1 s2 IH2
    | L A1 A2 E0 p1 IH1 p2 IH2 ];
    intros Δ E X HE Hbs HXS HXT.
  - apply sa_nat. apply (wf_env_remove_sub Δ E X).
    + rewrite <- HE. exact Hbs.
    + rewrite <- HE. exact h.
  - assert (HZ : Z <> X).
    { intro Heq. apply HXS. simpl. rewrite Heq. fsetdec. }
    apply sa_fvar.
    + apply (wf_env_remove_sub Δ E X).
      * rewrite <- HE. exact Hbs.
      * rewrite <- HE. exact h.
    + rewrite HE in Hb. apply (binds_remove Δ E X Z Hb HZ).
  - apply sa_top.
    + apply (wf_env_remove_sub Δ E X).
      * rewrite <- HE. exact Hbs.
      * rewrite <- HE. exact h.
    + apply (WF_remove_sub E0 A HWF Δ E X HE Hbs HXS).
  - apply sa_arrow.
    + apply (IH1 Δ E X HE Hbs).
      * simpl in HXT. intros H. apply HXT. simpl. fsetdec.
      * simpl in HXS. intros H. apply HXS. simpl. fsetdec.
    + apply (IH2 Δ E X HE Hbs).
      * simpl in HXS. intros H. apply HXS. simpl. fsetdec.
      * simpl in HXT. intros H. apply HXT. simpl. fsetdec.
  - apply sa_rec with (L := L \u {{X}}).
    + intros Z HZ.
      assert (HZL : Z \notin L) by fsetdec.
      assert (HZX : Z <> X) by fsetdec.
      assert (HXA1 : X \notin fv_tt A1).
      { unfold fv_tt in HXS. simpl in HXS. exact HXS. }
      assert (HXA2 : X \notin fv_tt A2).
      { unfold fv_tt in HXT. simpl in HXT. exact HXT. }
      apply (IH1 Z HZL (Z ~ bind_sub ++ Δ) E X).
      * rewrite HE. reflexivity.
      * apply bindsub_only_cons. exact Hbs.
      * apply notin_fv_open_fvar; [ exact HXA1 | exact HZX ].
      * apply notin_fv_open_fvar; [ exact HXA2 | exact HZX ].
    + intros Z HZ.
      assert (HZL : Z \notin L) by fsetdec.
      assert (HZX : Z <> X) by fsetdec.
      assert (HXA1 : X \notin fv_tt A1).
      { unfold fv_tt in HXS. simpl in HXS. exact HXS. }
      assert (HXA2 : X \notin fv_tt A2).
      { unfold fv_tt in HXT. simpl in HXT. exact HXT. }
      apply (IH2 Z HZL (Z ~ bind_sub ++ Δ) E X).
      * rewrite HE. reflexivity.
      * apply bindsub_only_cons. exact Hbs.
      * apply notin_fv_open_double; [ exact HXA1 | exact HZX ].
      * apply notin_fv_open_double; [ exact HXA2 | exact HZX ].
Qed.

Lemma sub_remove_head : forall E X S T,
  bindsub_only (X ~ bind_sub ++ E) ->
  sub (X ~ bind_sub ++ E) S T ->
  X \notin fv_tt S -> X \notin fv_tt T ->
  sub E S T.
Proof.
  intros E X S T Hbs H HS HT.
  exact (sub_remove_sub (X ~ bind_sub ++ E) S T H nil E X eq_refl Hbs HS HT).
Qed.

(* ================================================================== *)
(* npol is decidable.                                                  *)
(* ================================================================== *)

Lemma npol_dec : forall pos Z C D, {npol pos Z C D} + {~ npol pos Z C D}.
Proof.
  intros pos Z C. revert pos.
  induction C as [| |n|X|C IHC|C1 IH1 C2 IH2];
    intros pos D; destruct D as [| |m|Y|D0|D1 D2]; simpl;
    try (left; exact I).
  - destruct pos as [|]; [| left; exact I].
    destruct (X == Z) as [HX|HX]; [destruct (Y == Z) as [HY|HY]|];
      simpl; [ right; intro H; exact H | left; exact I | left; exact I ].
  - exact (IHC pos D0).
  - destruct (IH1 (negb pos) D1) as [H1|H1];
      destruct (IH2 pos D2) as [H2|H2].
    + left. split; assumption.
    + right. intros [A B]. apply H2. exact B.
    + right. intros [A B]. apply H1. exact A.
    + right. intros [A B]. apply H1. exact A.
Qed.

Definition pcond (tag : bool) (W : atom) (C D : typ) : Prop :=
  if tag then ~ npol true W C D else ~ npol false W C D.

Definition pconcl (tag : bool) (E : env) (S T : typ) : Prop :=
  if tag then sub E S T else sub E T S.

(* ================================================================== *)
(* Main extraction lemma.                                              *)
(* ================================================================== *)

Lemma purity_aux : forall E C D, sub E C D ->
  bindsub_only E -> wf_env E ->
  forall tag W S T,
    lc_tt S -> lc_tt T ->
    sub E (subst_tt W S C) (subst_tt W T D) ->
    pcond tag W C D ->
    pconcl tag E S T.
Proof.
  intros E C D H.
  induction H as
    [ E0 h
    | E0 Z h Hb
    | E0 A h HWF
    | E0 A1 A2 B1 B2 s1 IH1 s2 IH2
    | L A1 A2 E0 p1 IH1 p2 IH2 ];
    intros Hbs Hwf tag W S T HlcS HlcT HP2 Hcond.
  - destruct tag; simpl in Hcond; exfalso; apply Hcond; exact I.
  - destruct tag.
    + simpl in Hcond.
      destruct (Z == W) as [Heq|Hne]; simpl in Hcond.
      * subst Z. simpl in HP2. rewrite eq_dec_refl in HP2. simpl in HP2. exact HP2.
      * exfalso. apply Hcond. exact I.
    + simpl in Hcond. exfalso. apply Hcond. exact I.
  - destruct tag; destruct A; simpl in Hcond; exfalso; apply Hcond; exact I.
  - simpl in HP2.
    destruct (inv_arrow_l E0 (subst_tt W S A1) (subst_tt W S A2)
               (typ_arrow (subst_tt W T B1) (subst_tt W T B2)) HP2)
      as [ [Heq _] | [C1 [C2 [Heq [Hdom Hcod]]]]].
    + discriminate Heq.
    + inversion Heq; subst; clear Heq.
      destruct tag.
      * simpl in Hcond.
        destruct (npol_dec false W A1 B1) as [HP|HP].
        -- destruct (npol_dec true W A2 B2) as [HQ|HQ].
           ++ exfalso. apply Hcond. split; assumption.
           ++ exact (IH2 Hbs Hwf true W S T HlcS HlcT Hcod HQ).
        -- assert (HP' : ~ npol false W B1 A1).
           { intro Hn. apply HP. exact (proj1 (npol_sym false W B1 A1) Hn). }
           exact (IH1 Hbs Hwf false W T S HlcT HlcS Hdom HP').
      * simpl in Hcond.
        destruct (npol_dec true W A1 B1) as [HP|HP].
        -- destruct (npol_dec false W A2 B2) as [HQ|HQ].
           ++ exfalso. apply Hcond. split; assumption.
           ++ exact (IH2 Hbs Hwf false W S T HlcS HlcT Hcod HQ).
        -- assert (HP' : ~ npol true W B1 A1).
           { intro Hn. apply HP. exact (proj1 (npol_sym true W B1 A1) Hn). }
           exact (IH1 Hbs Hwf true W T S HlcT HlcS Hdom HP').
  - simpl in HP2.
    destruct (inv_mu_mu E0 (subst_tt W S A1) (subst_tt W T A2) HP2)
      as [L2 [HP2a HP2b]].
    destruct (atom_fresh (L \u L2 \u fv_tt S \u fv_tt T \u {{W}})) as [Y HY].
    assert (HYL : Y \notin L) by fsetdec.
    assert (HYL2 : Y \notin L2) by fsetdec.
    assert (HYW : Y <> W) by fsetdec.
    assert (HYS : Y \notin fv_tt S) by fsetdec.
    assert (HYT : Y \notin fv_tt T) by fsetdec.
    assert (HP2Y : sub (Y ~ bind_sub ++ E0)
        (subst_tt W S (open_tt A1 (typ_fvar Y)))
        (subst_tt W T (open_tt A2 (typ_fvar Y)))).
    { specialize (HP2a Y HYL2). unfold open_tt in HP2a.
      rewrite <- (subst_tt_open_atom_lc_rec W S A1 0 Y HlcS HYW) in HP2a.
      rewrite <- (subst_tt_open_atom_lc_rec W T A2 0 Y HlcT HYW) in HP2a.
      exact HP2a. }
    assert (HcY : pcond tag W (open_tt A1 (typ_fvar Y))
                             (open_tt A2 (typ_fvar Y))).
    { unfold pcond in Hcond |- *.
      destruct tag; simpl in *.
      - intro Hn. apply Hcond.
        exact (proj1 (npol_open_rec W Y HYW true 0 A1 A2) Hn).
      - intro Hn. apply Hcond.
        exact (proj1 (npol_open_rec W Y HYW false 0 A1 A2) Hn). }
    assert (Hres : pconcl tag (Y ~ bind_sub ++ E0) S T).
    { exact (IH1 Y HYL (bindsub_only_cons E0 Y Hbs)
               (sub_wf_env (Y ~ bind_sub ++ E0) (open_tt A1 (typ_fvar Y)) (open_tt A2 (typ_fvar Y)) (p1 Y HYL)) tag W S T HlcS HlcT HP2Y HcY). }
    destruct tag; simpl in Hres; simpl.
    + exact (sub_remove_head E0 Y S T (bindsub_only_cons E0 Y Hbs) Hres HYS HYT).
    + exact (sub_remove_head E0 Y T S (bindsub_only_cons E0 Y Hbs) Hres HYT HYS).
Qed.

(* ================================================================== *)
(* Purity corollary: if the two substitution types differ, every       *)
(* matched hole occurs at an even number of domain flips.              *)
(* ================================================================== *)

Lemma purity : forall E U V W,
  bindsub_only E -> wf_env E -> lc_tt U -> lc_tt V ->
  sub E U V ->
  sub E (subst_tt W U U) (subst_tt W V V) ->
  U <> V -> npol false W U V.
Proof.
  intros E U V W Hbs Hwf HlcU HlcV H1 H2 Hne.
  destruct (npol_dec false W U V) as [H|H]; [exact H|].
  exfalso. apply Hne.
  pose proof (purity_aux E U V H1 Hbs Hwf false W U V HlcU HlcV H2 H) as Hres.
  simpl in Hres.
  exact (sub_antisym E U V H1 Hres).
Qed.

(* ================================================================== *)
(* Core bad-frame exclusion battery.                                   *)
(*                                                                     *)
(* At a node with a source derivation [sub E C D] and an ancestor       *)
(* companion [sub E (subst W S C) (subst W T D)], an odd matched hole  *)
(* occurrence forces the reversed relation T <: S, contradicting any    *)
(* forward S <: T (with S <> T).  This is the single-step exclusion that *)
(* fires whenever the relevant hole occurrence sits at odd parity.      *)
(* ================================================================== *)

Lemma exclusion_at_node : forall E C D W S T,
  bindsub_only E ->
  wf_env E ->
  lc_tt S -> lc_tt T ->
  sub E C D ->
  sub E (subst_tt W S C) (subst_tt W T D) ->
  sub E S T ->
  S <> T ->
  ~ npol false W C D ->
  False.
Proof.
  intros E C D W S T Hbs Hwf HlcS HlcT H1 H2 Hfwd Hne Hcond.
  pose proof (purity_aux E C D H1 Hbs Hwf false W S T HlcS HlcT H2 Hcond)
    as Hrev.
  simpl in Hrev.
  exact (Hne (sub_antisym E S T Hfwd Hrev)).
Qed.

(* ================================================================== *)
(* Hole purity yields mode consistency for types whose fvars are       *)
(* exactly the hole.  (tag = false corresponds to even occurrences.)   *)
(* ================================================================== *)

Definition mflag (tag flag : bool) : bool := if tag then negb flag else flag.

Lemma mflag_negb : forall tag flag,
  mflag (negb tag) flag = negb (mflag tag flag).
Proof. destruct tag, flag; reflexivity. Qed.

Lemma modes_ok_of_npol : forall tag flag Ea Em U V W,
  (forall X, X \in fv_tt U -> X = W) ->
  (forall X, X \in fv_tt V -> X = W) ->
  mode_of W Ea Em = Some (sideB flag) ->
  npol tag W U V ->
  modes_ok (mflag tag flag) Ea Em U V.
Proof.
  intros tag flag Ea Em U. revert tag flag Ea Em.
  induction U as [| |n|X|U0 IHU|U1 IH1 U2 IH2].
  - intros tag flag Ea Em V W HfvU HfvV Hmode Hn.
    destruct V; simpl in *; exact I.
  - intros tag flag Ea Em V W HfvU HfvV Hmode Hn.
    destruct V; simpl in *; exact I.
  - intros tag flag Ea Em V W HfvU HfvV Hmode Hn.
    destruct V; simpl in *; exact I.
  - intros tag flag Ea Em V W HfvU HfvV Hmode Hn.
    destruct V as [| |m|Y|V0|V1 V2]; simpl in *; try exact I.
    destruct (X == Y) as [Heq|Hne].
    + subst Y.
      destruct tag.
      * simpl in Hn.
        assert (HXW : X = W) by (apply HfvU; simpl; fsetdec).
        subst X. simpl in Hn.
        repeat rewrite eq_dec_refl in Hn. simpl in Hn.
        exfalso. exact Hn.
      * rewrite (HfvU X) by (simpl; fsetdec).
        simpl. rewrite Hmode.
        destruct flag; simpl; reflexivity.
    + exact I.
  - intros tag flag Ea Em V W HfvU HfvV Hmode Hn.
    destruct V as [| |m|Y|V0|V1 V2]; simpl in *; try exact I.
    apply (IHU tag flag Ea Em V0 W).
    + intros Z HZ. apply HfvU. simpl. exact HZ.
    + intros Z HZ. apply HfvV. simpl. exact HZ.
    + exact Hmode.
    + exact Hn.
  - intros tag flag Ea Em V W HfvU HfvV Hmode Hn.
    destruct V as [| |m|Y|V0|V1 V2]; simpl in *; try exact I.
    destruct Hn as [Hn1 Hn2]. split.
    + rewrite <- mflag_negb. apply (IH1 (negb tag) flag Ea Em V1 W).
      * intros Z HZ. apply HfvU. simpl. fsetdec.
      * intros Z HZ. apply HfvV. simpl. fsetdec.
      * exact Hmode.
      * exact Hn1.
    + apply (IH2 tag flag Ea Em V2 W).
      * intros Z HZ. apply HfvU. simpl. fsetdec.
      * intros Z HZ. apply HfvV. simpl. fsetdec.
      * exact Hmode.
      * exact Hn2.
Qed.

(* ================================================================== *)
(* Corrected sa_rec hole lemma.                                        *)
(*                                                                     *)
(* The two additions are exactly the information that the sam_rec      *)
(* branch of a real induction carries:                                  *)
(*  - [A1 <> A2] is the complement of the sam_refl branch (if the two   *)
(*    translated mu bodies are equal, the seam is closed reflexively    *)
(*    and no new-atom mode check is needed);                            *)
(*  - the source context contains only bind_sub bindings (which is the  *)
(*    case for every context reachable from the empty top-level         *)
(*    context; it is what makes the ancestor invariant removable).      *)
(* The bodies are fvar-closed, i.e. after opening at W the only free    *)
(* atom is the hole itself.  This is the local instance of the          *)
(* context-indexed invariant [purity_aux], whose hypothesis carries the *)
(* ancestor's whole-body double premise.                                *)
(* ================================================================== *)

Lemma sa_rec_mode_hole_corrected : forall E A1 A2 flag Ea Em W,
  W \notin domA Ea ->
  W \notin fv_tt A1 -> W \notin fv_tt A2 ->
  wfe_amber Ea ->
  (forall X, binds X bind_sub E -> exists Y, In (X,Y) Ea) ->
  bindsub_only E ->
  (forall X, X \notin fv_tt A1) ->
  (forall X, X \notin fv_tt A2) ->
  sub (W ~ bind_sub ++ E) (open_tt A1 (typ_fvar W)) (open_tt A2 (typ_fvar W)) ->
  sub (W ~ bind_sub ++ E) (open_tt A1 (open_tt A1 (typ_fvar W)))
                          (open_tt A2 (open_tt A2 (typ_fvar W))) ->
  A1 <> A2 ->
  forall Y, Y \notin {{W}} \u domA Ea ->
    modes_ok flag ((W,Y)::Ea) ((sideB flag)::Em)
              (open_tt A1 (typ_fvar W)) (open_tt A2 (typ_fvar W)).
Proof.
  intros E A1 A2 flag Ea Em W Hdom HW1 HW2 Hwe Hpair Hbs HCl1 HCl2
         Hsub1 Hsub2 Hne Y HY.
  set (U := open_tt A1 (typ_fvar W)).
  set (V := open_tt A2 (typ_fvar W)).
  assert (Hsub1' : sub (W ~ bind_sub ++ E) U V).
  { unfold U. unfold V. exact Hsub1. }
  assert (Hsub2' : sub (W ~ bind_sub ++ E) (subst_tt W U U) (subst_tt W V V)).
  { unfold U. unfold V.
    rewrite <- (open_open_subst A1 W HW1).
    rewrite <- (open_open_subst A2 W HW2).
    exact Hsub2. }
  assert (HUVne : U <> V).
  { intro Heq. apply Hne. apply (open_tt_rec_inj A1 A2 0 W HW1 HW2).
    unfold U in Heq. unfold V in Heq. exact Heq. }
  assert (HlcU : lc_tt U).
  { apply (wf_lc (W ~ bind_sub ++ E) U). exact (proj1 (sub_wf (W ~ bind_sub ++ E) U V Hsub1')). }
  assert (HlcV : lc_tt V).
  { apply (wf_lc (W ~ bind_sub ++ E) V). exact (proj2 (sub_wf (W ~ bind_sub ++ E) U V Hsub1')). }
  assert (HwfWE : wf_env (W ~ bind_sub ++ E)).
  { exact (sub_wf_env (W ~ bind_sub ++ E) U V Hsub1'). }
  inversion HwfWE as [| E0 Z hwfE hnot | E0 x T hwfE hwfs hnot]; subst.
  assert (Hnn : npol false W U V).
  { apply (purity (W ~ bind_sub ++ E) U V W).
    - apply bindsub_only_cons. exact Hbs.
    - exact HwfWE.
    - exact HlcU.
    - exact HlcV.
    - exact Hsub1'.
    - exact Hsub2'.
    - exact HUVne. }
  assert (HfvU : forall X, X \in fv_tt U -> X = W).
  { intros Z HZ. unfold U in HZ.
    pose proof (fv_tt_open A1 W Z HZ) as H.
    apply union_iff in H. destruct H as [H|H].
    - exfalso. apply (HCl1 Z). exact H.
    - fsetdec. }
  assert (HfvV : forall X, X \in fv_tt V -> X = W).
  { intros Z HZ. unfold V in HZ.
    pose proof (fv_tt_open A2 W Z HZ) as H.
    apply union_iff in H. destruct H as [H|H].
    - exfalso. apply (HCl2 Z). exact H.
    - fsetdec. }
  assert (Hmode : mode_of W ((W,Y)::Ea) ((sideB flag)::Em) = Some (sideB flag)).
  { simpl. rewrite eq_dec_refl. reflexivity. }
  exact (modes_ok_of_npol false flag ((W,Y)::Ea) ((sideB flag)::Em) U V W
           HfvU HfvV Hmode Hnn).
Qed.

(* Rewriting an opening at a bvar index. *)
Lemma open_tt_rec_bvar_same : forall K W n,
  K = n -> open_tt_rec K (typ_fvar W) (typ_bvar n) = typ_fvar W.
Proof.
  intros K W n Heq. subst n. simpl. rewrite eq_dec_refl. reflexivity.
Qed.

Lemma open_tt_rec_bvar_neq : forall K W n,
  K <> n -> open_tt_rec K (typ_fvar W) (typ_bvar n) = typ_bvar n.
Proof.
  intros K W n Hne. simpl.
  destruct (K === n) as [e|e]; [exfalso; exact (Hne e)|reflexivity].
Qed.

(* ===== ambient-aware mode translation helpers ===== *)
Lemma mode_of_cons : forall X W Y Ea Em flag,
  mode_of X ((W,Y)::Ea) ((sideB flag)::Em) =
  if X == W then Some (sideB flag) else mode_of X Ea Em.
Proof. intros. simpl. reflexivity. Qed.

Lemma mode_of_cons_other_gen : forall X W Y Ea Em (m0 : Mode),
  X <> W ->
  mode_of X ((W,Y)::Ea) (m0::Em) = mode_of X Ea Em.
Proof.
  intros X W Y Ea Em m0 Hne. simpl.
  destruct (X == W) as [Heq|Hneq]; [exfalso; exact (Hne Heq)|reflexivity].
Qed.

Lemma polar_ok_sideB : forall flag, polar_ok flag (sideB flag).
Proof. destruct flag; reflexivity. Qed.

Lemma modes_ok_fvar_ext : forall flag0 Ea Em W Y X Z m0,
  X <> W -> Z <> W ->
  modes_ok flag0 Ea Em (typ_fvar X) (typ_fvar Z) ->
  modes_ok flag0 ((W,Y)::Ea) (m0::Em) (typ_fvar X) (typ_fvar Z).
Proof.
  intros flag0 Ea Em W Y X Z m0 HX HZ Hmo. unfold modes_ok in *.
  destruct (X == Z) as [Heq|Hneq].
  - subst Z. rewrite mode_of_cons_other_gen; [exact Hmo | exact HX].
  - exact I.
Qed.

Lemma modes_ok_hole_ext_left : forall tag flag Ea Em W Y Z,
  Z <> W ->
  modes_ok (mflag tag flag) ((W,Y)::Ea) ((sideB flag)::Em)
           (typ_fvar W) (typ_fvar Z).
Proof.
  intros tag flag Ea Em W Y Z HZ. unfold modes_ok.
  destruct (W == Z) as [Heq|Hneq].
  - exfalso. exact (HZ (eq_sym Heq)).
  - exact I.
Qed.

Lemma modes_ok_hole_ext_right : forall tag flag Ea Em W Y Z,
  Z <> W ->
  modes_ok (mflag tag flag) ((W,Y)::Ea) ((sideB flag)::Em)
           (typ_fvar Z) (typ_fvar W).
Proof.
  intros tag flag Ea Em W Y Z HZ. unfold modes_ok.
  destruct (Z == W) as [Heq|Hneq].
  - exfalso. exact (HZ Heq).
  - exact I.
Qed.

Lemma modes_ok_hole_hole : forall tag flag Ea Em W Y,
  npol tag W (typ_fvar W) (typ_fvar W) ->
  modes_ok (mflag tag flag) ((W,Y)::Ea) ((sideB flag)::Em)
           (typ_fvar W) (typ_fvar W).
Proof.
  intros tag flag Ea Em W Y Hnp. unfold modes_ok.
  rewrite eq_dec_refl. rewrite mode_of_cons. rewrite eq_dec_refl. simpl.
  destruct tag.
  - simpl in Hnp. rewrite eq_dec_refl in Hnp. simpl in Hnp.
    destruct flag; simpl; destruct Hnp.
  - destruct flag; simpl; reflexivity.
Qed.

(* ===== npol support: substitution invariance ===== *)
(* ================================================================== *)
(* Lemma 2: substitution of an ambient atom does not change the       *)
(* matched structure of a different atom.                             *)
(* ================================================================== *)

Lemma npol_no_fv_l : forall pos Z C D,
  Z \notin fv_tt C -> npol pos Z C D.
Proof.
  intros pos Z C. revert pos.
  induction C as [| |n|X|C0 IHC|C1 IH1 C2 IH2];
    intros pos D HZ; destruct D as [| |m|Y|D0|D1 D2]; simpl in *;
    try exact I.
  - destruct pos; [| exact I].
    destruct (X == Z) as [Heq|Hne]; simpl; [exfalso; apply HZ | exact I].
    subst X. simpl. fsetdec.
  - apply IHC. exact HZ.
  - assert (HZ1 : Z \notin fv_tt C1) by (intro H; apply HZ; simpl; fsetdec).
    assert (HZ2 : Z \notin fv_tt C2) by (intro H; apply HZ; simpl; fsetdec).
    split.
    + apply IH1. exact HZ1.
    + apply IH2. exact HZ2.
Qed.

Lemma npol_no_fv_r : forall pos Z C D,
  Z \notin fv_tt D -> npol pos Z C D.
Proof.
  intros pos Z C D HD.
  apply (proj2 (npol_sym pos Z C D)).
  apply npol_no_fv_l. exact HD.
Qed.

Lemma npol_fvar_ne_l : forall pos Z W D,
  W <> Z -> npol pos Z (typ_fvar W) D.
Proof.
  intros pos Z W D H. destruct D as [| |m|Y|D0|D1 D2]; simpl; try exact I.
  destruct (W == Z) as [Heq|Hne].
  - exfalso. exact (H Heq).
  - simpl. destruct pos; exact I.
Qed.

Lemma npol_subst_l : forall pos Z W U C D,
  Z <> W -> Z \notin fv_tt U ->
  (npol pos Z (subst_tt W U C) D <-> npol pos Z C D).
Proof.
  intros pos Z W U C. revert pos.
  induction C as [| |n|X|C0 IHC|C1 IH1 C2 IH2];
    intros pos D HZW HZU; simpl.
  - tauto.
  - tauto.
  - tauto.
  - (* fvar X *)
    destruct (X == W) as [HeqXW|HneXW].
    + subst X. split; intro H.
      * apply npol_fvar_ne_l. symmetry. exact HZW.
      * apply npol_no_fv_l. exact HZU.
    + split; intro H; exact H.
  - (* mu C0 *)
    destruct D as [| |m|Y|D0|D1 D2]; simpl; try tauto.
    apply IHC; assumption.
  - (* arrow C1 C2 *)
    destruct D as [| |m|Y|D0|D1 D2]; simpl; try tauto.
    destruct (IH1 (negb pos) D1 HZW HZU) as [H1l H1r].
    destruct (IH2 pos D2 HZW HZU) as [H2l H2r].
    split; intros [A B]; split.
    + apply H1l. exact A.
    + apply H2l. exact B.
    + apply H1r. exact A.
    + apply H2r. exact B.
Qed.

Lemma npol_subst_r : forall pos Z W V C D,
  Z <> W -> Z \notin fv_tt V ->
  (npol pos Z C (subst_tt W V D) <-> npol pos Z C D).
Proof.
  intros pos Z W V C D HZW HZV.
  transitivity (npol pos Z (subst_tt W V D) C).
  - apply npol_sym.
  - transitivity (npol pos Z D C).
    + apply npol_subst_l; assumption.
    + apply npol_sym.
Qed.

Lemma npol_subst_fvar : forall pos W W' U V X Y,
  W' <> W -> W' \notin fv_tt U -> W' \notin fv_tt V ->
  (npol pos W' (subst_tt W U X) (subst_tt W V Y) <-> npol pos W' X Y).
Proof.
  intros pos W W' U V X Y HZW HZU HZV.
  etransitivity.
  - apply npol_subst_l with (W := W) (U := U); assumption.
  - apply npol_subst_r with (W := W) (V := V); assumption.
Qed.

(* ===== no-bad-node core ===== *)
Lemma sam_inv_fvar_fvar : forall E X Y,
  sub_amber E (typ_fvar X) (typ_fvar Y) -> In (X,Y) E.
Proof.
  intros E X Y H. inversion H; subst; auto.
Qed.

Lemma open_arrow00_fvar : forall Z U,
  open_tt (typ_arrow (typ_arrow (typ_bvar 0) (typ_bvar 0)) (typ_fvar Z)) U
  = typ_arrow (typ_arrow U U) (typ_fvar Z).
Proof.
  intros Z U. unfold open_tt. simpl. reflexivity.
Qed.

Lemma not_in_cons_pair : forall (E : env_amber) X Y,
  X \notin domA E -> Y \notin domA E -> X <> Y ->
  ~ In (Y, X) ((X, Y) :: E).
Proof.
  intros E X Y HX HY Hne Hin. simpl in Hin.
  destruct Hin as [Heq|Hin].
  - inversion Heq. subst. exfalso. apply Hne. reflexivity.
  - pose proof (in_domA_pair_1 E Y X Hin) as Hd. fsetdec.
Qed.

(* The T1 conclusion is false: mu(arrow(arrow 0 0) X) is never an Amber
   subtype of mu(arrow(arrow 0 0) Y) for X <> Y, in any ambient env. *)
Lemma no_mu_arrow00 : forall E X Y, X <> Y ->
  ~ sub_amber E
      (typ_mu (typ_arrow (typ_arrow (typ_bvar 0) (typ_bvar 0)) (typ_fvar X)))
      (typ_mu (typ_arrow (typ_arrow (typ_bvar 0) (typ_bvar 0)) (typ_fvar Y))).
Proof.
  intros E X Y Hne H.
  remember (typ_mu (typ_arrow (typ_arrow (typ_bvar 0) (typ_bvar 0)) (typ_fvar X))) as M1 eqn:HM1.
  remember (typ_mu (typ_arrow (typ_arrow (typ_bvar 0) (typ_bvar 0)) (typ_fvar Y))) as M2 eqn:HM2.
  revert X Y Hne HM1 HM2.
  induction H; intros X0 Y0 Hne0 HM10 HM20.
  - inversion HM10.
  - inversion HM20.
  - inversion HM10.
  - inversion HM10.
  - inversion HM10. inversion HM20. subst.
    destruct (atom_fresh (L \u domA E \u {{X0}} \u {{Y0}})) as [X' HX'].
    destruct (atom_fresh (L \u domA E \u {{X0}} \u {{Y0}} \u {{X'}})) as [Y' HY'].
    assert (HX'L : X' \notin L) by fsetdec.
    assert (HY'L : Y' \notin L) by fsetdec.
    assert (HX'dom : X' \notin domA E) by fsetdec.
    assert (HY'dom : Y' \notin domA E) by fsetdec.
    assert (Hne' : X' <> Y') by fsetdec.
    assert (HY'fresh : Y' \notin {{X'}} \u L) by fsetdec.
    pose proof (H X' Y' HX'L HY'fresh) as Hsub.
    rewrite open_arrow00_fvar in Hsub.
    rewrite open_arrow00_fvar in Hsub.
    destruct (sam_inv_arrow_l ((X',Y')::E)
                (typ_arrow (typ_fvar X') (typ_fvar X')) (typ_fvar X0)
                (typ_arrow (typ_arrow (typ_fvar Y') (typ_fvar Y')) (typ_fvar Y0)) Hsub)
      as [Heqtop | [C1 [C2 [Heq [Hdom Hcod]]]]].
    + discriminate Heqtop.
    + inversion Heq; subst.
      destruct (sam_inv_arrow_l ((X',Y')::E)
                  (typ_fvar Y') (typ_fvar Y')
                  (typ_arrow (typ_fvar X') (typ_fvar X')) Hdom)
        as [Heqtop2 | [D1 [D2 [Heq2 [H1 H2]]]]].
      * discriminate Heqtop2.
      * inversion Heq2; subst.
        pose proof (sam_inv_fvar_fvar ((X',Y')::E) Y' X' H2) as Hin.
        exact (not_in_cons_pair E X' Y' HX'dom HY'dom Hne' Hin).
  - inversion HM10. inversion HM20. subst.
    exfalso. apply Hne0. injection H3 as Hc. exact Hc.
Qed.


(* ===== derivation-position pull-back (arrow segment) ===== *)
(* ================================================================== *)
(* Arrow-only positions and derivation pull-back.                      *)
(* A path is a list of arrow domain/codomain steps.  [par] is the      *)
(* parity: true means an odd number of domain steps.                   *)
(* ================================================================== *)

Inductive apath : Set :=
| a_here : apath
| a_dom : apath -> apath
| a_cod : apath -> apath.

Fixpoint apar (rho : apath) : bool :=
  match rho with
  | a_here => false
  | a_dom rho' => negb (apar rho')
  | a_cod rho' => apar rho'
  end.

(* Original-orientation occurrence.  At a domain step the child leaf is
   recorded swapped, so the head leaf (A,B) is always in the original
   (U,V) orientation. *)
Inductive oat : apath -> typ -> typ -> typ -> typ -> Prop :=
| oat_here : forall A B, oat a_here A B A B
| oat_cod : forall rho U1 U2 V1 V2 A B,
    oat rho U2 V2 A B ->
    oat (a_cod rho) (typ_arrow U1 U2) (typ_arrow V1 V2) A B
| oat_dom : forall rho U1 U2 V1 V2 A B,
    oat rho V1 U1 B A ->
    oat (a_dom rho) (typ_arrow U1 U2) (typ_arrow V1 V2) A B.

(* The pull-back: the subderivation at the leaf, in the direction fixed
   by the path parity. *)
Lemma sub_oat_par : forall rho E U V, sub E U V ->
  forall A B, oat rho U V A B ->
  if apar rho then sub E B A else sub E A B.
Proof.
  intros rho E U V D A B Hat. revert E D.
  induction Hat as
    [ A0 B0
    | rho U1 U2 V1 V2 A0 B0 Hchild IH
    | rho U1 U2 V1 V2 A0 B0 Hchild IH ];
    intros E D.
  - simpl. exact D.
  - simpl.
    destruct (inv_arrow_l E U1 U2 (typ_arrow V1 V2) D) as
        [[Heq _] | [C1 [C2 [Heq [H1 H2]]]]].
    + discriminate Heq.
    + inversion Heq; subst. apply IH. exact H2.
  - simpl.
    destruct (inv_arrow_l E U1 U2 (typ_arrow V1 V2) D) as
        [[Heq _] | [C1 [C2 [Heq [H1 H2]]]]].
    + discriminate Heq.
    + inversion Heq; subst.
      specialize (IH E H1).
      destruct (apar rho); simpl in *; assumption.
Qed.

(* Substituted occurrence: the two sides are substituted by possibly
   different types S and T.  At a domain step both the side orientation
   and the substitution types swap. *)
Inductive oatS : apath -> typ -> typ -> typ -> typ -> typ -> typ -> Prop :=
| oatS_here : forall S T A B, oatS a_here S T A B A B
| oatS_cod : forall rho S T U1 U2 V1 V2 A B,
    oatS rho S T U2 V2 A B ->
    oatS (a_cod rho) S T (typ_arrow U1 U2) (typ_arrow V1 V2) A B
| oatS_dom : forall rho S T U1 U2 V1 V2 A B,
    oatS rho T S V1 U1 B A ->
    oatS (a_dom rho) S T (typ_arrow U1 U2) (typ_arrow V1 V2) A B.

(* Pull-back through a substitution: from a derivation of the substituted
   types, the leaf comparison is the substituted leaf, with the direction
   flipped by parity. *)
Lemma sub_oatS_par : forall rho S T E W U V,
  sub E (subst_tt W S U) (subst_tt W T V) ->
  forall A B, oatS rho S T U V A B ->
  if apar rho
  then sub E (subst_tt W T B) (subst_tt W S A)
  else sub E (subst_tt W S A) (subst_tt W T B).
Proof.
  intros rho S T E W U V D A B Hat. revert E D.
  induction Hat as
    [ S0 T0 A0 B0
    | rho S0 T0 U1 U2 V1 V2 A0 B0 Hchild IH
    | rho S0 T0 U1 U2 V1 V2 A0 B0 Hchild IH ];
    intros E D.
  - simpl. exact D.
  - simpl. simpl in D.
    destruct (inv_arrow_l E (subst_tt W S0 U1) (subst_tt W S0 U2)
               (typ_arrow (subst_tt W T0 V1) (subst_tt W T0 V2)) D) as
        [[Heq _] | [C1 [C2 [Heq [H1 H2]]]]].
    + discriminate Heq.
    + inversion Heq; subst. apply IH. exact H2.
  - simpl. simpl in D.
    destruct (inv_arrow_l E (subst_tt W S0 U1) (subst_tt W S0 U2)
               (typ_arrow (subst_tt W T0 V1) (subst_tt W T0 V2)) D) as
        [[Heq _] | [C1 [C2 [Heq [H1 H2]]]]].
    + discriminate Heq.
    + inversion Heq; subst.
      specialize (IH E H1).
      destruct (apar rho); simpl in *; assumption.
Qed.


(* Composed-mu push: opening a substituted mu comparison at a fresh atom. *)
Lemma pullback_mu_push : forall E W S T C1 C2,
  lc_tt S -> lc_tt T ->
  sub E (typ_mu (subst_tt W S C1)) (typ_mu (subst_tt W T C2)) ->
  forall L0, exists X,
    X \notin L0 /\ X <> W /\
    sub (X ~ bind_sub ++ E) (subst_tt W S (open_tt C1 (typ_fvar X)))
                            (subst_tt W T (open_tt C2 (typ_fvar X))).
Proof.
  intros E W S T C1 C2 HlcS HlcT HD L0.
  destruct (inv_mu_mu E (subst_tt W S C1) (subst_tt W T C2) HD) as [L [H1 _]].
  destruct (atom_fresh (L \u L0 \u {{W}})) as [X HX].
  assert (HXL : X \notin L) by fsetdec.
  assert (HXW : X <> W) by fsetdec.
  exists X. split; [fsetdec|]. split; [fsetdec|].
  specialize (H1 X HXL). unfold open_tt in H1.
  rewrite <- (subst_tt_open_atom_lc_rec W S C1 0 X HlcS HXW) in H1.
  rewrite <- (subst_tt_open_atom_lc_rec W T C2 0 X HlcT HXW) in H1.
  exact H1.
Qed.

Lemma modes_ok_open_rec : forall tag flag Ea Em W Y A1 A2 K,
  modes_ok (mflag tag flag) Ea Em A1 A2 ->
  W \notin fv_tt A1 -> W \notin fv_tt A2 ->
  npol tag W (open_tt_rec K (typ_fvar W) A1)
               (open_tt_rec K (typ_fvar W) A2) ->
  modes_ok (mflag tag flag) ((W,Y)::Ea) ((sideB flag)::Em)
           (open_tt_rec K (typ_fvar W) A1)
           (open_tt_rec K (typ_fvar W) A2).
Proof.
  intros tag flag Ea Em W Y A1. revert tag.
  induction A1 as [| |n|X|A IHA|A11 IH1 A12 IH2].
  - (* top *) intros tag A2 K Hmo HW1 HW2 Hnp.
    destruct A2 as [| |m|Z|A2'|A21 A22]; simpl.
    + exact I. + exact I.
    + destruct (K === m); simpl; exact I.
    + exact I. + exact I. + exact I.
  - (* nat *) intros tag A2 K Hmo HW1 HW2 Hnp.
    destruct A2 as [| |m|Z|A2'|A21 A22]; simpl.
    + exact I. + exact I.
    + destruct (K === m); simpl; exact I.
    + exact I. + exact I. + exact I.
  - (* bvar n *) intros tag A2 K Hmo HW1 HW2 Hnp.
    destruct (K === n) as [en|en].
    + rewrite (open_tt_rec_bvar_same K W n en).
      rewrite (open_tt_rec_bvar_same K W n en) in Hnp.
      destruct A2 as [| |m|Z|A2'|A21 A22]; simpl.
      * exact I. * exact I.
      * destruct (K === m) as [em|em].
        -- rewrite (open_tt_rec_bvar_same K W m em) in Hnp.
           simpl. apply (modes_ok_hole_hole tag flag Ea Em W Y). exact Hnp.
        -- simpl. exact I.
      * simpl. apply (modes_ok_hole_ext_left tag flag Ea Em W Y Z).
        intro Heq. subst Z. simpl in HW2. fsetdec.
      * exact I. * exact I.
    + rewrite (open_tt_rec_bvar_neq K W n en).
      destruct A2 as [| |m|Z|A2'|A21 A22]; simpl.
      * exact I. * exact I.
      * destruct (K === m); simpl; exact I.
      * exact I. * exact I. * exact I.
  - (* fvar X *) intros tag A2 K Hmo HW1 HW2 Hnp.
    assert (HXW : X <> W) by (intro Heq; subst X; simpl in HW1; fsetdec).
    destruct A2 as [| |m|Z|A2'|A21 A22]; simpl.
    + exact I. + exact I.
    + destruct (K === m) as [em|em].
      * simpl. apply (modes_ok_hole_ext_right tag flag Ea Em W Y X). exact HXW.
      * simpl. exact I.
    + apply (modes_ok_fvar_ext (mflag tag flag) Ea Em W Y X Z (sideB flag)).
      * exact HXW.
      * intro Heq. subst Z. simpl in HW2. fsetdec.
      * exact Hmo.
    + exact I. + exact I.
  - (* mu A *) intros tag A2 K Hmo HW1 HW2 Hnp.
    destruct A2 as [| |m|Z|A2'|A21 A22]; simpl.
    + exact I. + exact I.
    + destruct (K === m); simpl; exact I.
    + exact I.
    + apply IHA.
      * exact Hmo.
      * exact HW1.
      * exact HW2.
      * exact Hnp.
    + exact I.
  - (* arrow *) intros tag A2 K Hmo HW1 HW2 Hnp.
    destruct A2 as [| |m|Z|A2'|A21 A22]; simpl.
    + exact I. + exact I.
    + destruct (K === m); simpl; exact I.
    + exact I. + exact I.
    + destruct Hmo as [Hdom Hcod]. destruct Hnp as [Hnpd Hnpc]. split.
      * rewrite <- mflag_negb. rewrite <- mflag_negb in Hdom.
        apply (IH1 (negb tag) A21 K).
        -- exact Hdom.
        -- intro HZ. apply HW1. simpl. fsetdec.
        -- intro HZ. apply HW2. simpl. fsetdec.
        -- exact Hnpd.
      * apply (IH2 tag A22 K Hcod).
        -- intro HZ. apply HW1. simpl. fsetdec.
        -- intro HZ. apply HW2. simpl. fsetdec.
        -- exact Hnpc.
Qed.

(* Paths with mu steps; the atom for each mu step is chosen during the
   pull-back, so [follow] takes the list of chosen atoms. *)

Inductive mpath : Set :=
| mp_here : mpath
| mp_dom : mpath -> mpath
| mp_cod : mpath -> mpath
| mp_mu : mpath -> mpath.

Fixpoint mpar (p : mpath) : bool :=
  match p with
  | mp_here => false
  | mp_dom p' => negb (mpar p')
  | mp_cod p' => mpar p'
  | mp_mu p' => mpar p'
  end.

Fixpoint atoms_env (ats : list atom) (E : env) : env :=
  match ats with
  | nil => E
  | X :: ats' => atoms_env ats' (X ~ bind_sub ++ E)
  end.

Fixpoint follow (ats : list atom) (p : mpath) (U V : typ) : option (typ * typ) :=
  match p with
  | mp_here => Some (U, V)
  | mp_dom p' =>
      match U, V with
      | typ_arrow U1 U2, typ_arrow V1 V2 =>
          match follow ats p' V1 U1 with
          | Some (A, B) => Some (B, A)
          | None => None
          end
      | _,_ => None
      end
  | mp_cod p' =>
      match U, V with
      | typ_arrow U1 U2, typ_arrow V1 V2 => follow ats p' U2 V2
      | _,_ => None
      end
  | mp_mu p' =>
      match ats with
      | nil => None
      | X :: ats' =>
          match U, V with
          | typ_mu C1, typ_mu C2 =>
              follow ats' p' (open_tt C1 (typ_fvar X)) (open_tt C2 (typ_fvar X))
          | _,_ => None
          end
      end
  end.

Inductive mocc : mpath -> typ -> typ -> Prop :=
| mocc_here : forall A B, mocc mp_here A B
| mocc_dom : forall p U1 U2 V1 V2,
    mocc p U1 V1 -> mocc (mp_dom p) (typ_arrow U1 U2) (typ_arrow V1 V2)
| mocc_cod : forall p U1 U2 V1 V2,
    mocc p U2 V2 -> mocc (mp_cod p) (typ_arrow U1 U2) (typ_arrow V1 V2)
| mocc_mu : forall p C1 C2,
    mocc p C1 C2 -> mocc (mp_mu p) (typ_mu C1) (typ_mu C2).

Lemma mocc_sym : forall p U V, mocc p U V -> mocc p V U.
Proof.
  intros p U V H. induction H as
    [ A B | p U1 U2 V1 V2 Hc IH | p U1 U2 V1 V2 Hc IH | p C1 C2 Hc IH ].
  - apply mocc_here.
  - apply (mocc_dom p V1 V2 U1 U2). exact IH.
  - apply (mocc_cod p V1 V2 U1 U2). exact IH.
  - apply (mocc_mu p C2 C1). exact IH.
Qed.

Lemma mocc_open_rec : forall p C1 C2, mocc p C1 C2 ->
  forall K X, mocc p (open_tt_rec K (typ_fvar X) C1)
                     (open_tt_rec K (typ_fvar X) C2).
Proof.
  intros p C1 C2 H. induction H as
    [ A B | p U1 U2 V1 V2 Hc IH | p U1 U2 V1 V2 Hc IH | p C1' C2' Hc IH ];
    intros K X; simpl.
  - apply mocc_here.
  - apply (mocc_dom p (open_tt_rec K (typ_fvar X) U1)
                      (open_tt_rec K (typ_fvar X) U2)
                      (open_tt_rec K (typ_fvar X) V1)
                      (open_tt_rec K (typ_fvar X) V2)).
    apply IH.
  - apply (mocc_cod p (open_tt_rec K (typ_fvar X) U1)
                      (open_tt_rec K (typ_fvar X) U2)
                      (open_tt_rec K (typ_fvar X) V1)
                      (open_tt_rec K (typ_fvar X) V2)).
    apply IH.
  - apply (mocc_mu p (open_tt_rec (S K) (typ_fvar X) C1')
                      (open_tt_rec (S K) (typ_fvar X) C2')).
    apply IH.
Qed.

(* Main composition: from a derivation of the substituted types, follow
   the path, choosing fresh atoms at each mu step, and obtain the subderivation
   at the substituted leaf, with direction fixed by the parity. *)

Lemma compose_pullback : forall p U V, mocc p U V ->
  forall E W S T,
    lc_tt S -> lc_tt T ->
    sub E (subst_tt W S U) (subst_tt W T V) ->
    forall L0,
    exists ats Ecur A B,
      Ecur = atoms_env ats E /\
      (forall Z, In Z ats -> Z \notin L0 /\ Z <> W) /\
      follow ats p U V = Some (A, B) /\
      (if mpar p
       then sub Ecur (subst_tt W T B) (subst_tt W S A)
       else sub Ecur (subst_tt W S A) (subst_tt W T B)).
Proof.
  induction p as [|p IH|p IH|p IH]; intros U V Hocc E W S T HlcS HlcT D L0.
  - (* here *)
    inversion Hocc; subst.
    exists nil, E, U, V. simpl.
    split; [reflexivity|]. split.
    + intros Z HZ. simpl in HZ. destruct HZ.
    + split; [reflexivity|]. exact D.
  - (* dom *)
    inversion Hocc as [A B | p0 U1 U2 V1 V2 Hch | p0 U1 U2 V1 V2 Hch | p0 C1 C2 Hch];
      subst.
    simpl in D.
    destruct (inv_arrow_l E (subst_tt W S U1) (subst_tt W S U2)
               (typ_arrow (subst_tt W T V1) (subst_tt W T V2)) D) as
        [[Heq _] | [C1 [C2 [Heq [Hdom Hcod]]]]].
    + discriminate Heq.
    + inversion Heq; subst.
      destruct (IH V1 U1 (mocc_sym p U1 V1 Hch) E W T S HlcT HlcS Hdom L0)
        as [ats [Ecur [A' [B' [HEq [Hfresh [Hfollow Hsub]]]]]]].
      exists ats, Ecur, B', A'. simpl.
      split; [exact HEq|]. split; [exact Hfresh|]. split.
      * simpl. rewrite Hfollow. reflexivity.
      * destruct (mpar p); simpl in *; assumption.
  - (* cod *)
    inversion Hocc as [A B | p0 U1 U2 V1 V2 Hch | p0 U1 U2 V1 V2 Hch | p0 C1 C2 Hch];
      subst.
    simpl in D.
    destruct (inv_arrow_l E (subst_tt W S U1) (subst_tt W S U2)
               (typ_arrow (subst_tt W T V1) (subst_tt W T V2)) D) as
        [[Heq _] | [C1 [C2 [Heq [Hdom Hcod]]]]].
    + discriminate Heq.
    + inversion Heq; subst.
      destruct (IH U2 V2 Hch E W S T HlcS HlcT Hcod L0)
        as [ats [Ecur [A' [B' [HEq [Hfresh [Hfollow Hsub]]]]]]].
      exists ats, Ecur, A', B'.
      split; [exact HEq|]. split; [exact Hfresh|]. split; [exact Hfollow|].
      exact Hsub.
  - (* mu *)
    inversion Hocc as [A B | p0 U1 U2 V1 V2 Hch | p0 U1 U2 V1 V2 Hch | p0 C1 C2 Hch];
      subst.
    change (sub E (typ_mu (subst_tt W S C1)) (typ_mu (subst_tt W T C2))) in D.
    destruct (pullback_mu_push E W S T C1 C2 HlcS HlcT D (L0 \u {{W}}))
      as [X [HXnot [HXW HsubX]]].
    assert (HX0 : X \notin L0) by fsetdec.
    assert (Hmo : mocc p (open_tt C1 (typ_fvar X)) (open_tt C2 (typ_fvar X))).
    { apply (mocc_open_rec p C1 C2 Hch 0 X). }
    destruct (IH (open_tt C1 (typ_fvar X)) (open_tt C2 (typ_fvar X)) Hmo
                (X ~ bind_sub ++ E) W S T HlcS HlcT HsubX (L0 \u {{X}}))
      as [ats [Ecur [A' [B' [HEq [Hfresh [Hfollow Hsub]]]]]]].
    exists (X :: ats), Ecur, A', B'.
    split.
    + simpl. exact HEq.
    + split.
      * intros Z HZ. simpl in HZ. destruct HZ as [HeqZ|Hin].
        -- subst Z. split; assumption.
        -- destruct (Hfresh Z Hin) as [HZnot HZW]. split; fsetdec.
      * split.
        -- simpl. exact Hfollow.
        -- exact Hsub.
Qed.

(* ===== verified occurrence / exclusion toolkit ===== *)

(* Absolute-parity occurrence predicate (parity counted from the root,
   flipping at each arrow domain, matching [npol]'s traversal). *)
Fixpoint haspT (p : bool) (Z : atom) (T : typ) : Prop :=
  match T with
  | typ_top => False
  | typ_nat => False
  | typ_bvar _ => False
  | typ_fvar X => X = Z /\ p = false
  | typ_arrow A B => haspT (negb p) Z A \/ haspT p Z B
  | typ_mu A => haspT p Z A
  end.

(* Free-binder occurrence at depth K, at absolute parity q. *)
Fixpoint bvoccT (q : bool) (K : nat) (T : typ) : Prop :=
  match T with
  | typ_top => False
  | typ_nat => False
  | typ_bvar J => J = K /\ q = false
  | typ_fvar _ => False
  | typ_arrow A B => bvoccT (negb q) K A \/ bvoccT q K B
  | typ_mu A => bvoccT q (S K) A
  end.

Lemma negb_invol : forall b, negb (negb b) = b.
Proof. destruct b; reflexivity. Qed.

Lemma xorb_eq_false : forall p q, xorb p q = false <-> p = q.
Proof. destruct p, q; simpl; split; congruence. Qed.

Lemma xorb_neg_l : forall p q, xorb (negb p) q = xorb p (negb q).
Proof. destruct p, q; reflexivity. Qed.

Lemma xorb_neg_neg : forall p q, xorb (negb p) (negb q) = xorb p q.
Proof. destruct p, q; reflexivity. Qed.

Lemma hasp_open_rec : forall C K U p Z,
  haspT p Z (open_tt_rec K U C) <->
  haspT p Z C \/
  (exists q, bvoccT q K C /\ haspT (xorb p q) Z U).
Proof.
  induction C as [| |n|X|C IHC|C1 IH1 C2 IH2];
    intros K U p Z; simpl.
  - (* top *) simpl.
    split; [contradiction|]. intros [H|H]; [contradiction|].
    destruct H as [q [HF _]]. exact HF.
  - (* nat *) simpl.
    split; [contradiction|]. intros [H|H]; [contradiction|].
    destruct H as [q [HF _]]. exact HF.
  - (* bvar n *) simpl.
    destruct (K === n) as [Heq|Hne].
    + subst n. simpl. split.
      * intro H. right. exists false. split.
        -- simpl. split; [reflexivity|reflexivity].
        -- rewrite xorb_false_r. exact H.
      * intros [H|H].
        -- destruct H.
        -- destruct H as [q [[_ Hq] HU]]. subst q.
           rewrite xorb_false_r in HU. exact HU.
    + simpl. split; [contradiction|]. intros [H|H]; [contradiction|].
      destruct H as [q [[Hq _] _]]. exfalso. apply Hne. symmetry. exact Hq.
  - (* fvar X *) simpl. split.
    + intro H. left. exact H.
    + intros [H|H]; [exact H|].
      destruct H as [q [HF _]]. exfalso. exact HF.
  - (* mu *) simpl. apply IHC.
  - (* arrow *) simpl.
    rewrite IH1. rewrite IH2. simpl.
    split.
    + intros [[A1|E1]|[A2|E2]].
      * left. left. exact A1.
      * right. destruct E1 as [q [B1 HU]]. exists (negb q). split.
        -- rewrite negb_invol. left. exact B1.
        -- rewrite <- xorb_neg_l. exact HU.
      * left. right. exact A2.
      * right. destruct E2 as [q [B2 HU]]. exists q. split.
        -- simpl. right. exact B2.
        -- exact HU.
    + intros [[A1|A2]|E].
      * left. left. exact A1.
      * right. left. exact A2.
      * destruct E as [q [[B1|B2] HU]].
        -- left. right. exists (negb q). split; [exact B1|].
           rewrite xorb_neg_neg. exact HU.
        -- right. right. exists q. split; [exact B2| exact HU].
Qed.

Lemma hasp_fv : forall T p Z, haspT p Z T -> Z \in fv_tt T.
Proof.
  induction T as [| |n|X|T IHT|T1 IH1 T2 IH2];
    intros p Z H; simpl in *.
  - contradiction.
  - contradiction.
  - contradiction.
  - destruct H as [Heq _]. subst X. fsetdec.
  - apply (IHT p Z H).
  - destruct H as [H|H]; apply union_iff; [left|right];
      [apply (IH1 (negb p) Z H)|apply (IH2 p Z H)].
Qed.

Lemma hasp_open_fvar_other : forall C Z W p,
  W <> Z -> Z \notin fv_tt C ->
  (haspT p W (open_tt C (typ_fvar Z)) <-> haspT p W C).
Proof.
  intros C Z W p Hne HZ. unfold open_tt. rewrite hasp_open_rec.
  split.
  - intros [H|H]; [exact H|].
    destruct H as [q [_ HU]]. simpl in HU.
    destruct HU as [Heq _]. exfalso. apply Hne. symmetry. exact Heq.
  - intro H. left. exact H.
Qed.

Lemma hasp_open_fvar_same : forall C Z p,
  Z \notin fv_tt C ->
  (haspT p Z (open_tt C (typ_fvar Z)) <-> bvoccT p 0 C).
Proof.
  intros C Z p HZ. unfold open_tt. rewrite hasp_open_rec.
  split.
  - intros [H|H].
    + exfalso. apply HZ. apply (hasp_fv C p Z H).
    + destruct H as [q [Hb HU]]. simpl in HU.
      destruct HU as [_ Hq].
      apply (proj1 (xorb_eq_false p q)) in Hq. subst q. exact Hb.
  - intro Hb. right. exists p. split; [exact Hb|]. simpl.
    destruct p; simpl; split; reflexivity.
Qed.

(* If C has an odd free-binder occurrence and an even occurrence of W in
   its opening, then the second unfolding has an odd occurrence of W. *)
Lemma hasp_second_unfold_odd : forall C Z W,
  bvoccT true 0 C ->
  haspT false W (open_tt C (typ_fvar Z)) ->
  haspT true W (open_tt C (open_tt C (typ_fvar Z))).
Proof.
  intros C Z W Hb HW.
  change (haspT true W (open_tt_rec 0 (open_tt C (typ_fvar Z)) C)).
  rewrite hasp_open_rec.
  right. exists true. split; [exact Hb|].
  change (xorb true true) with false.
  exact HW.
Qed.

(* npol on identical types is exactly absence of an occurrence at the
   complementary absolute parity. *)
Lemma npol_self : forall T pos Z,
  npol pos Z T T <-> ~ haspT (negb pos) Z T.
Proof.
  induction T as [| |n|X|T IHT|T1 IH1 T2 IH2];
    intros pos Z; simpl.
  - tauto.
  - tauto.
  - tauto.
  - destruct pos; simpl.
    + destruct (X == Z) as [Heq|Hne]; simpl.
      * subst X. split.
        -- intros [].
        -- intros H. exfalso. apply H. split; [reflexivity|reflexivity].
      * simpl. split.
        -- intros _ H. apply Hne. exact (proj1 H).
        -- intros _. exact I.
    + simpl. split; [intros _ Hc; destruct Hc as [_ Hp]; discriminate Hp
                     | intros _; exact I].
  - apply IHT.
  - simpl.
    rewrite (IH1 (negb pos) Z).
    rewrite (IH2 pos Z).
    rewrite negb_invol.
    split.
    + intros [H1 H2] Hc. destruct Hc as [Hc|Hc].
      * exact (H1 Hc).
      * exact (H2 Hc).
    + intros H. split.
      * intro Hc. apply H. left. exact Hc.
      * intro Hc. apply H. right. exact Hc.
Qed.

Lemma npol_self_false : forall Z T, npol false Z T T <-> ~ haspT true Z T.
Proof. intros Z T. apply npol_self. Qed.

Lemma npol_self_true : forall Z T, npol true Z T T <-> ~ haspT false Z T.
Proof. intros Z T. apply npol_self. Qed.

(* Every free occurrence has one of the two absolute parities. *)
Lemma fv_hasp : forall T W,
  W \in fv_tt T -> haspT true W T \/ haspT false W T.
Proof.
  induction T as [| |n|X|T IHT|T1 IH1 T2 IH2]; simpl; intros W HW.
  - fsetdec.
  - fsetdec.
  - fsetdec.
  - apply AtomSetImpl.singleton_1 in HW. subst X.
    right. simpl. split; [reflexivity|reflexivity].
  - apply IHT. exact HW.
  - apply union_iff in HW. destruct HW as [HW|HW].
    + destruct (IH1 W HW) as [H|H].
      * right. simpl. left. exact H.
      * left. simpl. left. exact H.
    + destruct (IH2 W HW) as [H|H].
      * left. simpl. right. exact H.
      * right. simpl. right. exact H.
Qed.

(* ------------------------------------------------------------------ *)
(* Level-1 exclusion: an odd occurrence of the companion atom in the    *)
(* opened body fires directly.                                          *)
(* ------------------------------------------------------------------ *)

Lemma equal_mu_bad_odd : forall E C Z W S T,
  bindsub_only (Z ~ bind_sub ++ E) ->
  wf_env (Z ~ bind_sub ++ E) ->
  lc_tt S -> lc_tt T -> S <> T ->
  sub (Z ~ bind_sub ++ E) (open_tt C (typ_fvar Z))
                          (open_tt C (typ_fvar Z)) ->
  sub (Z ~ bind_sub ++ E) (subst_tt W S (open_tt C (typ_fvar Z)))
                          (subst_tt W T (open_tt C (typ_fvar Z))) ->
  sub (Z ~ bind_sub ++ E) S T ->
  haspT true W (open_tt C (typ_fvar Z)) ->
  False.
Proof.
  intros E C Z W S T Hbs Hwf HlcS HlcT Hne H1 H2 Hfwd Hodd.
  apply (exclusion_at_node (Z ~ bind_sub ++ E)
           (open_tt C (typ_fvar Z)) (open_tt C (typ_fvar Z))
           W S T Hbs Hwf HlcS HlcT H1 H2 Hfwd Hne).
  intro Hnp. exact (proj1 (npol_self_false W (open_tt C (typ_fvar Z))) Hnp Hodd).
Qed.

(* ------------------------------------------------------------------ *)
(* Level-2 exclusion: an even occurrence of the companion atom plus an  *)
(* odd free-binder occurrence of the body becomes odd after the second  *)
(* unfolding, and fires there.                                          *)
(* ------------------------------------------------------------------ *)

Lemma equal_mu_bad_even : forall E C Z W S T,
  bindsub_only (Z ~ bind_sub ++ E) ->
  wf_env (Z ~ bind_sub ++ E) ->
  lc_tt S -> lc_tt T -> S <> T ->
  sub (Z ~ bind_sub ++ E)
      (open_tt C (open_tt C (typ_fvar Z)))
      (open_tt C (open_tt C (typ_fvar Z))) ->
  sub (Z ~ bind_sub ++ E)
      (subst_tt W S (open_tt C (open_tt C (typ_fvar Z))))
      (subst_tt W T (open_tt C (open_tt C (typ_fvar Z)))) ->
  sub (Z ~ bind_sub ++ E) S T ->
  bvoccT true 0 C ->
  haspT false W (open_tt C (typ_fvar Z)) ->
  False.
Proof.
  intros E C Z W S T Hbs Hwf HlcS HlcT Hne H1 H2 Hfwd Hb Heven.
  pose proof (hasp_second_unfold_odd C Z W Hb Heven) as Hodd.
  apply (exclusion_at_node (Z ~ bind_sub ++ E)
           (open_tt C (open_tt C (typ_fvar Z)))
           (open_tt C (open_tt C (typ_fvar Z)))
           W S T Hbs Hwf HlcS HlcT H1 H2 Hfwd Hne).
  intro Hnp.
  exact (proj1 (npol_self_false W (open_tt C (open_tt C (typ_fvar Z))))
           Hnp Hodd).
Qed.

(* ------------------------------------------------------------------ *)
(* Combined equal-body mu exclusion: if the body C has an odd free     *)
(* binder occurrence and contains a free atom W (so the two cov images  *)
(* differ), then the source p1/p2 plus the projected companion and the  *)
(* forward ancestor relation are contradictory.                        *)
(* ------------------------------------------------------------------ *)

Lemma equal_mu_bad_excluded : forall E C Z W S T,
  bindsub_only (Z ~ bind_sub ++ E) ->
  wf_env (Z ~ bind_sub ++ E) ->
  lc_tt S -> lc_tt T -> S <> T ->
  W <> Z -> Z \notin fv_tt C -> W \in fv_tt C ->
  sub (Z ~ bind_sub ++ E) (open_tt C (typ_fvar Z))
                          (open_tt C (typ_fvar Z)) ->
  sub (Z ~ bind_sub ++ E)
      (open_tt C (open_tt C (typ_fvar Z)))
      (open_tt C (open_tt C (typ_fvar Z))) ->
  sub (Z ~ bind_sub ++ E) (subst_tt W S (open_tt C (typ_fvar Z)))
                          (subst_tt W T (open_tt C (typ_fvar Z))) ->
  sub (Z ~ bind_sub ++ E)
      (subst_tt W S (open_tt C (open_tt C (typ_fvar Z))))
      (subst_tt W T (open_tt C (open_tt C (typ_fvar Z)))) ->
  sub (Z ~ bind_sub ++ E) S T ->
  bvoccT true 0 C ->
  False.
Proof.
  intros E C Z W S T Hbs Hwf HlcS HlcT Hne HWZ HZC HWC
         H1 H1b H2 H2b Hfwd Hb.
  assert (Hpar : haspT true W (open_tt C (typ_fvar Z)) \/
                 haspT false W (open_tt C (typ_fvar Z))).
  { destruct (fv_hasp C W HWC) as [H|H].
    - left. apply (hasp_open_fvar_other C Z W true HWZ HZC). exact H.
    - right. apply (hasp_open_fvar_other C Z W false HWZ HZC). exact H. }
  destruct Hpar as [Hodd|Heven].
  - exact (equal_mu_bad_odd E C Z W S T Hbs Hwf HlcS HlcT Hne
             H1 H2 Hfwd Hodd).
  - exact (equal_mu_bad_even E C Z W S T Hbs Hwf HlcS HlcT Hne
             H1b H2b Hfwd Hb Heven).
Qed.

(* ===== verified structural layer for the assembly ===== *)

Lemma hasp_second_unfold_even : forall C Z W,
  bvoccT true 0 C ->
  haspT true W (open_tt C (typ_fvar Z)) ->
  haspT false W (open_tt C (open_tt C (typ_fvar Z))).
Proof.
  intros C Z W Hb Hodd.
  change (haspT false W (open_tt_rec 0 (open_tt C (typ_fvar Z)) C)).
  rewrite hasp_open_rec.
  right. exists true. split; [exact Hb|].
  change (xorb false true) with true. exact Hodd.
Qed.

Lemma exclusion_at_node_rev : forall E C D W S T,
  bindsub_only E ->
  wf_env E ->
  lc_tt S -> lc_tt T ->
  sub E C D ->
  sub E (subst_tt W T C) (subst_tt W S D) ->
  sub E S T ->
  S <> T ->
  ~ npol true W C D ->
  False.
Proof.
  intros E C D W S T Hbs Hwf HlcS HlcT H1 H2 Hfwd Hne Hcond.
  pose proof (purity_aux E C D H1 Hbs Hwf true W T S HlcT HlcS H2 Hcond)
    as Hrev.
  simpl in Hrev.
  exact (Hne (sub_antisym E S T Hfwd Hrev)).
Qed.

Lemma equal_mu_excluded_par : forall E C Z W S T (par : bool),
  bindsub_only (Z ~ bind_sub ++ E) ->
  wf_env (Z ~ bind_sub ++ E) ->
  lc_tt S -> lc_tt T -> S <> T ->
  W <> Z -> Z \notin fv_tt C -> W \in fv_tt C ->
  sub (Z ~ bind_sub ++ E) (open_tt C (typ_fvar Z)) (open_tt C (typ_fvar Z)) ->
  sub (Z ~ bind_sub ++ E) (open_tt C (open_tt C (typ_fvar Z)))
                          (open_tt C (open_tt C (typ_fvar Z))) ->
  (if par
   then sub (Z ~ bind_sub ++ E) (subst_tt W T (open_tt C (typ_fvar Z)))
                                 (subst_tt W S (open_tt C (typ_fvar Z)))
   else sub (Z ~ bind_sub ++ E) (subst_tt W S (open_tt C (typ_fvar Z)))
                                 (subst_tt W T (open_tt C (typ_fvar Z)))) ->
  (if par
   then sub (Z ~ bind_sub ++ E)
            (subst_tt W T (open_tt C (open_tt C (typ_fvar Z))))
            (subst_tt W S (open_tt C (open_tt C (typ_fvar Z))))
   else sub (Z ~ bind_sub ++ E)
            (subst_tt W S (open_tt C (open_tt C (typ_fvar Z))))
            (subst_tt W T (open_tt C (open_tt C (typ_fvar Z))))) ->
  sub (Z ~ bind_sub ++ E) S T ->
  bvoccT true 0 C ->
  False.
Proof.
  intros E C Z W S T par Hbs Hwf HlcS HlcT Hne HWZ HZC HWC
         H1 H1b H2 H2b Hfwd Hb.
  assert (Hpar : haspT true W (open_tt C (typ_fvar Z)) \/
                 haspT false W (open_tt C (typ_fvar Z))).
  { destruct (fv_hasp C W HWC) as [H|H].
    - left. apply (hasp_open_fvar_other C Z W true HWZ HZC). exact H.
    - right. apply (hasp_open_fvar_other C Z W false HWZ HZC). exact H. }
  destruct par.
  - (* par = true *)
    destruct Hpar as [Hodd|Heven].
    + (* odd occurrence: level 2, mirrored (even at level 2) *)
      pose proof (hasp_second_unfold_even C Z W Hb Hodd) as Heven2.
      apply (exclusion_at_node_rev (Z ~ bind_sub ++ E)
               (open_tt C (open_tt C (typ_fvar Z)))
               (open_tt C (open_tt C (typ_fvar Z)))
               W S T Hbs Hwf HlcS HlcT H1b H2b Hfwd Hne).
      intro Hnp.
      exact (proj1 (npol_self_true W (open_tt C (open_tt C (typ_fvar Z))))
               Hnp Heven2).
    + (* even occurrence: level 1 mirrored *)
      apply (exclusion_at_node_rev (Z ~ bind_sub ++ E)
               (open_tt C (typ_fvar Z)) (open_tt C (typ_fvar Z))
               W S T Hbs Hwf HlcS HlcT H1 H2 Hfwd Hne).
      intro Hnp.
      exact (proj1 (npol_self_true W (open_tt C (typ_fvar Z))) Hnp Heven).
  - (* par = false *)
    destruct Hpar as [Hodd|Heven].
    + (* odd occurrence: level 1 *)
      apply (exclusion_at_node (Z ~ bind_sub ++ E)
               (open_tt C (typ_fvar Z)) (open_tt C (typ_fvar Z))
               W S T Hbs Hwf HlcS HlcT H1 H2 Hfwd Hne).
      intro Hnp.
      exact (proj1 (npol_self_false W (open_tt C (typ_fvar Z))) Hnp Hodd).
    + (* even occurrence: level 2 *)
      pose proof (hasp_second_unfold_odd C Z W Hb Heven) as Hodd2.
      apply (exclusion_at_node (Z ~ bind_sub ++ E)
               (open_tt C (open_tt C (typ_fvar Z)))
               (open_tt C (open_tt C (typ_fvar Z)))
               W S T Hbs Hwf HlcS HlcT H1b H2b Hfwd Hne).
      intro Hnp.
      exact (proj1 (npol_self_false W (open_tt C (open_tt C (typ_fvar Z))))
               Hnp Hodd2).
Qed.

Lemma modes_ok_sym : forall flag Ea Em A B,
  modes_ok flag Ea Em A B -> modes_ok flag Ea Em B A.
Proof.
  intros flag Ea Em A. revert flag Ea Em.
  induction A as [| |n|x|A0 IHA|A1 IH1 A2 IH2];
    intros flag Ea Em B H; destruct B as [| |m|y|B0|B1 B2]; simpl in *;
    try exact I.
  - destruct (x == y) as [Heq|Hne].
    + subst y. rewrite eq_dec_refl. exact H.
    + destruct (y == x) as [Hyx|Hyx];
      [exfalso; exact (Hne (eq_sym Hyx)) | exact I].
  - apply IHA. exact H.
  - destruct H as [H1 H2]. split.
    + apply (IH1 (negb flag) Ea Em B1). exact H1.
    + apply (IH2 flag Ea Em B2). exact H2.
Qed.

Lemma sideA_negb : forall flag, sideA (negb flag) = sideB flag.
Proof. destruct flag; reflexivity. Qed.
Lemma sideB_negb : forall flag, sideB (negb flag) = sideA flag.
Proof. destruct flag; reflexivity. Qed.
Lemma eqMode_sideB_sideA : forall flag, eqMode (sideB flag) (sideA flag) = false.
Proof. destruct flag; reflexivity. Qed.
Lemma sideA_neq_sideB : forall flag, sideA flag <> sideB flag.
Proof. destruct flag; discriminate. Qed.

Lemma subst_tt_self_fvar : forall Z Y, subst_tt Z Y (typ_fvar Z) = Y.
Proof. intros. simpl. rewrite eq_dec_refl. reflexivity. Qed.

Lemma amber_cov_fresh_left : forall Ea Em Z m,
  Z \notin domA Ea ->
  amber_cov Ea Em (typ_fvar Z) m = typ_fvar Z.
Proof.
  intros Ea Em Z m HZ. apply amber_cov_fvar_fresh.
  intros X Y Hin. pose proof (in_domA_pair_1 Ea X Y Hin). fsetdec.
Qed.

Lemma amber_cov_mu_left : forall Ea Em Z Y C flag,
  Z \notin fv_tt C -> Z \notin domA Ea -> Y \notin domA Ea ->
  amber_cov ((Z,Y)::Ea) ((sideB flag)::Em)
            (open_tt C (typ_fvar Z)) (sideA flag)
  = open_tt (amber_cov Ea Em C (sideA flag)) (typ_fvar Z).
Proof.
  intros Ea Em Z Y C flag HZC HZ HY.
  rewrite amber_cov_open.
  rewrite amber_cov_fresh_pair; [|exact HZC].
  assert (Hcov : amber_cov ((Z,Y)::Ea) ((sideB flag)::Em)
                  (typ_fvar Z) (sideA flag) = typ_fvar Z).
  { simpl. rewrite eqMode_sideB_sideA. simpl.
    apply amber_cov_fresh_left. exact HZ. }
  rewrite Hcov. reflexivity.
Qed.

Lemma amber_cov_mu_right : forall Ea Em Z Y C flag,
  Z \notin fv_tt C -> Z \notin domA Ea -> Y \notin domA Ea ->
  amber_cov ((Z,Y)::Ea) ((sideB flag)::Em)
            (open_tt C (typ_fvar Z)) (sideB flag)
  = open_tt (amber_cov Ea Em C (sideB flag)) (typ_fvar Y).
Proof.
  intros Ea Em Z Y C flag HZC HZ HY.
  rewrite amber_cov_open.
  rewrite amber_cov_fresh_pair; [|exact HZC].
  assert (Hcov : amber_cov ((Z,Y)::Ea) ((sideB flag)::Em)
                  (typ_fvar Z) (sideB flag) = typ_fvar Y).
  { simpl. rewrite eqMode_refl. simpl.
    rewrite eq_dec_refl. simpl.
    apply amber_cov_fresh_left. exact HY. }
  rewrite Hcov. reflexivity.
Qed.

(* ===== proof-free companion data / assembly reduction ===== *)

(* Proof-free companion data: only the computable fields. *)
Record gen_data := {
  gd_w : atom;
  gd_s : typ;
  gd_t : typ;
  gd_par : bool
}.

Definition gd_atoms (d : gen_data) : atoms :=
  {{gd_w d}} \u fv_tt (gd_s d) \u fv_tt (gd_t d).

(* The derivational content lives in Prop, so inversion lemmas may be
   eliminated while building proofs. *)
Definition gen_spec (E : env) (A B : typ) (d : gen_data) : Prop :=
  sub E (subst_tt (gd_w d) (if gd_par d then gd_t d else gd_s d) A)
        (subst_tt (gd_w d) (if gd_par d then gd_s d else gd_t d) B)
  /\ sub E (gd_s d) (gd_t d)
  /\ gd_s d <> gd_t d
  /\ lc_tt (gd_s d) /\ lc_tt (gd_t d).

Definition items_ok (E : env) (A B : typ) (L : list gen_data) : Prop :=
  forall d, In d L -> gen_spec E A B d.

Definition items_cover (E : env) (L : list gen_data) : Prop :=
  forall X, binds X bind_sub E -> exists d, In d L /\ gd_w d = X.

Definition items_ok_dom (E : env) (L : list gen_data) : Prop :=
  forall d, In d L -> gd_w d \in dom E.

(* Arrow projections preserve w/s/t; domain toggles par. *)
Definition gd_dom (d : gen_data) : gen_data :=
  {| gd_w := gd_w d; gd_s := gd_s d; gd_t := gd_t d; gd_par := negb (gd_par d) |}.
Definition gd_cod (d : gen_data) : gen_data :=
  {| gd_w := gd_w d; gd_s := gd_s d; gd_t := gd_t d; gd_par := gd_par d |}.

Lemma gd_dom_w : forall d, gd_w (gd_dom d) = gd_w d.
Proof. reflexivity. Qed.
Lemma gd_cod_w : forall d, gd_w (gd_cod d) = gd_w d.
Proof. reflexivity. Qed.

Lemma gen_spec_dom : forall E A1 A2 B1 B2 d,
  gen_spec E (typ_arrow A1 A2) (typ_arrow B1 B2) d ->
  gen_spec E B1 A1 (gd_dom d).
Proof.
  intros E A1 A2 B1 B2 d Hspec.
  unfold gen_spec in Hspec.
  destruct Hspec as [Hd2 Hrest1].
  destruct Hrest1 as [Hfwd Hrest2].
  destruct Hrest2 as [Hne Hrest3].
  destruct Hrest3 as [Hlcs Hlct].
  destruct d as [w s t par]; simpl in *.
  unfold gen_spec; simpl.
  split; [|split; [|split; [|split]]].
  - change (sub E (typ_arrow (subst_tt w (if par then t else s) A1)
                             (subst_tt w (if par then t else s) A2))
                 (typ_arrow (subst_tt w (if par then s else t) B1)
                            (subst_tt w (if par then s else t) B2))) in Hd2.
    destruct (inv_arrow_l E (subst_tt w (if par then t else s) A1)
               (subst_tt w (if par then t else s) A2)
               (typ_arrow (subst_tt w (if par then s else t) B1)
                          (subst_tt w (if par then s else t) B2)) Hd2)
      as [[Heq _]|[C1 [C2 [Heq [H1 H2]]]]].
    + discriminate Heq.
    + inversion Heq; subst. destruct par; simpl in *; exact H1.
  - exact Hfwd.
  - exact Hne.
  - exact Hlcs.
  - exact Hlct.
Qed.

Lemma gen_spec_cod : forall E A1 A2 B1 B2 d,
  gen_spec E (typ_arrow A1 A2) (typ_arrow B1 B2) d ->
  gen_spec E A2 B2 (gd_cod d).
Proof.
  intros E A1 A2 B1 B2 d Hspec.
  unfold gen_spec in Hspec.
  destruct Hspec as [Hd2 Hrest1].
  destruct Hrest1 as [Hfwd Hrest2].
  destruct Hrest2 as [Hne Hrest3].
  destruct Hrest3 as [Hlcs Hlct].
  destruct d as [w s t par]; simpl in *.
  unfold gen_spec; simpl.
  split; [|split; [|split; [|split]]].
  - change (sub E (typ_arrow (subst_tt w (if par then t else s) A1)
                             (subst_tt w (if par then t else s) A2))
                 (typ_arrow (subst_tt w (if par then s else t) B1)
                            (subst_tt w (if par then s else t) B2))) in Hd2.
    destruct (inv_arrow_l E (subst_tt w (if par then t else s) A1)
               (subst_tt w (if par then t else s) A2)
               (typ_arrow (subst_tt w (if par then s else t) B1)
                          (subst_tt w (if par then s else t) B2)) Hd2)
      as [[Heq _]|[C1 [C2 [Heq [H1 H2]]]]].
    + discriminate Heq.
    + inversion Heq; subst. exact H2.
  - exact Hfwd.
  - exact Hne.
  - exact Hlcs.
  - exact Hlct.
Qed.

Lemma project_items_dom : forall E A1 A2 B1 B2 (L : list gen_data),
  items_ok E (typ_arrow A1 A2) (typ_arrow B1 B2) L ->
  items_ok E B1 A1 (List.map gd_dom L).
Proof.
  intros E A1 A2 B1 B2 L Hok. induction L as [|d L' IH].
  - unfold items_ok. intros d1 Hin. simpl in Hin. destruct Hin.
  - unfold items_ok in *. intros d1 Hin. simpl in Hin.
    destruct Hin as [Heq|Hin].
    + subst d1.
      assert (Hspec : gen_spec E (typ_arrow A1 A2) (typ_arrow B1 B2) d).
      { apply Hok. left. reflexivity. }
      exact (@gen_spec_dom E A1 A2 B1 B2 d Hspec).
    + apply IH; [intros d0 H0; apply Hok; right; exact H0 | exact Hin].
Qed.

Lemma project_items_cod : forall E A1 A2 B1 B2 (L : list gen_data),
  items_ok E (typ_arrow A1 A2) (typ_arrow B1 B2) L ->
  items_ok E A2 B2 (List.map gd_cod L).
Proof.
  intros E A1 A2 B1 B2 L Hok. induction L as [|d L' IH].
  - unfold items_ok. intros d1 Hin. simpl in Hin. destruct Hin.
  - unfold items_ok in *. intros d1 Hin. simpl in Hin.
    destruct Hin as [Heq|Hin].
    + subst d1.
      assert (Hspec : gen_spec E (typ_arrow A1 A2) (typ_arrow B1 B2) d).
      { apply Hok. left. reflexivity. }
      exact (@gen_spec_cod E A1 A2 B1 B2 d Hspec).
    + apply IH; [intros d0 H0; apply Hok; right; exact H0 | exact Hin].
Qed.

(* Mu projection at an arbitrary common fresh atom: the data is unchanged,
   only the spec moves to the opened bodies.  The freshness set is
   existential in Prop so that the main (Prop-valued) induction can collect
   all item freshness sets before choosing the sam_rec opening atoms. *)
Lemma gen_spec_mu : forall (E : env) (A1 A2 : typ) (d : gen_data),
  gen_spec E (typ_mu A1) (typ_mu A2) d ->
  exists L0, forall Z, Z \notin L0 -> Z \notin dom E ->
    gen_spec (Z ~ bind_sub ++ E) (open_tt A1 (typ_fvar Z))
                                  (open_tt A2 (typ_fvar Z)) d.
Proof.
  intros E A1 A2 d Hspec.
  unfold gen_spec in Hspec.
  destruct Hspec as [Hd2 Hrest1].
  destruct Hrest1 as [Hfwd Hrest2].
  destruct Hrest2 as [Hne Hrest3].
  destruct Hrest3 as [Hlcs Hlct].
  destruct d as [w s t par]; simpl in *.
  change (sub E (typ_mu (subst_tt w (if par then t else s) A1))
               (typ_mu (subst_tt w (if par then s else t) A2))) in Hd2.
  destruct (inv_mu_mu E (subst_tt w (if par then t else s) A1)
             (subst_tt w (if par then s else t) A2) Hd2) as [L [Hp1 Hp2]].
  exists (L \u {{w}} \u fv_tt s \u fv_tt t \u dom E).
  intros Z HZ Hdom.
  assert (HZL : Z \notin L) by fsetdec.
  assert (HZw : Z <> w) by (intro Heq; subst Z; apply HZ; fsetdec).
  assert (HZs : Z \notin fv_tt s) by fsetdec.
  assert (HZt : Z \notin fv_tt t) by fsetdec.
  assert (Hfwd' : sub (Z ~ bind_sub ++ E) s t).
  { exact (sub_mono E s t Hfwd (Z ~ bind_sub ++ E)
             (wf_env_sub E Z (sub_wf_env E s t Hfwd) Hdom)
             (fun X Hb => or_intror Hb)). }
  specialize (Hp1 Z HZL).
  unfold open_tt in Hp1.
  destruct par.
  - simpl in Hp1.
    rewrite <- (subst_tt_open_atom_lc_rec w t A1 0 Z Hlct HZw) in Hp1.
    rewrite <- (subst_tt_open_atom_lc_rec w s A2 0 Z Hlcs HZw) in Hp1.
    unfold gen_spec; simpl.
    split; [exact Hp1 |]. split; [exact Hfwd' |]. split; [exact Hne |].
    split; [exact Hlcs | exact Hlct].
  - simpl in Hp1.
    rewrite <- (subst_tt_open_atom_lc_rec w s A1 0 Z Hlcs HZw) in Hp1.
    rewrite <- (subst_tt_open_atom_lc_rec w t A2 0 Z Hlct HZw) in Hp1.
    unfold gen_spec; simpl.
    split; [exact Hp1 |]. split; [exact Hfwd' |]. split; [exact Hne |].
    split; [exact Hlcs | exact Hlct].
Qed.

Lemma project_items_mu : forall (E : env) (A1 A2 : typ) (L : list gen_data),
  items_ok E (typ_mu A1) (typ_mu A2) L ->
  exists L0, forall Z, Z \notin L0 -> Z \notin dom E ->
    items_ok (Z ~ bind_sub ++ E) (open_tt A1 (typ_fvar Z))
                                  (open_tt A2 (typ_fvar Z)) L.
Proof.
  intros E A1 A2 L Hok. induction L as [|d L' IH].
  - exists empty. intros Z HZ Hdom d Hin. simpl in Hin. destruct Hin.
  - unfold items_ok in *.
    assert (Hd : gen_spec E (typ_mu A1) (typ_mu A2) d).
    { apply Hok. left. reflexivity. }
    assert (Htail : forall d0, In d0 L' -> gen_spec E (typ_mu A1) (typ_mu A2) d0).
    { intros d0 Hin. apply Hok. right. exact Hin. }
    destruct (@gen_spec_mu E A1 A2 d Hd) as [Ld Hproj].
    destruct (IH Htail) as [Lrest Hrest].
    exists (Ld \u Lrest).
    intros Z HZ Hdom d0 Hin. simpl in Hin.
    destruct Hin as [Heq|Hin].
    + subst d0. apply Hproj; [fsetdec | exact Hdom].
    + apply Hrest; [fsetdec | exact Hdom | exact Hin].
Qed.

(* ------------------------------------------------------------------ *)
(* Generalized assembly statement with the proof-free item data.        *)
(* ------------------------------------------------------------------ *)
Definition Assembly : Prop :=
  forall (E : env) (A B : typ), sub E A B ->
  bindsub_only E -> wf_env E ->
  forall (flag : bool) (Ea : env_amber) (Em : env_mode)
         (L : list gen_data),
    wfe_amber Ea ->
    (forall X, binds X bind_sub E -> exists Y, In (X, Y) Ea) ->
    modes_ok flag Ea Em A B ->
    items_ok E A B L ->
    items_cover E L ->
    items_ok_dom E L ->
    sub_amber Ea (amber_cov Ea Em A (sideA flag))
                (amber_cov Ea Em B (sideB flag)).

Lemma amber_complete_of_Assembly : Assembly ->
  forall A B, sub nil A B ->
    sub_amber nil (amber_cov nil nil A Neg) (amber_cov nil nil B Pos).
Proof.
  intros Hassembly A B Hsub.
  rewrite amber_cov_nil. rewrite amber_cov_nil.
  change (sub_amber nil (amber_cov nil nil A (sideA true))
                       (amber_cov nil nil B (sideB true))).
  apply (Hassembly nil A B Hsub bindsub_only_nil wf_env_empty true nil nil nil).
  - apply wfea_base.
  - intros X HX. simpl in HX. destruct HX.
  - assert (HAcl : forall X, X \notin fv_tt A).
    { intros X HX.
      pose proof (wf_fv_bindsub nil A (proj1 (sub_wf nil A B Hsub)) X HX) as HE.
      simpl in HE. fsetdec. }
    assert (HBcl : forall X, X \notin fv_tt B).
    { intros X HX.
      pose proof (wf_fv_bindsub nil B (proj2 (sub_wf nil A B Hsub)) X HX) as HE.
      simpl in HE. fsetdec. }
    apply modes_ok_closed; assumption.
  - unfold items_ok. intros d Hin. simpl in Hin. destruct Hin.
  - intros X HX. simpl in HX. destruct HX.
  - unfold items_ok_dom. intros d Hin. simpl in Hin. destruct Hin.
Qed.

(* ================================================================== *)
(* cov_fun lookup on a well-formed environment.                        *)
(* Needed for the sa_fvar base case of Assembly.                       *)
(* ================================================================== *)

Lemma cov_fun_pair : forall Ea Em X Y m m',
  wfe_amber Ea -> In (X,Y) Ea -> mode_of X Ea Em = Some m ->
  cov_fun Ea Em m' X = if eqMode m m' then Y else X.
Proof.
  induction Ea as [| [X0 Y0] Ea IH]; intros Em X Y m m' Hwe Hin Hmo.
  - simpl in Hin. destruct Hin.
  - destruct Em as [|m0 Em].
    + simpl in Hmo. discriminate Hmo.
    + inversion Hwe as [| X1 Y1 E1 HX HY Hwe']; subst.
      simpl.
      destruct (X == X0) as [Heq|Hneq].
      * subst X. simpl in Hmo. rewrite eq_dec_refl in Hmo. injection Hmo as Hm. subst m.
        simpl in Hin. destruct Hin as [HeqPair|Hin].
        -- inversion HeqPair; subst Y0.
           simpl. destruct (eqMode m0 m'); reflexivity.
        -- pose proof (in_domA_pair_1 Ea X0 Y Hin). fsetdec.
      * simpl in Hmo.
        destruct (X == X0) as [Heq2|Hne2].
        -- exfalso. exact (Hneq Heq2).
        -- simpl in Hmo. simpl in Hin. destruct Hin as [HeqPair|Hin].
           ++ inversion HeqPair; subst X0 Y0. exfalso. exact (Hneq eq_refl).
           ++ simpl. exact (IH Em X Y m m' Hwe' Hin Hmo).
Qed.

(* ================================================================== *)
(* Projections of the item invariants along arrow domains/codomains.   *)
(* gd_dom/gd_cod preserve gd_w, hence cover and dom-membership transfer.*)
(* ================================================================== *)

Lemma items_cover_map_dom : forall E (L : list gen_data),
  items_cover E L -> items_cover E (List.map gd_dom L).
Proof.
  intros E L H X Hb.
  destruct (H X Hb) as [d [Hin Hw]].
  exists (gd_dom d). split.
  - apply in_map. exact Hin.
  - simpl. exact Hw.
Qed.

Lemma items_cover_map_cod : forall E (L : list gen_data),
  items_cover E L -> items_cover E (List.map gd_cod L).
Proof.
  intros E L H X Hb.
  destruct (H X Hb) as [d [Hin Hw]].
  exists (gd_cod d). split.
  - apply in_map. exact Hin.
  - simpl. exact Hw.
Qed.

Lemma items_ok_dom_map_dom : forall E (L : list gen_data),
  items_ok_dom E L -> items_ok_dom E (List.map gd_dom L).
Proof.
  intros E L H. induction L as [|d L' IH].
  - unfold items_ok_dom. intros d0 Hin. simpl in Hin. destruct Hin.
  - unfold items_ok_dom in *. intros d0 Hin. simpl in Hin.
    destruct Hin as [Heq|Hin].
    + subst d0. simpl. apply (H d (or_introl eq_refl)).
    + apply IH.
      * intros d1 H1. apply H. right. exact H1.
      * exact Hin.
Qed.

Lemma items_ok_dom_map_cod : forall E (L : list gen_data),
  items_ok_dom E L -> items_ok_dom E (List.map gd_cod L).
Proof.
  intros E L H. induction L as [|d L' IH].
  - unfold items_ok_dom. intros d0 Hin. simpl in Hin. destruct Hin.
  - unfold items_ok_dom in *. intros d0 Hin. simpl in Hin.
    destruct Hin as [Heq|Hin].
    + subst d0. simpl. apply (H d (or_introl eq_refl)).
    + apply IH.
      * intros d1 H1. apply H. right. exact H1.
      * exact Hin.
Qed.

(* ================================================================== *)
(* The cover obstruction at an equal-body mu node.                     *)
(* The child environment gains the fresh atom Z, but every projected   *)
(* item still has its atom in dom E, so no item can cover Z.  This is   *)
(* precisely why the equal case needs the deep ancestor/path exclusion; *)
(* it cannot simply push a new frame (whose gen_spec would require      *)
(* s <> t, impossible when both bodies are the same).                   *)
(* ================================================================== *)

Lemma equal_node_cover_obstruction :
  forall (E : env) (Z : atom) (L : list gen_data),
    Z \notin dom E ->
    items_ok_dom E L ->
    ~ items_cover (Z ~ bind_sub ++ E) L.
Proof.
  intros E Z L HZ Hdom Hcover.
  assert (Hb : binds Z bind_sub (Z ~ bind_sub ++ E)).
  { unfold binds. simpl. left. reflexivity. }
  destruct (Hcover Z Hb) as [d [Hin Hw]].
  apply HZ.
  rewrite <- Hw.
  apply Hdom. exact Hin.
Qed.


(* ================================================================== *)
(* Deep equal-mu exclusion.                                            *)
(*                                                                     *)
(* The equality body C of an iso-recursive mu node may contain a       *)
(* deeper mu subterm D = mu Dbody whose own binder occurs at odd        *)
(* parity in Dbody, while C's own binder reaches Dbody.  The second     *)
(* unfolding premise of [sa_rec] at D then re-uses the substituted      *)
(* image of C's binder with opposite variance, producing a reversed     *)
(* subtyping derivation at a node where the companion atom W occurs;    *)
(* exclusion_at_node / equal_mu_excluded_par then yields a             *)
(* contradiction.                                                       *)
(*                                                                     *)
(* This file proves:                                                    *)
(*   * occurrence-freeness preservation under opening;                 *)
(*   * a syntactic one-hole path relation [at_path] and the bridge      *)
(*     from a bad syntactic leaf inside T to the leaf selected by       *)
(*     [follow] along a [mocc] path;                                    *)
(*   * the joint projection of the self and companion derivations       *)
(*     ([compose_pullback_self]);                                       *)
(*   * the deep exclusion theorem.                                      *)
(* ================================================================== *)

(* ------------------------------------------------------------------ *)
(* A syntactic path with a distinguished leaf, tied to that leaf.      *)
(* ------------------------------------------------------------------ *)

Inductive at_path : mpath -> typ -> typ -> Prop :=
| ap_here : forall D, at_path mp_here D D
| ap_dom : forall p A B D,
    at_path p A D -> at_path (mp_dom p) (typ_arrow A B) D
| ap_cod : forall p A B D,
    at_path p B D -> at_path (mp_cod p) (typ_arrow A B) D
| ap_mu : forall p A D,
    at_path p A D -> at_path (mp_mu p) (typ_mu A) D.

(* ------------------------------------------------------------------ *)
(* Opening at an index distinct from the tracked binder index never    *)
(* destroys an occurrence of the tracked binder.  The replacement may  *)
(* add occurrences, which only helps.                                  *)
(* ------------------------------------------------------------------ *)

Lemma bvoccT_open_imp : forall q K T s U,
  K <> s -> bvoccT q K T -> bvoccT q K (open_tt_rec s U T).
Proof.
  intros q K T. revert q K. induction T as [| |n|X|A IHA|A1 IH1 A2 IH2];
    intros q K s U Hne Hb; simpl in *.
  - exact Hb.
  - exact Hb.
  - (* typ_bvar n *)
    destruct Hb as [Heq Hq]. subst n.
    destruct (s === K) as [Hs|Hs].
    + exfalso. apply Hne. symmetry. exact Hs.
    + simpl. destruct (s === K) as [Hs'|_].
      * exfalso. apply Hne. symmetry. exact Hs'.
      * split; [reflexivity|exact Hq].
  - exact Hb.
  - (* mu *)
    change (bvoccT q (S K) (open_tt_rec (S s) U A)).
    exact (IHA q (S K) (S s) U (fun H => Hne (f_equal Nat.pred H)) Hb).
  - (* arrow *)
    destruct Hb as [Hb|Hb].
    + left. apply (IH1 (negb q) K s U Hne Hb).
    + right. apply (IH2 q K s U Hne Hb).
Qed.

(* Free variables of a type survive any opening (only bound variables
   are replaced). *)
Lemma fv_open_rec_incl : forall T K U z,
  z \in fv_tt T -> z \in fv_tt (open_tt_rec K U T).
Proof.
  intros T. induction T as [| |n|X|A IHA|A1 IH1 A2 IH2];
    intros K U z Hz; simpl in *.
  - fsetdec.
  - fsetdec.
  - fsetdec.
  - fsetdec.
  - apply IHA. exact Hz.
  - apply union_iff in Hz. destruct Hz as [Hz|Hz].
    + apply union_iff. left. apply IH1. exact Hz.
    + apply union_iff. right. apply IH2. exact Hz.
Qed.

(* ------------------------------------------------------------------ *)
(* A bad syntactic leaf stays bad after opening the enclosing context  *)
(* at a fresh atom.  The opening at the leaf body has shift at least 1, *)
(* so the leaf mu's own binder (index 0) is never replaced, and the     *)
(* atom is chosen distinct from W.                                      *)
(* ------------------------------------------------------------------ *)

Lemma at_path_open_bad : forall p R D,
  at_path p R D ->
  forall shift X B0 W,
    D = typ_mu B0 ->
    bvoccT true 0 B0 ->
    W \in fv_tt B0 ->
    X <> W ->
    exists D',
      at_path p (open_tt_rec shift (typ_fvar X) R) D' /\
      (exists B1, D' = typ_mu B1 /\ bvoccT true 0 B1 /\ W \in fv_tt B1).
Proof.
  intros p R D H. induction H as
    [ D | p A B D Hp IH | p A B D Hp IH | p A D Hp IH ];
    intros shift X B0 W Heq Hb HW HXW.
  - (* here *)
    subst D. simpl.
    exists (typ_mu (open_tt_rec (S shift) (typ_fvar X) B0)).
    split.
    + apply ap_here.
    + exists (open_tt_rec (S shift) (typ_fvar X) B0). split; [reflexivity|].
      split.
      * apply (bvoccT_open_imp true 0 B0 (S shift) (typ_fvar X)).
        -- intro Hc. inversion Hc.
        -- exact Hb.
      * apply (fv_open_rec_incl B0 (S shift) (typ_fvar X) W). exact HW.
  - (* dom *)
    simpl. destruct (IH shift X B0 W Heq Hb HW HXW) as [D' [Hp' [B1 [HD' [Hb1 HW1]]]]].
    exists D'. split.
    + apply (ap_dom p (open_tt_rec shift (typ_fvar X) A) (open_tt_rec shift (typ_fvar X) B) D' Hp').
    + exists B1. split; [exact HD'|]. split; assumption.
  - (* cod *)
    simpl. destruct (IH shift X B0 W Heq Hb HW HXW) as [D' [Hp' [B1 [HD' [Hb1 HW1]]]]].
    exists D'. split.
    + apply (ap_cod p (open_tt_rec shift (typ_fvar X) A) (open_tt_rec shift (typ_fvar X) B) D' Hp').
    + exists B1. split; [exact HD'|]. split; assumption.
  - (* mu *)
    simpl. destruct (IH (S shift) X B0 W Heq Hb HW HXW) as [D' [Hp' [B1 [HD' [Hb1 HW1]]]]].
    exists D'. split.
    + apply (ap_mu p (open_tt_rec (S shift) (typ_fvar X) A) D' Hp').
    + exists B1. split; [exact HD'|]. split; assumption.
Qed.

(* Inversion principles for [at_path]. *)
Lemma at_path_dom_inv : forall p R D, at_path (mp_dom p) R D ->
  exists A B, R = typ_arrow A B /\ at_path p A D.
Proof. intros p R D H. inversion H; subst; eauto. Qed.

Lemma at_path_cod_inv : forall p R D, at_path (mp_cod p) R D ->
  exists A B, R = typ_arrow A B /\ at_path p B D.
Proof. intros p R D H. inversion H; subst; eauto. Qed.

Lemma at_path_mu_inv : forall p R D, at_path (mp_mu p) R D ->
  exists A, R = typ_mu A /\ at_path p A D.
Proof. intros p R D H. inversion H; subst; eauto. Qed.

(* ------------------------------------------------------------------ *)
(* The leaf selected by [follow] along a [mocc] path is the syntactic  *)
(* leaf opened at the fresh atoms of the path.  Thus a bad syntactic    *)
(* leaf yields a bad [follow] leaf.                                     *)
(* ------------------------------------------------------------------ *)

Lemma follow_preserves_bad : forall p,
  forall R D, at_path p R D ->
  forall ats A B W B0,
    follow ats p R R = Some (A, B) ->
    (forall X, In X ats -> X <> W) ->
    D = typ_mu B0 ->
    bvoccT true 0 B0 ->
    W \in fv_tt B0 ->
    A = B /\ (exists B1, A = typ_mu B1 /\ bvoccT true 0 B1 /\ W \in fv_tt B1).
Proof.
  induction p as [|p IH|p IH|p IH];
    intros R D Hpath ats A B W Bc HeqD Hfresh HD Hb HW.
  - (* here *)
    inversion Hpath; subst. simpl in HeqD. inversion HeqD; subst.
    split; [reflexivity|]. exists Bc. split; [reflexivity|]. split; assumption.
  - (* dom *)
    destruct (at_path_dom_inv p R D Hpath) as [A0 [B0' [HeqR Hch]]].
    subst R. clear Hpath.
    simpl in HeqD.
    remember (follow ats p A0 A0) as opt eqn:Ef.
    destruct opt as [[A' B']|].
    + injection HeqD as HBA HAB.
      destruct (IH A0 D Hch ats A' B' W Bc (eq_sym Ef) Hfresh HD Hb HW)
        as [Heq' [B1 [HA [Hb1 HW1]]]].
      split.
      * exact (eq_trans (eq_sym HBA) (eq_trans (eq_sym Heq') HAB)).
      * exists B1. split.
        -- exact (eq_trans (eq_sym HBA) (eq_trans (eq_sym Heq') HA)).
        -- split; assumption.
    + simpl in HeqD. discriminate HeqD.
  - (* cod *)
    destruct (at_path_cod_inv p R D Hpath) as [A0 [B0' [HeqR Hch]]].
    subst R. clear Hpath.
    simpl in HeqD.
    destruct (IH B0' D Hch ats A B W Bc HeqD Hfresh HD Hb HW)
      as [Heq' [B1 [HA [Hb1 HW1]]]].
    split; [exact Heq'|]. exists B1. split; [exact HA|]. split; assumption.
  - (* mu *)
    destruct (at_path_mu_inv p R D Hpath) as [A0 [HeqR Hch]].
    subst R. clear Hpath.
    destruct ats as [|X ats'].
    + simpl in HeqD. discriminate HeqD.
    + simpl in HeqD.
      assert (HXW : X <> W).
      { apply Hfresh. left. reflexivity. }
      destruct (at_path_open_bad p A0 D Hch 0 X Bc W HD Hb HW HXW)
        as [D' [Hp' [B1 [HD' [Hb1 HW1]]]]].
      destruct (IH (open_tt_rec 0 (typ_fvar X) A0) D' Hp' ats' A B W B1
                  HeqD (fun Z HZ => Hfresh Z (or_intror HZ)) HD' Hb1 HW1)
        as [Heq' [B2 [HA [Hb2 HW2]]]].
      split; [exact Heq'|]. exists B2. split; [exact HA|]. split; assumption.
Qed.

(* ------------------------------------------------------------------ *)
(* Subtype-only environments are stable under adding fresh bind_sub    *)
(* atoms.                                                              *)
(* ------------------------------------------------------------------ *)

Lemma bindsub_only_atoms_env : forall ats E,
  bindsub_only E -> bindsub_only (atoms_env ats E).
Proof.
  induction ats as [|X ats IH]; intros E Hb.
  - simpl. exact Hb.
  - simpl. apply IH. apply bindsub_only_cons. exact Hb.
Qed.

(* Bindings are stable under [atoms_env], which only conses further     *)
(* subtype bindings on the front.                                      *)
Lemma binds_atoms_env : forall ats E X,
  binds X bind_sub E -> binds X bind_sub (atoms_env ats E).
Proof.
  induction ats as [|Y ats IH]; intros E X Hb; simpl.
  - exact Hb.
  - apply IH. exact (or_intror Hb).
Qed.

(* ------------------------------------------------------------------ *)
(* Joint projection of the self derivation and the companion           *)
(* derivation along a [mocc] path.  The two derivations are processed  *)
(* with the same fresh atoms, so the selected leaf and environment     *)
(* coincide.  The companion orientation is fixed by [mpar]; the self   *)
(* derivation is reflexive at the leaf.                                *)
(* ------------------------------------------------------------------ *)

Lemma sub_arrow_inv_both : forall E A1 A2 B1 B2,
  sub E (typ_arrow A1 A2) (typ_arrow B1 B2) ->
  sub E B1 A1 /\ sub E A2 B2.
Proof. intros E A1 A2 B1 B2 H. inversion H; subst; auto. Qed.

Lemma compose_pullback_self : forall p T,
  mocc p T T ->
  forall E W S U,
    lc_tt S -> lc_tt U ->
    sub E T T ->
    sub E (subst_tt W S T) (subst_tt W U T) ->
    forall L0 : atoms,
    exists ats Ecur A,
      Ecur = atoms_env ats E /\
      (forall Z, In Z ats -> Z \notin L0 /\ Z <> W) /\
      follow ats p T T = Some (A, A) /\
      sub Ecur A A /\
      (if mpar p
       then sub Ecur (subst_tt W U A) (subst_tt W S A)
       else sub Ecur (subst_tt W S A) (subst_tt W U A)).
Proof.
  induction p as [|p IH|p IH|p IH];
    intros T Hocc E W S U HlcS HlcU Hself Hcomp L0.
  - (* here *)
    inversion Hocc; subst.
    exists nil, E, T. simpl.
    split; [reflexivity|]. split.
    + intros Z HZ. simpl in HZ. destruct HZ.
    + split; [reflexivity|]. split; [exact Hself|]. exact Hcomp.
  - (* dom *)
    inversion Hocc as [A B | p0 U1 U2 V1 V2 Hch | p0 U1 U2 V1 V2 Hch | p0 C1 C2 Hch];
      subst.
    simpl in Hcomp.
    destruct (sub_arrow_inv_both E U1 U2 U1 U2 Hself) as [HselfD HselfC].
    destruct (sub_arrow_inv_both E (subst_tt W S U1) (subst_tt W S U2)
               (subst_tt W U U1) (subst_tt W U U2) Hcomp) as [HcompD HcompC].
    destruct (IH U1 Hch E W U S HlcU HlcS HselfD HcompD L0)
      as [ats [Ecur [A [HEq [Hfresh [Hfollow [HselfA HcompA]]]]]]].
    exists ats, Ecur, A. split; [exact HEq|]. split; [exact Hfresh|]. split.
    + simpl. rewrite Hfollow. reflexivity.
    + split; [exact HselfA|].
      destruct (mpar p) eqn:Epar; simpl in *; rewrite Epar in *; simpl in *.
      * exact HcompA.
      * exact HcompA.
  - (* cod *)
    inversion Hocc as [A B | p0 U1 U2 V1 V2 Hch | p0 U1 U2 V1 V2 Hch | p0 C1 C2 Hch];
      subst.
    simpl in Hcomp.
    destruct (sub_arrow_inv_both E U1 U2 U1 U2 Hself) as [HselfD HselfC].
    destruct (sub_arrow_inv_both E (subst_tt W S U1) (subst_tt W S U2)
               (subst_tt W U U1) (subst_tt W U U2) Hcomp) as [HcompD HcompC].
    destruct (IH U2 Hch E W S U HlcS HlcU HselfC HcompC L0)
      as [ats [Ecur [A [HEq [Hfresh [Hfollow [HselfA HcompA]]]]]]].
    exists ats, Ecur, A. split; [exact HEq|]. split; [exact Hfresh|]. split.
    + exact Hfollow.
    + split; assumption.
  - (* mu *)
    inversion Hocc as [A B | p0 U1 U2 V1 V2 Hch | p0 U1 U2 V1 V2 Hch | p0 C1 C2 Hch];
      subst.
    change (sub E (typ_mu (subst_tt W S C1)) (typ_mu (subst_tt W U C1))) in Hcomp.
    destruct (inv_mu_mu E C1 C1 Hself) as [Lself [HselfA1 _]].
    destruct (inv_mu_mu E (subst_tt W S C1) (subst_tt W U C1) Hcomp)
      as [Lcomp [HcompA1 _]].
    destruct (atom_fresh (Lself \u Lcomp \u L0 \u {{W}})) as [X HX].
    assert (HXLs : X \notin Lself) by fsetdec.
    assert (HXLc : X \notin Lcomp) by fsetdec.
    assert (HXL0 : X \notin L0) by fsetdec.
    assert (HXW : X <> W) by fsetdec.
    specialize (HselfA1 X HXLs).
    specialize (HcompA1 X HXLc).
    unfold open_tt in HcompA1.
    rewrite <- (subst_tt_open_atom_lc_rec W S C1 0 X HlcS HXW) in HcompA1.
    rewrite <- (subst_tt_open_atom_lc_rec W U C1 0 X HlcU HXW) in HcompA1.
    assert (Hmo : mocc p (open_tt C1 (typ_fvar X)) (open_tt C1 (typ_fvar X))).
    { apply (mocc_open_rec p C1 C1 Hch 0 X). }
    destruct (IH (open_tt C1 (typ_fvar X)) Hmo (X ~ bind_sub ++ E) W S U
                HlcS HlcU HselfA1 HcompA1 (L0 \u {{X}}))
      as [ats [Ecur [A [HEq [Hfresh [Hfollow [HselfA HcompA]]]]]]].
    exists (X :: ats), Ecur, A. split.
    + simpl. exact HEq.
    + split.
      * intros Z HZ. simpl in HZ. destruct HZ as [HeqZ|Hin].
        -- subst Z. split; assumption.
        -- destruct (Hfresh Z Hin) as [HZL HZX]. split; fsetdec.
      * split.
        -- simpl. exact Hfollow.
        -- split; assumption.
Qed.

(* A syntactic path is a valid [mocc] path on the diagonal.  This lets *)
(* the main theorem below take only the syntactic certificate.         *)
Lemma mocc_self_of_at_path : forall p R D,
  at_path p R D -> mocc p R R.
Proof.
  intros p R D H.
  induction H.
  - apply mocc_here.
  - apply mocc_dom. exact IHat_path.
  - apply mocc_cod. exact IHat_path.
  - apply mocc_mu. exact IHat_path.
Qed.

(* ------------------------------------------------------------------ *)
(* Main deep equal-mu exclusion theorem.                               *)
(*                                                                     *)
(* [T0] is the double unfolding of the equality body [C].  The target  *)
(* self derivation and the companion derivation are projected along a  *)
(* path [p] to a syntactic leaf [mu B0] that carries a bad own-binder  *)
(* occurrence and a free occurrence of W.  The projected leaf is a mu  *)
(* with the same two properties, at which the level-1 equal-mu         *)
(* exclusion [equal_mu_excluded_par] applies.                          *)
(* ------------------------------------------------------------------ *)

Theorem deep_equal_mu_excluded :
  forall E C Z W S U (T0 : typ) (p : mpath) (B0 : typ),
    bindsub_only (Z ~ bind_sub ++ E) ->
    wf_env (Z ~ bind_sub ++ E) ->
    lc_tt S -> lc_tt U -> S <> U ->
    W <> Z -> Z \notin fv_tt C -> W \in fv_tt C ->
    T0 = open_tt C (open_tt C (typ_fvar Z)) ->
    sub (Z ~ bind_sub ++ E) T0 T0 ->
    sub (Z ~ bind_sub ++ E) (subst_tt W S T0) (subst_tt W U T0) ->
    sub (Z ~ bind_sub ++ E) S U ->
    mocc p T0 T0 ->
    at_path p T0 (typ_mu B0) ->
    bvoccT true 0 B0 ->
    W \in fv_tt B0 ->
    False.
Proof.
  intros E C Z W S U T0 p B0 Hbs Hwf HlcS HlcU Hne HWZ HZC HWC HT0
         Hself Hcomp Hfwd Hmo Hpath Hb HbW.
  destruct (compose_pullback_self p T0 Hmo (Z ~ bind_sub ++ E) W S U
              HlcS HlcU Hself Hcomp (fv_tt T0 \u {{W}}))
    as [ats [Ecur [A [HEq [Hfresh [Hfollow [HselfA HcompA]]]]]]].
  subst Ecur.
  destruct (follow_preserves_bad p T0 (typ_mu B0) Hpath ats A A W B0
              Hfollow (fun X HX => proj2 (Hfresh X HX)) eq_refl Hb HbW)
    as [_ [B1 [HA [Hb1 HW1]]]].
  subst A.
  simpl in HcompA.
  assert (HbsE : bindsub_only (atoms_env ats (Z ~ bind_sub ++ E))).
  { apply bindsub_only_atoms_env. exact Hbs. }
  destruct (mpar p) eqn:Epar; simpl in HcompA.
  - (* par = true : companion compares t-image on the left *)
    destruct (inv_mu_mu (atoms_env ats (Z ~ bind_sub ++ E)) B1 B1 HselfA)
      as [Ls [Hs1 Hs2]].
    destruct (inv_mu_mu (atoms_env ats (Z ~ bind_sub ++ E))
               (subst_tt W U B1) (subst_tt W S B1) HcompA) as [Lc [Hc1 Hc2]].
    destruct (atom_fresh (Ls \u Lc \u fv_tt B1 \u {{W}})) as [X HX].
    assert (HXLs : X \notin Ls) by fsetdec.
    assert (HXLc : X \notin Lc) by fsetdec.
    assert (HXfv : X \notin fv_tt B1) by fsetdec.
    assert (HXW : X <> W) by fsetdec.
    specialize (Hs1 X HXLs). specialize (Hs2 X HXLs).
    specialize (Hc1 X HXLc). specialize (Hc2 X HXLc).
    unfold open_tt in Hc1, Hc2.
    rewrite <- (subst_tt_open_atom_lc_rec W U B1 0 X HlcU HXW) in Hc1.
    rewrite <- (subst_tt_open_atom_lc_rec W S B1 0 X HlcS HXW) in Hc1.
    rewrite <- (subst_tt_open_atom_lc_rec W U B1 0 X HlcU HXW) in Hc2.
    rewrite <- (subst_tt_open_atom_lc_rec W S B1 0 X HlcS HXW) in Hc2.
    rewrite <- (subst_tt_open_ty_rec W U B1 (open_tt_rec 0 (typ_fvar X) B1) 0 HlcU) in Hc2.
    rewrite <- (subst_tt_open_ty_rec W S B1 (open_tt_rec 0 (typ_fvar X) B1) 0 HlcS) in Hc2.
    assert (HwfX : wf_env (X ~ bind_sub ++ atoms_env ats (Z ~ bind_sub ++ E)))
      by (apply (sub_wf_env _ _ _ Hs1)).
    assert (HbsX : bindsub_only (X ~ bind_sub ++ atoms_env ats (Z ~ bind_sub ++ E)))
      by (apply bindsub_only_cons; exact HbsE).
    assert (HfwdE : sub (atoms_env ats (Z ~ bind_sub ++ E)) S U).
    { apply (sub_mono (Z ~ bind_sub ++ E) S U Hfwd
               (atoms_env ats (Z ~ bind_sub ++ E))
               (sub_wf_env _ _ _ HselfA)).
      intros Y HY. exact (binds_atoms_env ats (Z ~ bind_sub ++ E) Y HY). }
    assert (Hlift : sub (X ~ bind_sub ++ atoms_env ats (Z ~ bind_sub ++ E)) S U).
    { apply (sub_mono (atoms_env ats (Z ~ bind_sub ++ E)) S U HfwdE
               (X ~ bind_sub ++ atoms_env ats (Z ~ bind_sub ++ E)) HwfX).
      intros Y HY. unfold binds in *. simpl. right. exact HY. }
    exact (equal_mu_excluded_par (atoms_env ats (Z ~ bind_sub ++ E)) B1 X W S U true
             HbsX HwfX HlcS HlcU Hne (fun H => HXW (eq_sym H)) HXfv HW1 Hs1 Hs2 Hc1 Hc2 Hlift Hb1).
  - (* par = false : companion compares s-image on the left *)
    destruct (inv_mu_mu (atoms_env ats (Z ~ bind_sub ++ E)) B1 B1 HselfA)
      as [Ls [Hs1 Hs2]].
    destruct (inv_mu_mu (atoms_env ats (Z ~ bind_sub ++ E))
               (subst_tt W S B1) (subst_tt W U B1) HcompA) as [Lc [Hc1 Hc2]].
    destruct (atom_fresh (Ls \u Lc \u fv_tt B1 \u {{W}})) as [X HX].
    assert (HXLs : X \notin Ls) by fsetdec.
    assert (HXLc : X \notin Lc) by fsetdec.
    assert (HXfv : X \notin fv_tt B1) by fsetdec.
    assert (HXW : X <> W) by fsetdec.
    specialize (Hs1 X HXLs). specialize (Hs2 X HXLs).
    specialize (Hc1 X HXLc). specialize (Hc2 X HXLc).
    unfold open_tt in Hc1, Hc2.
    rewrite <- (subst_tt_open_atom_lc_rec W S B1 0 X HlcS HXW) in Hc1.
    rewrite <- (subst_tt_open_atom_lc_rec W U B1 0 X HlcU HXW) in Hc1.
    rewrite <- (subst_tt_open_atom_lc_rec W S B1 0 X HlcS HXW) in Hc2.
    rewrite <- (subst_tt_open_atom_lc_rec W U B1 0 X HlcU HXW) in Hc2.
    rewrite <- (subst_tt_open_ty_rec W S B1 (open_tt_rec 0 (typ_fvar X) B1) 0 HlcS) in Hc2.
    rewrite <- (subst_tt_open_ty_rec W U B1 (open_tt_rec 0 (typ_fvar X) B1) 0 HlcU) in Hc2.
    assert (HwfX : wf_env (X ~ bind_sub ++ atoms_env ats (Z ~ bind_sub ++ E)))
      by (apply (sub_wf_env _ _ _ Hs1)).
    assert (HbsX : bindsub_only (X ~ bind_sub ++ atoms_env ats (Z ~ bind_sub ++ E)))
      by (apply bindsub_only_cons; exact HbsE).
    assert (HfwdE : sub (atoms_env ats (Z ~ bind_sub ++ E)) S U).
    { apply (sub_mono (Z ~ bind_sub ++ E) S U Hfwd
               (atoms_env ats (Z ~ bind_sub ++ E))
               (sub_wf_env _ _ _ HselfA)).
      intros Y HY. exact (binds_atoms_env ats (Z ~ bind_sub ++ E) Y HY). }
    assert (Hlift : sub (X ~ bind_sub ++ atoms_env ats (Z ~ bind_sub ++ E)) S U).
    { apply (sub_mono (atoms_env ats (Z ~ bind_sub ++ E)) S U HfwdE
               (X ~ bind_sub ++ atoms_env ats (Z ~ bind_sub ++ E)) HwfX).
      intros Y HY. unfold binds in *. simpl. right. exact HY. }
    exact (equal_mu_excluded_par (atoms_env ats (Z ~ bind_sub ++ E)) B1 X W S U false
             HbsX HwfX HlcS HlcU Hne (fun H => HXW (eq_sym H)) HXfv HW1 Hs1 Hs2 Hc1 Hc2 Hlift Hb1).
Qed.

(* The same result with the [mocc] side condition discharged: the only *)
(* certificate needed is a syntactic path to a bad leaf that carries a *)
(* free occurrence of W.                                                *)
Corollary deep_equal_mu_excluded_path :
  forall E C Z W S U (T0 : typ) (p : mpath) (B0 : typ),
    bindsub_only (Z ~ bind_sub ++ E) ->
    wf_env (Z ~ bind_sub ++ E) ->
    lc_tt S -> lc_tt U -> S <> U ->
    W <> Z -> Z \notin fv_tt C -> W \in fv_tt C ->
    T0 = open_tt C (open_tt C (typ_fvar Z)) ->
    sub (Z ~ bind_sub ++ E) T0 T0 ->
    sub (Z ~ bind_sub ++ E) (subst_tt W S T0) (subst_tt W U T0) ->
    sub (Z ~ bind_sub ++ E) S U ->
    at_path p T0 (typ_mu B0) ->
    bvoccT true 0 B0 ->
    W \in fv_tt B0 ->
    False.
Proof.
  intros E C Z W S U T0 p B0 Hbs Hwf HlcS HlcU Hne HWZ HZC HWC HT0
         Hself Hcomp Hfwd Hpath Hb HbW.
  exact (deep_equal_mu_excluded E C Z W S U T0 p B0 Hbs Hwf HlcS HlcU Hne
           HWZ HZC HWC HT0 Hself Hcomp Hfwd
           (mocc_self_of_at_path p T0 (typ_mu B0) Hpath) Hpath Hb HbW).
Qed.

(* ------------------------------------------------------------------ *)
(* Assumption audit.                                                   *)
(* ------------------------------------------------------------------ *)
Print Assumptions compose_pullback_self.
Print Assumptions follow_preserves_bad.
Print Assumptions at_path_open_bad.
Print Assumptions deep_equal_mu_excluded.
Print Assumptions deep_equal_mu_excluded_path.
Print Assumptions mocc_self_of_at_path.

(* ================================================================== *)
(* PRECISE REPORT                                                      *)
(* ================================================================== *)
(*                                                                     *)
(* File: /tmp/deep/Deep.v.  It imports TaskBase8 (hence AmberBase,     *)
(* Rules, infra, DoubleUnfolding, Metalib) and contains no forbidden    *)
(* proof escapes or extra global assumptions.  The final audit          *)
(* prints "Closed under the global context" for compose_pullback_self, *)
(* follow_preserves_bad, at_path_open_bad, deep_equal_mu_excluded,     *)
(* deep_equal_mu_excluded_path and mocc_self_of_at_path.               *)
(* Compile with:                                                       *)
(*   rocq compile -q -R /workspace "" \                                *)
(*     -R /workspace/.rocq-deps/Metalib Metalib -R /tmp/deep "" Deep.v *)
(*                                                                     *)
(* RESULTS.                                                            *)
(*                                                                     *)
(* at_path p R D: a syntactic one-hole path in [R] whose distinguished *)
(*   leaf is exactly [D] (mp_here, mp_dom, mp_cod, mp_mu).             *)
(* bvoccT_open_imp: opening at an index different from the occurrence  *)
(*   index preserves a positive/negative bound-variable occurrence.    *)
(* fv_open_rec_incl: opening never removes free atoms.                 *)
(* at_path_open_bad: opening the enclosing context of a path does not  *)
(*   destroy a bad mu leaf: if the old leaf is mu B0 with bvoccT true  *)
(*   0 B0 and W in fv B0, the new leaf is mu B1 with the same two      *)
(*   properties (for any fresh opening atom X <> W).                   *)
(* follow_preserves_bad: if follow ats p R R = Some (A, B) selects a   *)
(*   leaf along such a path, then A = B and A is itself a mu B1 with   *)
(*   bvoccT true 0 B1 and W in fv B1.                                  *)
(* bindsub_only_atoms_env, binds_atoms_env: [atoms_env] only conses    *)
(*   bind_sub entries, so it preserves bindsub_only and binds.         *)
(* sub_arrow_inv_both: inversion of arrow-arrow subtyping into both    *)
(*   component subtyping judgements with stable names.                 *)
(* compose_pullback_self: the engine.  For mocc p T T, a self          *)
(*   derivation sub E T T and a companion derivation sub E             *)
(*   (subst W S T) (subst W U T), it produces shared fresh atoms ats,  *)
(*   Ecur = atoms_env ats E, a leaf A with follow ats p T T =          *)
(*   Some (A, A), the self derivation sub Ecur A A, and the companion  *)
(*   at the same leaf, oriented by mpar p:                             *)
(*     if mpar p then sub Ecur (subst W U A) (subst W S A)             *)
(*     else            sub Ecur (subst W S A) (subst W U A).           *)
(*   The same atoms are used in both projections, so the leaves and    *)
(*   environments coincide.                                            *)
(* mocc_self_of_at_path: at_path p R D implies mocc p R R, so the      *)
(*   mocc side condition of the main theorem is not an extra          *)
(*   assumption.                                                       *)
(*                                                                     *)
(* deep_equal_mu_excluded_path (and deep_equal_mu_excluded, its        *)
(*   mocc-explicit form) has hypotheses:                               *)
(*     bindsub_only (Z ~ bind_sub ++ E), wf_env (Z ~ bind_sub ++ E),   *)
(*     lc_tt S, lc_tt U, S <> U, W <> Z, Z notin fv_tt C,              *)
(*     W in fv_tt C, T0 = open_tt C (open_tt C (fvar Z)),              *)
(*     sub (Z ~ E) T0 T0,                                              *)
(*     sub (Z ~ E) (subst_tt W S T0) (subst_tt W U T0),                *)
(*     sub (Z ~ E) S U,                                                *)
(*     at_path p T0 (typ_mu B0), bvoccT true 0 B0, W in fv_tt B0;      *)
(*   conclusion: False.                                                *)
(*                                                                     *)
(* MAP TO THE ORIGINAL GAP.                                            *)
(*   E is the surrounding environment, C the common mu body, Z the     *)
(*   fresh binder of the equal-body node, W the companion atom, and    *)
(*   S = s, U = t.  [T0 = open C (open C Z)] is the second (double)    *)
(*   unfolding.  The hypothesis sub (Z ~ E) T0 T0 is exactly the       *)
(*   second premise p2 of the self sa_rec node; the hypothesis sub     *)
(*   (Z ~ E) (subst W S T0) (subst W U T0) is exactly the companion    *)
(*   second premise q2 after substituting W.  The hypothesis sub       *)
(*   (Z ~ E) S U is the base derivation.  The first premises p1 and    *)
(*   q1 are NOT hypotheses: the leaf-level forward derivation required *)
(*   by equal_mu_excluded_par is recovered from q2 by inverting the    *)
(*   leaf mu with inv_mu_mu, which exposes BOTH sa_rec premises, and by *)
(*   commuting the substitution through the opening.  This is the crux *)
(*   of why the deep case closes: q2 alone supplies both leaf facts.   *)
(*                                                                     *)
(* PROOF SKETCH.                                                       *)
(*   1. Apply compose_pullback_self to Hself and Hcomp with shared     *)
(*      atoms fresh from fv T0 and W.  Obtain Ecur, a leaf A, the      *)
(*      diagonal follow equation and the two leaf derivations.         *)
(*   2. Apply follow_preserves_bad to the syntactic certificate        *)
(*      (at_path p T0 (mu B0), bvoccT true 0 B0, W in fv B0), using   *)
(*      the freshness returned by compose_pullback_self, and get       *)
(*      A = mu B1 with bvoccT true 0 B1 and W in fv B1.                *)
(*   3. Invert the self derivation at mu B1 with inv_mu_mu, and invert *)
(*      the companion at mu (subst S B1) / mu (subst U B1) (order      *)
(*      fixed by mpar p), choosing one fresh X outside all L sets,     *)
(*      fv B1 and W.  Commute substitution through opening with        *)
(*      subst_tt_open_atom_lc_rec (first unfolding) and                *)
(*      subst_tt_open_ty_rec (second unfolding).                       *)
(*   4. Apply equal_mu_excluded_par with E := Ecur, C := B1, Z := X,   *)
(*      W := W, S := S, T := U, par := mpar p.  Supply bindsub_only    *)
(*      and wf_env for X ~ Ecur (from bindsub_only_atoms_env and       *)
(*      sub_wf_env on the self leaf), the forward derivation lifted by *)
(*      sub_mono along binds_atoms_env, the branch-specific q1/q2      *)
(*      obtained in step 3, and bvoccT true 0 B1.  The result is False.*)
(*                                                                     *)
(* COUNTEREXAMPLE STATUS.                                              *)
(*   No counterexample was found, and no refutation of the target was  *)
(*   produced.  The earlier candidate                                             *)
(*     C = arrow(nat, mu(arrow(arrow W 0) (bvar 1)))                   *)
(*   is not a counterexample: the second sa_rec premise of the         *)
(*   companion forces reverse subtyping between the two partially      *)
(*   unfolded images P and P' (arrow(arrow nat X) Z versus               *)
(*   arrow(arrow top X) Z), so q2 is not derivable from sub s t and    *)
(*   the self derivation, and the instance is consistent.  A body that *)
(*   omits the outer binder occurrence cannot produce q2 either.  The  *)
(*   parity flip (bvoccT true, odd own binder) is what turns the        *)
(*   second unfolding into the reversed leaf comparison, and that flip *)
(*   is exactly what the level-1 exclusion exploits.                   *)
(*                                                                     *)
(* REMAINING OBLIGATION FOR THE ASSEMBLY.                              *)
(*   All hypotheses of deep_equal_mu_excluded_path are either given    *)
(*   by the equal-body node or structural, except the certificate      *)
(*     (exists p B0, at_path p T0 (mu B0) /\\                             *)
(*      bvoccT true 0 B0 /\\ W in fv_tt B0),                             *)
(*   with T0 = open C (open C Z).  (mocc is discharged by              *)
(*   mocc_self_of_at_path.)  The gap's assumption (b) supplies a       *)
(*   path to a mu leaf whose body has bvoccT true 0; at_path_open_bad  *)
(*   shows this survives the two openings.  What is genuinely extra is *)
(*   placing W inside that leaf's body.  W in fv C alone does not      *)
(*   force this syntactically, because W may occur in another part of  *)
(*   C.  The expected discharge is: when the occurrence of C's binder  *)
(*   inside Dbody is replaced during the double unfolding by an image  *)
(*   of C, that image carries the free occurrences of C, in particular *)
(*   those of W; choosing the path that descends through that binder   *)
(*   occurrence therefore yields a leaf B0 with W in fv B0.  This is a *)
(*   purely syntactic occurrence lemma, independent of subtyping, and  *)
(*   is the precise missing step for wiring the theorem into the       *)
(*   equal-body case of the Assembly.  If W does not reach any bad     *)
(*   leaf, the deep exclusion does not apply and that instance has to  *)
(*   be closed by the ordinary (non-deep) argument.                    *)
(*                                                                     *)
(* WHAT THIS DOES NOT CLAIM.                                           *)
(*   The final target amber_complete is not proved.  Only the deep     *)
(*   equal-mu exclusion family above is established.                   *)
(* ================================================================== *)
(* ===== assembly helper lemmas ===== *)

Lemma typ_eq_dec : forall A B : typ, {A = B} + {A <> B}.
Proof. decide equality; apply eq_dec. Qed.


Fixpoint bvoccT_dec (q : bool) (K : nat) (C : typ) {struct C} :
  {bvoccT q K C} + {~ bvoccT q K C}.
Proof.
  destruct C as [| |n|X|C0|C1 C2]; simpl.
  - right. intro H. exact H.
  - right. intro H. exact H.
  - destruct (Nat.eq_dec n K) as [e|ne].
    + subst n. destruct q.
      * right. intro H. destruct H as [_ Hq]. discriminate Hq.
      * left. split; [reflexivity|reflexivity].
    + right. intro H. destruct H as [Hn _]. apply ne. exact Hn.
  - right. intro H. exact H.
  - exact (bvoccT_dec q (S K) C0).
  - destruct (bvoccT_dec (negb q) K C1) as [H1|H1];
      destruct (bvoccT_dec q K C2) as [H2|H2].
    + left. left. exact H1.
    + left. left. exact H1.
    + left. right. exact H2.
    + right. intro H. destruct H as [H|H].
      * exact (H1 H).
      * exact (H2 H).
Defined.



Lemma amber_cov_fvar_val : forall Ea Em X m,
  wfe_amber Ea ->
  amber_cov Ea Em (typ_fvar X) m = typ_fvar (cov_fun Ea Em m X).
Proof.
  intros Ea Em X m Hwe.
  rewrite (amber_cov_ren Ea Hwe Em (typ_fvar X) m). reflexivity.
Qed.

(* Placeholder interface for the deep equal-body exclusion; the running
   worker is proving a concrete version. *)

Fixpoint typ_fvar_witness (A : typ) : option atom :=
  match A with
  | typ_fvar X => Some X
  | typ_arrow A1 A2 =>
      match typ_fvar_witness A1 with Some X => Some X | None => typ_fvar_witness A2 end
  | typ_mu A0 => typ_fvar_witness A0
  | _ => None
  end.

Lemma typ_fvar_witness_some : forall A X,
  typ_fvar_witness A = Some X -> X \in fv_tt A.
Proof.
  induction A as [| |n|Y|A0 IHA|A1 IH1 A2 IH2]; simpl; intros X H.
  - discriminate.
  - discriminate.
  - discriminate.
  - injection H as Heq. subst X. fsetdec.
  - apply IHA. exact H.
  - destruct (typ_fvar_witness A1) as [Y|] eqn:E.
    + simpl in H. injection H as Heq. subst X.
      apply union_iff. left. exact (IH1 Y eq_refl).
    + simpl in H. apply union_iff. right. exact (IH2 X H).
Qed.

Lemma typ_fvar_witness_none : forall A,
  typ_fvar_witness A = None -> forall X, X \notin fv_tt A.
Proof.
  induction A as [| |n|Y|A0 IHA|A1 IH1 A2 IH2]; simpl; intros H X HX.
  - fsetdec.
  - fsetdec.
  - fsetdec.
  - discriminate H.
  - apply (IHA H X). exact HX.
  - apply union_iff in HX. destruct HX as [HX|HX].
    + destruct (typ_fvar_witness A1) as [Y|] eqn:E.
      * simpl in H. discriminate H.
      * simpl in H. exact (IH1 eq_refl X HX).
    + destruct (typ_fvar_witness A1) as [Y|] eqn:E.
      * simpl in H. discriminate H.
      * simpl in H. exact (IH2 H X HX).
Qed.

Lemma amber_cov_no_fv : forall Ea Em A m,
  (forall X, X \notin fv_tt A) -> amber_cov Ea Em A m = A.
Proof.
  intros Ea. induction Ea as [|[Z Y] Ea IH]; intros Em A m H.
  - destruct Em; reflexivity.
  - destruct Em as [|m' Em']; [reflexivity|].
    simpl. destruct (eqMode m' m).
    + rewrite (subst_tt_fresh Z Y A (H Z)). apply IH. exact H.
    + apply IH. exact H.
Qed.

(* ===== Deep2: parameterized deep exclusion + path certificate ===== *)


(* ================================================================== *)
(* Deep2: parameterized deep exclusion and the path certificate.       *)
(* ================================================================== *)

(* ------------------------------------------------------------------ *)
(* Reversed joint projection.  It is the companion-orientation mirror  *)
(* of compose_pullback_self.  It follows immediately from the original *)
(* engine by exchanging the roles of S and U: the companion hypothesis *)
(* of the original at (U, S) is exactly the reversed companion at      *)
(* (S, U), and the [mpar] branch is then already the required mirror.  *)
(* ------------------------------------------------------------------ *)
Lemma compose_pullback_self_rev : forall p T,
  mocc p T T ->
  forall E W S U,
    lc_tt S -> lc_tt U ->
    sub E T T ->
    sub E (subst_tt W U T) (subst_tt W S T) ->
    forall L0 : atoms,
    exists ats Ecur A,
      Ecur = atoms_env ats E /\
      (forall Z, In Z ats -> Z \notin L0 /\ Z <> W) /\
      follow ats p T T = Some (A, A) /\
      sub Ecur A A /\
      (if mpar p
       then sub Ecur (subst_tt W S A) (subst_tt W U A)
       else sub Ecur (subst_tt W U A) (subst_tt W S A)).
Proof.
  intros p T Hmo E W S U HlcS HlcU Hself Hcomp L0.
  destruct (compose_pullback_self p T Hmo E W U S HlcU HlcS Hself Hcomp L0)
    as [ats [Ecur [A [HEq [Hfresh [Hfollow [HselfA HcompA]]]]]]].
  exists ats, Ecur, A. split; [exact HEq|]. split; [exact Hfresh|].
  split; [exact Hfollow|]. split; [exact HselfA|]. exact HcompA.
Qed.

(* ------------------------------------------------------------------ *)
(* Parameterized deep equal-mu exclusion.  [par] selects the           *)
(* orientation of the companion at T0.  The proof splits on [par].     *)
(* The par = false branch is the untangled corollary.  In the par =    *)
(* true branch the reversed engine projects the companion; at the      *)
(* selected leaf its orientation is flipped by [mpar p], so the        *)
(* battery is applied with parity [negb (mpar p)] in order to match    *)
(* the leaf companion premise.  The forward derivation sub S U is      *)
(* always used in the same direction (lifted by sub_mono).             *)
(* ------------------------------------------------------------------ *)
Theorem deep_equal_mu_excluded_path_par :
  forall E C Z W S U (T0 : typ) (p : mpath) (B0 : typ) (par : bool),
    bindsub_only (Z ~ bind_sub ++ E) ->
    wf_env (Z ~ bind_sub ++ E) ->
    lc_tt S -> lc_tt U -> S <> U ->
    W <> Z -> Z \notin fv_tt C -> W \in fv_tt C ->
    T0 = open_tt C (open_tt C (typ_fvar Z)) ->
    sub (Z ~ bind_sub ++ E) T0 T0 ->
    (if par
     then sub (Z ~ bind_sub ++ E) (subst_tt W U T0) (subst_tt W S T0)
     else sub (Z ~ bind_sub ++ E) (subst_tt W S T0) (subst_tt W U T0)) ->
    sub (Z ~ bind_sub ++ E) S U ->
    at_path p T0 (typ_mu B0) ->
    bvoccT true 0 B0 ->
    W \in fv_tt B0 ->
    False.
Proof.
  intros E C Z W S U T0 p B0 par Hbs Hwf HlcS HlcU Hne HWZ HZC HWC HT0
         Hself Hcomp Hfwd Hpath Hb HbW.
  destruct par; simpl in Hcomp.
  - (* par = true : reversed companion at T0 *)
    destruct (compose_pullback_self_rev p T0
                (mocc_self_of_at_path p T0 (typ_mu B0) Hpath)
                (Z ~ bind_sub ++ E) W S U HlcS HlcU Hself Hcomp
                (fv_tt T0 \u {{W}}))
      as [ats [Ecur [A [HEq [Hfresh [Hfollow [HselfA HcompA]]]]]]].
    subst Ecur.
    destruct (follow_preserves_bad p T0 (typ_mu B0) Hpath ats A A W B0
                Hfollow (fun X HX => proj2 (Hfresh X HX)) eq_refl Hb HbW)
      as [_ [B1 [HA [Hb1 HW1]]]].
    subst A. simpl in HcompA.
    assert (HbsE : bindsub_only (atoms_env ats (Z ~ bind_sub ++ E))).
    { apply bindsub_only_atoms_env. exact Hbs. }
    destruct (mpar p) eqn:Epar; simpl in HcompA.
    + (* mpar p = true : leaf companion is S-left / U-right *)
      destruct (inv_mu_mu (atoms_env ats (Z ~ bind_sub ++ E)) B1 B1 HselfA)
        as [Ls [Hs1 Hs2]].
      destruct (inv_mu_mu (atoms_env ats (Z ~ bind_sub ++ E))
                 (subst_tt W S B1) (subst_tt W U B1) HcompA) as [Lc [Hc1 Hc2]].
      destruct (atom_fresh (Ls \u Lc \u fv_tt B1 \u {{W}})) as [X HX].
      assert (HXLs : X \notin Ls) by fsetdec.
      assert (HXLc : X \notin Lc) by fsetdec.
      assert (HXfv : X \notin fv_tt B1) by fsetdec.
      assert (HXW : X <> W) by fsetdec.
      specialize (Hs1 X HXLs). specialize (Hs2 X HXLs).
      specialize (Hc1 X HXLc). specialize (Hc2 X HXLc).
      unfold open_tt in Hc1, Hc2.
      rewrite <- (subst_tt_open_atom_lc_rec W S B1 0 X HlcS HXW) in Hc1.
      rewrite <- (subst_tt_open_atom_lc_rec W U B1 0 X HlcU HXW) in Hc1.
      rewrite <- (subst_tt_open_atom_lc_rec W S B1 0 X HlcS HXW) in Hc2.
      rewrite <- (subst_tt_open_atom_lc_rec W U B1 0 X HlcU HXW) in Hc2.
      rewrite <- (subst_tt_open_ty_rec W S B1 (open_tt_rec 0 (typ_fvar X) B1) 0 HlcS) in Hc2.
      rewrite <- (subst_tt_open_ty_rec W U B1 (open_tt_rec 0 (typ_fvar X) B1) 0 HlcU) in Hc2.
      assert (HwfX : wf_env (X ~ bind_sub ++ atoms_env ats (Z ~ bind_sub ++ E)))
        by (apply (sub_wf_env _ _ _ Hs1)).
      assert (HbsX : bindsub_only (X ~ bind_sub ++ atoms_env ats (Z ~ bind_sub ++ E)))
        by (apply bindsub_only_cons; exact HbsE).
      assert (HfwdE : sub (atoms_env ats (Z ~ bind_sub ++ E)) S U).
      { apply (sub_mono (Z ~ bind_sub ++ E) S U Hfwd
                 (atoms_env ats (Z ~ bind_sub ++ E))
                 (sub_wf_env _ _ _ HselfA)).
        intros Y HY. exact (binds_atoms_env ats (Z ~ bind_sub ++ E) Y HY). }
      assert (Hlift : sub (X ~ bind_sub ++ atoms_env ats (Z ~ bind_sub ++ E)) S U).
      { apply (sub_mono (atoms_env ats (Z ~ bind_sub ++ E)) S U HfwdE
                 (X ~ bind_sub ++ atoms_env ats (Z ~ bind_sub ++ E)) HwfX).
        intros Y HY. unfold binds in *. simpl. right. exact HY. }
      exact (equal_mu_excluded_par (atoms_env ats (Z ~ bind_sub ++ E)) B1 X W S U false
               HbsX HwfX HlcS HlcU Hne (fun H => HXW (eq_sym H)) HXfv HW1 Hs1 Hs2 Hc1 Hc2 Hlift Hb1).
    + (* mpar p = false : leaf companion is U-left / S-right *)
      destruct (inv_mu_mu (atoms_env ats (Z ~ bind_sub ++ E)) B1 B1 HselfA)
        as [Ls [Hs1 Hs2]].
      destruct (inv_mu_mu (atoms_env ats (Z ~ bind_sub ++ E))
                 (subst_tt W U B1) (subst_tt W S B1) HcompA) as [Lc [Hc1 Hc2]].
      destruct (atom_fresh (Ls \u Lc \u fv_tt B1 \u {{W}})) as [X HX].
      assert (HXLs : X \notin Ls) by fsetdec.
      assert (HXLc : X \notin Lc) by fsetdec.
      assert (HXfv : X \notin fv_tt B1) by fsetdec.
      assert (HXW : X <> W) by fsetdec.
      specialize (Hs1 X HXLs). specialize (Hs2 X HXLs).
      specialize (Hc1 X HXLc). specialize (Hc2 X HXLc).
      unfold open_tt in Hc1, Hc2.
      rewrite <- (subst_tt_open_atom_lc_rec W U B1 0 X HlcU HXW) in Hc1.
      rewrite <- (subst_tt_open_atom_lc_rec W S B1 0 X HlcS HXW) in Hc1.
      rewrite <- (subst_tt_open_atom_lc_rec W U B1 0 X HlcU HXW) in Hc2.
      rewrite <- (subst_tt_open_atom_lc_rec W S B1 0 X HlcS HXW) in Hc2.
      rewrite <- (subst_tt_open_ty_rec W U B1 (open_tt_rec 0 (typ_fvar X) B1) 0 HlcU) in Hc2.
      rewrite <- (subst_tt_open_ty_rec W S B1 (open_tt_rec 0 (typ_fvar X) B1) 0 HlcS) in Hc2.
      assert (HwfX : wf_env (X ~ bind_sub ++ atoms_env ats (Z ~ bind_sub ++ E)))
        by (apply (sub_wf_env _ _ _ Hs1)).
      assert (HbsX : bindsub_only (X ~ bind_sub ++ atoms_env ats (Z ~ bind_sub ++ E)))
        by (apply bindsub_only_cons; exact HbsE).
      assert (HfwdE : sub (atoms_env ats (Z ~ bind_sub ++ E)) S U).
      { apply (sub_mono (Z ~ bind_sub ++ E) S U Hfwd
                 (atoms_env ats (Z ~ bind_sub ++ E))
                 (sub_wf_env _ _ _ HselfA)).
        intros Y HY. exact (binds_atoms_env ats (Z ~ bind_sub ++ E) Y HY). }
      assert (Hlift : sub (X ~ bind_sub ++ atoms_env ats (Z ~ bind_sub ++ E)) S U).
      { apply (sub_mono (atoms_env ats (Z ~ bind_sub ++ E)) S U HfwdE
                 (X ~ bind_sub ++ atoms_env ats (Z ~ bind_sub ++ E)) HwfX).
        intros Y HY. unfold binds in *. simpl. right. exact HY. }
      exact (equal_mu_excluded_par (atoms_env ats (Z ~ bind_sub ++ E)) B1 X W S U true
               HbsX HwfX HlcS HlcU Hne (fun H => HXW (eq_sym H)) HXfv HW1 Hs1 Hs2 Hc1 Hc2 Hlift Hb1).
  - (* par = false : untangled companion; the previous corollary applies *)
    exact (deep_equal_mu_excluded_path E C Z W S U T0 p B0 Hbs Hwf HlcS HlcU Hne
             HWZ HZC HWC HT0 Hself Hcomp Hfwd Hpath Hb HbW).
Qed.

(* ================================================================== *)
(* Part 2: syntactic path certificate.                                 *)
(* ================================================================== *)

(* Boolean XOR is its own inverse. *)
Lemma xorb_xorb_cancel : forall p q, xorb (xorb p q) q = p.
Proof. destruct p, q; reflexivity. Qed.

(* If T has a bound-variable occurrence at depth K and U has a free    *)
(* occurrence of W, then opening T at K with U makes W occur.  This is *)
(* the forward direction of hasp_open_rec for the appropriate parity.  *)
Lemma bvoccT_open_fv : forall q K T U W,
  bvoccT q K T ->
  W \in fv_tt U ->
  W \in fv_tt (open_tt_rec K U T).
Proof.
  intros q K T U W Hb HW.
  destruct (fv_hasp U W HW) as [HU|HU].
  - apply hasp_fv with (p := xorb true q).
    rewrite hasp_open_rec.
    right. exists q. split; [exact Hb|].
    rewrite xorb_xorb_cancel. exact HU.
  - apply hasp_fv with (p := xorb false q).
    rewrite hasp_open_rec.
    right. exists q. split; [exact Hb|].
    rewrite xorb_xorb_cancel. exact HU.
Qed.

(* Converse information for free variables: opening introduces a free  *)
(* variable only if it already occurred in the body or an occurrence of *)
(* the opened index was substituted.                                   *)
Lemma fv_open_rec_elim : forall K U T W,
  W \in fv_tt (open_tt_rec K U T) ->
  W \in fv_tt T \/ (exists q, bvoccT q K T).
Proof.
  intros K U T W HW.
  destruct (fv_hasp (open_tt_rec K U T) W HW) as [Hp|Hp];
    apply (proj1 (hasp_open_rec T K U _ W)) in Hp;
    destruct Hp as [Hbody | [q [Hb _]]].
  - left. exact (hasp_fv T _ W Hbody).
  - right. exists q. exact Hb.
  - left. exact (hasp_fv T _ W Hbody).
  - right. exists q. exact Hb.
Qed.

(* ------------------------------------------------------------------ *)
(* One-hole type contexts, their path, and the number of encompassing  *)
(* mu binders.  [plug c D] fills the hole with D; [ctx_path c] is the  *)
(* corresponding mpath; [ctx_depth c] is the number of mu constructors *)
(* on the path from the root to the hole.                              *)
(* ------------------------------------------------------------------ *)
Inductive tctx : Set :=
| tc_hole : tctx
| tc_arrow_l : tctx -> typ -> tctx
| tc_arrow_r : typ -> tctx -> tctx
| tc_mu : tctx -> tctx.

Fixpoint plug (c : tctx) (D : typ) : typ :=
  match c with
  | tc_hole => D
  | tc_arrow_l c' B => typ_arrow (plug c' D) B
  | tc_arrow_r A c' => typ_arrow A (plug c' D)
  | tc_mu c' => typ_mu (plug c' D)
  end.

Fixpoint ctx_path (c : tctx) : mpath :=
  match c with
  | tc_hole => mp_here
  | tc_arrow_l c' _ => mp_dom (ctx_path c')
  | tc_arrow_r _ c' => mp_cod (ctx_path c')
  | tc_mu c' => mp_mu (ctx_path c')
  end.

Fixpoint ctx_depth (c : tctx) : nat :=
  match c with
  | tc_hole => 0
  | tc_arrow_l c' _ => ctx_depth c'
  | tc_arrow_r _ c' => ctx_depth c'
  | tc_mu c' => S (ctx_depth c')
  end.

(* Opening the filled context descends to the hole with shift equal to *)
(* the number of mus on the path.                                      *)
Lemma at_path_open_plug : forall c D K U,
  at_path (ctx_path c)
    (open_tt_rec K U (plug c D))
    (open_tt_rec (K + ctx_depth c) U D).
Proof.
  induction c as [|c IH B|A c IH|c IH]; intros D K U; simpl.
  - replace (K + 0) with K by lia. apply ap_here.
  - apply ap_dom. apply IH.
  - apply ap_cod. apply IH.
  - replace (K + S (ctx_depth c)) with (S K + ctx_depth c) by lia.
    apply ap_mu. apply IH.
Qed.

(* The map from a context to its hole is a valid syntactic path. *)
Lemma at_path_plug : forall c D, at_path (ctx_path c) (plug c D) D.
Proof.
  induction c as [|c IH B|A c IH|c IH]; intros D; simpl.
  - apply ap_here.
  - apply ap_dom. apply IH.
  - apply ap_cod. apply IH.
  - apply ap_mu. apply IH.
Qed.

(* ------------------------------------------------------------------ *)
(* Certificate: a bad mu subterm D = mu Dbody of C, together with an   *)
(* occurrence of C's own binder inside Dbody (at depth [ctx_depth c + *)
(* 1], or with W occurring directly in Dbody), yields, after the       *)
(* double opening, a syntactic path to a mu leaf whose body has the    *)
(* odd own-binder occurrence and contains W.                           *)
(*                                                                     *)
(* The leaf is exactly the image of D under the opening, at the path   *)
(* determined by the context.  Its body is                          *)
(*   open_tt_rec (S (ctx_depth c)) U Dbody                             *)
(* where U = open_tt C (fvar Z) is the second-unfolding argument.      *)
(* ------------------------------------------------------------------ *)
Lemma bad_leaf_certificate :
  forall C Z W (c : tctx) (Dbody : typ),
    C = plug c (typ_mu Dbody) ->
    bvoccT true 0 Dbody ->
    (W \in fv_tt Dbody \/
     (exists q, bvoccT q (S (ctx_depth c)) Dbody)) ->
    W \in fv_tt C ->
    exists p B0,
      at_path p (open_tt C (open_tt C (typ_fvar Z))) (typ_mu B0) /\
      bvoccT true 0 B0 /\
      W \in fv_tt B0.
Proof.
  intros C Z W c Dbody HC Hb Hocc HW.
  subst C.
  set (U := open_tt (plug c (typ_mu Dbody)) (typ_fvar Z)).
  set (B0 := open_tt_rec (S (ctx_depth c)) U Dbody).
  exists (ctx_path c), B0.
  subst B0.
  split.
  - (* syntactic path in the double unfolding *)
    change (at_path (ctx_path c)
              (open_tt_rec 0 U (plug c (typ_mu Dbody)))
              (typ_mu (open_tt_rec (S (ctx_depth c)) U Dbody))).
    pose proof (at_path_open_plug c (typ_mu Dbody) 0 U) as HAP.
    simpl in HAP. exact HAP.
  - split.
    + (* odd own-binder occurrence survives opening at a positive shift *)
      apply (bvoccT_open_imp true 0 Dbody (S (ctx_depth c)) U).
      * intro H. discriminate H.
      * exact Hb.
    + (* W reaches the leaf body *)
      destruct Hocc as [Hbody | [q Hq]].
      * apply (fv_open_rec_incl Dbody (S (ctx_depth c)) U W Hbody).
      * apply (bvoccT_open_fv q (S (ctx_depth c)) Dbody U W Hq).
        apply (fv_open_rec_incl (plug c (typ_mu Dbody)) 0 (typ_fvar Z) W HW).
Qed.

(* ------------------------------------------------------------------ *)
(* Constructive complementary facts.                                   *)
(*                                                                     *)
(* (1) At a bad leaf whose body does not contain W, substituting W has *)
(*     no effect on either side, so the companion comparison at that   *)
(*     leaf is literally the reflexive self comparison; no reversed    *)
(*     information is produced there and the deep exclusion is not     *)
(*     applicable.                                                      *)
(*                                                                     *)
(* (2) If [Dbody] contains neither W nor an occurrence of C's binder,  *)
(*     then the leaf built at D's path from the double opening does    *)
(*     not carry W either.  Hence the certificate of the previous      *)
(*     lemma genuinely needs one of those two occurrence conditions.    *)
(* ------------------------------------------------------------------ *)
Lemma bad_leaf_without_W_companion_self :
  forall E W S U (B0 : typ),
    W \notin fv_tt B0 ->
    (sub E (subst_tt W S (typ_mu B0)) (subst_tt W U (typ_mu B0)) <->
     sub E (typ_mu B0) (typ_mu B0)).
Proof.
  intros E W S U B0 HW.
  assert (Hs : subst_tt W S (typ_mu B0) = typ_mu B0)
    by (simpl; f_equal; apply subst_tt_fresh; exact HW).
  assert (Hu : subst_tt W U (typ_mu B0) = typ_mu B0)
    by (simpl; f_equal; apply subst_tt_fresh; exact HW).
  rewrite Hs, Hu. reflexivity.
Qed.

Lemma constructed_leaf_without_W :
  forall c Dbody Z W,
    ~ (exists q, bvoccT q (S (ctx_depth c)) Dbody) ->
    W \notin fv_tt Dbody ->
    W \notin fv_tt (open_tt_rec (S (ctx_depth c))
                    (open_tt (plug c (typ_mu Dbody)) (typ_fvar Z)) Dbody).
Proof.
  intros c Dbody Z W Hno Hbody HW.
  destruct (fv_open_rec_elim (S (ctx_depth c))
              (open_tt (plug c (typ_mu Dbody)) (typ_fvar Z)) Dbody W HW)
    as [Hin|Hocc].
  - exact (Hbody Hin).
  - exact (Hno Hocc).
Qed.

(* Decidability of having an occurrence of the opened index at a given *)
(* depth, stated as a constructive dichotomy (no classical axioms).    *)
Lemma outer_occ_dec : forall K T,
  (exists q, bvoccT q K T) \/ ~ (exists q, bvoccT q K T).
Proof.
  intros K T.
  destruct (bvoccT_dec true K T) as [H|H].
  - left. exists true. exact H.
  - destruct (bvoccT_dec false K T) as [H0|H0].
    + left. exists false. exact H0.
    + right. intros [q Hq]. destruct q.
      * exact (H Hq).
      * exact (H0 Hq).
Qed.

(* ------------------------------------------------------------------ *)
(* Assumption audit.                                                   *)
(* ------------------------------------------------------------------ *)
Print Assumptions compose_pullback_self_rev.
Print Assumptions deep_equal_mu_excluded_path_par.
Print Assumptions bvoccT_open_fv.
Print Assumptions fv_open_rec_elim.
Print Assumptions at_path_open_plug.
Print Assumptions bad_leaf_certificate.
Print Assumptions bad_leaf_without_W_companion_self.
Print Assumptions constructed_leaf_without_W.
Print Assumptions bvoccT_dec.
Print Assumptions outer_occ_dec.

(* ================================================================== *)
(* REPORT FOR DEEP2                                                    *)
(* ================================================================== *)
(*                                                                     *)
(* File: /tmp/deep/Deep2.v.  Imports TaskBase8 (and Deep, which is     *)
(* already Closed) and Lia.  No admits, axioms, parameters or other    *)
(* escapes.  Compiles with:                                            *)
(*   rocq compile -q -R /workspace "" \                                *)
(*     -R /workspace/.rocq-deps/Metalib Metalib -R /tmp/deep "" Deep2.v*)
(* All ten audited constants print "Closed under the global context".  *)
(*                                                                     *)
(* PART 1.  PARAMETERIZED DEEP LEMMA.                                  *)
(*                                                                     *)
(* compose_pullback_self_rev :                                         *)
(*   forall p T, mocc p T T ->                                         *)
(*   forall E W S U, lc_tt S -> lc_tt U -> sub E T T ->                *)
(*     sub E (subst_tt W U T) (subst_tt W S T) ->                      *)
(*     forall L0, exists ats Ecur A,                                   *)
(*       Ecur = atoms_env ats E /\                                     *)
(*       (forall Z, In Z ats -> Z notin L0 /\ Z <> W) /\              *)
(*       follow ats p T T = Some (A, A) /\ sub Ecur A A /\            *)
(*       (if mpar p then sub Ecur (subst_tt W S A)(subst_tt W U A)     *)
(*                   else sub Ecur (subst_tt W U A)(subst_tt W S A)).  *)
(*   Proof: derive from compose_pullback_self instantiated at (U, S).  *)
(*   That call's companion hypothesis is exactly the reversed          *)
(*   companion at (S, U), and its [mpar] branch is already the mirror  *)
(*   orientation; no separate induction is needed.  This is logically  *)
(*   the same as re-running the original induction with the roles of   *)
(*   S and U exchanged.                                                *)
(*                                                                     *)
(* deep_equal_mu_excluded_path_par :                                   *)
(*   forall E C Z W S U T0 p B0 par,                                   *)
(*     bindsub_only (Z ~ bind_sub ++ E) -> wf_env (Z ~ bind_sub ++ E)  *)
(*     -> lc_tt S -> lc_tt U -> S <> U                                 *)
(*     -> W <> Z -> Z notin fv_tt C -> W in fv_tt C                    *)
(*     -> T0 = open_tt C (open_tt C (typ_fvar Z))                      *)
(*     -> sub (Z ~ bind_sub ++ E) T0 T0                                *)
(*     -> (if par then sub (Z ~ bind_sub ++ E)                         *)
(*                       (subst_tt W U T0) (subst_tt W S T0)           *)
(*            else sub (Z ~ bind_sub ++ E)                             *)
(*                       (subst_tt W S T0) (subst_tt W U T0))          *)
(*     -> sub (Z ~ bind_sub ++ E) S U                                  *)
(*     -> at_path p T0 (typ_mu B0) -> bvoccT true 0 B0                 *)
(*     -> W in fv_tt B0 -> False.                                      *)
(*   Proof: destruct par.  The false branch is exactly                 *)
(*   deep_equal_mu_excluded_path.  The true branch uses the reversed   *)
(*   engine, follow_preserves_bad, inv_mu_mu at the leaf, substitution *)
(*   commutation through the two openings                              *)
(*   (subst_tt_open_atom_lc_rec and subst_tt_open_ty_rec), and the     *)
(*   level-1 battery equal_mu_excluded_par.                            *)
(*                                                                     *)
(*   PRECISE PARITY NOTE.  With the reversed engine the leaf companion *)
(*   orientation is: mpar p = true  gives S-left / U-right;            *)
(*                   mpar p = false gives U-left / S-right.            *)
(*   The battery's [par] selects its companion premise as:             *)
(*     par = true  -> U-left / S-right;                                *)
(*     par = false -> S-left / U-right.                                *)
(*   Hence the battery must be invoked with [negb (mpar p)], not with  *)
(*   [mpar p].  The forward derivation sub S U is used in the same     *)
(*   direction in both mpar subcases (lifted by sub_mono and            *)
(*   binds_atoms_env); no backward derivation is required.             *)
(*                                                                     *)
(* PART 2.  SYNTACTIC PATH CERTIFICATE.                                *)
(*                                                                     *)
(* New inductive tctx of one-hole contexts (hole, arrow-left,          *)
(* arrow-right, mu), with plug, ctx_path (the mpath to the hole), and  *)
(* ctx_depth (the number of mu constructors on the path to the hole).  *)
(*                                                                     *)
(* at_path_open_plug :                                                 *)
(*   forall c D K U, at_path (ctx_path c)                              *)
(*     (open_tt_rec K U (plug c D))                                    *)
(*     (open_tt_rec (K + ctx_depth c) U D).                            *)
(*   Opening a filled context reaches the hole with shift increased by *)
(*   the number of mus on the path.                                    *)
(*                                                                     *)
(* at_path_plug : forall c D, at_path (ctx_path c) (plug c D) D.       *)
(*                                                                     *)
(* bad_leaf_certificate :                                              *)
(*   forall C Z W (c : tctx) (Dbody : typ),                            *)
(*     C = plug c (typ_mu Dbody) ->                                    *)
(*     bvoccT true 0 Dbody ->                                          *)
(*     (W in fv_tt Dbody \/                                            *)
(*      (exists q, bvoccT q (S (ctx_depth c)) Dbody)) ->               *)
(*     W in fv_tt C ->                                                 *)
(*     exists p B0,                                                    *)
(*       at_path p (open_tt C (open_tt C (typ_fvar Z))) (typ_mu B0) /\ *)
(*       bvoccT true 0 B0 /\ W in fv_tt B0.                            *)
(*   The witness is p = ctx_path c and                                *)
(*   B0 = open_tt_rec (S (ctx_depth c)) U Dbody, where                 *)
(*   U = open_tt C (typ_fvar Z).  This is exactly the certificate the  *)
(*   parameterized deep theorem consumes.                              *)
(*                                                                     *)
(*   WHY THE INDEX IS [S (ctx_depth c)].  If D sits under d =          *)
(*   ctx_depth c enclosing mus inside C, then C's own de Bruijn binder *)
(*   (index 0 at the root of C) has index d + 1 = S d when seen inside *)
(*   Dbody, because each crossed mu increments it.  bvoccT itself      *)
(*   increments its index under inner mus, so bvoccT q (S d) Dbody     *)
(*   detects precisely the occurrences of C's binder inside Dbody at   *)
(*   the correct absolute parity q (q = false at the leaf, flipped     *)
(*   under arrow domains).  This matches the gap's "free occurrence of *)
(*   C's binder" condition with K = ctx_depth c.                       *)
(*                                                                     *)
(*   WHY W REACHES THE LEAF.  During the double opening, the second    *)
(*   unfolding argument U = open_tt C (fvar Z) is substituted for      *)
(*   exactly those occurrences of C's binder.  So if one exists,       *)
(*   bvoccT_open_fv puts W into the leaf body because W in fv_tt C and *)
(*   opening never removes free atoms (fv_open_rec_incl).  If instead  *)
(*   W occurs directly in Dbody, fv_open_rec_incl alone puts it in the *)
(*   leaf body.  Hence the disjunction in the hypothesis is exactly    *)
(*   the union of the two ways W can reach the leaf.  W <> Z is not    *)
(*   needed by this lemma.                                             *)
(*                                                                     *)
(* COMPLEMENTARY CONSTRUCTIVE FACTS.                                   *)
(*                                                                     *)
(* fv_open_rec_elim : if W occurs in open_tt_rec K U T, then either W  *)
(*   occurs in T or T has a bound-variable occurrence at K (with some  *)
(*   parity).  Converse of the insertion behaviour.                    *)
(*                                                                     *)
(* constructed_leaf_without_W : if Dbody has no occurrence of C's      *)
(*   binder at S (ctx_depth c) and W is not free in Dbody, then the   *)
(*   leaf B0 built at D's path does not contain W either.  Thus the    *)
(*   certificate genuinely needs one of the two occurrence conditions; *)
(*   this is the exact complementary case to bad_leaf_certificate.     *)
(*                                                                     *)
(* bad_leaf_without_W_companion_self : at a bad leaf whose body lacks  *)
(*   W, subst_tt W S and subst_tt W U are both the identity on the     *)
(*   whole mu leaf, so the companion premise at that leaf is logically *)
(*   the same as the reflexive self premise.  No reversed comparison   *)
(*   arises there, so the deep exclusion is not applicable and the     *)
(*   equal node is to be opened and handled at the body (the ordinary  *)
(*   path), exactly as required for the complementary case.            *)
(*                                                                     *)
(* bvoccT_dec and outer_occ_dec give constructive decidability of      *)
(* having an outer-binder occurrence at a given depth, so the Assembly *)
(* can case-split between the certificate case and the complementary   *)
(* case without any classical axiom.  A literal disjunction             *)
(* "certificate OR no certificate" over all paths is not stated,       *)
(* because it would require classical logic over an unbounded path     *)
(* quantifier and would break the Closed audit; the two lemmas above   *)
(* provide the same case analysis constructively.                      *)
(*                                                                     *)
(* RESIDUAL.  The Assembly must supply the decomposition C = plug c    *)
(* (typ_mu Dbody) with bvoccT true 0 Dbody, and either W in fv_tt      *)
(* Dbody or an occurrence bvoccT q (S (ctx_depth c)) Dbody.  In the    *)
(* intended use, condition (b) of the gap (the occurrence of C's       *)
(* binder inside Dbody) is exactly the second alternative, with the    *)
(* depth read as ctx_depth c; W in fv_tt C is given.  No further       *)
(* subtyping obligation remains for the certificate.                   *)
(* ================================================================== *)

(* ===== Deep3: bad-leaf search and frozen predicate ===== *)


(* ================================================================== *)
(* Deep3: syntactic search, frozen predicate, and the Assembly plug.   *)
(* ================================================================== *)

(* ------------------------------------------------------------------ *)
(* Decidable tests.                                                    *)
(* ------------------------------------------------------------------ *)

Lemma fv_dec : forall (W : atom) (T : typ),
  {W \in fv_tt T} + {~ W \in fv_tt T}.
Proof.
  intros W T.
  destruct (AtomSetImpl.mem W (fv_tt T)) eqn:E.
  - left. apply AtomSetImpl.mem_2. exact E.
  - right. intro H. apply AtomSetImpl.mem_1 in H. rewrite H in E. discriminate E.
Qed.

Lemma outer_occ_sumbool : forall K T,
  {(exists q, bvoccT q K T)} + {~ (exists q, bvoccT q K T)}.
Proof.
  intros K T.
  destruct (bvoccT_dec true K T) as [H|H].
  - left. exists true. exact H.
  - destruct (bvoccT_dec false K T) as [H0|H0].
    + left. exists false. exact H0.
    + right. intros [q Hq]. destruct q.
      * exact (H Hq).
      * exact (H0 Hq).
Qed.

(* [bad_at W K D] says D is a mu body with the odd own-binder occurrence *)
(* and either W free in D or an occurrence of the outer binder at the   *)
(* depth one below the current absolute depth [K].                      *)
Definition bad_at (W : atom) (K : nat) (D : typ) : Prop :=
  bvoccT true 0 D /\
  (W \in fv_tt D \/ (exists q, bvoccT q (S K) D)).

Lemma bad_at_dec : forall W K D,
  {bad_at W K D} + {~ bad_at W K D}.
Proof.
  intros W K D. unfold bad_at.
  destruct (bvoccT_dec true 0 D) as [Hb|Hb].
  - destruct (fv_dec W D) as [Hf|Hf].
    + left. split; [exact Hb|left; exact Hf].
    + destruct (outer_occ_sumbool (S K) D) as [Ho|Ho].
      * left. split; [exact Hb|right; exact Ho].
      * right. intros [Hb' [Hf'|Ho']].
        -- exact (Hf Hf').
        -- exact (Ho Ho').
  - right. intros [Hb' _]. exact (Hb Hb').
Qed.

(* ------------------------------------------------------------------ *)
(* Syntactic search.  [K] is the absolute depth (number of mu          *)
(* constructors outside the current subterm).  A bad mu at the current *)
(* node is returned with the context relative to the searched term;    *)
(* the absolute depth of the returned leaf is K + ctx_depth c.         *)
(* ------------------------------------------------------------------ *)
Fixpoint find_bad (C : typ) (W : atom) (K : nat) {struct C}
  : option (tctx * typ) :=
  match C with
  | typ_top => None
  | typ_nat => None
  | typ_bvar _ => None
  | typ_fvar _ => None
  | typ_arrow A B =>
      match find_bad A W K with
      | Some (c, D) => Some (tc_arrow_l c B, D)
      | None =>
          match find_bad B W K with
          | Some (c, D) => Some (tc_arrow_r A c, D)
          | None => None
          end
      end
  | typ_mu Dbody =>
      if bad_at_dec W K Dbody
      then Some (tc_hole, Dbody)
      else
        match find_bad Dbody W (S K) with
        | Some (c, D) => Some (tc_mu c, D)
        | None => None
        end
  end.

(* ------------------------------------------------------------------ *)
(* Soundness.                                                          *)
(* ------------------------------------------------------------------ *)
Lemma find_bad_sound : forall C W K c D,
  find_bad C W K = Some (c, D) ->
  C = plug c (typ_mu D) /\ bad_at W (K + ctx_depth c) D.
Proof.
  induction C as [| |n|X|Dbody IHD|A IHA B IHB];
    intros W K c D H; simpl in H.
  - discriminate H.
  - discriminate H.
  - discriminate H.
  - discriminate H.
  - (* mu *)
    destruct (bad_at_dec W K Dbody) as [Hb|Hb]; simpl in H.
    + injection H as Hc HD. subst c D.
      split; [reflexivity|]. simpl.
      replace (K + 0) with K by lia. exact Hb.
    + destruct (find_bad Dbody W (S K)) as [[c0 D0]|] eqn:E; simpl in H.
      * injection H as Hc HD. subst c D.
        destruct (IHD W (S K) c0 D0 E) as [HEq Hbad].
        split.
        -- simpl. rewrite HEq. reflexivity.
        -- simpl. replace (K + S (ctx_depth c0)) with (S K + ctx_depth c0) by lia.
           exact Hbad.
      * discriminate H.
  - (* arrow A B *)
    destruct (find_bad A W K) as [[c0 D0]|] eqn:EA; simpl in H.
    + injection H as Hc HD. subst c D.
      destruct (IHA W K c0 D0 EA) as [HEq Hbad].
      split.
      * simpl. rewrite HEq. reflexivity.
      * simpl. exact Hbad.
    + destruct (find_bad B W K) as [[c0 D0]|] eqn:EB; simpl in H.
      * injection H as Hc HD. subst c D.
        destruct (IHB W K c0 D0 EB) as [HEq Hbad].
        split.
        -- simpl. rewrite HEq. reflexivity.
        -- simpl. exact Hbad.
      * discriminate H.
Qed.

(* ------------------------------------------------------------------ *)
(* The frozen predicate: at absolute depth [K] no mu subterm is bad.   *)
(* At a mu node this means exactly: the body is not [bad_at W K] and   *)
(* the body is frozen at depth S K.  Arrows preserve the depth.        *)
(* ------------------------------------------------------------------ *)
Fixpoint frozen_under (C : typ) (W : atom) (K : nat) : Prop :=
  match C with
  | typ_top => True
  | typ_nat => True
  | typ_bvar _ => True
  | typ_fvar _ => True
  | typ_arrow A B => frozen_under A W K /\ frozen_under B W K
  | typ_mu Dbody => ~ bad_at W K Dbody /\ frozen_under Dbody W (S K)
  end.

(* ------------------------------------------------------------------ *)
(* None case: no bad leaf means frozen everywhere.                     *)
(* ------------------------------------------------------------------ *)
Lemma find_bad_none_frozen : forall C W K,
  find_bad C W K = None -> frozen_under C W K.
Proof.
  induction C as [| |n|X|Dbody IHD|A IHA B IHB]; intros W K H; simpl in H.
  - simpl. exact I.
  - simpl. exact I.
  - simpl. exact I.
  - simpl. exact I.
  - (* mu *)
    destruct (bad_at_dec W K Dbody) as [Hb|Hb]; simpl in H.
    + discriminate H.
    + destruct (find_bad Dbody W (S K)) as [[c0 D0]|] eqn:E; simpl in H.
      * discriminate H.
      * simpl. split; [exact Hb|]. apply IHD. exact E.
  - (* arrow *)
    destruct (find_bad A W K) as [[c0 D0]|] eqn:EA; simpl in H.
    + discriminate H.
    + destruct (find_bad B W K) as [[c0 D0]|] eqn:EB; simpl in H.
      * discriminate H.
      * simpl. split.
        -- apply IHA. exact EA.
        -- apply IHB. exact EB.
Qed.

(* ------------------------------------------------------------------ *)
(* Frozen-at-depth interface: every context decomposition of a bad mu  *)
(* is excluded at the corresponding absolute depth.                    *)
(* ------------------------------------------------------------------ *)
Lemma frozen_under_bad_leaf : forall c C W K D,
  frozen_under C W K ->
  C = plug c (typ_mu D) ->
  ~ bad_at W (K + ctx_depth c) D.
Proof.
  induction c as [|c IH B|A c IH|c IH]; intros C W K D Hf HEq; simpl in *.
  - subst C. simpl in Hf. destruct Hf as [Hbad _].
    replace (K + 0) with K by lia. exact Hbad.
  - subst C. simpl in Hf. destruct Hf as [HfA _].
    exact (IH (plug c (typ_mu D)) W K D HfA eq_refl).
  - subst C. simpl in Hf. destruct Hf as [_ HfB].
    exact (IH (plug c (typ_mu D)) W K D HfB eq_refl).
  - subst C. simpl in Hf. destruct Hf as [_ HfD].
    replace (K + S (ctx_depth c)) with (S K + ctx_depth c) by lia.
    exact (IH (plug c (typ_mu D)) W (S K) D HfD eq_refl).
Qed.

(* Combined interface: no bad leaf from the search, and any bad mu      *)
(* subterm reached through a context decomposition is frozen.          *)
Corollary find_bad_none_ctx : forall C W K c D,
  find_bad C W K = None ->
  C = plug c (typ_mu D) ->
  bvoccT true 0 D ->
  ~ (W \in fv_tt D \/
     (exists q, bvoccT q (S (K + ctx_depth c)) D)).
Proof.
  intros C W K c D Hnone HEq Hb.
  pose proof (frozen_under_bad_leaf c C W K D
                (find_bad_none_frozen C W K Hnone) HEq) as Hno.
  intro H. apply Hno. unfold bad_at. split; [exact Hb|exact H].
Qed.

(* The frozen condition the covariance worker uses at top level.       *)
Definition frozen_cov (C : typ) (W : atom) : Prop :=
  forall c D,
    C = plug c (typ_mu D) ->
    bvoccT true 0 D ->
    W \notin fv_tt D /\ (forall q, ~ bvoccT q (S (ctx_depth c)) D).

Corollary find_bad_frozen_cov : forall C W,
  find_bad C W 0 = None -> frozen_cov C W.
Proof.
  intros C W Hnone c D HEq Hb.
  pose proof (frozen_under_bad_leaf c C W 0 D
                (find_bad_none_frozen C W 0 Hnone) HEq) as Hno.
  split.
  - intro HW. apply Hno. unfold bad_at. split; [exact Hb|left; exact HW].
  - intros q Hq. apply Hno. unfold bad_at. split; [exact Hb|right].
    exists q. replace (0 + ctx_depth c) with (ctx_depth c) by lia. exact Hq.
Qed.

(* ------------------------------------------------------------------ *)
(* Assembly plug: the search result feeds bad_leaf_certificate, which  *)
(* feeds the parameterized deep exclusion.                             *)
(* ------------------------------------------------------------------ *)
Corollary find_bad_deep_exclusion :
  forall E C Z W s u (T0 : typ) (par : bool) (c : tctx) (Dbody : typ),
    bindsub_only (Z ~ bind_sub ++ E) ->
    wf_env (Z ~ bind_sub ++ E) ->
    lc_tt s -> lc_tt u -> s <> u -> W <> Z ->
    Z \notin fv_tt C -> W \in fv_tt C ->
    T0 = open_tt C (open_tt C (typ_fvar Z)) ->
    sub (Z ~ bind_sub ++ E) T0 T0 ->
    (if par
     then sub (Z ~ bind_sub ++ E) (subst_tt W u T0) (subst_tt W s T0)
     else sub (Z ~ bind_sub ++ E) (subst_tt W s T0) (subst_tt W u T0)) ->
    sub (Z ~ bind_sub ++ E) s u ->
    find_bad C W 0 = Some (c, Dbody) ->
    False.
Proof.
  intros E C Z W s u T0 par c Dbody Hbs Hwf Hlcs Hlcu Hne HWZ HZC HWC HT0
         Hself Hcomp Hfwd Hfind.
  destruct (find_bad_sound C W 0 c Dbody Hfind) as [HEq Hbad].
  unfold bad_at in Hbad. destruct Hbad as [Hb Hocc].
  assert (Hocc' : W \in fv_tt Dbody \/
                  (exists q, bvoccT q (S (ctx_depth c)) Dbody)).
  { destruct Hocc as [Hf|Ho]; [left; exact Hf|right].
    destruct Ho as [q Hq]. exists q.
    replace (0 + ctx_depth c) with (ctx_depth c) in Hq by lia. exact Hq. }
  destruct (bad_leaf_certificate C Z W c Dbody HEq Hb Hocc' HWC)
    as [p0 [B0 [Hpath [Hb0 HW0]]]].
  rewrite <- HT0 in Hpath.
  exact (deep_equal_mu_excluded_path_par E C Z W s u T0 p0 B0 par
           Hbs Hwf Hlcs Hlcu Hne HWZ HZC HWC HT0 Hself Hcomp Hfwd
           Hpath Hb0 HW0).
Qed.

(* ------------------------------------------------------------------ *)
(* Assumption audit.                                                   *)
(* ------------------------------------------------------------------ *)
Print Assumptions fv_dec.
Print Assumptions bad_at_dec.
Print Assumptions find_bad_sound.
Print Assumptions find_bad_none_frozen.
Print Assumptions frozen_under_bad_leaf.
Print Assumptions find_bad_none_ctx.
Print Assumptions find_bad_frozen_cov.
Print Assumptions find_bad_deep_exclusion.

(* ================================================================== *)
(* REPORT FOR DEEP3                                                    *)
(* ================================================================== *)
(*                                                                     *)
(* File: /tmp/deep/Deep3.v.  Imports TaskBase8, Deep, Deep2 and Lia.   *)
(* No admits, axioms, parameters or other escapes.  Compiles with:     *)
(*   rocq compile -q -R /workspace "" \                                *)
(*     -R /workspace/.rocq-deps/Metalib Metalib -R /tmp/deep "" Deep3.v*)
(* All eight audited constants print "Closed under the global context".*)
(*                                                                     *)
(* DECISIONS.                                                          *)
(*                                                                     *)
(* fv_dec : forall W T, {W in fv_tt T} + {~ W in fv_tt T}, built from  *)
(*   AtomSetImpl.mem and mem_1/mem_2.  outer_occ_sumbool :             *)
(*   {(exists q, bvoccT q K T)} + {~ ...}, built from bvoccT_dec.      *)
(*                                                                     *)
(* bad_at W K D :=                                                     *)
(*   bvoccT true 0 D /\                                                *)
(*   (W in fv_tt D \/ (exists q, bvoccT q (S K) D)).                   *)
(* bad_at_dec : forall W K D, {bad_at W K D} + {~ bad_at W K D}.       *)
(*                                                                     *)
(* SEARCH.                                                             *)
(*                                                                     *)
(* find_bad : typ -> atom -> nat -> option (tctx * typ), structurally  *)
(* recursive on the type.  [K] is the absolute depth, i.e. the number  *)
(* of mu constructors outside the current subterm.                     *)
(*   - top, nat, bvar, fvar: None.                                     *)
(*   - arrow A B: search A at depth K (on success wrap the relative    *)
(*     context with tc_arrow_l c B and return); otherwise search B at *)
(*     depth K (wrap with tc_arrow_r A c).                             *)
(*   - mu Dbody: if bad_at W K Dbody then return Some (tc_hole, Dbody) *)
(*     for this node; otherwise search Dbody at depth S K and, on      *)
(*     success, wrap the relative context with tc_mu c.                *)
(* The returned context is relative to the searched term C, so         *)
(* C = plug c (mu D) holds exactly.                                    *)
(*                                                                     *)
(* find_bad_sound :                                                    *)
(*   forall C W K c D, find_bad C W K = Some (c,D) ->                  *)
(*     C = plug c (typ_mu D) /\ bad_at W (K + ctx_depth c) D.          *)
(*   The occurrence/index carried by bad_at is therefore at            *)
(*   S (K + ctx_depth c).  At the Assembly's intended call K = 0 this  *)
(*   is precisely S (ctx_depth c), the index demanded by                *)
(*   bad_leaf_certificate.                                             *)
(*                                                                     *)
(* NOTE ON THE REQUESTED ctx_depth EQUATION.  The literal statement    *)
(*   find_bad C W K = Some (c,D) -> ctx_depth c = K                    *)
(* cannot hold for an all-depth search: the returned context is        *)
(* relative to C and its depth is the depth of the found leaf inside   *)
(* C, while K is the ambient offset.  Even for K = 0, a leaf five mus  *)
(* below the root has ctx_depth c = 5, not 0.  The correct and         *)
(* strongest form is C = plug c (mu D) with absolute depth             *)
(* K + ctx_depth c; this reduces to ctx_depth c = leaf depth when      *)
(* K = 0.  This is the form proved and used.  If an exact-depth search *)
(* is ever needed, it can be obtained by filtering this result on       *)
(* ctx_depth c = d.                                                    *)
(*                                                                     *)
(* FROZEN PREDICATE.                                                   *)
(*                                                                     *)
(* frozen_under C W K is the recursive conjunction over the type at    *)
(* absolute depth K:                                                   *)
(*   - True at top, nat, bvar, fvar;                                   *)
(*   - at arrow A B: frozen_under A W K /\ frozen_under B W K;         *)
(*   - at mu Dbody: ~ bad_at W K Dbody /\ frozen_under Dbody W (S K).  *)
(*                                                                     *)
(* find_bad_none_frozen : find_bad C W K = None -> frozen_under C W K. *)
(*                                                                     *)
(* frozen_under_bad_leaf : forall c C W K D,                           *)
(*   frozen_under C W K -> C = plug c (typ_mu D) ->                    *)
(*   ~ bad_at W (K + ctx_depth c) D.                                   *)
(*   Proved by induction on the context c, inverting plug and          *)
(*   ctx_depth.  This is the constructive all-contexts completeness     *)
(*   form: every syntactic occurrence of a mu subterm is covered,      *)
(*   without a classical axiom and without an unbounded path search.   *)
(*                                                                     *)
(* find_bad_none_ctx : forall C W K c D,                               *)
(*   find_bad C W K = None -> C = plug c (typ_mu D) ->                 *)
(*   bvoccT true 0 D ->                                                 *)
(*   ~ (W in fv_tt D \/                                                *)
(*      (exists q, bvoccT q (S (K + ctx_depth c)) D)).                 *)
(*                                                                     *)
(* COVARIANCE INTERFACE.                                               *)
(*                                                                     *)
(* frozen_cov C W :=                                                   *)
(*   forall c D, C = plug c (typ_mu D) -> bvoccT true 0 D ->           *)
(*     W notin fv_tt D /\ (forall q, ~ bvoccT q (S (ctx_depth c)) D). *)
(*                                                                     *)
(* find_bad_frozen_cov : find_bad C W 0 = None -> frozen_cov C W.      *)
(*   This is the precise predicate the covariance worker should use:   *)
(*   every bad mu subterm Dbody at depth K = ctx_depth c has a         *)
(*   W-free body and no own-binder-image occurrence bvoccT q (S K)     *)
(*   Dbody for any parity q.  Thus the deep exclusion is not           *)
(*   applicable anywhere and the equal node is handled at the body.    *)
(*                                                                     *)
(* ASSEMBLY PLUG (Some branch).                                        *)
(*                                                                     *)
(* find_bad_deep_exclusion :                                           *)
(*   forall E C Z W s u T0 par c Dbody,                                *)
(*     bindsub_only (Z ~ bind_sub ++ E) ->                             *)
(*     wf_env (Z ~ bind_sub ++ E) ->                                   *)
(*     lc_tt s -> lc_tt u -> s <> u -> W <> Z ->                       *)
(*     Z notin fv_tt C -> W in fv_tt C ->                              *)
(*     T0 = open_tt C (open_tt C (typ_fvar Z)) ->                      *)
(*     sub (Z ~ E) T0 T0 ->                                            *)
(*     (if par then sub (Z ~ E) (subst_tt W u T0)(subst_tt W s T0)     *)
(*             else sub (Z ~ E) (subst_tt W s T0)(subst_tt W u T0)) -> *)
(*     sub (Z ~ E) s u ->                                              *)
(*     find_bad C W 0 = Some (c,Dbody) -> False.                       *)
(*   Proof: find_bad_sound gives C = plug c (mu Dbody), the odd        *)
(*   own-binder occurrence and the occurrence-or-W condition;          *)
(*   bad_leaf_certificate (Deep2) turns this into at_path p0 T0        *)
(*   (mu B0) with bvoccT true 0 B0 and W in fv B0; then                *)
(*   deep_equal_mu_excluded_path_par (Deep2) with the given [par]      *)
(*   yields False.  This is exactly the call site the Assembly can     *)
(*   use for the equal-body node.                                      *)
(*                                                                     *)
(* RESIDUAL.  None for the search/dichotomy itself: the search is a    *)
(* total computable function, soundness and the None-to-frozen          *)
(* direction are proved for it, and the frozen-to-covariance           *)
(* interface covers every context decomposition constructively.  The   *)
(* Assembly still has to provide the side conditions of                 *)
(* find_bad_deep_exclusion (the environment, lc, s <> u, freshness of  *)
(* W and Z, the self and companion derivations, and the forward sub)   *)
(* and then branch on find_bad C W 0.  In the Some branch it is        *)
(* closed; in the None branch frozen_cov C W is available for the      *)
(* covariance argument.  Both branches use only constructive logic,    *)
(* so all audits remain Closed.                                        *)
(* ================================================================== *)


Lemma polar_ok_eq_sideB : forall flag m, polar_ok flag m -> m = sideB flag.
Proof. intros flag m H. destruct flag, m; simpl in *; congruence. Qed.

Lemma open_tt_fvar_top_inv : forall A X, open_tt A (typ_fvar X) = typ_top -> A = typ_top.
Proof.
  intros A. induction A as [| |n|Y|A0 IHA|A1 IH1 A2 IH2]; intros X H; simpl in *.
  - reflexivity.
  - discriminate.
  - unfold open_tt in H. simpl in H. destruct (0 === n); discriminate.
  - discriminate.
  - discriminate.
  - discriminate.
Qed.

Theorem amber_complete: forall  A B,
    sub nil A B ->
    sub_amber nil (amber_cov nil nil A Neg) (amber_cov nil nil B Pos) .
