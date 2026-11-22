Require Import Syntax Algo.
Require Import Coq.Arith.Compare_dec.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.micromega.Lia.
Require Import Coq.Lists.List.

(* ============================================================ *)
(*                 Basic arithmetic / shift facts               *)
(* ============================================================ *)

Lemma punchIn_ge : forall k X, k <= X -> punchIn k X = S X.
Proof.
  intros k X H. unfold punchIn. apply Nat.leb_le in H. rewrite H. reflexivity.
Qed.

Lemma punchIn_lt : forall k X, X < k -> punchIn k X = X.
Proof.
  intros k X H. unfold punchIn.
  assert (Hf : (k <=? X) = false) by (apply Nat.leb_gt; lia).
  rewrite Hf. reflexivity.
Qed.

(* ============================================================ *)
(*                     Structural type equality                 *)
(* ============================================================ *)

Fixpoint typ_eqb (A B : Typ) : bool :=
  match A with
  | Int => match B with Int => true | _ => false end
  | TVar x => match B with TVar y => x =? y | _ => false end
  | Arr A1 A2 =>
      match B with Arr B1 B2 => andb (typ_eqb A1 B1) (typ_eqb A2 B2) | _ => false end
  | All A1 =>
      match B with All B1 => typ_eqb A1 B1 | _ => false end
  end.

Lemma typ_eqb_eq : forall A B, typ_eqb A B = true <-> A = B.
Proof.
  induction A; destruct B; simpl; try (split; discriminate).
  - split; intros; reflexivity.
  - split; intro H.
    + apply Nat.eqb_eq in H. subst. reflexivity.
    + inversion H. subst. apply Nat.eqb_eq. reflexivity.
  - rewrite Bool.andb_true_iff. rewrite IHA1. rewrite IHA2. split.
    + intros [H1 H2]. subst. reflexivity.
    + intros H. inversion H. subst. auto.
  - rewrite IHA. split.
    + intros H. subst. reflexivity.
    + intros H. inversion H. subst. auto.
Qed.

Lemma typ_eqb_refl : forall A, typ_eqb A A = true.
Proof. intro A. apply typ_eqb_eq. reflexivity. Qed.

Lemma typ_eqb_neq : forall A B, typ_eqb A B = false -> A <> B.
Proof. intros A B H E. subst. rewrite typ_eqb_refl in H. discriminate. Qed.

(* ============================================================ *)
(*                 Inverse of ty_shift (partial)                *)
(* ============================================================ *)

Fixpoint ty_unshift (A : Typ) (k : nat) : option Typ :=
  match A with
  | Int => Some Int
  | TVar Y =>
      if Y <? k then Some (TVar Y)
      else if Y =? k then None
      else Some (TVar (Y - 1))
  | Arr A1 A2 =>
      match ty_unshift A1 k with
      | Some A1' =>
          match ty_unshift A2 k with
          | Some A2' => Some (Arr A1' A2')
          | None => None
          end
      | None => None
      end
  | All A1 =>
      match ty_unshift A1 (S k) with
      | Some A1' => Some (All A1')
      | None => None
      end
  end.

Lemma ty_unshift_shift : forall A k, ty_unshift (ty_shift A k) k = Some A.
Proof.
  induction A; intro k; simpl.
  - reflexivity.
  - unfold punchIn.
    destruct (k <=? n) eqn:E.
    + apply Nat.leb_le in E.
      cbn [ty_unshift].
      replace (S n <? k) with false by (symmetry; apply Nat.ltb_ge; lia).
      replace (S n =? k) with false by (symmetry; apply Nat.eqb_neq; lia).
      replace (S n - 1) with n by lia.
      reflexivity.
    + apply Nat.leb_gt in E.
      cbn [ty_unshift].
      replace (n <? k) with true by (symmetry; apply Nat.ltb_lt; lia).
      reflexivity.
  - simpl. rewrite IHA1, IHA2. reflexivity.
  - simpl. rewrite IHA. reflexivity.
Qed.

Lemma ty_shift_unshift : forall B k A, ty_unshift B k = Some A -> ty_shift A k = B.
Proof.
  induction B; intros k A H; simpl in H.
  - inversion H. subst. reflexivity.
  - destruct (n <? k) eqn:E1.
    + apply Nat.ltb_lt in E1. inversion H. subst. simpl. rewrite punchIn_lt by lia. reflexivity.
    + apply Nat.ltb_ge in E1.
      destruct (n =? k) eqn:E2.
      * discriminate.
      * apply Nat.eqb_neq in E2. inversion H. subst. simpl. rewrite punchIn_ge by lia.
        replace (S (n - 1)) with n by lia. reflexivity.
  - destruct (ty_unshift B1 k) as [A1'|] eqn:E1; try discriminate.
    destruct (ty_unshift B2 k) as [A2'|] eqn:E2; try discriminate.
    inversion H. subst.
    simpl. rewrite (IHB1 k A1' E1). rewrite (IHB2 k A2' E2). reflexivity.
  - destruct (ty_unshift B (S k)) as [A1'|] eqn:E1; try discriminate.
    inversion H. subst. simpl. rewrite (IHB (S k) A1' E1). reflexivity.
Qed.

Lemma ty_unshift_none : forall B k, ty_unshift B k = None ->
  forall A, ty_shift A k <> B.
Proof.
  intros B k H A E. rewrite <- E in H. rewrite ty_unshift_shift in H. discriminate.
Qed.

(* ============================================================ *)
(*                     Environment lookups                      *)
(* ============================================================ *)

Fixpoint lookupTyD (D : Env) (x : nat) : bool :=
  match D with
  | EnvEmpty => false
  | TmCons G _ => lookupTyD G x
  | ExCons G => match x with 0 => false | S x' => lookupTyD G x' end
  | TyCons G => match x with 0 => true | S x' => lookupTyD G x' end
  | ExTyCons G _ => match x with 0 => false | S x' => lookupTyD G x' end
  | SepCons G => lookupTyD G x
  end.

Lemma lookupTyD_sound : forall D x, lookupTyD D x = true -> lookupTy D x.
Proof.
  induction D as [| G IHG A | G IHG | G IHG | G IHG A | G IHG];
    intros x H; simpl in H.
  - discriminate.
  - apply l_ty_STm. apply IHG. exact H.
  - destruct x.
    + discriminate.
    + simpl in H. apply l_ty_SEx. apply IHG. exact H.
  - destruct x.
    + apply l_ty_Z.
    + simpl in H. apply l_ty_STy. apply IHG. exact H.
  - destruct x.
    + discriminate.
    + simpl in H. apply l_ty_SExTy. apply IHG. exact H.
  - apply l_ty_SSep. apply IHG. exact H.
Qed.

Lemma lookupTyD_complete : forall D x, lookupTy D x -> lookupTyD D x = true.
Proof.
  intros D x H. induction H; simpl; try reflexivity; assumption.
Qed.

Fixpoint lookupExD (D : Env) (x : nat) : bool :=
  match D with
  | EnvEmpty => false
  | TmCons G _ => lookupExD G x
  | ExCons G => match x with 0 => true | S x' => lookupExD G x' end
  | TyCons G => match x with 0 => false | S x' => lookupExD G x' end
  | ExTyCons G _ => match x with 0 => false | S x' => lookupExD G x' end
  | SepCons G => lookupExD G x
  end.

Lemma lookupExD_sound : forall D x, lookupExD D x = true -> lookupEx D x.
Proof.
  induction D as [| G IHG A | G IHG | G IHG | G IHG A | G IHG];
    intros x H; simpl in H.
  - discriminate.
  - apply l_ex_STm. apply IHG. exact H.
  - destruct x.
    + apply l_ex_Z.
    + simpl in H. apply l_ex_SEx. apply IHG. exact H.
  - destruct x.
    + discriminate.
    + simpl in H. apply l_ex_STy. apply IHG. exact H.
  - destruct x.
    + discriminate.
    + simpl in H. apply l_ex_SExTy. apply IHG. exact H.
  - apply l_ex_SSep. apply IHG. exact H.
Qed.

Lemma lookupExD_complete : forall D x, lookupEx D x -> lookupExD D x = true.
Proof.
  intros D x H. induction H; simpl.
  - reflexivity.
  - assumption.
  - assumption.
  - assumption.
  - assumption.
  - assumption.
Qed.

Fixpoint lookupExTy'D (D : Env) (x : nat) : bool :=
  match D with
  | EnvEmpty => false
  | TmCons G _ => lookupExTy'D G x
  | ExCons G => match x with 0 => false | S x' => lookupExTy'D G x' end
  | TyCons G => match x with 0 => false | S x' => lookupExTy'D G x' end
  | ExTyCons G _ => match x with 0 => true | S x' => lookupExTy'D G x' end
  | SepCons _ => false
  end.

Lemma lookupExTy'D_sound : forall D x, lookupExTy'D D x = true -> lookupExTy' D x.
Proof.
  induction D as [| G IHG A | G IHG | G IHG | G IHG A | G IHG];
    intros x H; simpl in H.
  - discriminate.
  - apply l_exty'_STm. apply IHG. exact H.
  - destruct x.
    + discriminate.
    + simpl in H. apply l_exty'_STEx. apply IHG. exact H.
  - destruct x.
    + discriminate.
    + simpl in H. apply l_exty'_STy. apply IHG. exact H.
  - destruct x.
    + apply l_exty'_Z.
    + simpl in H. apply l_exty'_STExTy. apply IHG. exact H.
  - discriminate.
Qed.

Lemma lookupExTy'D_complete : forall D x, lookupExTy' D x -> lookupExTy'D D x = true.
Proof.
  intros D x H. induction H; simpl.
  - reflexivity.
  - assumption.
  - assumption.
  - assumption.
  - assumption.
Qed.

Fixpoint lookupTmD (D : Env) (x : nat) : option Typ :=
  match D with
  | EnvEmpty => None
  | TmCons G A => match x with 0 => Some A | S x' => lookupTmD G x' end
  | ExCons G => match lookupTmD G x with Some A => Some (ty_shift A 0) | None => None end
  | TyCons G => match lookupTmD G x with Some A => Some (ty_shift A 0) | None => None end
  | ExTyCons G _ => match lookupTmD G x with Some A => Some (ty_shift A 0) | None => None end
  | SepCons _ => None
  end.

Lemma lookupTmD_sound : forall D x A, lookupTmD D x = Some A -> lookupTm D x A.
Proof.
  induction D as [| G IHG B | G IHG | G IHG | G IHG B | G IHG];
    intros x A H; simpl in H.
  - discriminate.
  - destruct x.
    + inversion H. subst. apply l_tm_Z.
    + apply l_tm_STm. apply IHG. exact H.
  - destruct (lookupTmD G x) as [C|] eqn:E; try discriminate.
    inversion H. subst. apply l_tm_SEx. apply IHG. exact E.
  - destruct (lookupTmD G x) as [C|] eqn:E; try discriminate.
    inversion H. subst. apply l_tm_STy. apply IHG. exact E.
  - destruct (lookupTmD G x) as [C|] eqn:E; try discriminate.
    inversion H. subst. apply l_tm_SExTy. apply IHG. exact E.
  - discriminate.
Qed.

Lemma lookupTmD_complete : forall D x A, lookupTm D x A -> lookupTmD D x = Some A.
Proof.
  intros D x A H. induction H; simpl.
  - reflexivity.
  - assumption.
  - rewrite IHlookupTm. reflexivity.
  - rewrite IHlookupTm. reflexivity.
  - rewrite IHlookupTm. reflexivity.
Qed.

Fixpoint lookupExTyD (D : Env) (x : nat) : option Typ :=
  match D with
  | EnvEmpty => None
  | TmCons G _ => lookupExTyD G x
  | ExCons G =>
      match x with 0 => None
      | S x' => match lookupExTyD G x' with Some A => Some (ty_shift A 0) | None => None end end
  | TyCons G =>
      match x with 0 => None
      | S x' => match lookupExTyD G x' with Some A => Some (ty_shift A 0) | None => None end end
  | ExTyCons G B =>
      match x with 0 => Some (ty_shift B 0)
      | S x' => match lookupExTyD G x' with Some A => Some (ty_shift A 0) | None => None end end
  | SepCons _ => None
  end.

Lemma lookupExTyD_sound : forall D x A, lookupExTyD D x = Some A -> lookupExTy D x A.
Proof.
  induction D as [| G IHG A | G IHG | G IHG | G IHG A | G IHG];
    intros x A0 H; simpl in H.
  - discriminate.
  - apply l_exty_STm. apply IHG. exact H.
  - destruct x.
    + discriminate.
    + simpl in H. destruct (lookupExTyD G x) as [C|] eqn:E; try discriminate.
      inversion H. subst. apply l_exty_SEx. apply IHG. exact E.
  - destruct x.
    + discriminate.
    + simpl in H. destruct (lookupExTyD G x) as [C|] eqn:E; try discriminate.
      inversion H. subst. apply l_exty_STy. apply IHG. exact E.
  - destruct x.
    + inversion H. subst. apply l_exty_Z.
    + simpl in H. destruct (lookupExTyD G x) as [C|] eqn:E; try discriminate.
      inversion H. subst. apply l_exty_SExTy. apply IHG. exact E.
  - discriminate.
Qed.

Lemma lookupExTyD_complete : forall D x A, lookupExTy D x A -> lookupExTyD D x = Some A.
Proof.
  intros D x A H. induction H; simpl.
  - reflexivity.
  - rewrite IHlookupExTy. reflexivity.
  - rewrite IHlookupExTy. reflexivity.
  - rewrite IHlookupExTy. reflexivity.
  - assumption.
Qed.

(* ============================================================ *)
(*                Regularity deciders                           *)
(* ============================================================ *)

Fixpoint RegularTypD (G : Env) (A : Typ) : bool :=
  match A with
  | Int => true
  | TVar n => lookupTyD G n
  | Arr A1 A2 => andb (RegularTypD G A1) (RegularTypD G A2)
  | All A1 => RegularTypD (TyCons G) A1
  end.

Lemma RegularTypD_sound : forall A G, RegularTypD G A = true -> RegularTyp G A.
Proof.
  induction A; intros G H; simpl in H.
  - apply r_int.
  - apply r_var. apply lookupTyD_sound. exact H.
  - apply Bool.andb_true_iff in H. destruct H. apply r_arr.
    + apply IHA1. exact H.
    + apply IHA2. exact H0.
  - apply r_all. apply IHA. exact H.
Qed.

Lemma RegularTypD_complete : forall G A, RegularTyp G A -> RegularTypD G A = true.
Proof.
  intros G A H. induction H; simpl.
  - reflexivity.
  - apply lookupTyD_complete. exact H.
  - apply Bool.andb_true_iff. split; assumption.
  - assumption.
Qed.

Fixpoint TRegularD (G : Env) : bool :=
  match G with
  | EnvEmpty => true
  | TmCons G' A => andb (TRegularD G') (RegularTypD G' A)
  | ExCons G' => TRegularD G'
  | TyCons G' => TRegularD G'
  | ExTyCons G' A => andb (TRegularD G') (RegularTypD G' A)
  | SepCons _ => false
  end.

Lemma TRegularD_sound : forall G, TRegularD G = true -> TRegular G.
Proof.
  induction G as [| G IHG A | G IHG | G IHG | G IHG A | G IHG]; simpl; intro H.
  - apply treg_Z.
  - apply Bool.andb_true_iff in H. destruct H. apply treg_STm.
    + apply IHG. exact H.
    + apply RegularTypD_sound. exact H0.
  - apply treg_SEx. apply IHG. exact H.
  - apply treg_STy. apply IHG. exact H.
  - apply Bool.andb_true_iff in H. destruct H. apply treg_SExTy.
    + apply IHG. exact H.
    + apply RegularTypD_sound. exact H0.
  - discriminate.
Qed.

Lemma TRegularD_complete : forall G, TRegular G -> TRegularD G = true.
Proof.
  intros G H. induction H; simpl.
  - reflexivity.
  - apply Bool.andb_true_iff. split.
    + exact IHTRegular.
    + apply RegularTypD_complete. exact H0.
  - exact IHTRegular.
  - exact IHTRegular.
  - apply Bool.andb_true_iff. split.
    + exact IHTRegular.
    + apply RegularTypD_complete. exact H0.
Qed.

Fixpoint SRegularD (D : Env) : bool :=
  match D with
  | EnvEmpty => false
  | TmCons G _ => false
  | ExCons G => SRegularD G
  | TyCons G => SRegularD G
  | ExTyCons G A => andb (SRegularD G) (RegularTypD G A)
  | SepCons G => TRegularD G
  end.

Lemma SRegularD_sound : forall D, SRegularD D = true -> SRegular D.
Proof.
  induction D as [| G A | G IHG | G IHG | G IHG A | G IHG]; simpl; intro H.
  - discriminate.
  - discriminate.
  - apply sreg_SEx. apply IHG. exact H.
  - apply sreg_STy. apply IHG. exact H.
  - apply Bool.andb_true_iff in H. destruct H. apply sreg_SExTy.
    + apply IHG. exact H.
    + apply RegularTypD_sound. exact H0.
  - apply sreg_Z. apply TRegularD_sound. exact H.
Qed.

Lemma SRegularD_complete : forall D, SRegular D -> SRegularD D = true.
Proof.
  intros D H. induction H; simpl.
  - apply TRegularD_complete. exact H.
  - exact IHSRegular.
  - exact IHSRegular.
  - apply Bool.andb_true_iff. split.
    + exact IHSRegular.
    + apply RegularTypD_complete. exact H0.
Qed.

(* ============================================================ *)
(*                substEnv decider                              *)
(* ============================================================ *)

Fixpoint substEnvD (A : Typ) (k : nat) (D : Env) {struct D} : option Env :=
  match D with
  | EnvEmpty => None
  | TmCons _ _ => None
  | ExCons G =>
      match k with
      | 0 =>
          match ty_unshift A 0 with
          | Some A0 =>
              if andb (SRegularD G) (RegularTypD G A0)
              then Some (ExTyCons G A0) else None
          | None => None
          end
      | S k' =>
          match ty_unshift A 0 with
          | Some A0 =>
              match substEnvD A0 k' G with
              | Some G' => Some (ExCons G')
              | None => None
              end
          | None => None
          end
      end
  | TyCons G =>
      match k with
      | 0 => None
      | S k' =>
          match ty_unshift A 0 with
          | Some A0 =>
              match substEnvD A0 k' G with
              | Some G' => Some (TyCons G')
              | None => None
              end
          | None => None
          end
      end
  | ExTyCons G B =>
      match k with
      | 0 => None
      | S k' =>
          if RegularTypD G B then
            match ty_unshift A 0 with
            | Some A0 =>
                match substEnvD A0 k' G with
                | Some G' => Some (ExTyCons G' B)
                | None => None
                end
            | None => None
            end
          else None
      end
  | SepCons _ => None
  end.

Lemma substEnvD_sound : forall A k D Psi, substEnvD A k D = Some Psi -> substEnv A k D Psi.
Proof.
  intros A k D Psi H. revert H. revert Psi. revert k. revert A.
  induction D as [| G IHG B | G IHG | G IHG | G IHG B | G IHG];
    intros A k Psi H; simpl in H.
  - inversion H.
  - inversion H.
  - (* ExCons *) destruct k as [| k'].
    + simpl in H.
      destruct (ty_unshift A 0) as [A0|] eqn:E; simpl in H.
      * destruct (andb (SRegularD G) (RegularTypD G A0)) eqn:Eb; simpl in H.
        -- apply Bool.andb_true_iff in Eb. destruct Eb.
           inversion H. subst.
           apply se_ExZ with (A := A0) (A' := A).
           ++ symmetry. apply ty_shift_unshift. exact E.
           ++ apply RegularTypD_sound. exact H1.
           ++ apply SRegularD_sound. exact H0.
        -- inversion H.
      * inversion H.
    + simpl in H.
      destruct (ty_unshift A 0) as [A0|] eqn:E; simpl in H.
      * destruct (substEnvD A0 k' G) as [G'|] eqn:E2; simpl in H.
        -- inversion H. subst. apply se_ExS with (A := A0) (k := k').
           ++ apply IHG. exact E2.
           ++ symmetry. apply ty_shift_unshift. exact E.
        -- inversion H.
      * inversion H.
  - (* TyCons *) destruct k as [| k'].
    + simpl in H. inversion H.
    + simpl in H.
      destruct (ty_unshift A 0) as [A0|] eqn:E; simpl in H.
      * destruct (substEnvD A0 k' G) as [G'|] eqn:E2; simpl in H.
        -- inversion H. subst. apply se_TyS with (A := A0) (k := k').
           ++ apply IHG. exact E2.
           ++ symmetry. apply ty_shift_unshift. exact E.
        -- inversion H.
      * inversion H.
  - (* ExTyCons *) destruct k as [| k'].
    + simpl in H. inversion H.
    + simpl in H.
      destruct (RegularTypD G B) eqn:Er; simpl in H.
      * destruct (ty_unshift A 0) as [A0|] eqn:E; simpl in H.
        -- destruct (substEnvD A0 k' G) as [G'|] eqn:E2; simpl in H.
           ++ inversion H. subst. apply se_ExTyS with (A := A0) (k := k') (B := B).
              ** apply IHG. exact E2.
              ** symmetry. apply ty_shift_unshift. exact E.
              ** apply RegularTypD_sound. exact Er.
           ++ inversion H.
        -- inversion H.
      * inversion H.
  - inversion H.
Qed.

Lemma substEnvD_complete : forall A k D Psi, substEnv A k D Psi -> substEnvD A k D = Some Psi.
Proof.
  intros A k D Psi H. induction H.
  - (* se_ExZ *) simpl. destruct (ty_unshift A' 0) as [A0|] eqn:E.
    + assert (A0 = A) as HA.
      { rewrite H in E. rewrite ty_unshift_shift in E. injection E as ->. reflexivity. }
      subst A0. rewrite (SRegularD_complete Γ H1). rewrite (RegularTypD_complete Γ A H0). reflexivity.
    + rewrite H in E. rewrite ty_unshift_shift in E. discriminate.
  - (* se_ExS *) simpl. destruct (ty_unshift A' 0) as [A0|] eqn:E.
    + assert (A0 = A) as HA.
      { rewrite H0 in E. rewrite ty_unshift_shift in E. injection E as ->. reflexivity. }
      subst A0. rewrite IHsubstEnv. reflexivity.
    + rewrite H0 in E. rewrite ty_unshift_shift in E. discriminate.
  - (* se_TyS *) simpl. destruct (ty_unshift A' 0) as [A0|] eqn:E.
    + assert (A0 = A) as HA.
      { rewrite H0 in E. rewrite ty_unshift_shift in E. injection E as ->. reflexivity. }
      subst A0. rewrite IHsubstEnv. reflexivity.
    + rewrite H0 in E. rewrite ty_unshift_shift in E. discriminate.
  - (* se_ExTyS *) simpl. rewrite (RegularTypD_complete Γ B H1).
    destruct (ty_unshift A' 0) as [A0|] eqn:E.
    + assert (A0 = A) as HA.
      { rewrite H0 in E. rewrite ty_unshift_shift in E. injection E as ->. reflexivity. }
      subst A0. rewrite IHsubstEnv. reflexivity.
    + rewrite H0 in E. rewrite ty_unshift_shift in E. discriminate.
Qed.

(* ============================================================ *)
(*                  open / close / grd_typ                      *)
(* ============================================================ *)

Fixpoint openD (D : Env) (A : Typ) : bool :=
  match A with
  | Int => false
  | TVar x => lookupExD D x
  | Arr A1 A2 => orb (openD D A1) (openD D A2)
  | All A1 => openD (TyCons D) A1
  end.

Lemma openD_sound : forall A D, openD D A = true -> open D A.
Proof.
  induction A; intros D H; simpl in H.
  - discriminate.
  - apply o_var_ex. apply lookupExD_sound. exact H.
  - apply Bool.orb_true_iff in H. destruct H.
    + apply o_arr_l. apply IHA1. exact H.
    + apply o_arr_r. apply IHA2. exact H.
  - apply o_all. apply IHA. exact H.
Qed.

Lemma openD_complete : forall D A, open D A -> openD D A = true.
Proof.
  intros D A H. induction H; simpl.
  - apply lookupExD_complete. exact H.
  - apply Bool.orb_true_iff. left. exact IHopen.
  - apply Bool.orb_true_iff. right. exact IHopen.
  - exact IHopen.
Qed.

Fixpoint closeD (D : Env) (A : Typ) : bool :=
  match A with
  | Int => true
  | TVar x => orb (lookupTyD D x) (lookupExTy'D D x)
  | Arr A1 A2 => andb (closeD D A1) (closeD D A2)
  | All A1 => closeD (TyCons D) A1
  end.

Lemma closeD_sound : forall A D, closeD D A = true -> close D A.
Proof.
  induction A; intros D H; simpl in H.
  - apply c_int.
  - apply Bool.orb_true_iff in H. destruct H.
    + apply c_var_ty. apply lookupTyD_sound. exact H.
    + apply c_var_exty. apply lookupExTy'D_sound. exact H.
  - apply Bool.andb_true_iff in H. destruct H. apply c_arr.
    + apply IHA1. exact H.
    + apply IHA2. exact H0.
  - apply c_all. apply IHA. exact H.
Qed.

Lemma closeD_complete : forall D A, close D A -> closeD D A = true.
Proof.
  intros D A H. induction H; simpl.
  - reflexivity.
  - apply Bool.orb_true_iff. left. apply lookupTyD_complete. exact H.
  - apply Bool.orb_true_iff. right. apply lookupExTy'D_complete. exact H.
  - apply Bool.andb_true_iff. split; assumption.
  - exact IHclose.
Qed.

Fixpoint grdTypD (D : Env) (A : Typ) : option Typ :=
  match A with
  | Int => Some Int
  | TVar x =>
      match lookupExTyD D x with
      | Some A' => Some A'
      | None => if lookupTyD D x then Some (TVar x) else None
      end
  | Arr A1 A2 =>
      match grdTypD D A1 with
      | Some A1' =>
          match grdTypD D A2 with
          | Some A2' => Some (Arr A1' A2')
          | None => None
          end
      | None => None
      end
  | All A1 =>
      match grdTypD (TyCons D) A1 with
      | Some A1' => Some (All A1')
      | None => None
      end
  end.

Lemma grdTypD_sound : forall A D A', grdTypD D A = Some A' -> grd_typ D A A'.
Proof.
  induction A as [| n | A1 IHA1 A2 IHA2 | A1 IHA]; intros D A0 H; simpl in H.
  - inversion H. subst. apply grd_int.
  - destruct (lookupExTyD D n) as [B|] eqn:E; simpl in H.
    + inversion H. subst. apply grd_var_exty. apply lookupExTyD_sound. exact E.
    + destruct (lookupTyD D n) eqn:E2; simpl in H.
      * inversion H. subst. apply grd_var_ty. apply lookupTyD_sound. exact E2.
      * discriminate.
  - destruct (grdTypD D A1) as [B1|] eqn:E1; simpl in H.
    + destruct (grdTypD D A2) as [B2|] eqn:E2; simpl in H.
      * inversion H. subst. apply grd_arr.
        -- apply IHA1. exact E1.
        -- apply IHA2. exact E2.
      * discriminate.
    + discriminate.
  - destruct (grdTypD (TyCons D) A1) as [B|] eqn:E; simpl in H.
    + inversion H. subst. apply grd_all. apply IHA. exact E.
    + discriminate.
Qed.

Lemma grdTypD_complete : forall D A A', grd_typ D A A' -> exists B, grdTypD D A = Some B.
Proof.
  intros D A A' H. induction H; simpl.
  - exists Int. reflexivity.
  - destruct (lookupExTyD Δ x) as [B|] eqn:E.
    + exists B. reflexivity.
    + rewrite (lookupExTyD_complete Δ x A H) in E. discriminate.
  - destruct (lookupExTyD Δ x) as [B|] eqn:E.
    + exists B. reflexivity.
    + rewrite (lookupTyD_complete Δ x H). exists (TVar x). reflexivity.
  - destruct IHgrd_typ1 as [B1 E1]. destruct IHgrd_typ2 as [B2 E2].
    rewrite E1. rewrite E2. exists (Arr B1 B2). reflexivity.
  - destruct IHgrd_typ as [B E]. rewrite E. exists (All B). reflexivity.
Qed.

(* ============================================================ *)
(*                     sub : all results                        *)
(* ============================================================ *)

Fixpoint tsize (A : Typ) : nat :=
  match A with
  | Int => 1
  | TVar _ => 1
  | Arr A1 A2 => S (tsize A1 + tsize A2)
  | All A1 => S (tsize A1)
  end.

Fixpoint subAll (n : nat) (D : Env) (A : Typ) (p : Polar) (B : Typ) {struct n} : list Env :=
  match n with
  | 0 => nil
  | S n' =>
      app
        (match A with
         | Int =>
             match B with
             | Int => if SRegularD D then (D :: nil) else nil
             | _ => nil
             end
         | TVar x =>
             match B with
             | TVar y =>
                 if andb (x =? y) (andb (SRegularD D) (lookupTyD D x))
                 then (D :: nil) else nil
             | _ => nil
             end
         | Arr A1 A2 =>
             match B with
             | Arr C D2 => flat_map (fun om => subAll n' om A2 p D2)
                                    (subAll n' D C (neg p) A1)
             | _ => nil
             end
         | All A1 =>
             match B with
             | All B1 =>
                 flat_map
                   (fun Psi' => match Psi' with TyCons Psi => (Psi :: nil) | _ => nil end)
                   (subAll n' (TyCons D) A1 p B1)
             | _ => nil
             end
         end)
        (match p with
         | Pos =>
             match A with
             | TVar x =>
                 app
                   (match substEnvD B x D with Some Psi => (Psi :: nil) | None => nil end)
                   (if SRegularD D then
                      match lookupExTyD D x with
                      | Some A' => if typ_eqb A' B then (D :: nil) else nil
                      | None => nil
                      end
                    else nil)
             | _ => nil
             end
         | Neg =>
             match B with
             | TVar y =>
                 app
                   (match substEnvD A y D with Some Psi => (Psi :: nil) | None => nil end)
                   (if SRegularD D then
                      match lookupExTyD D y with
                      | Some A' => if typ_eqb A' A then (D :: nil) else nil
                      | None => nil
                      end
                    else nil)
             | _ => nil
             end
         end)
  end.

Lemma eq_or_false : forall (A : Type) (x y : A), (x = y \/ False) -> x = y.
Proof. intros A x y [H|H]; [exact H | destruct H]. Qed.

Ltac cleanup Hin :=
  first [ exfalso; exact Hin
        | apply eq_or_false in Hin; subst ].

Lemma subAll_sound : forall n D A p B Psi, In Psi (subAll n D A p B) -> sub D A p B Psi.
Proof.
  induction n; intros D A p B Psi Hin.
  - simpl in Hin. inversion Hin.
  - simpl in Hin. apply in_app_or in Hin. destruct Hin as [Hin | Hin].
    + (* structural branch *)
      destruct A as [| x | A1 A2 | A1]; simpl in Hin.
      * (* Int *)
        destruct B as [| y | C D2 | B1]; simpl in Hin.
        { destruct (SRegularD D) eqn:E; simpl in Hin.
          { apply eq_or_false in Hin. subst. apply s_int. apply SRegularD_sound. exact E. }
          { cleanup Hin. } }
        { cleanup Hin. }
        { cleanup Hin. }
        { cleanup Hin. }
      * (* TVar *)
        destruct B as [| y | C D2 | B1]; simpl in Hin.
        { cleanup Hin. }
        { destruct (x =? y) eqn:Ex; simpl in Hin.
          { destruct (andb (SRegularD D) (lookupTyD D x)) eqn:Eb; simpl in Hin.
            { apply Bool.andb_true_iff in Eb. destruct Eb.
              apply eq_or_false in Hin. subst. apply Nat.eqb_eq in Ex. subst y. apply s_var_ty.
              - apply SRegularD_sound. exact H.
              - apply lookupTyD_sound. exact H0. }
            { cleanup Hin. } }
          { cleanup Hin. } }
        { cleanup Hin. }
        { cleanup Hin. }
      * (* Arr *)
        destruct B as [| y | C D2 | B1]; simpl in Hin.
        { cleanup Hin. }
        { cleanup Hin. }
        { apply in_flat_map in Hin. destruct Hin as [om [Hin1 Hin2]].
          apply s_arr with (C := C) (D := D2) (Ω := om).
          - apply IHn. exact Hin1.
          - apply IHn. exact Hin2. }
        { cleanup Hin. }
      * (* All *)
        destruct B as [| y | C D2 | B1]; simpl in Hin.
        { cleanup Hin. }
        { cleanup Hin. }
        { cleanup Hin. }
        { apply in_flat_map in Hin. destruct Hin as [Psi' [Hin1 Hinf]].
          destruct Psi' as [| G A' | G | G | G A' | G]; simpl in Hinf.
          { cleanup Hinf. }
          { cleanup Hinf. }
          { cleanup Hinf. }
          { apply eq_or_false in Hinf. subst. apply s_all. apply IHn. exact Hin1. }
          { cleanup Hinf. }
          { cleanup Hinf. } }
    + (* variable-based branch *)
      destruct p; simpl in Hin.
      * (* Pos *)
        destruct A as [| x | A1 A2 | A1]; simpl in Hin.
        { cleanup Hin. }
        { apply in_app_or in Hin. destruct Hin as [Hin | Hin].
          - destruct (substEnvD B x D) as [Psi'|] eqn:E.
            { apply eq_or_false in Hin. subst. apply s_ex_l with (A := B) (x := x).
              apply substEnvD_sound. exact E. }
            { cleanup Hin. }
          - destruct (SRegularD D) eqn:E2; simpl in Hin.
            { destruct (lookupExTyD D x) as [A'|] eqn:E3; simpl in Hin.
              { destruct (typ_eqb A' B) eqn:E4; simpl in Hin.
                { apply eq_or_false in Hin. subst. apply typ_eqb_eq in E4. subst B.
                  apply s_exty_l with (x := x).
                  - apply SRegularD_sound. exact E2.
                  - apply lookupExTyD_sound. exact E3. }
                { cleanup Hin. } }
              { cleanup Hin. } }
            { cleanup Hin. } }
        { cleanup Hin. }
        { cleanup Hin. }
      * (* Neg *)
        destruct B as [| y | C D2 | B1]; simpl in Hin.
        { cleanup Hin. }
        { apply in_app_or in Hin. destruct Hin as [Hin | Hin].
          - destruct (substEnvD A y D) as [Psi'|] eqn:E.
            { apply eq_or_false in Hin. subst. apply s_ex_r with (A := A) (x := y).
              apply substEnvD_sound. exact E. }
            { cleanup Hin. }
          - destruct (SRegularD D) eqn:E2; simpl in Hin.
            { destruct (lookupExTyD D y) as [A'|] eqn:E3; simpl in Hin.
              { destruct (typ_eqb A' A) eqn:E4; simpl in Hin.
                { apply eq_or_false in Hin. subst. apply typ_eqb_eq in E4. subst A.
                  apply s_exty_r with (x := y).
                  - apply SRegularD_sound. exact E2.
                  - apply lookupExTyD_sound. exact E3. }
                { cleanup Hin. } }
              { cleanup Hin. } }
            { cleanup Hin. } }
        { cleanup Hin. }
        { cleanup Hin. }
Qed.

Lemma subAll_complete : forall n D A p B Psi, sub D A p B Psi ->
  tsize A + tsize B <= n -> In Psi (subAll n D A p B).
Proof.
  intros n D A p B Psi Hsub. revert n.
  induction Hsub; intros n Hn.
  - (* s_int *) destruct n as [| n']; [simpl in Hn; lia|].
    simpl. apply in_or_app. left.
    assert (E : SRegularD Δ = true) by (apply SRegularD_complete; assumption).
    rewrite E. simpl. left. reflexivity.
  - (* s_var_ty *) destruct n as [| n']; [simpl in Hn; lia|].
    simpl. apply in_or_app. left.
    assert (E1 : SRegularD Δ = true) by (apply SRegularD_complete; assumption).
    assert (E2 : lookupTyD Δ x = true) by (apply lookupTyD_complete; assumption).
    rewrite Nat.eqb_refl. rewrite E1. rewrite E2. simpl. left. reflexivity.
  - (* s_ex_l *) destruct n as [| n']; [simpl in Hn; lia|].
    simpl. apply in_or_app. right. apply in_or_app. left.
    assert (E : substEnvD A x Δ = Some Ψ) by (apply substEnvD_complete; assumption).
    rewrite E. simpl. left. reflexivity.
  - (* s_ex_r *) destruct n as [| n']; [simpl in Hn; lia|].
    simpl. apply in_or_app. right. apply in_or_app. left.
    assert (E : substEnvD A x Δ = Some Ψ) by (apply substEnvD_complete; assumption).
    rewrite E. simpl. left. reflexivity.
  - (* s_exty_l *) destruct n as [| n']; [simpl in Hn; lia|].
    simpl. apply in_or_app. right. apply in_or_app. right.
    assert (E1 : SRegularD Δ = true) by (apply SRegularD_complete; assumption).
    assert (E2 : lookupExTyD Δ x = Some A) by (apply lookupExTyD_complete; assumption).
    rewrite E1. simpl. rewrite E2. simpl. rewrite typ_eqb_refl. simpl. left. reflexivity.
  - (* s_exty_r *) destruct n as [| n']; [simpl in Hn; lia|].
    simpl. apply in_or_app. right. apply in_or_app. right.
    assert (E1 : SRegularD Δ = true) by (apply SRegularD_complete; assumption).
    assert (E2 : lookupExTyD Δ x = Some A) by (apply lookupExTyD_complete; assumption).
    rewrite E1. simpl. rewrite E2. simpl. rewrite typ_eqb_refl. simpl. left. reflexivity.
  - (* s_arr *) destruct n as [| n']; [simpl in Hn; lia|].
    simpl. apply in_or_app. left.
    apply in_flat_map. exists Ω. split.
    + apply IHHsub1. simpl in Hn. lia.
    + apply IHHsub2. simpl in Hn. lia.
  - (* s_all *) destruct n as [| n']; [simpl in Hn; lia|].
    simpl. apply in_or_app. left.
    apply in_flat_map. exists (TyCons Ψ). split.
    + apply IHHsub. simpl in Hn. lia.
    + simpl. left. reflexivity.
Qed.

Theorem dec_sub : forall Δ A p B,
  {Ω | sub Δ A p B Ω} + {~ exists Ω, sub Δ A p B Ω}.
Proof.
  intros D A p B.
  destruct (subAll (tsize A + tsize B) D A p B) as [| Om rest] eqn:E.
  - right. intro Hex. destruct Hex as [Om H].
    assert (Hin : In Om (subAll (tsize A + tsize B) D A p B)).
    { eapply subAll_complete. exact H. lia. }
    rewrite E in Hin. inversion Hin.
  - left. exists Om. apply subAll_sound with (n := tsize A + tsize B). rewrite E. left. reflexivity.
Qed.

(* ============================================================ *)
(*        Sizes and maximum variable indices (for dec_ty)       *)
(* ============================================================ *)

Fixpoint trsize (e : Trm) : nat :=
  match e with
  | Lit _ => 1
  | Var _ => 1
  | Lam e => S (trsize e)
  | App e1 e2 => S (trsize e1 + trsize e2)
  | Ann e _ => S (trsize e)
  | TLam e => S (trsize e)
  | TApp e _ => S (trsize e)
  end.

(* maximum variable index occurring in a type (raw de Bruijn indices) *)
Fixpoint tmi (A : Typ) : nat :=
  match A with
  | Int => 0
  | TVar x => S x
  | Arr A1 A2 => max (tmi A1) (tmi A2)
  | All A1 => tmi A1
  end.

(* maximum index of a stored type in an environment *)
Fixpoint emi (D : Env) : nat :=
  match D with
  | EnvEmpty => 0
  | TmCons G A => max (emi G) (tmi A)
  | ExCons G => emi G
  | TyCons G => emi G
  | ExTyCons G A => max (emi G) (tmi A)
  | SepCons G => emi G
  end.

(* number of binders of an environment *)
Fixpoint esz (D : Env) : nat :=
  match D with
  | EnvEmpty => 0
  | TmCons G _ => S (esz G)
  | ExCons G => S (esz G)
  | TyCons G => S (esz G)
  | ExTyCons G _ => S (esz G)
  | SepCons G => S (esz G)
  end.

Fixpoint csz (C : Context) : nat :=
  match C with
  | CtxEmpty => 0
  | CtxTyp _ => 1
  | CtxTrm e C' => Datatypes.S (csz C')
  | CtxTApp _ C' => Datatypes.S (csz C')
  end.

(* sum of sizes of the terms occurring in a context *)
Fixpoint cwt (C : Context) : nat :=
  match C with
  | CtxEmpty => 0
  | CtxTyp _ => 0
  | CtxTrm e C' => trsize e + cwt C'
  | CtxTApp _ C' => cwt C'
  end.

(* maximum type index occurring in a context, including annotations in terms *)
Fixpoint tmi_tm (e : Trm) : nat :=
  match e with
  | Lit _ => 0
  | Var _ => 0
  | Lam e => tmi_tm e
  | App e1 e2 => max (tmi_tm e1) (tmi_tm e2)
  | Ann e A => max (tmi_tm e) (tmi A)
  | TLam e => tmi_tm e
  | TApp e A => max (tmi_tm e) (tmi A)
  end.

Fixpoint cmi (C : Context) : nat :=
  match C with
  | CtxEmpty => 0
  | CtxTyp A => tmi A
  | CtxTrm e C' => max (tmi_tm e) (cmi C')
  | CtxTApp A C' => max (tmi A) (cmi C')
  end.

(* size of a term including the sizes of its type annotations *)
Fixpoint tszall (e : Trm) : nat :=
  match e with
  | Lit _ => 1
  | Var _ => 1
  | Lam e => Datatypes.S (tszall e)
  | App e1 e2 => Datatypes.S (tszall e1 + tszall e2)
  | Ann e A => Datatypes.S (tszall e) + tsize A
  | TLam e => Datatypes.S (tszall e)
  | TApp e A => Datatypes.S (tszall e) + tsize A
  end.

(* size of a context including types and term annotations *)
Fixpoint cszall (C : Context) : nat :=
  match C with
  | CtxEmpty => 0
  | CtxTyp A => tsize A
  | CtxTrm e C' => tszall e + cszall C'
  | CtxTApp A C' => tsize A + cszall C'
  end.

(* ============================================================ *)
(*   Shift lemmas for max index                                 *)
(* ============================================================ *)

Lemma punchIn_le : forall k x, punchIn k x <= Datatypes.S (x + k).
Proof.
  intros k x. unfold punchIn. destruct (k <=? x) eqn:E.
  - apply Nat.leb_le in E. lia.
  - lia.
Qed.

Lemma tmi_ty_shift : forall A k, tmi (ty_shift A k) <= tmi A + k + tsize A.
Proof.
  induction A; intros k; simpl.
  - lia.
  - pose proof (punchIn_le k n). lia.
  - specialize (IHA1 k). specialize (IHA2 k). lia.
  - specialize (IHA (Datatypes.S k)). lia.
Qed.

Lemma tmi_tm_shift : forall e k, tmi_tm (ty_shift_tm e k) <= tmi_tm e + k + tszall e.
Proof.
  induction e as [n | n | e IHe | e1 IHe1 e2 IHe2 | e IHe A | e IHe | e IHe A];
    intros k; simpl.
  - lia.
  - lia.
  - specialize (IHe k). lia.
  - specialize (IHe1 k). specialize (IHe2 k). lia.
  - specialize (IHe k). pose proof (tmi_ty_shift A k). lia.
  - specialize (IHe (Datatypes.S k)). lia.
  - specialize (IHe k). pose proof (tmi_ty_shift A k). lia.
Qed.
Lemma tmi_cmi_ty_shift_ctx : forall C k, cmi (ty_shift_ctx C k) <= cmi C + k + cszall C.
Proof.
  induction C as [| A | e C IHC | A C IHC]; intros k; simpl.
  - lia.
  - pose proof (tmi_ty_shift A k). lia.
  - pose proof (IHC k). pose proof (tmi_tm_shift e k). lia.
  - pose proof (tmi_ty_shift A k). pose proof (IHC k). lia.
Qed.

Lemma tmi_cmi_ty_shift_ctx0 : forall C, cmi (ty_shift_ctx C 0) <= cmi C + cszall C.
Proof. intros. pose proof (tmi_cmi_ty_shift_ctx C 0). lia. Qed.

Lemma csz_ty_shift_ctx : forall C k, csz (ty_shift_ctx C k) = csz C.
Proof.
  induction C; intros k; simpl; auto.
Qed.

Lemma cwt_tszall_shift_tm : forall e k, trsize (ty_shift_tm e k) = trsize e.
Proof.
  induction e as [n | n | e IHe | e1 IHe1 e2 IHe2 | e IHe A | e IHe | e IHe A];
    intros k; simpl.
  - reflexivity.
  - reflexivity.
  - rewrite IHe. reflexivity.
  - rewrite IHe1, IHe2. reflexivity.
  - rewrite IHe. reflexivity.
  - rewrite (IHe (Datatypes.S k)). reflexivity.
  - rewrite IHe. reflexivity.
Qed.

Lemma cwt_ty_shift_ctx : forall C k, cwt (ty_shift_ctx C k) = cwt C.
Proof.
  induction C as [| A | e C IHC | A C IHC]; intros k; simpl.
  - reflexivity.
  - reflexivity.
  - rewrite cwt_tszall_shift_tm. rewrite IHC. reflexivity.
  - rewrite IHC. reflexivity.
Qed.

(* ============================================================ *)
(*  Bounds for lookupExTy results                               *)
(* ============================================================ *)

Lemma ty_shift_tvar : forall A k y, ty_shift A k = TVar y ->
  exists y0, A = TVar y0 /\ y = punchIn k y0.
Proof.
  intros A. induction A; intros k y H; simpl in H; try discriminate.
  - exists n. split; [reflexivity | ].
    inversion H. reflexivity.
Qed.

Lemma lookupExTy_var_gt : forall D x A, lookupExTy D x A ->
  forall y, A = TVar y -> x < y.
Proof.
  intros D x A H. induction H; intros y HA.
  - (* l_exty_Z *) apply ty_shift_tvar in HA. destruct HA as [y0 [Heq Hy]].
    rewrite Hy. unfold punchIn. destruct (0 <=? y0) eqn:E; try (apply Nat.leb_le in E); try (apply Nat.leb_gt in E); lia.
  - (* l_exty_STy *) apply ty_shift_tvar in HA. destruct HA as [y0 [Heq Hy]].
    pose proof (IHlookupExTy y0 Heq).
    rewrite Hy. unfold punchIn. destruct (0 <=? y0) eqn:E; try (apply Nat.leb_le in E); try (apply Nat.leb_gt in E); lia.
  - (* l_exty_SEx *) apply ty_shift_tvar in HA. destruct HA as [y0 [Heq Hy]].
    pose proof (IHlookupExTy y0 Heq).
    rewrite Hy. unfold punchIn. destruct (0 <=? y0) eqn:E; try (apply Nat.leb_le in E); try (apply Nat.leb_gt in E); lia.
  - (* l_exty_SExTy *) apply ty_shift_tvar in HA. destruct HA as [y0 [Heq Hy]].
    pose proof (IHlookupExTy y0 Heq).
    rewrite Hy. unfold punchIn. destruct (0 <=? y0) eqn:E; try (apply Nat.leb_le in E); try (apply Nat.leb_gt in E); lia.
  - (* l_exty_STm *) exact (IHlookupExTy y HA).
Qed.

(* sum of the sizes of the types stored in an environment *)
Fixpoint esum (D : Env) : nat :=
  match D with
  | EnvEmpty => 0
  | TmCons G A => esum G + tsize A
  | ExCons G => esum G
  | TyCons G => esum G
  | ExTyCons G A => esum G + tsize A
  | SepCons G => esum G
  end.

Definition ebound (D : Env) : nat :=
  emi D + esz D * (esum D + 1) + esum D + 1.

Lemma tsize_ty_shift : forall A k, tsize (ty_shift A k) = tsize A.
Proof.
  induction A as [| n | A1 IHA1 A2 IHA2 | A1 IHA]; intros k; simpl.
  - reflexivity.
  - reflexivity.
  - rewrite IHA1, IHA2. reflexivity.
  - rewrite (IHA (Datatypes.S k)). reflexivity.
Qed.

Lemma lookupExTy_tsize : forall D x A, lookupExTy D x A -> tsize A <= esum D.
Proof.
  intros D x A0 H.
  induction H as [G B | G B x IH | G B x IH | G B C x IH | G B C x IH]; simpl.
  - rewrite tsize_ty_shift. lia.
  - rewrite tsize_ty_shift. exact IHIH.
  - rewrite tsize_ty_shift. exact IHIH.
  - rewrite tsize_ty_shift. lia.
  - lia.
Qed.

(* ============================================================ *)
(*   Evolution machinery for sub_ctx: shifts, All-peeling       *)
(* ============================================================ *)

Fixpoint exk (k : nat) (D : Env) : Env :=
  match k with
  | 0 => D
  | S k' => ExCons (exk k' D)
  end.

Fixpoint shiftk (k : nat) (A : Typ) : Typ :=
  match k with
  | 0 => A
  | S k' => ty_shift (shiftk k' A) 0
  end.

Fixpoint alls (j : nat) (A : Typ) : Typ :=
  match j with
  | 0 => A
  | S j' => All (alls j' A)
  end.

Fixpoint iterP (j k m : nat) : nat :=
  match k with
  | 0 => m
  | S k' => punchIn j (iterP j k' m)
  end.

Fixpoint pv (A : Typ) : option nat :=
  match A with
  | All B => pv B
  | TVar x => Some x
  | _ => None
  end.

Fixpoint ad (A : Typ) : nat :=
  match A with
  | All B => S (ad B)
  | _ => 0
  end.

Lemma pv_alls : forall j m, pv (alls j (TVar m)) = Some m.
Proof.
  induction j; intros m; simpl.
  - reflexivity.
  - apply IHj.
Qed.

Lemma ad_alls : forall j m, ad (alls j (TVar m)) = j.
Proof.
  induction j; intros m; simpl.
  - reflexivity.
  - rewrite IHj. reflexivity.
Qed.

Lemma shift_all : forall t k m,
  ty_shift (alls t (TVar m)) k = alls t (TVar (punchIn (k + t) m)).
Proof.
  induction t; intros k m; simpl.
  - rewrite Nat.add_0_r. reflexivity.
  - rewrite IHt.
    replace (punchIn (S k + t) m) with (punchIn (k + S t) m).
    + reflexivity.
    + f_equal. lia.
Qed.

Lemma iterP_succ : forall j k m, iterP j (S k) m = punchIn j (iterP j k m).
Proof. reflexivity. Qed.

Lemma shiftk_alls : forall k j m,
  shiftk k (alls j (TVar m)) = alls j (TVar (iterP j k m)).
Proof.
  induction k; intros j m; simpl.
  - reflexivity.
  - rewrite IHk. rewrite shift_all.
    replace (0 + j) with j by lia. reflexivity.
Qed.

Lemma shiftk_alls_peel : forall k j m,
  pv (shiftk k (alls j (TVar m))) = Some (iterP j k m).
Proof.
  intros. rewrite shiftk_alls. apply pv_alls.
Qed.

(* iterP and the punchIn gap: if 0 < ... *)
Lemma punchIn_ge_j : forall j n, j <= n -> punchIn j n = Datatypes.S n.
Proof. intros. apply punchIn_ge. exact H. Qed.

Lemma punchIn_lt_j : forall j n, n < j -> punchIn j n = n.
Proof. intros. apply punchIn_lt. exact H. Qed.

(* iterP either stays (small) or grows by 1 per step *)
Lemma iterP_small : forall j k m, m < j -> iterP j k m = m.
Proof.
  induction k; intros m H; simpl.
  - reflexivity.
  - rewrite IHk by exact H. apply punchIn_lt. exact H.
Qed.

Lemma iterP_big : forall j k m, j <= m -> iterP j k m = m + k.
Proof.
  induction k; intros m H; simpl.
  - lia.
  - rewrite IHk by lia. rewrite punchIn_ge by lia. lia.
Qed.

(* the stored type found by (unshifted) existential lookup *)
Fixpoint lookupStored (D : Env) (x : nat) : option Typ :=
  match D with
  | EnvEmpty => None
  | TmCons G _ => lookupStored G x
  | ExCons G => match x with 0 => None | S x' => lookupStored G x' end
  | TyCons G => match x with 0 => None | S x' => lookupStored G x' end
  | ExTyCons G B => match x with 0 => Some B | S x' => lookupStored G x' end
  | SepCons _ => None
  end.

Lemma lookupStored_sound : forall D x A,
  lookupExTy D x A -> exists d, lookupStored D x = Some d.
Proof.
  intros D x A H.
  induction H as [G B | G B x Hp IHHp | G B x Hp IHHp | G B C x Hp IHHp | G B C x Hp IHHp];
    simpl.
  - exists B. reflexivity.
  - exact IHHp.
  - exact IHHp.
  - exact IHHp.
  - exact IHHp.
Qed.

Lemma lookupExTy_shift_form : forall D x A,
  lookupExTy D x A -> exists d, lookupStored D x = Some d /\ A = shiftk (S x) d.
Proof.
  intros D x A H.
  induction H as [G B | G B x Hp IHHp | G B x Hp IHHp | G B C x Hp IHHp | G B C x Hp IHHp];
    simpl.
  - exists B. split; [reflexivity | reflexivity].
  - destruct IHHp as [d [Ed HA]]. exists d. split.
    + exact Ed.
    + rewrite HA. reflexivity.
  - destruct IHHp as [d [Ed HA]]. exists d. split.
    + exact Ed.
    + rewrite HA. reflexivity.
  - destruct IHHp as [d [Ed HA]]. exists d. split.
    + exact Ed.
    + rewrite HA. reflexivity.
  - destruct IHHp as [d [Ed HA]]. exists d. split.
    + exact Ed.
    + rewrite HA. reflexivity.
Qed.

(* Key arithmetic: after an expansion and peeling the Alls, either the chain
   is trapped (index below the leading ExCons) or the resolved index strictly grows. *)
Lemma iterP_next : forall j k m0 y,
  (m0 < j /\ iterP j k (iterP j (Datatypes.S y) m0) < k + j) \/
  (j <= m0 /\ y < iterP j k (iterP j (Datatypes.S y) m0) - (k + j)).
Proof.
  intros j k m0 y. destruct (Nat.lt_ge_cases m0 j) as [Hlt | Hge].
  - left. split; [exact Hlt | ].
    assert (E1 : iterP j (Datatypes.S y) m0 = m0) by (apply iterP_small; lia).
    rewrite E1.
    assert (E2 : iterP j k m0 = m0) by (apply iterP_small; lia).
    rewrite E2. lia.
  - right. split; [exact Hge | ].
    assert (E1 : iterP j (Datatypes.S y) m0 = m0 + Datatypes.S y)
      by (apply iterP_big; lia).
    rewrite E1.
    assert (E2 : iterP j k (m0 + Datatypes.S y) = m0 + Datatypes.S y + k)
      by (apply iterP_big; lia).
    rewrite E2. lia.
Qed.

(* ============================================================ *)
(*   pv / ad under ty_shift and shiftk                          *)
(* ============================================================ *)

Lemma pv_ty_shift_none : forall X k, pv X = None -> pv (ty_shift X k) = None.
Proof.
  induction X; intros k H; simpl in *; try discriminate.
  - reflexivity.
  - reflexivity.
  - apply IHX. exact H.
Qed.

Lemma pv_ty_shift_some : forall X k m,
  pv X = Some m -> pv (ty_shift X k) = Some (punchIn (k + ad X) m).
Proof.
  induction X; intros k m H; simpl in *; try discriminate.
  - (* TVar *) inversion H. subst.
    replace (k + 0) with k by lia. reflexivity.
  - (* All *)
    pose proof (IHX (Datatypes.S k) m H) as H'.
    rewrite H'.
    replace (Datatypes.S k + ad X) with (k + Datatypes.S (ad X)) by lia.
    reflexivity.
Qed.

Lemma ad_ty_shift : forall X k, ad (ty_shift X k) = ad X.
Proof.
  induction X; intros k; simpl; auto.
Qed.

Lemma ad_shiftk : forall n d, ad (shiftk n d) = ad d.
Proof.
  induction n; intros d; simpl.
  - reflexivity.
  - rewrite ad_ty_shift. apply IHn.
Qed.

Lemma pv_shiftk_none : forall n d, pv d = None -> pv (shiftk n d) = None.
Proof.
  induction n; intros d H; simpl.
  - exact H.
  - apply pv_ty_shift_none. apply IHn. exact H.
Qed.

Lemma pv_shiftk_some : forall n d m,
  pv d = Some m -> pv (shiftk n d) = Some (iterP (ad d) n m).
Proof.
  induction n; intros d m H; simpl.
  - exact H.
  - rewrite pv_ty_shift_some with (X := shiftk n d) (k := 0) (m := iterP (ad d) n m).
    + rewrite ad_shiftk.
      replace (0 + ad d) with (ad d) by lia. reflexivity.
    + apply IHn. exact H.
Qed.

(* ============================================================ *)
(*   Environment decomposition: leading ExCons + tail            *)
(* ============================================================ *)

Fixpoint leadE (D : Env) : nat :=
  match D with
  | ExCons G => Datatypes.S (leadE G)
  | _ => 0
  end.

Fixpoint stripE (D : Env) : Env :=
  match D with
  | ExCons G => stripE G
  | _ => D
  end.

Lemma exk_succ : forall k D, exk (Datatypes.S k) D = ExCons (exk k D).
Proof. reflexivity. Qed.

Lemma esz_exk : forall k D, esz (exk k D) = k + esz D.
Proof.
  induction k; intros D; simpl.
  - lia.
  - rewrite IHk. simpl. lia.
Qed.

Lemma leadE_exk : forall k D, leadE (exk k D) = k + leadE D.
Proof.
  induction k; intros D; simpl.
  - lia.
  - rewrite IHk. lia.
Qed.

Lemma stripE_exk : forall k D, stripE (exk k D) = stripE D.
Proof.
  induction k; intros D; simpl.
  - reflexivity.
  - apply IHk.
Qed.

Lemma esz_stripE : forall D, esz D = leadE D + esz (stripE D).
Proof.
  induction D; simpl.
  - reflexivity.
  - reflexivity.
  - rewrite IHD. simpl. lia.
  - reflexivity.
  - reflexivity.
  - reflexivity.
Qed.

Lemma env_decomp : forall D, D = exk (leadE D) (stripE D).
Proof.
  induction D as [| G A | G IHG | G IHG | G A IHG | G IHG]; simpl.
  - reflexivity.
  - reflexivity.
  - f_equal. exact IHG.
  - reflexivity.
  - reflexivity.
  - reflexivity.
Qed.

Lemma leadE_stripE : forall D, leadE (stripE D) = 0.
Proof.
  induction D; simpl; auto.
Qed.

Lemma stripE_stripE : forall D, stripE (stripE D) = stripE D.
Proof.
  induction D; simpl; auto.
Qed.

(* lookup decomposition under a prefix of ExCons *)
Lemma lookupExTy_exk : forall k D y A0,
  lookupExTy (exk k D) (k + y) A0 ->
  exists A, lookupExTy D y A /\ A0 = shiftk k A.
Proof.
  induction k; intros D y A0 H; simpl in H.
  - exists A0. split; [exact H | reflexivity].
  - inversion H; subst.
    match goal with
    | Hp : lookupExTy (exk k D) (k + y) ?B |- _ =>
        destruct (IHk D y B Hp) as [A' [Hl HA]];
        exists A'; split; [ exact Hl | rewrite HA; reflexivity ]
    end.
Qed.

Lemma shiftk_shiftk : forall a b A, shiftk a (shiftk b A) = shiftk (a + b) A.
Proof.
  induction a; intros b A; simpl.
  - replace (0 + b) with b by lia. reflexivity.
  - rewrite IHa. replace (Datatypes.S a + b) with (Datatypes.S (a + b)) by lia.
    reflexivity.
Qed.

(* ============================================================ *)
(*   The evolution measure                                      *)
(* ============================================================ *)

Definition wfst (D : Env) (A : Typ) : nat :=
  match pv A with
  | Some x =>
      if (leadE D + ad A) <=? x
      then esz (stripE D) - (x - leadE D - ad A)
      else 0
  | None => 0
  end.

Lemma wfst_all : forall D B, wfst (ExCons D) B = wfst D (All B).
Proof.
  intros D B. unfold wfst.
  change (pv (All B)) with (pv B).
  change (ad (All B)) with (Datatypes.S (ad B)).
  change (leadE (ExCons D)) with (Datatypes.S (leadE D)).
  change (stripE (ExCons D)) with (stripE D).
  destruct (pv B) as [x|].
  - replace (Datatypes.S (leadE D) + ad B) with (leadE D + Datatypes.S (ad B)) by lia.
    destruct (leadE D + Datatypes.S (ad B) <=? x) eqn:E.
    + replace (x - Datatypes.S (leadE D) - ad B)
        with (x - leadE D - Datatypes.S (ad B)) by lia.
      reflexivity.
    + reflexivity.
  - reflexivity.
Qed.

Lemma lookupExTy_lt_esz : forall D x A, lookupExTy D x A -> x < esz D.
Proof.
  intros D x A H.
  induction H as [G B | G B x Hp IH | G B x Hp IH | G B C x Hp IH | G B C x Hp IH];
    simpl; lia.
Qed.

Lemma lookupExTy_exk_lead : forall k D x A, lookupExTy (exk k D) x A -> k <= x.
Proof.
  induction k; intros D x A H; simpl in H.
  - lia.
  - destruct x as [| x'].
    + inversion H.
    + inversion H; subst. apply le_n_S.
      match goal with Hp : lookupExTy (exk k D) x' _ |- _ => eapply IHk; exact Hp end.
Qed.

(* the expansion strictly decreases the first component of the measure *)
Lemma wfst_step : forall D x A0,
  lookupExTy D x A0 -> wfst D A0 < wfst D (TVar x).
Proof.
  intros D x A0 Hlk.
  remember (leadE D) as k eqn:Ek.
  remember (stripE D) as D0 eqn:ED0.
  assert (Hdec : D = exk k D0).
  { rewrite (env_decomp D). rewrite Ek, ED0. reflexivity. }
  assert (Hkle : k <= x).
  { eapply lookupExTy_exk_lead. rewrite <- Hdec. exact Hlk. }
  assert (Hlk2 : lookupExTy (exk k D0) (k + (x - k)) A0).
  { replace (k + (x - k)) with x by lia. rewrite <- Hdec. exact Hlk. }
  destruct (lookupExTy_exk k D0 (x - k) A0 Hlk2) as [A' [Hl HA0]].
  destruct (lookupExTy_shift_form D0 (x - k) A' Hl) as [d [Ed HA]].
  assert (Hpos : 0 < esz D0 - (x - k)).
  { assert (x - k < esz D0) by (eapply lookupExTy_lt_esz; exact Hl). lia. }
  assert (Hwv : wfst D (TVar x) = esz D0 - (x - k)).
  { unfold wfst. simpl.
    replace (leadE D + 0) with (leadE D) by lia.
    destruct (leadE D <=? x) eqn:E.
    - replace (x - leadE D - 0) with (x - leadE D) by lia.
      rewrite ED0, Ek. reflexivity.
    - apply Nat.leb_gt in E. exfalso. rewrite Ek in Hkle. lia. }
  destruct (pv d) as [m0|] eqn:Epv.
  - (* variable core *)
    assert (HA0' : A0 = shiftk (k + Datatypes.S (x - k)) d).
    { rewrite HA0, HA, shiftk_shiftk. reflexivity. }
    assert (Hpvn : pv A0 = Some (iterP (ad d) (k + Datatypes.S (x - k)) m0)).
    { rewrite HA0'. rewrite (pv_shiftk_some (k + Datatypes.S (x - k)) d m0 Epv). reflexivity. }
    assert (Hadn : ad A0 = ad d).
    { rewrite HA0'. apply ad_shiftk. }
    destruct (Nat.lt_ge_cases m0 (ad d)) as [Hlt | Hge].
    + (* trapped *)
      assert (Hn : iterP (ad d) (k + Datatypes.S (x - k)) m0 = m0).
      { apply iterP_small. exact Hlt. }
      unfold wfst at 1. rewrite Hpvn.
      replace (ad A0) with (ad d) by (symmetry; exact Hadn).
      rewrite Hn.
      assert (Hcond : (leadE D + ad d <=? m0) = false).
      { apply Nat.leb_gt. rewrite <- Ek. lia. }
      rewrite Hcond. simpl. rewrite Hwv. exact Hpos.
    + (* grows *)
      assert (Hn : iterP (ad d) (k + Datatypes.S (x - k)) m0
                   = m0 + (k + Datatypes.S (x - k))).
      { apply iterP_big. lia. }
      unfold wfst at 1. rewrite Hpvn.
      replace (ad A0) with (ad d) by (symmetry; exact Hadn).
      rewrite Hn.
      assert (Hcond : (leadE D + ad d <=? (m0 + (k + Datatypes.S (x - k)))) = true).
      { apply Nat.leb_le. rewrite <- Ek. lia. }
      rewrite Hcond. simpl. rewrite Hwv.
      assert (Hsub : m0 + (k + Datatypes.S (x - k)) - leadE D - ad d
                     = m0 + Datatypes.S (x - k) - ad d).
      { rewrite <- Ek. lia. }
      rewrite Hsub. rewrite <- ED0.
      assert (Hlt2 : x - k < m0 + Datatypes.S (x - k) - ad d) by lia.
      assert (Hlt3 : x - k < esz D0) by (eapply lookupExTy_lt_esz; exact Hl).
      lia.
  - (* no variable core *)
    assert (Hpvn : pv A0 = None).
    { rewrite HA0, HA. apply pv_shiftk_none. apply pv_shiftk_none. exact Epv. }
    unfold wfst at 1. rewrite Hpvn. simpl. rewrite Hwv. exact Hpos.
Qed.

(* ============================================================ *)
(*   Structural equality for terms and environments             *)
(* ============================================================ *)

Fixpoint trm_eqb (e1 e2 : Trm) : bool :=
  match e1 with
  | Lit n => match e2 with Lit m => n =? m | _ => false end
  | Var x => match e2 with Var y => x =? y | _ => false end
  | Lam e => match e2 with Lam e' => trm_eqb e e' | _ => false end
  | App a b => match e2 with App a' b' => andb (trm_eqb a a') (trm_eqb b b') | _ => false end
  | Ann e A => match e2 with Ann e' A' => andb (trm_eqb e e') (typ_eqb A A') | _ => false end
  | TLam e => match e2 with TLam e' => trm_eqb e e' | _ => false end
  | TApp e A => match e2 with TApp e' A' => andb (trm_eqb e e') (typ_eqb A A') | _ => false end
  end.

Lemma trm_eqb_eq : forall e1 e2, trm_eqb e1 e2 = true <-> e1 = e2.
Proof.
  induction e1; destruct e2; simpl; try (split; discriminate).
  - split; intro H.
    + apply Nat.eqb_eq in H. subst. reflexivity.
    + inversion H. subst. apply Nat.eqb_eq. reflexivity.
  - split; intro H.
    + apply Nat.eqb_eq in H. subst. reflexivity.
    + inversion H. subst. apply Nat.eqb_eq. reflexivity.
  - rewrite IHe1. split; [intros H; subst; reflexivity | intro H; inversion H; auto].
  - rewrite Bool.andb_true_iff, IHe1_1, IHe1_2. split.
    + intros [H1 H2]. subst. reflexivity.
    + intro H. inversion H. subst. auto.
  - rewrite Bool.andb_true_iff, IHe1, typ_eqb_eq. split.
    + intros [H1 H2]. subst. reflexivity.
    + intro H. inversion H. subst. auto.
  - rewrite IHe1. split; [intros H; subst; reflexivity | intro H; inversion H; auto].
  - rewrite Bool.andb_true_iff, IHe1, typ_eqb_eq. split.
    + intros [H1 H2]. subst. reflexivity.
    + intro H. inversion H. subst. auto.
Qed.

Fixpoint env_eqb (D1 D2 : Env) : bool :=
  match D1 with
  | EnvEmpty => match D2 with EnvEmpty => true | _ => false end
  | TmCons G A => match D2 with TmCons G' A' => andb (env_eqb G G') (typ_eqb A A') | _ => false end
  | ExCons G => match D2 with ExCons G' => env_eqb G G' | _ => false end
  | TyCons G => match D2 with TyCons G' => env_eqb G G' | _ => false end
  | ExTyCons G A => match D2 with ExTyCons G' A' => andb (env_eqb G G') (typ_eqb A A') | _ => false end
  | SepCons G => match D2 with SepCons G' => env_eqb G G' | _ => false end
  end.

Lemma env_eqb_eq : forall D1 D2, env_eqb D1 D2 = true <-> D1 = D2.
Proof.
  induction D1; destruct D2; simpl; try (split; discriminate).
  - split; intros; reflexivity.
  - rewrite Bool.andb_true_iff, IHD1, typ_eqb_eq. split.
    + intros [H1 H2]. subst. reflexivity.
    + intro H. inversion H. subst. auto.
  - rewrite IHD1. split; [intros H; subst; reflexivity | intro H; inversion H; auto].
  - rewrite IHD1. split; [intros H; subst; reflexivity | intro H; inversion H; auto].
  - rewrite Bool.andb_true_iff, IHD1, typ_eqb_eq. split.
    + intros [H1 H2]. subst. reflexivity.
    + intro H. inversion H. subst. auto.
  - rewrite IHD1. split; [intros H; subst; reflexivity | intro H; inversion H; auto].
Qed.

(* ============================================================ *)
(*   Symbolic targets (for the existential instantiation B)      *)
(* ============================================================ *)

Inductive Tgt : Type :=
| tB : Env -> Tgt
| tEx : Tgt -> Tgt
| tExTy : Tgt -> option Typ -> Tgt.

Fixpoint tmatch (t : Tgt) (D : Env) : bool :=
  match t with
  | tB D0 => env_eqb D0 D
  | tEx t' => match D with ExCons D' => tmatch t' D' | _ => false end
  | tExTy t' oB =>
      match D with
      | ExTyCons D' B' =>
          match oB with
          | None => tmatch t' D'
          | Some B => andb (typ_eqb B B') (tmatch t' D')
          end
      | _ => false
      end
  end.

Lemma tmatch_base : forall D, tmatch (tB D) D = true.
Proof. intros. simpl. apply env_eqb_eq. reflexivity. Qed.

Lemma tmatch_base_inv : forall D D', tmatch (tB D) D' = true -> D = D'.
Proof. intros. simpl in H. apply env_eqb_eq in H. exact H. Qed.

Lemma tmatch_ex : forall t D, tmatch (tEx t) (ExCons D) = tmatch t D.
Proof. intros. reflexivity. Qed.

Lemma tmatch_ex_inv : forall t D, tmatch (tEx t) D = true ->
  exists D', D = ExCons D' /\ tmatch t D' = true.
Proof.
  intros t D H. simpl in H.
  destruct D; simpl in H; try discriminate.
  exists D. split; [reflexivity | exact H].
Qed.

(* ============================================================ *)
(*   The decision procedures for ty / sub_ctx / infs            *)
(* ============================================================ *)

Definition nonemptyb (C : Context) : bool :=
  match C with CtxEmpty => false | _ => true end.

Definition nonemptyL (l : list Typ) : bool :=
  match l with nil => false | _ => true end.

Definition unshiftArrL (R : Typ) : list Typ :=
  match R with
  | Arr C' D' =>
      match ty_unshift C' 0 with
      | Some C => match ty_unshift D' 0 with
                  | Some D => (Arr C D :: nil)
                  | None => nil
                  end
      | None => nil
      end
  | _ => nil
  end.

(* Evolution fuel: bounds the length of a TVar/All unwinding chain. *)
Definition fuelAt (D : Env) (A : Typ) : nat :=
  (wfst D A + 1) * (esum D + 2) + tsize A.

Lemma fuelAt_all : forall D A0,
  fuelAt D (All A0) = Datatypes.S (fuelAt (ExCons D) A0).
Proof.
  intros D A0. unfold fuelAt. simpl. rewrite wfst_all. lia.
Qed.

Lemma fuelAt_tvar : forall D x A0, lookupExTy D x A0 ->
  fuelAt D A0 < fuelAt D (TVar x).
Proof.
  intros D x A0 Hlk. unfold fuelAt. simpl.
  set (w := wfst D (TVar x)). set (w0 := wfst D A0).
  set (e := esum D). set (s0 := tsize A0).
  assert (Hw : w0 < w) by (unfold w, w0; exact (wfst_step D x A0 Hlk)).
  assert (Hs : s0 <= e) by (unfold s0, e; exact (lookupExTy_tsize D x A0 Hlk)).
  assert (Hwle : w0 + 1 <= w) by lia.
  assert (Hmul : (w0 + 1) * (e + 2) <= w * (e + 2))
    by (apply Nat.mul_le_mono_r; exact Hwle).
  cut ((w0 + 1) * (e + 2) + s0 < (w + 1) * (e + 2) + 1). { lia. }
  assert (Hlt : w * (e + 2) < (w + 1) * (e + 2))
    by (apply Nat.mul_lt_mono_pos_r; lia).
  lia.
Qed.

(* Chain helpers for the CtxTrm / CtxTApp sub_ctx rules, parameterised
   by the mutual decision procedures so they can be proved independently. *)

Fixpoint chainT
    (infF : nat -> Env -> Context -> list Typ)
    (scF : nat -> Env -> Typ -> Context -> Tgt -> list Typ)
    (tyF : nat -> Env -> Context -> Trm -> list Typ)
    (cfuel efuel : nat) (D : Env) (T : Typ) (tm : Trm) (Sx : Context) (tg : Tgt)
    {struct efuel} : list Typ :=
  match efuel with
  | 0 => nil
  | S ef =>
      match T with
      | TVar x =>
          flat_map (fun Ainf =>
                      match substEnvD Ainf x D with
                      | Some Psi' => if tmatch tg Psi' then (Ainf :: nil) else nil
                      | None => nil
                      end)
                   (infF cfuel D (CtxTrm tm Sx))
          ++ (if tmatch tg D then
                match lookupExTyD D x with
                | Some A0 =>
                    flat_map (fun R => match R with
                                       | Arr B0 C0 => (Arr B0 C0 :: nil)
                                       | _ => nil end)
                             (chainT infF scF tyF cfuel ef D A0 tm Sx (tB D))
                | None => nil
                end
              else nil)
      | All A0 =>
          flat_map unshiftArrL (chainT infF scF tyF cfuel ef (ExCons D) A0 (ty_shift_tm tm 0) (ty_shift_ctx Sx 0) (tExTy tg None))
          ++ flat_map unshiftArrL (chainT infF scF tyF cfuel ef (ExCons D) A0 (ty_shift_tm tm 0) (ty_shift_ctx Sx 0) (tEx tg))
      | Arr A1 B1 =>
          (if closeD D A1 then
             match grdTypD D A1 with
             | Some G' =>
                 if nonemptyL (tyF cfuel (rm_sep D) (CtxTyp G') tm) then
                   flat_map (fun D' => (Arr G' D' :: nil)) (scF cfuel D B1 Sx tg)
                 else nil
             | None => nil
             end
           else nil)
          ++ (if openD D A1 then
                flat_map (fun C =>
                  flat_map (fun Om =>
                    flat_map (fun D' => (Arr C D' :: nil)) (scF cfuel Om B1 Sx tg))
                    (subAll (tsize C + tsize A1) D C Neg A1))
                  (tyF cfuel (rm_sep D) CtxEmpty tm)
              else nil)
      | Int => nil
      end
  end.

Fixpoint chainA
    (scF : nat -> Env -> Typ -> Context -> Tgt -> list Typ)
    (cfuel efuel : nat) (D : Env) (T : Typ) (B : Typ) (Sx : Context) (tg : Tgt)
    {struct efuel} : list Typ :=
  match efuel with
  | 0 => nil
  | S ef =>
      match T with
      | TVar x =>
          (if tmatch tg D then
             match lookupExTyD D x with
             | Some A0 =>
                 flat_map (fun R => match R with
                                    | All C0 => (All C0 :: nil)
                                    | _ => nil end)
                          (chainA scF cfuel ef D A0 B Sx (tB D))
             | None => nil
             end
           else nil)
      | All A0 =>
          flat_map (fun C => (All C :: nil))
            (scF cfuel (ExTyCons D B) A0 (ty_shift_ctx Sx 0) (tExTy tg (Some B)))
      | _ => nil
      end
  end.

Fixpoint tyD (fuel : nat) (Γ : Env) (Σ : Context) (e : Trm) {struct fuel} : list Typ :=
  match fuel with
  | 0 => nil
  | S f =>
      let subpart :=
          (if nonemptyb Σ then
             flat_map (fun Aty => scD f (SepCons Γ) Aty Σ (tB (SepCons Γ)))
                      (tyD f Γ CtxEmpty e)
           else nil) in
      match e with
      | Lit n =>
          (if andb (negb (nonemptyb Σ)) (TRegularD Γ) then (Int :: nil) else nil)
          ++ subpart
      | Var x =>
          (if andb (negb (nonemptyb Σ)) (TRegularD Γ) then
             match lookupTmD Γ x with Some A => (A :: nil) | None => nil end
           else nil)
          ++ subpart
      | Ann e0 A0 =>
          (if negb (nonemptyb Σ) then
             if nonemptyL (tyD f Γ (CtxTyp A0) e0) then (A0 :: nil) else nil
           else nil)
          ++ subpart
      | Lam e0 =>
          (match Σ with
           | CtxTyp A =>
               match A with
               | Arr A0 B =>
                   flat_map (fun C => (Arr A0 C :: nil))
                            (tyD f (TmCons Γ A0) (CtxTyp B) e0)
               | _ => nil
               end
           | _ => nil
           end)
          ++ (match Σ with
              | CtxTrm e2 Σ' =>
                  flat_map (fun A =>
                    flat_map (fun B => (Arr A B :: nil))
                             (tyD f (TmCons Γ A) (tm_shift_ctx Σ' 0) e0))
                    (tyD f Γ CtxEmpty e2)
              | _ => nil
              end)
      | App e1 e2 =>
          flat_map (fun T => match T with Arr A B => (B :: nil) | _ => nil end)
                   (tyD f Γ (CtxTrm e2 Σ) e1)
      | TLam e0 =>
          (match Σ with
           | CtxEmpty => flat_map (fun A => (All A :: nil)) (tyD f (TyCons Γ) CtxEmpty e0)
           | CtxTyp A =>
               match A with
               | All A0 =>
                   if nonemptyL (tyD f (TyCons Γ) (CtxTyp A0) e0) then (All A0 :: nil) else nil
               | _ => nil
               end
           | _ => nil
           end)
          ++ subpart
      | TApp e0 A0 =>
          flat_map (fun T => match T with All B => (subst B 0 A0 :: nil) | _ => nil end)
                   (tyD f Γ (CtxTApp A0 Σ) e0)
      end
  end
with scD (fuel : nat) (Δ : Env) (A : Typ) (Σ : Context) (t : Tgt) {struct fuel} : list Typ :=
  match fuel with
  | 0 => nil
  | S f =>
      match Σ with
      | CtxEmpty =>
          if andb (SRegularD Δ) (andb (tmatch t Δ) (closeD Δ A)) then
            match grdTypD Δ A with Some A' => (A' :: nil) | None => nil end
          else nil
      | CtxTyp B =>
          if existsb (fun Psi' => tmatch t Psi') (subAll (tsize A + tsize B) Δ A Pos B)
          then (B :: nil) else nil
      | CtxTrm e Σ' =>
          chainT infD scD tyD f (fuelAt Δ A) Δ A e Σ' t
      | CtxTApp B Σ' =>
          chainA scD f (fuelAt Δ A) Δ A B Σ' t
      end
  end
with infD (fuel : nat) (Γ : Env) (Σ : Context) {struct fuel} : list Typ :=
  match fuel with
  | 0 => nil
  | S f =>
      match Σ with
      | CtxTyp A =>
          if andb (TRegularD Γ) (RegularTypD Γ A) then (A :: nil) else nil
      | CtxTrm e Σ' =>
          flat_map (fun A =>
            flat_map (fun B => (Arr A B :: nil)) (infD f Γ Σ'))
            (tyD f Γ CtxEmpty e)
      | _ => nil
      end
  end.

(* ============================================================ *)
(*   Lemmas for the target/symbolic helpers                     *)
(* ============================================================ *)

Lemma tmatch_exty_none_inv : forall tg D, tmatch (tExTy tg None) D = true ->
  exists Psi B, D = ExTyCons Psi B /\ tmatch tg Psi = true.
Proof.
  intros tg D H. simpl in H. destruct D; simpl in H; try discriminate.
  exists D, t. split; [reflexivity | exact H].
Qed.

Lemma tmatch_exty_some_inv : forall tg B0 D, tmatch (tExTy tg (Some B0)) D = true ->
  exists Psi B, D = ExTyCons Psi B /\ typ_eqb B0 B = true /\ tmatch tg Psi = true.
Proof.
  intros tg B0 D H. simpl in H. destruct D; simpl in H; try discriminate.
  apply Bool.andb_true_iff in H. destruct H as [Hb Ht].
  exists D, t. split; [reflexivity | split; [exact Hb | exact Ht]].
Qed.

Lemma nonemptyL_spec : forall (l : list Typ), nonemptyL l = true -> exists x, In x l.
Proof.
  intros l H. destruct l as [| x xs]; simpl in H; try discriminate.
  exists x. left. reflexivity.
Qed.

Lemma unshiftArrL_spec : forall R' R, In R (unshiftArrL R') ->
  exists C D C' D', R' = Arr C' D' /\ ty_unshift C' 0 = Some C /\
                   ty_unshift D' 0 = Some D /\ R = Arr C D.
Proof.
  intros R' R H. destruct R' as [| n | C' D' | A0].
  - cbn [unshiftArrL] in H. exfalso; exact H.
  - cbn [unshiftArrL] in H. exfalso; exact H.
  - cbn [unshiftArrL] in H.
    destruct (ty_unshift C' 0) as [C|] eqn:EC.
    + destruct (ty_unshift D' 0) as [D|] eqn:ED.
      * cbn in H. apply eq_or_false in H. subst R.
        exists C, D, C', D'.
        split; [reflexivity | split; [exact EC | split; [exact ED | reflexivity]]].
      * cbn in H. exfalso; exact H.
    + cbn in H. exfalso; exact H.
  - cbn [unshiftArrL] in H. exfalso; exact H.
Qed.

(* ============================================================ *)
(*   Computation equations for the chain helpers                *)
(* ============================================================ *)

Lemma chainT_int : forall infF scF tyF cfuel ef D tm Sx tg,
  chainT infF scF tyF cfuel (S ef) D Int tm Sx tg = nil.
Proof. reflexivity. Qed.

Lemma chainT_tvar : forall infF scF tyF cfuel ef D x tm Sx tg,
  chainT infF scF tyF cfuel (S ef) D (TVar x) tm Sx tg =
  flat_map (fun Ainf =>
              match substEnvD Ainf x D with
              | Some Psi' => if tmatch tg Psi' then (Ainf :: nil) else nil
              | None => nil
              end)
           (infF cfuel D (CtxTrm tm Sx))
  ++ (if tmatch tg D then
        match lookupExTyD D x with
        | Some A0 =>
            flat_map (fun R => match R with
                               | Arr B0 C0 => (Arr B0 C0 :: nil)
                               | _ => nil end)
                     (chainT infF scF tyF cfuel ef D A0 tm Sx (tB D))
        | None => nil
        end
      else nil).
Proof. reflexivity. Qed.

Lemma chainT_all : forall infF scF tyF cfuel ef D A0 tm Sx tg,
  chainT infF scF tyF cfuel (S ef) D (All A0) tm Sx tg =
  flat_map unshiftArrL (chainT infF scF tyF cfuel ef (ExCons D) A0 (ty_shift_tm tm 0) (ty_shift_ctx Sx 0) (tExTy tg None))
  ++ flat_map unshiftArrL (chainT infF scF tyF cfuel ef (ExCons D) A0 (ty_shift_tm tm 0) (ty_shift_ctx Sx 0) (tEx tg)).
Proof. reflexivity. Qed.

Lemma chainT_arr : forall infF scF tyF cfuel ef D A1 B1 tm Sx tg,
  chainT infF scF tyF cfuel (S ef) D (Arr A1 B1) tm Sx tg =
  (if closeD D A1 then
     match grdTypD D A1 with
     | Some G' =>
         if nonemptyL (tyF cfuel (rm_sep D) (CtxTyp G') tm) then
           flat_map (fun D' => (Arr G' D' :: nil)) (scF cfuel D B1 Sx tg)
         else nil
     | None => nil
     end
   else nil)
  ++ (if openD D A1 then
        flat_map (fun C =>
          flat_map (fun Om =>
            flat_map (fun D' => (Arr C D' :: nil)) (scF cfuel Om B1 Sx tg))
            (subAll (tsize C + tsize A1) D C Neg A1))
          (tyF cfuel (rm_sep D) CtxEmpty tm)
      else nil).
Proof. reflexivity. Qed.

Lemma chainA_tvar : forall scF cfuel ef D x B Sx tg,
  chainA scF cfuel (S ef) D (TVar x) B Sx tg =
  (if tmatch tg D then
     match lookupExTyD D x with
     | Some A0 =>
         flat_map (fun R => match R with
                            | All C0 => (All C0 :: nil)
                            | _ => nil end)
                  (chainA scF cfuel ef D A0 B Sx (tB D))
     | None => nil
     end
   else nil).
Proof. reflexivity. Qed.

Lemma chainA_all : forall scF cfuel ef D A0 B Sx tg,
  chainA scF cfuel (S ef) D (All A0) B Sx tg =
  flat_map (fun C => (All C :: nil))
    (scF cfuel (ExTyCons D B) A0 (ty_shift_ctx Sx 0) (tExTy tg (Some B))).
Proof. reflexivity. Qed.

Lemma chainA_int : forall scF cfuel ef D B Sx tg,
  chainA scF cfuel (S ef) D Int B Sx tg = nil.
Proof. reflexivity. Qed.

Lemma chainA_arr : forall scF cfuel ef D A1 B1 B0 Sx tg,
  chainA scF cfuel (S ef) D (Arr A1 B1) B0 Sx tg = nil.
Proof. reflexivity. Qed.

(* ============================================================ *)
(*   Soundness of the chain helpers                             *)
(* ============================================================ *)

Lemma chainT_sound :
  forall infF scF tyF cfuel,
    (forall D Sx A, In A (infF cfuel D Sx) -> infs D Sx A) ->
    (forall D A Sx t R, In R (scF cfuel D A Sx t) ->
        exists Psi, tmatch t Psi = true /\ sub_ctx D A Sx Psi R) ->
    (forall G Sx e A, In A (tyF cfuel G Sx e) -> ty G Sx e A) ->
    forall efuel D T tm Sx tg R,
      In R (chainT infF scF tyF cfuel efuel D T tm Sx tg) ->
      exists Psi, tmatch tg Psi = true /\ sub_ctx D T (CtxTrm tm Sx) Psi R.
Proof.
  intros infF scF tyF cfuel Hinf Hsc Hty.
  induction efuel as [| ef IH]; intros D T tm Sx tg R HR.
  - simpl in HR. exact (False_ind _ HR).
  - destruct T as [| x | A1 B1 | A0].
    + rewrite chainT_int in HR. exact (False_ind _ HR).
    + rewrite chainT_tvar in HR.
      apply in_app_or in HR. destruct HR as [HR | HR].
      * apply in_flat_map in HR. destruct HR as [Ainf [HAinf HR]].
        destruct (substEnvD Ainf x D) as [Psi'|] eqn:E.
        -- destruct (tmatch tg Psi') eqn:Et.
           ++ apply eq_or_false in HR. subst R.
              exists Psi'. split; [exact Et | ].
              eapply s_evar_infers with (A := Ainf) (x := x).
              ** apply Hinf. exact HAinf.
              ** apply substEnvD_sound. exact E.
           ++ exact (False_ind _ HR).
        -- exact (False_ind _ HR).
      * destruct (tmatch tg D) eqn:Et.
        -- destruct (lookupExTyD D x) as [A0'|] eqn:El.
           ++ apply in_flat_map in HR. destruct HR as [R0 [HR0 HRf]].
              destruct R0 as [| n | B0 C0 | A00].
              ** cbn in HRf. exact (False_ind _ HRf).
              ** cbn in HRf. exact (False_ind _ HRf).
              ** apply eq_or_false in HRf. subst R.
                 destruct (IH D A0' tm Sx (tB D) (Arr B0 C0) HR0) as [Psi [Ht Hsub]].
                 assert (Psi = D) by (symmetry; apply tmatch_base_inv; exact Ht). subst Psi.
                 exists D. split; [exact Et | ].
                 eapply s_svar_trm with (x := x) (A := A0').
                 --- apply lookupExTyD_sound. exact El.
                 --- exact Hsub.
              ** cbn in HRf. exact (False_ind _ HRf).
           ++ exact (False_ind _ HR).
        -- exact (False_ind _ HR).
    + rewrite chainT_arr in HR.
      apply in_app_or in HR. destruct HR as [HR | HR].
      * destruct (closeD D A1) eqn:Ecl.
        -- destruct (grdTypD D A1) as [G'|] eqn:Eg.
           ++ destruct (nonemptyL (tyF cfuel (rm_sep D) (CtxTyp G') tm)) eqn:En.
              ** apply in_flat_map in HR. destruct HR as [D' [HD' HR]].
                 apply eq_or_false in HR. subst R.
                 destruct (Hsc D B1 Sx tg D' HD') as [Psi [Ht Hsub]].
                 exists Psi. split; [exact Ht | ].
                 apply nonemptyL_spec in En. destruct En as [A'' HA''].
                 eapply s_trm_c with (A := A1) (B := B1) (A' := G') (A'' := A'').
                 --- apply closeD_sound. exact Ecl.
                 --- apply grdTypD_sound. exact Eg.
                 --- apply Hty. exact HA''.
                 --- exact Hsub.
              ** exact (False_ind _ HR).
           ++ exact (False_ind _ HR).
        -- exact (False_ind _ HR).
      * destruct (openD D A1) eqn:Eop.
        -- apply in_flat_map in HR. destruct HR as [C [HC HR]].
           apply in_flat_map in HR. destruct HR as [Om [HOm HR]].
           apply in_flat_map in HR. destruct HR as [D' [HD' HR]].
           apply eq_or_false in HR. subst R.
           destruct (Hsc Om B1 Sx tg D' HD') as [Psi [Ht Hsub]].
           exists Psi. split; [exact Ht | ].
           eapply s_trm_o with (A := A1) (B := B1) (C := C) (D := D') (Ω := Om).
           ++ apply openD_sound. exact Eop.
           ++ apply Hty. exact HC.
           ++ exact (subAll_sound (tsize C + tsize A1) D C Neg A1 Om HOm).
           ++ exact Hsub.
        -- exact (False_ind _ HR).
    + rewrite chainT_all in HR.
      apply in_app_or in HR. destruct HR as [HR | HR].
      * apply in_flat_map in HR. destruct HR as [R' [HR' HRu]].
        destruct (IH (ExCons D) A0 (ty_shift_tm tm 0) (ty_shift_ctx Sx 0) (tExTy tg None) R' HR') as [Psi_p [Ht Hsub]].
        apply tmatch_exty_none_inv in Ht. destruct Ht as [Psi [B [Heq Ht]]]. subst Psi_p.
        apply unshiftArrL_spec in HRu. destruct HRu as [C [D0 [C' [D' [Heq [Eu [Ev HeqR]]]]]]]. subst R' R.
        rewrite <- (ty_shift_unshift C' 0 C Eu) in Hsub.
        rewrite <- (ty_shift_unshift D' 0 D0 Ev) in Hsub.
        exists Psi. split; [exact Ht | ].
        eapply s_alll. exact Hsub.
      * apply in_flat_map in HR. destruct HR as [R' [HR' HRu]].
        destruct (IH (ExCons D) A0 (ty_shift_tm tm 0) (ty_shift_ctx Sx 0) (tEx tg) R' HR') as [Psi_p [Ht Hsub]].
        apply tmatch_ex_inv in Ht. destruct Ht as [Psi [Heq Ht]]. subst Psi_p.
        apply unshiftArrL_spec in HRu. destruct HRu as [C [D0 [C' [D' [Heq [Eu [Ev HeqR]]]]]]]. subst R' R.
        rewrite <- (ty_shift_unshift C' 0 C Eu) in Hsub.
        rewrite <- (ty_shift_unshift D' 0 D0 Ev) in Hsub.
        exists Psi. split; [exact Ht | ].
        eapply s_alll_no. exact Hsub.
Qed.

Lemma chainA_sound :
  forall scF cfuel,
    (forall D A Sx t R, In R (scF cfuel D A Sx t) ->
        exists Psi, tmatch t Psi = true /\ sub_ctx D A Sx Psi R) ->
    forall efuel D T B Sx tg R,
      In R (chainA scF cfuel efuel D T B Sx tg) ->
      exists Psi, tmatch tg Psi = true /\ sub_ctx D T (CtxTApp B Sx) Psi R.
Proof.
  intros scF cfuel Hsc.
  induction efuel as [| ef IH]; intros D T B Sx tg R HR.
  - simpl in HR. exact (False_ind _ HR).
  - destruct T as [| x | A1 B1 | A0].
    + rewrite chainA_int in HR. exact (False_ind _ HR).
    + rewrite chainA_tvar in HR.
      destruct (tmatch tg D) eqn:Et.
      * destruct (lookupExTyD D x) as [A0'|] eqn:El.
        -- apply in_flat_map in HR. destruct HR as [R0 [HR0 HRf]].
           destruct R0 as [| n | B0 C0 | C00].
           ++ cbn in HRf. exact (False_ind _ HRf).
           ++ cbn in HRf. exact (False_ind _ HRf).
           ++ cbn in HRf. exact (False_ind _ HRf).
           ++ apply eq_or_false in HRf. subst R.
              destruct (IH D A0' B Sx (tB D) (All C00) HR0) as [Psi [Ht Hsub]].
              assert (Psi = D) by (symmetry; apply tmatch_base_inv; exact Ht). subst Psi.
              exists D. split; [exact Et | ].
              eapply s_svar_tapp with (x := x) (A := A0').
              ** apply lookupExTyD_sound. exact El.
              ** exact Hsub.
        -- exact (False_ind _ HR).
      * exact (False_ind _ HR).
    + rewrite chainA_arr in HR. exact (False_ind _ HR).
    + rewrite chainA_all in HR.
      apply in_flat_map in HR. destruct HR as [C [HC HR]].
      apply eq_or_false in HR. subst R.
      destruct (Hsc (ExTyCons D B) A0 (ty_shift_ctx Sx 0) (tExTy tg (Some B)) C HC) as [Psi_p [Ht Hsub]].
      apply tmatch_exty_some_inv in Ht. destruct Ht as [Psi [B0 [Heq [Eb Ht]]]]. subst Psi_p.
      apply typ_eqb_eq in Eb. subst B0.
      exists Psi. split; [exact Ht | ].
      eapply s_tapp. exact Hsub.
Qed.

(* ============================================================ *)
(*   Soundness of the mutual decision procedures                *)
(* ============================================================ *)

Lemma nonemptyb_false : forall C, nonemptyb C = false -> C = CtxEmpty.
Proof.
  intros C H. destruct C; simpl in H; try discriminate; reflexivity.
Qed.

Lemma nonemptyb_spec : forall C, nonemptyb C = true -> NonEmpty C.
Proof.
  intros C H. destruct C as [| B | e Sx | B Sx]; simpl in H; try discriminate.
  - exact (ne_τ B).
  - exact (ne_app e Sx).
  - exact (ne_tapp B Sx).
Qed.

Definition tyDs (n : nat) : Prop :=
  forall Γ Σ e A, In A (tyD n Γ Σ e) -> ty Γ Σ e A.

Definition scDs (n : nat) : Prop :=
  forall Δ A Σ t R, In R (scD n Δ A Σ t) ->
    exists Psi, tmatch t Psi = true /\ sub_ctx Δ A Σ Psi R.

Definition infDs (n : nat) : Prop :=
  forall Γ Σ A, In A (infD n Γ Σ) -> infs Γ Σ A.

Lemma tyD_scD_infD_sound : forall n, tyDs n /\ scDs n /\ infDs n.
Proof.
  induction n as [| n' IH].
  - split; [| split].
    + intros Γ Σ e A H. simpl in H. exact (False_ind _ H).
    + intros Δ A Σ t R H. simpl in H. exact (False_ind _ H).
    + intros Γ Σ A H. simpl in H. exact (False_ind _ H).
  - destruct IH as [Hty [Hsc Hinf]].
    split; [| split].
    + (* tyDs (S n') *)
      intros Γ Σ e A H.
      destruct e as [n0 | x | e0 | e1 e2 | e0 A0 | e0 | e0 A0].
      * (* Lit *)
        simpl in H. apply in_app_or in H. destruct H as [H | H].
        -- destruct (andb (negb (nonemptyb Σ)) (TRegularD Γ)) eqn:E.
           ++ apply eq_or_false in H. subst A.
              apply Bool.andb_true_iff in E. destruct E as [En ET].
              apply Bool.negb_true_iff in En.
              assert (Heq : Σ = CtxEmpty) by (apply nonemptyb_false; exact En). subst Σ.
              apply ty_lit. apply TRegularD_sound. exact ET.
           ++ exact (False_ind _ H).
        -- destruct (nonemptyb Σ) eqn:Enb.
           ++ apply in_flat_map in H. destruct H as [Aty [HAty HR]].
              destruct (Hsc (SepCons Γ) Aty Σ (tB (SepCons Γ)) A HR) as [Psi [Ht Hsub]].
              assert (Psi = SepCons Γ) by (symmetry; apply tmatch_base_inv; exact Ht). subst Psi.
              eapply ty_sub with (A := Aty).
              ** apply Hty. exact HAty.
              ** apply nonemptyb_spec. exact Enb.
              ** exact I.
              ** exact Hsub.
           ++ exact (False_ind _ H).
      * (* Var *)
        simpl in H. apply in_app_or in H. destruct H as [H | H].
        -- destruct (andb (negb (nonemptyb Σ)) (TRegularD Γ)) eqn:E.
           ++ apply Bool.andb_true_iff in E. destruct E as [En ET].
              apply Bool.negb_true_iff in En.
              assert (Heq : Σ = CtxEmpty) by (apply nonemptyb_false; exact En). subst Σ.
              destruct (lookupTmD Γ x) as [B|] eqn:El.
              ** apply eq_or_false in H. subst A.
                 apply ty_var with (A := B).
                 --- apply TRegularD_sound. exact ET.
                 --- apply lookupTmD_sound. exact El.
              ** exact (False_ind _ H).
           ++ exact (False_ind _ H).
        -- destruct (nonemptyb Σ) eqn:Enb.
           ++ apply in_flat_map in H. destruct H as [Aty [HAty HR]].
              destruct (Hsc (SepCons Γ) Aty Σ (tB (SepCons Γ)) A HR) as [Psi [Ht Hsub]].
              assert (Psi = SepCons Γ) by (symmetry; apply tmatch_base_inv; exact Ht). subst Psi.
              eapply ty_sub with (A := Aty).
              ** apply Hty. exact HAty.
              ** apply nonemptyb_spec. exact Enb.
              ** exact I.
              ** exact Hsub.
           ++ exact (False_ind _ H).
      * (* Lam *)
        simpl in H. apply in_app_or in H. destruct H as [H | H].
        -- destruct Σ as [| B | e2 Sx | B Sx].
           ++ exact (False_ind _ H).
           ++ destruct B as [| y | A1 B1 | A00].
              ** cbn [In] in H. exact (False_ind _ H).
              ** cbn [In] in H. exact (False_ind _ H).
              ** apply in_flat_map in H. destruct H as [C [HC HR]].
                 apply eq_or_false in HR. subst A.
                 apply ty_lam1 with (A := A1) (B := B1) (C := C).
                 apply Hty. exact HC.
              ** cbn [In] in H. exact (False_ind _ H).
           ++ exact (False_ind _ H).
           ++ exact (False_ind _ H).
        -- destruct Σ as [| B | e2 Sx | B Sx].
           ++ exact (False_ind _ H).
           ++ exact (False_ind _ H).
           ++ apply in_flat_map in H. destruct H as [A1 [HA1 HR]].
              apply in_flat_map in HR. destruct HR as [B1 [HB1 HR]].
              apply eq_or_false in HR. subst A.
              eapply ty_lam2 with (Σ := Sx) (e2 := e2) (A := A1) (B := B1).
              ** apply Hty. exact HA1.
              ** apply Hty. exact HB1.
           ++ exact (False_ind _ H).
      * (* App *)
        simpl in H. apply in_flat_map in H. destruct H as [T [HT HR]].
        destruct T as [| n0 | A1 B1 | A00].
        -- cbn [In] in HR. exact (False_ind _ HR).
        -- cbn [In] in HR. exact (False_ind _ HR).
        -- apply eq_or_false in HR. subst A.
           apply ty_app with (A := A1) (B := B1).
           apply Hty. exact HT.
        -- cbn [In] in HR. exact (False_ind _ HR).
      * (* Ann *)
        simpl in H. apply in_app_or in H. destruct H as [H | H].
        -- destruct (negb (nonemptyb Σ)) eqn:En.
           ++ apply Bool.negb_true_iff in En.
              assert (Heq : Σ = CtxEmpty) by (apply nonemptyb_false; exact En). subst Σ.
              destruct (nonemptyL (tyD n' Γ (CtxTyp A0) e0)) eqn:Enl.
              ** apply eq_or_false in H. subst A.
                 apply nonemptyL_spec in Enl. destruct Enl as [B HB].
                 apply ty_ann with (A := A0) (B := B).
                 apply Hty. exact HB.
              ** exact (False_ind _ H).
           ++ exact (False_ind _ H).
        -- destruct (nonemptyb Σ) eqn:Enb.
           ++ apply in_flat_map in H. destruct H as [Aty [HAty HR]].
              destruct (Hsc (SepCons Γ) Aty Σ (tB (SepCons Γ)) A HR) as [Psi [Ht Hsub]].
              assert (Psi = SepCons Γ) by (symmetry; apply tmatch_base_inv; exact Ht). subst Psi.
              eapply ty_sub with (A := Aty).
              ** apply Hty. exact HAty.
              ** apply nonemptyb_spec. exact Enb.
              ** exact I.
              ** exact Hsub.
           ++ exact (False_ind _ H).
      * (* TLam *)
        simpl in H. apply in_app_or in H. destruct H as [H | H].
        -- destruct Σ as [| B | e2 Sx | B Sx].
           ++ apply in_flat_map in H. destruct H as [B0 [HB HR]].
              apply eq_or_false in HR. subst A.
              apply ty_tabs with (A := B0).
              apply Hty. exact HB.
           ++ destruct B as [| y | A1 B1 | A00].
              ** cbn [In] in H. exact (False_ind _ H).
              ** cbn [In] in H. exact (False_ind _ H).
              ** cbn [In] in H. exact (False_ind _ H).
              ** destruct (nonemptyL (tyD n' (TyCons Γ) (CtxTyp A00) e0)) eqn:Enl.
                 --- apply eq_or_false in H. subst A.
                     apply nonemptyL_spec in Enl. destruct Enl as [B0 HB].
                     apply ty_tabs_ty with (A := A00) (B := B0).
                     apply Hty. exact HB.
                 --- exact (False_ind _ H).
           ++ exact (False_ind _ H).
           ++ exact (False_ind _ H).
        -- destruct (nonemptyb Σ) eqn:Enb.
           ++ apply in_flat_map in H. destruct H as [Aty [HAty HR]].
              destruct (Hsc (SepCons Γ) Aty Σ (tB (SepCons Γ)) A HR) as [Psi [Ht Hsub]].
              assert (Psi = SepCons Γ) by (symmetry; apply tmatch_base_inv; exact Ht). subst Psi.
              eapply ty_sub with (A := Aty).
              ** apply Hty. exact HAty.
              ** apply nonemptyb_spec. exact Enb.
              ** exact I.
              ** exact Hsub.
           ++ exact (False_ind _ H).
      * (* TApp *)
        simpl in H. apply in_flat_map in H. destruct H as [T [HT HR]].
        destruct T as [| n0 | A1 B1 | A00].
        -- cbn [In] in HR. exact (False_ind _ HR).
        -- cbn [In] in HR. exact (False_ind _ HR).
        -- cbn [In] in HR. exact (False_ind _ HR).
        -- apply eq_or_false in HR. subst A.
           apply ty_tapp with (B := A00) (A := A0).
           ++ apply Hty. exact HT.
           ++ reflexivity.
    + (* scDs (S n') *)
      intros Δ A Σ t R H. simpl in H.
      destruct Σ as [| B | e Sx | B Sx].
      * (* CtxEmpty *)
        destruct (andb (SRegularD Δ) (andb (tmatch t Δ) (closeD Δ A))) eqn:E.
        -- apply Bool.andb_true_iff in E. destruct E as [ES E2].
           apply Bool.andb_true_iff in E2. destruct E2 as [Et Ec].
           destruct (grdTypD Δ A) as [A'|] eqn:Eg.
           ++ apply eq_or_false in H. subst R.
              exists Δ. split; [exact Et | ].
              eapply s_empty.
              ** apply SRegularD_sound. exact ES.
              ** apply closeD_sound. exact Ec.
              ** apply grdTypD_sound. exact Eg.
           ++ exact (False_ind _ H).
        -- exact (False_ind _ H).
      * (* CtxTyp B *)
        destruct (existsb (fun Psi' => tmatch t Psi') (subAll (tsize A + tsize B) Δ A Pos B)) eqn:Eb.
        -- apply eq_or_false in H. subst R.
           apply existsb_exists in Eb. destruct Eb as [Psi [HPsi Ht]].
           exists Psi. split; [exact Ht | ].
           eapply s_typ.
           exact (subAll_sound (tsize A + tsize B) Δ A Pos B Psi HPsi).
        -- exact (False_ind _ H).
      * (* CtxTrm e Sx *)
        exact (chainT_sound infD scD tyD n' Hinf Hsc Hty (fuelAt Δ A) Δ A e Sx t R H).
      * (* CtxTApp B Sx *)
        exact (chainA_sound scD n' Hsc (fuelAt Δ A) Δ A B Sx t R H).
    + (* infDs (S n') *)
      intros Γ Σ A H. simpl in H.
      destruct Σ as [| B | e Sx | B Sx].
      * exact (False_ind _ H).
      * (* CtxTyp B *)
        destruct (andb (TRegularD Γ) (RegularTypD Γ B)) eqn:E.
        -- apply Bool.andb_true_iff in E. destruct E as [ET ER].
           apply eq_or_false in H. subst A.
           apply infs_z.
           ++ apply TRegularD_sound. exact ET.
           ++ apply RegularTypD_sound. exact ER.
        -- exact (False_ind _ H).
      * (* CtxTrm e Sx *)
        apply in_flat_map in H. destruct H as [A0 [HA0 HR]].
        apply in_flat_map in HR. destruct HR as [B0 [HB0 HR]].
        apply eq_or_false in HR. subst A.
        eapply infs_s with (A := A0) (B := B0).
        -- apply Hty. exact HA0.
        -- apply Hinf. exact HB0.
      * exact (False_ind _ H).
Qed.

(* ============================================================ *)
(*   Fuel monotonicity helpers and completeness setup           *)
(* ============================================================ *)

Lemma fuelAt_pos : forall D A, 0 < fuelAt D A.
Proof.
  intros D A. unfold fuelAt.
  assert (H1 : 1 * 1 <= (wfst D A + 1) * (esum D + 2))
    by (apply Nat.mul_le_mono; lia).
  lia.
Qed.

Lemma nonemptyL_In : forall (l : list Typ) x, In x l -> nonemptyL l = true.
Proof. intros l x H. destruct l as [| a l]; [exact (False_ind _ H) | reflexivity]. Qed.

Lemma lookupTy_no_ex : forall D x, lookupTy D x -> forall A, lookupExTy D x A -> False.
Proof.
  intros D x Ht. induction Ht; intros A0 He.
  - inversion He.
  - inversion He; subst; eapply IHHt; eassumption.
  - inversion He; subst; eapply IHHt; eassumption.
  - inversion He; subst; eapply IHHt; eassumption.
  - inversion He; subst; eapply IHHt; eassumption.
  - inversion He.
Qed.

Lemma lookupTyD_no_ex : forall D x, lookupTy D x -> lookupExTyD D x = None.
Proof.
  intros D x Ht. destruct (lookupExTyD D x) as [A|] eqn:E; [|reflexivity].
  exfalso. eapply lookupTy_no_ex; [exact Ht | apply lookupExTyD_sound; exact E].
Qed.

Lemma grdTypD_eq : forall D A A', grd_typ D A A' -> grdTypD D A = Some A'.
Proof.
  intros D A A' H. induction H; simpl.
  - reflexivity.
  - rewrite (lookupExTyD_complete Δ x A H). reflexivity.
  - rewrite (lookupTyD_no_ex Δ x H). rewrite (lookupTyD_complete Δ x H). reflexivity.
  - rewrite IHgrd_typ1, IHgrd_typ2. reflexivity.
  - rewrite IHgrd_typ. reflexivity.
Qed.

Lemma tmatch_exy_none : forall Ψ B, tmatch (tExTy (tB Ψ) None) (ExTyCons Ψ B) = true.
Proof. intros. change (tmatch (tB Ψ) Ψ = true). apply tmatch_base. Qed.

Lemma tmatch_exy_some : forall Ψ B, tmatch (tExTy (tB Ψ) (Some B)) (ExTyCons Ψ B) = true.
Proof.
  intros. change (andb (typ_eqb B B) (tmatch (tB Ψ) Ψ) = true).
  rewrite typ_eqb_refl, tmatch_base. reflexivity.
Qed.

Lemma tmatch_ex_base : forall Ψ, tmatch (tEx (tB Ψ)) (ExCons Ψ) = true.
Proof. intros. rewrite tmatch_ex. apply tmatch_base. Qed.

(* Mutual induction principles *)
Scheme ty_mut := Induction for ty Sort Prop
  with sub_ctx_mut := Induction for sub_ctx Sort Prop
  with infs_mut := Induction for infs Sort Prop.
Combined Scheme ty_all from ty_mut, sub_ctx_mut, infs_mut.

Definition ty_comp (Γ : Env) (Σ : Context) (e : Trm) (A : Typ)
    (H : ty Γ Σ e A) : Prop :=
  exists n, forall m, n <= m -> In A (tyD m Γ Σ e).

Definition infs_comp (Γ : Env) (Σ : Context) (A : Typ)
    (H : infs Γ Σ A) : Prop :=
  exists n, forall m, n <= m -> In A (infD m Γ Σ).

Definition sub_ctx_comp (Δ : Env) (A : Typ) (Σ : Context) (Ψ : Env) (R : Typ)
    (H : sub_ctx Δ A Σ Ψ R) : Prop :=
  (forall t, tmatch t Ψ = true ->
     exists n, forall m, n <= m -> In R (scD m Δ A Σ t))
  /\ (match Σ with
      | CtxTrm tm Sx =>
          forall t, tmatch t Ψ = true ->
          forall efuel, fuelAt Δ A <= efuel ->
          exists k, forall cfuel, k <= cfuel ->
            In R (chainT infD scD tyD cfuel efuel Δ A tm Sx t)
      | _ => True
      end)
  /\ (match Σ with
      | CtxTApp B Sx =>
          forall t, tmatch t Ψ = true ->
          forall efuel, fuelAt Δ A <= efuel ->
          exists k, forall cfuel, k <= cfuel ->
            In R (chainA scD cfuel efuel Δ A B Sx t)
      | _ => True
      end).

Lemma nonemptyb_true : forall C, NonEmpty C -> nonemptyb C = true.
Proof. intros C H. destruct H; reflexivity. Qed.

Lemma existsb_true : forall (X : Type) (l : list X) (f : X -> bool),
  (exists x, In x l /\ f x = true) -> existsb f l = true.
Proof.
  intros X l f [x [Hx Hf]]. induction l as [| a l IH].
  - exact (False_ind _ Hx).
  - simpl. destruct (f a) eqn:E; [reflexivity|].
    destruct Hx as [Heq | Hx].
    + subst a. rewrite Hf in E. discriminate.
    + apply IH. exact Hx.
Qed.

Lemma tmatch_ex' : forall t Ψ, tmatch t Ψ = true -> tmatch (tEx t) (ExCons Ψ) = true.
Proof. intros. change (tmatch t Ψ = true). exact H. Qed.

Lemma tmatch_exy_none' : forall t Ψ B, tmatch t Ψ = true ->
  tmatch (tExTy t None) (ExTyCons Ψ B) = true.
Proof. intros. change (tmatch t Ψ = true). exact H. Qed.

Lemma tmatch_exy_some' : forall t Ψ B, tmatch t Ψ = true ->
  tmatch (tExTy t (Some B)) (ExTyCons Ψ B) = true.
Proof.
  intros. change (andb (typ_eqb B B) (tmatch t Ψ) = true).
  rewrite typ_eqb_refl, H. reflexivity.
Qed.

Lemma completeness_all :
  (forall Γ Σ e A (H : ty Γ Σ e A), ty_comp Γ Σ e A H) /\
  (forall Δ A Σ Ψ R (H : sub_ctx Δ A Σ Ψ R), sub_ctx_comp Δ A Σ Ψ R H) /\
  (forall Γ Σ A (H : infs Γ Σ A), infs_comp Γ Σ A H).
Proof.
  apply (ty_all ty_comp sub_ctx_comp infs_comp).
  - (* ty_lit *)
    intros Γ n t. unfold ty_comp.
    exists 1. intros m Hm. destruct m as [| m']; [lia|].
    cbn [tyD]. rewrite (TRegularD_complete Γ t). cbn. left. reflexivity.
  - (* ty_var *)
    intros Γ x A t l. unfold ty_comp.
    exists 1. intros m Hm. destruct m as [| m']; [lia|].
    cbn [tyD]. rewrite (TRegularD_complete Γ t).
    rewrite (lookupTmD_complete Γ x A l). cbn. left. reflexivity.
  - (* ty_ann *)
    intros Γ e A B t IH. unfold ty_comp in IH. destruct IH as [n1 H1]. unfold ty_comp.
    exists (n1 + 1). intros m Hm. destruct m as [| m']; [lia|].
    assert (Hn : n1 <= m') by lia. specialize (H1 m' Hn).
    cbn [tyD]. rewrite (nonemptyL_In _ _ H1). cbn. left. reflexivity.
  - (* ty_app *)
    intros Γ Σ e1 e2 A B t IH. unfold ty_comp in IH. destruct IH as [n1 H1]. unfold ty_comp.
    exists (n1 + 1). intros m Hm. destruct m as [| m']; [lia|].
    assert (Hn : n1 <= m') by lia. specialize (H1 m' Hn).
    cbn [tyD]. apply in_flat_map. exists (A `→ B). split.
    + exact H1.
    + cbn. left. reflexivity.
  - (* ty_lam1 *)
    intros Γ A B C e t IH. unfold ty_comp in IH. destruct IH as [n1 H1]. unfold ty_comp.
    exists (n1 + 1). intros m Hm. destruct m as [| m']; [lia|].
    assert (Hn : n1 <= m') by lia. specialize (H1 m' Hn).
    cbn [tyD]. apply in_or_app. left. apply in_flat_map. exists C. split.
    + exact H1.
    + cbn. left. reflexivity.
  - (* ty_lam2 *)
    intros Γ Σ A B e e2 t1 IH1 t2 IH2. unfold ty_comp in IH1, IH2.
    destruct IH1 as [n1 H1]. destruct IH2 as [n2 H2]. unfold ty_comp.
    exists (max n1 n2 + 1). intros m Hm. destruct m as [| m']; [lia|].
    assert (Hn1 : n1 <= m') by lia. assert (Hn2 : n2 <= m') by lia.
    specialize (H1 m' Hn1). specialize (H2 m' Hn2).
    cbn [tyD]. apply in_flat_map. exists A. split.
    + exact H1.
    + apply in_flat_map. exists B. split.
      * exact H2.
      * cbn. left. reflexivity.
  - (* ty_sub *)
    intros Γ Σ g A B t IH1 nΣ gc s IH2.
    unfold ty_comp in IH1. destruct IH1 as [n1 H1].
    unfold sub_ctx_comp in IH2. destruct IH2 as [H2sc [H2c H2a]].
    specialize (H2sc (tB (Γ ⋈)) (tmatch_base (Γ ⋈))).
    destruct H2sc as [n2 H2].
    assert (Enb : nonemptyb Σ = true) by (apply nonemptyb_true; exact nΣ).
    unfold ty_comp. exists (max n1 n2 + 1). intros m Hm. destruct m as [| m']; [lia|].
    assert (Hn1 : n1 <= m') by lia. assert (Hn2 : n2 <= m') by lia.
    specialize (H1 m' Hn1). specialize (H2 m' Hn2).
    destruct g as [n0 | x | e0 | e1 e2 | e0 A0 | e0 | e0 A0].
    + (* Lit *) cbn [tyD]. rewrite Enb. cbn. apply in_flat_map. exists A. split.
      * exact H1.
      * exact H2.
    + (* Var *) cbn [tyD]. rewrite Enb. cbn. apply in_flat_map. exists A. split.
      * exact H1.
      * exact H2.
    + (* Lam *) exfalso. exact gc.
    + (* App *) exfalso. exact gc.
    + (* Ann *) cbn [tyD]. rewrite Enb. cbn. apply in_flat_map. exists A. split.
      * exact H1.
      * exact H2.
    + (* TLam *) cbn [tyD]. rewrite Enb. cbn. apply in_or_app. right.
      apply in_flat_map. exists A. split.
      * exact H1.
      * exact H2.
    + (* TApp *) exfalso. exact gc.
  - (* ty_tabs *)
    intros Γ e A t IH. unfold ty_comp in IH. destruct IH as [n1 H1]. unfold ty_comp.
    exists (n1 + 1). intros m Hm. destruct m as [| m']; [lia|].
    assert (Hn : n1 <= m') by lia. specialize (H1 m' Hn).
    cbn [tyD]. apply in_or_app. left. apply in_flat_map. exists A. split.
    + exact H1.
    + cbn. left. reflexivity.
  - (* ty_tapp *)
    intros Γ Σ e A B B' t IH eB. unfold ty_comp in IH. destruct IH as [n1 H1]. unfold ty_comp.
    exists (n1 + 1). intros m Hm. destruct m as [| m']; [lia|].
    assert (Hn : n1 <= m') by lia. specialize (H1 m' Hn).
    cbn [tyD]. apply in_flat_map. exists (`∀ B). split.
    + exact H1.
    + cbn. rewrite eB. left. reflexivity.
  - (* ty_tabs_ty *)
    intros Γ e A B t IH. unfold ty_comp in IH. destruct IH as [n1 H1]. unfold ty_comp.
    exists (n1 + 1). intros m Hm. destruct m as [| m']; [lia|].
    assert (Hn : n1 <= m') by lia. specialize (H1 m' Hn).
    cbn [tyD]. rewrite (nonemptyL_In _ _ H1). cbn [In]. left. reflexivity.
  - (* s_empty *)
    intros Δ A A' s c g. cbn [sub_ctx_comp].
    split; [| split].
    + intros t Ht. exists 1. intros m Hm. destruct m as [| m']; [lia|].
      cbn [scD]. rewrite (SRegularD_complete Δ s). rewrite (closeD_complete Δ A c).
      rewrite Ht. rewrite (grdTypD_eq Δ A A' g). cbn. left. reflexivity.
    + exact I.
    + exact I.
  - (* s_typ *)
    intros Δ A B Ψ s0. cbn [sub_ctx_comp].
    split; [| split].
    + intros t Ht. exists 1. intros m Hm. destruct m as [| m']; [lia|].
      cbn [scD].
      assert (Hin : In Ψ (subAll (tsize A + tsize B) Δ A Pos B))
        by (apply subAll_complete; [exact s0 | lia]).
      assert (Hb : existsb (fun Psi' => tmatch t Psi') (subAll (tsize A + tsize B) Δ A Pos B) = true).
      { apply existsb_true. exists Ψ. split; [exact Hin | exact Ht]. }
      rewrite Hb. cbn. left. reflexivity.
    + exact I.
    + exact I.
  - (* s_trm_c *)
    intros Δ A B Σ Ψ e A' A'' D c g tTy IHTy sPrem IHSc. cbn [sub_ctx_comp].
    unfold ty_comp in IHTy. destruct IHTy as [n1 H1].
    unfold sub_ctx_comp in IHSc. destruct IHSc as [Hsc1 [Hsc2 Hsc3]].
    assert (HC : forall t, tmatch t Ψ = true ->
        forall efuel, fuelAt Δ (A `→ B) <= efuel ->
        exists k, forall cfuel, k <= cfuel ->
          In (A' `→ D) (chainT infD scD tyD cfuel efuel Δ (A `→ B) e Σ t)).
    { intros t Ht efuel Hfuel. destruct efuel as [| ef].
      - exfalso. pose proof (fuelAt_pos Δ (A `→ B)). lia.
      - destruct (Hsc1 t Ht) as [n2 H2].
        exists (max n1 n2). intros cfuel Hc.
        rewrite chainT_arr. apply in_or_app. left.
        rewrite (closeD_complete Δ A c). rewrite (grdTypD_eq Δ A A' g).
        assert (Hn1 : n1 <= cfuel) by lia. assert (Hn2 : n2 <= cfuel) by lia.
        specialize (H1 cfuel Hn1). specialize (H2 cfuel Hn2).
        rewrite (nonemptyL_In _ _ H1). cbn.
        apply in_flat_map. exists D. split.
        + exact H2.
        + cbn. left. reflexivity. }
    split.
    + intros t Ht. destruct (HC t Ht (fuelAt Δ (A `→ B)) (Nat.le_refl _)) as [k Hk].
      exists (k + 1). intros m Hm. destruct m as [| m']; [lia|].
      cbn [scD]. apply Hk. lia.
    + split; [exact HC | exact I].
  - (* s_trm_o *)
    intros Δ A B e Σ Ψ C D Ω o tTy IHTy sSub sPrem IHSc. cbn [sub_ctx_comp].
    unfold ty_comp in IHTy. destruct IHTy as [n1 H1].
    unfold sub_ctx_comp in IHSc. destruct IHSc as [Hsc1 [Hsc2 Hsc3]].
    assert (HC : forall t, tmatch t Ψ = true ->
        forall efuel, fuelAt Δ (A `→ B) <= efuel ->
        exists k, forall cfuel, k <= cfuel ->
          In (C `→ D) (chainT infD scD tyD cfuel efuel Δ (A `→ B) e Σ t)).
    { intros t Ht efuel Hfuel. destruct efuel as [| ef].
      - exfalso. pose proof (fuelAt_pos Δ (A `→ B)). lia.
      - destruct (Hsc1 t Ht) as [n2 H2].
        exists (max n1 n2). intros cfuel Hc.
        rewrite chainT_arr. apply in_or_app. right.
        rewrite (openD_complete Δ A o). cbn.
        assert (Hn1 : n1 <= cfuel) by lia. assert (Hn2 : n2 <= cfuel) by lia.
        specialize (H1 cfuel Hn1). specialize (H2 cfuel Hn2).
        apply in_flat_map. exists C. split.
        + exact H1.
        + apply in_flat_map. exists Ω. split.
          * apply subAll_complete; [exact sSub | lia].
          * apply in_flat_map. exists D. split.
            { exact H2. }
            { cbn. left. reflexivity. } }
    split.
    + intros t Ht. destruct (HC t Ht (fuelAt Δ (A `→ B)) (Nat.le_refl _)) as [k Hk].
      exists (k + 1). intros m Hm. destruct m as [| m']; [lia|].
      cbn [scD]. apply Hk. lia.
    + split; [exact HC | exact I].
  - (* s_alll *)
    intros Δ A e Σ Ψ B C D sPrem IHSc. cbn [sub_ctx_comp].
    unfold sub_ctx_comp in IHSc. destruct IHSc as [Hsc1 [Hsc2 Hsc3]].
    assert (HC : forall t, tmatch t Ψ = true ->
        forall efuel, fuelAt Δ (`∀ A) <= efuel ->
        exists k, forall cfuel, k <= cfuel ->
          In (C `→ D) (chainT infD scD tyD cfuel efuel Δ (`∀ A) e Σ t)).
    { intros t Ht efuel. induction efuel as [| ef IHef]; intros Hfuel.
      - exfalso. pose proof (fuelAt_pos Δ (`∀ A)). lia.
      - assert (Hfa : fuelAt (Δ, ^) A <= ef)
          by (rewrite fuelAt_all in Hfuel; lia).
        destruct (Hsc2 (tExTy t None) (tmatch_exy_none' t Ψ B Ht) ef Hfa) as [k Hk].
        exists k. intros cfuel Hc.
        rewrite chainT_all. apply in_or_app. left. apply in_flat_map.
        exists (ty_shift C 0 `→ ty_shift D 0). split.
        + apply Hk. exact Hc.
        + cbn [unshiftArrL]. rewrite !ty_unshift_shift. cbn. left. reflexivity. }
    split.
    + intros t Ht. destruct (HC t Ht (fuelAt Δ (`∀ A)) (Nat.le_refl _)) as [k Hk].
      exists (k + 1). intros m Hm. destruct m as [| m']; [lia|].
      cbn [scD]. apply Hk. lia.
    + split; [exact HC | exact I].
  - (* s_alll_no *)
    intros Δ A e Σ Ψ C D sPrem IHSc. cbn [sub_ctx_comp].
    unfold sub_ctx_comp in IHSc. destruct IHSc as [Hsc1 [Hsc2 Hsc3]].
    assert (HC : forall t, tmatch t Ψ = true ->
        forall efuel, fuelAt Δ (`∀ A) <= efuel ->
        exists k, forall cfuel, k <= cfuel ->
          In (C `→ D) (chainT infD scD tyD cfuel efuel Δ (`∀ A) e Σ t)).
    { intros t Ht efuel. induction efuel as [| ef IHef]; intros Hfuel.
      - exfalso. pose proof (fuelAt_pos Δ (`∀ A)). lia.
      - assert (Hfa : fuelAt (Δ, ^) A <= ef)
          by (rewrite fuelAt_all in Hfuel; lia).
        destruct (Hsc2 (tEx t) (tmatch_ex' t Ψ Ht) ef Hfa) as [k Hk].
        exists k. intros cfuel Hc.
        rewrite chainT_all. apply in_or_app. right. apply in_flat_map.
        exists (ty_shift C 0 `→ ty_shift D 0). split.
        + apply Hk. exact Hc.
        + cbn [unshiftArrL]. rewrite !ty_unshift_shift. cbn. left. reflexivity. }
    split.
    + intros t Ht. destruct (HC t Ht (fuelAt Δ (`∀ A)) (Nat.le_refl _)) as [k Hk].
      exists (k + 1). intros m Hm. destruct m as [| m']; [lia|].
      cbn [scD]. apply Hk. lia.
    + split; [exact HC | exact I].
  - (* s_tapp *)
    intros Δ A B Σ Ψ C sPrem IHSc. cbn [sub_ctx_comp].
    unfold sub_ctx_comp in IHSc. destruct IHSc as [Hsc1 [Hsc2 Hsc3]].
    assert (HD : forall t, tmatch t Ψ = true ->
        forall efuel, fuelAt Δ (`∀ A) <= efuel ->
        exists k, forall cfuel, k <= cfuel ->
          In (`∀ C) (chainA scD cfuel efuel Δ (`∀ A) B Σ t)).
    { intros t Ht efuel Hfuel. destruct efuel as [| ef].
      - exfalso. pose proof (fuelAt_pos Δ (`∀ A)). lia.
      - destruct (Hsc1 (tExTy t (Some B)) (tmatch_exy_some' t Ψ B Ht)) as [n2 H2].
        exists n2. intros cfuel Hc.
        rewrite chainA_all. cbn. apply in_flat_map. exists C. split.
        + apply H2. exact Hc.
        + cbn. left. reflexivity. }
    split.
    + intros t Ht. destruct (HD t Ht (fuelAt Δ (`∀ A)) (Nat.le_refl _)) as [k Hk].
      exists (k + 1). intros m Hm. destruct m as [| m']; [lia|].
      cbn [scD]. apply Hk. lia.
    + split; [exact I | exact HD].
  - (* s_svar_trm *)
    intros Δ x e Σ A B C l sPrem IHSc. cbn [sub_ctx_comp].
    unfold sub_ctx_comp in IHSc. destruct IHSc as [Hsc1 [Hsc2 Hsc3]].
    assert (HC : forall t, tmatch t Δ = true ->
        forall efuel, fuelAt Δ (‶ x) <= efuel ->
        exists k, forall cfuel, k <= cfuel ->
          In (B `→ C) (chainT infD scD tyD cfuel efuel Δ (‶ x) e Σ t)).
    { intros t Ht efuel. induction efuel as [| ef IHef]; intros Hfuel.
      - exfalso. pose proof (fuelAt_pos Δ (‶ x)). lia.
      - assert (Hfa : fuelAt Δ A <= ef) by (pose proof (fuelAt_tvar Δ x A l); lia).
        destruct (Hsc2 (tB Δ) (tmatch_base Δ) ef Hfa) as [k Hk].
        exists k. intros cfuel Hc.
        rewrite chainT_tvar. apply in_or_app. right.
        rewrite Ht. cbn. rewrite (lookupExTyD_complete Δ x A l). cbn.
        apply in_flat_map. exists (B `→ C). split.
        + apply Hk. exact Hc.
        + cbn. left. reflexivity. }
    split.
    + intros t Ht. destruct (HC t Ht (fuelAt Δ (‶ x)) (Nat.le_refl _)) as [k Hk].
      exists (k + 1). intros m Hm. destruct m as [| m']; [lia|].
      cbn [scD]. apply Hk. lia.
    + split; [exact HC | exact I].
  - (* s_svar_tapp *)
    intros Δ x Σ A B C l sPrem IHSc. cbn [sub_ctx_comp].
    unfold sub_ctx_comp in IHSc. destruct IHSc as [Hsc1 [Hsc2 Hsc3]].
    assert (HD : forall t, tmatch t Δ = true ->
        forall efuel, fuelAt Δ (‶ x) <= efuel ->
        exists k, forall cfuel, k <= cfuel ->
          In (`∀ C) (chainA scD cfuel efuel Δ (‶ x) B Σ t)).
    { intros t Ht efuel. induction efuel as [| ef IHef]; intros Hfuel.
      - exfalso. pose proof (fuelAt_pos Δ (‶ x)). lia.
      - assert (Hfa : fuelAt Δ A <= ef) by (pose proof (fuelAt_tvar Δ x A l); lia).
        destruct (Hsc3 (tB Δ) (tmatch_base Δ) ef Hfa) as [k Hk].
        exists k. intros cfuel Hc.
        rewrite chainA_tvar. rewrite Ht. cbn. rewrite (lookupExTyD_complete Δ x A l). cbn.
        apply in_flat_map. exists (`∀ C). split.
        + apply Hk. exact Hc.
        + cbn. left. reflexivity. }
    split.
    + intros t Ht. destruct (HD t Ht (fuelAt Δ (‶ x)) (Nat.le_refl _)) as [k Hk].
      exists (k + 1). intros m Hm. destruct m as [| m']; [lia|].
      cbn [scD]. apply Hk. lia.
    + split; [exact I | exact HD].
  - (* s_evar_infers *)
    intros Δ x e Σ Ψ A i IHInf sSub. cbn [sub_ctx_comp].
    unfold infs_comp in IHInf. destruct IHInf as [n1 H1].
    assert (HC : forall t, tmatch t Ψ = true ->
        forall efuel, fuelAt Δ (‶ x) <= efuel ->
        exists k, forall cfuel, k <= cfuel ->
          In A (chainT infD scD tyD cfuel efuel Δ (‶ x) e Σ t)).
    { intros t Ht efuel Hfuel. destruct efuel as [| ef].
      - exfalso. pose proof (fuelAt_pos Δ (‶ x)). lia.
      - exists n1. intros cfuel Hc.
        rewrite chainT_tvar. apply in_or_app. left.
        apply in_flat_map. exists A. split.
        + apply H1. exact Hc.
        + rewrite (substEnvD_complete A x Δ Ψ sSub). rewrite Ht. cbn. left. reflexivity. }
    split.
    + intros t Ht. destruct (HC t Ht (fuelAt Δ (‶ x)) (Nat.le_refl _)) as [k Hk].
      exists (k + 1). intros m Hm. destruct m as [| m']; [lia|].
      cbn [scD]. apply Hk. lia.
    + split; [exact HC | exact I].
  - (* infs_z *)
    intros Γ A t r. unfold infs_comp.
    exists 1. intros m Hm. destruct m as [| m']; [lia|].
    cbn [infD]. rewrite (TRegularD_complete Γ t). rewrite (RegularTypD_complete Γ A r).
    cbn. left. reflexivity.
  - (* infs_s *)
    intros Γ e Σ A B t IH i IHi. unfold infs_comp in IH, IHi.
    destruct IH as [n1 H1]. destruct IHi as [n2 H2]. unfold infs_comp.
    exists (max n1 n2 + 1). intros m Hm. destruct m as [| m']; [lia|].
    assert (Hn1 : n1 <= m') by lia. assert (Hn2 : n2 <= m') by lia.
    specialize (H1 m' Hn1). specialize (H2 m' Hn2).
    cbn [infD]. apply in_flat_map. exists A. split.
    + exact H1.
    + apply in_flat_map. exists B. split.
      * exact H2.
      * cbn. left. reflexivity.
Qed.

(* ============================================================ *)
(*   Quantitative fuel bounds                                   *)
(* ============================================================ *)

Definition Fty (Σ : Context) (e : Trm) : nat :=
  (cwt Σ + trsize e + 2) * (cwt Σ + trsize e + csz Σ + 2).

Definition Finf (Σ : Context) : nat :=
  cwt Σ * cwt Σ + 6 * cwt Σ + csz Σ + 4.

Definition Ksc (Σ : Context) : nat :=
  cwt Σ * cwt Σ + 6 * cwt Σ + csz Σ + 10.

Lemma trsize_tm_shift : forall e k, trsize (tm_shift e k) = trsize e.
Proof.
  induction e as [n | x | e IHe | e1 IHe1 e2 IHe2 | e IHe A | e IHe | e IHe A]; intros k; simpl.
  - reflexivity.
  - reflexivity.
  - rewrite (IHe (Datatypes.S k)). reflexivity.
  - rewrite IHe1, IHe2. reflexivity.
  - rewrite IHe. reflexivity.
  - rewrite IHe. reflexivity.
  - rewrite IHe. reflexivity.
Qed.

Lemma cwt_tm_shift_ctx : forall Σ k, cwt (tm_shift_ctx Σ k) = cwt Σ.
Proof.
  induction Σ as [| A | e Sx IH | A Sx IH]; intros k; simpl.
  - reflexivity.
  - reflexivity.
  - rewrite trsize_tm_shift, IH. reflexivity.
  - rewrite IH. reflexivity.
Qed.

Lemma csz_tm_shift_ctx : forall Σ k, csz (tm_shift_ctx Σ k) = csz Σ.
Proof.
  induction Σ; intros k; simpl; auto.
Qed.

Lemma Ksc_shift : forall Σ, Ksc (ty_shift_ctx Σ 0) = Ksc Σ.
Proof.
  intros. unfold Ksc. rewrite cwt_ty_shift_ctx, csz_ty_shift_ctx. reflexivity.
Qed.

Lemma Ksc_shift_tm : forall e Σ,
  Ksc (CtxTrm (ty_shift_tm e 0) (ty_shift_ctx Σ 0)) = Ksc (CtxTrm e Σ).
Proof.
  intros. unfold Ksc. simpl. rewrite cwt_tszall_shift_tm, cwt_ty_shift_ctx, csz_ty_shift_ctx.
  reflexivity.
Qed.

Lemma nonempty_csz : forall Σ, NonEmpty Σ -> 1 <= csz Σ.
Proof. intros Σ H. destruct H; simpl; lia. Qed.

Lemma Ksc_Fty : forall Σ g, 1 <= csz Σ -> Ksc Σ + 1 <= Fty Σ g.
Proof.
  intros Σ g Hc. unfold Ksc, Fty. assert (Ht : 1 <= trsize g) by (destruct g; simpl; lia).
  nia.
Qed.

Lemma Ksc_tail_tm : forall e Σ, Ksc Σ + 1 <= Ksc (CtxTrm e Σ).
Proof.
  intros e Σ. unfold Ksc. simpl. assert (Ht : 1 <= trsize e) by (destruct e; simpl; lia). nia.
Qed.

Lemma Ksc_tail_app : forall B Σ, Ksc Σ + 1 <= Ksc (CtxTApp B Σ).
Proof. intros B Σ. unfold Ksc. simpl. nia. Qed.

Lemma FtyTyp_le_Ksc : forall A e Σ, Fty (CtxTyp A) e + 1 <= Ksc (CtxTrm e Σ).
Proof.
  intros A e Σ. unfold Fty, Ksc. simpl. nia.
Qed.

Lemma FtyEmpty_le_Ksc : forall e Σ, Fty CtxEmpty e + 1 <= Ksc (CtxTrm e Σ).
Proof.
  intros e Σ. unfold Fty, Ksc. simpl. nia.
Qed.

Lemma Finf_le_Ksc : forall Σ, Finf Σ + 1 <= Ksc Σ.
Proof. intros Σ. unfold Finf, Ksc. nia. Qed.

Lemma Finf_ctx_le_Ksc : forall e Σ, Finf (CtxTrm e Σ) + 1 <= Ksc (CtxTrm e Σ).
Proof. intros e Σ. unfold Finf, Ksc. simpl. nia. Qed.

Lemma FtyEmpty_le_Finf : forall e Σ, Fty CtxEmpty e + 1 <= Finf (CtxTrm e Σ).
Proof.
  intros e Σ. unfold Fty, Finf. simpl.
  assert (Ht : 1 <= trsize e) by (destruct e; simpl; lia). nia.
Qed.

Lemma Finf_tail_tm : forall e Σ, Finf Σ + 1 <= Finf (CtxTrm e Σ).
Proof.
  intros e Σ. unfold Finf. simpl. assert (Ht : 1 <= trsize e) by (destruct e; simpl; lia). nia.
Qed.

Lemma Finf_tail_app : forall B Σ, Finf Σ + 1 <= Finf (CtxTApp B Σ).
Proof. intros B Σ. unfold Finf. simpl. nia. Qed.

Lemma Ksc_shift_tail_app : forall B Σ, Ksc (ty_shift_ctx Σ 0) + 1 <= Ksc (CtxTApp B Σ).
Proof. intros B Σ. rewrite Ksc_shift. unfold Ksc. simpl. nia. Qed.

Lemma Fty_pos : forall Σ e, 1 <= Fty Σ e.
Proof.
  intros. unfold Fty. assert (Ht : 1 <= trsize e) by (destruct e; simpl; lia). nia.
Qed.

Lemma Finf_pos : forall Σ, 1 <= Finf Σ.
Proof. intros. unfold Finf. nia. Qed.

Lemma Ksc_pos : forall Σ, 1 <= Ksc Σ.
Proof. intros. unfold Ksc. nia. Qed.

Lemma Fty_empty_le : forall Σ g, 1 <= csz Σ -> Fty CtxEmpty g + 1 <= Fty Σ g.
Proof.
  intros Σ g Hc. unfold Fty. simpl.
  assert (Ht : 1 <= trsize g) by (destruct g; simpl; lia). nia.
Qed.

(* ============================================================ *)
(*   Quantitative completeness                                  *)
(* ============================================================ *)

Definition tyb (Γ : Env) (Σ : Context) (e : Trm) (A : Typ)
    (H : ty Γ Σ e A) : Prop :=
  forall k, Fty Σ e <= k -> In A (tyD k Γ Σ e).

Definition infb (Γ : Env) (Σ : Context) (A : Typ)
    (H : infs Γ Σ A) : Prop :=
  forall k, Finf Σ <= k -> In A (infD k Γ Σ).

Definition subb (Δ : Env) (A : Typ) (Σ : Context) (Ψ : Env) (R : Typ)
    (H : sub_ctx Δ A Σ Ψ R) : Prop :=
  (forall t, tmatch t Ψ = true ->
     forall k, Ksc Σ <= k -> In R (scD k Δ A Σ t))
  /\ (match Σ with
      | CtxTrm e Sx =>
          forall t, tmatch t Ψ = true ->
          forall ef k, fuelAt Δ A <= ef -> Ksc (CtxTrm e Sx) <= k ->
            In R (chainT infD scD tyD (k-1) ef Δ A e Sx t)
      | _ => True
      end)
  /\ (match Σ with
      | CtxTApp B Sx =>
          forall t, tmatch t Ψ = true ->
          forall ef k, fuelAt Δ A <= ef -> Ksc (CtxTApp B Sx) <= k ->
            In R (chainA scD (k-1) ef Δ A B Sx t)
      | _ => True
      end).

Lemma completeness_bound :
  (forall Γ Σ e A (H : ty Γ Σ e A), tyb Γ Σ e A H) /\
  (forall Δ A Σ Ψ R (H : sub_ctx Δ A Σ Ψ R), subb Δ A Σ Ψ R H) /\
  (forall Γ Σ A (H : infs Γ Σ A), infb Γ Σ A H).
Proof.
  apply (ty_all tyb subb infb).
  - (* ty_lit *)
    intros Γ n t. unfold tyb. intros k Hk.
    destruct k as [| k']; [exfalso; pose proof (Fty_pos CtxEmpty (Lit n)); lia|].
    cbn [tyD]. rewrite (TRegularD_complete Γ t). cbn. left. reflexivity.
  - (* ty_var *)
    intros Γ x A t l. unfold tyb. intros k Hk.
    destruct k as [| k']; [exfalso; pose proof (Fty_pos CtxEmpty (Var x)); lia|].
    cbn [tyD]. rewrite (TRegularD_complete Γ t).
    rewrite (lookupTmD_complete Γ x A l). cbn. left. reflexivity.
  - (* ty_ann *)
    intros Γ e A B t IH. unfold tyb in IH. unfold tyb. intros k Hk.
    destruct k as [| k']; [exfalso; pose proof (Fty_pos CtxEmpty (Ann e A)); lia|].
    assert (Hle : Fty (CtxTyp A) e <= k').
    { unfold Fty in *. simpl in *. nia. }
    specialize (IH k' Hle).
    cbn [tyD]. rewrite (nonemptyL_In _ _ IH). cbn. left. reflexivity.
  - (* ty_app *)
    intros Γ Σ e1 e2 A B t IH. unfold tyb in IH. unfold tyb. intros k Hk.
    destruct k as [| k']; [exfalso; pose proof (Fty_pos Σ (App e1 e2)); lia|].
    assert (Hle : Fty (CtxTrm e2 Σ) e1 <= k').
    { unfold Fty in *. simpl in *. nia. }
    specialize (IH k' Hle).
    cbn [tyD]. apply in_flat_map. exists (A `→ B). split.
    + exact IH.
    + cbn. left. reflexivity.
  - (* ty_lam1 *)
    intros Γ A B C e t IH. unfold tyb in IH. unfold tyb. intros k Hk.
    destruct k as [| k']; [exfalso; pose proof (Fty_pos (CtxTyp (A `→ B)) (Lam e)); lia|].
    assert (Hle : Fty (CtxTyp B) e <= k').
    { unfold Fty in *. simpl in *. nia. }
    specialize (IH k' Hle).
    cbn [tyD]. apply in_or_app. left. apply in_flat_map. exists C. split.
    + exact IH.
    + cbn. left. reflexivity.
  - (* ty_lam2 *)
    intros Γ Σ A B e e2 t1 IH1 t2 IH2. unfold tyb in IH1, IH2. unfold tyb. intros k Hk.
    destruct k as [| k']; [exfalso; pose proof (Fty_pos (CtxTrm e2 Σ) (Lam e)); lia|].
    assert (Hle1 : Fty CtxEmpty e2 <= k').
    { unfold Fty in *. simpl in *. nia. }
    assert (Hle2 : Fty (tm_shift_ctx Σ 0) e <= k').
    { unfold Fty in *. simpl in *. rewrite cwt_tm_shift_ctx, csz_tm_shift_ctx. nia. }
    specialize (IH1 k' Hle1). specialize (IH2 k' Hle2).
    cbn [tyD]. apply in_flat_map. exists A. split.
    + exact IH1.
    + apply in_flat_map. exists B. split.
      * exact IH2.
      * cbn. left. reflexivity.
  - (* ty_sub *)
    intros Γ Σ g A B t IH1 nΣ gc s IH2.
    unfold tyb in IH1. unfold subb in IH2. destruct IH2 as [Hsc [Hch Hca]].
    specialize (Hsc (tB (Γ ⋈)) (tmatch_base (Γ ⋈))).
    unfold tyb. intros k Hk.
    destruct k as [| k']; [exfalso; pose proof (Fty_pos Σ g); lia|].
    assert (Hc : 1 <= csz Σ) by (apply nonempty_csz; exact nΣ).
    assert (Hle1 : Fty CtxEmpty g <= k').
    { pose proof (Fty_empty_le Σ g Hc). lia. }
    assert (Hle2 : Ksc Σ <= k').
    { pose proof (Ksc_Fty Σ g Hc). lia. }
    specialize (IH1 k' Hle1). specialize (Hsc k' Hle2).
    assert (Enb : nonemptyb Σ = true) by (apply nonemptyb_true; exact nΣ).
    destruct g as [n0 | x | e0 | e1 e2 | e0 A0 | e0 | e0 A0].
    + (* Lit *) cbn [tyD]. rewrite Enb. cbn. apply in_flat_map. exists A. split.
      * exact IH1.
      * exact Hsc.
    + (* Var *) cbn [tyD]. rewrite Enb. cbn. apply in_flat_map. exists A. split.
      * exact IH1.
      * exact Hsc.
    + (* Lam *) exfalso. exact gc.
    + (* App *) exfalso. exact gc.
    + (* Ann *) cbn [tyD]. rewrite Enb. cbn. apply in_flat_map. exists A. split.
      * exact IH1.
      * exact Hsc.
    + (* TLam *) cbn [tyD]. rewrite Enb. cbn. apply in_or_app. right.
      apply in_flat_map. exists A. split.
      * exact IH1.
      * exact Hsc.
    + (* TApp *) exfalso. exact gc.
  - (* ty_tabs *)
    intros Γ e A t IH. unfold tyb in IH. unfold tyb. intros k Hk.
    destruct k as [| k']; [exfalso; pose proof (Fty_pos CtxEmpty (TLam e)); lia|].
    assert (Hle : Fty CtxEmpty e <= k').
    { unfold Fty in *. simpl in *. nia. }
    specialize (IH k' Hle).
    cbn [tyD]. apply in_or_app. left. apply in_flat_map. exists A. split.
    + exact IH.
    + cbn. left. reflexivity.
  - (* ty_tapp *)
    intros Γ Σ e A B B' t IH eB. unfold tyb in IH. unfold tyb. intros k Hk.
    destruct k as [| k']; [exfalso; pose proof (Fty_pos Σ (TApp e A)); lia|].
    assert (Hle : Fty (CtxTApp A Σ) e <= k').
    { unfold Fty in *. simpl in *. nia. }
    specialize (IH k' Hle).
    cbn [tyD]. apply in_flat_map. exists (`∀ B). split.
    + exact IH.
    + cbn. rewrite eB. left. reflexivity.
  - (* ty_tabs_ty *)
    intros Γ e A B t IH. unfold tyb in IH. unfold tyb. intros k Hk.
    destruct k as [| k']; [exfalso; pose proof (Fty_pos (CtxTyp (`∀ A)) (TLam e)); lia|].
    assert (Hle : Fty (CtxTyp A) e <= k').
    { unfold Fty in *. simpl in *. nia. }
    specialize (IH k' Hle).
    cbn [tyD]. rewrite (nonemptyL_In _ _ IH). cbn [In]. left. reflexivity.
  - (* s_empty *)
    intros Δ A A' s c g. cbn [subb]. split; [| split].
    + intros t Ht k Hk. destruct k as [| k']; [exfalso; pose proof (Ksc_pos CtxEmpty); lia|].
      cbn [scD]. rewrite (SRegularD_complete Δ s). rewrite (closeD_complete Δ A c).
      rewrite Ht. rewrite (grdTypD_eq Δ A A' g). cbn. left. reflexivity.
    + exact I.
    + exact I.
  - (* s_typ *)
    intros Δ A B Ψ s0. cbn [subb]. split; [| split].
    + intros t Ht k Hk. destruct k as [| k']; [exfalso; pose proof (Ksc_pos (CtxTyp B)); lia|].
      cbn [scD].
      assert (Hin : In Ψ (subAll (tsize A + tsize B) Δ A Pos B))
        by (apply subAll_complete; [exact s0 | lia]).
      assert (Hb : existsb (fun Psi' => tmatch t Psi') (subAll (tsize A + tsize B) Δ A Pos B) = true).
      { apply existsb_true. exists Ψ. split; [exact Hin | exact Ht]. }
      rewrite Hb. cbn. left. reflexivity.
    + exact I.
    + exact I.
  - (* s_trm_c *)
    intros Δ A B Σ Ψ e A' A'' D c g tTy IHTy sPrem IHSc. cbn [subb].
    unfold tyb in IHTy. unfold subb in IHSc. destruct IHSc as [Hsc [Hch Hca]].
    assert (HC : forall t, tmatch t Ψ = true ->
        forall ef k, fuelAt Δ (A `→ B) <= ef -> Ksc (CtxTrm e Σ) <= k ->
          In (A' `→ D) (chainT infD scD tyD (k-1) ef Δ (A `→ B) e Σ t)).
    { intros t Ht ef k Hef Hk.
      destruct ef as [| ef']; [exfalso; pose proof (fuelAt_pos Δ (A `→ B)); lia|].
      destruct k as [| k']; [exfalso; pose proof (Ksc_pos (CtxTrm e Σ)); lia|].
      replace (S k' - 1) with k' by lia.
      assert (Hk' : Ksc Σ <= k').
      { pose proof (Ksc_tail_tm e Σ). lia. }
      assert (Hty : Fty (CtxTyp A') e <= k').
      { pose proof (FtyTyp_le_Ksc A' e Σ). lia. }
      specialize (Hsc t Ht k' Hk'). specialize (IHTy k' Hty).
      rewrite chainT_arr. apply in_or_app. left.
      rewrite (closeD_complete Δ A c). rewrite (grdTypD_eq Δ A A' g).
      rewrite (nonemptyL_In _ _ IHTy). cbn.
      apply in_flat_map. exists D. split.
      + exact Hsc.
      + cbn. left. reflexivity. }
    split.
    + intros t Ht k Hk. destruct k as [| k']; [exfalso; pose proof (Ksc_pos (CtxTrm e Σ)); lia|].
      replace k' with (S k' - 1) by lia.
      cbn [scD]. apply (HC t Ht (fuelAt Δ (A `→ B)) (S k') (Nat.le_refl _) Hk).
    + split; [exact HC | exact I].
  - (* s_trm_o *)
    intros Δ A B e Σ Ψ C D Ω o tTy IHTy sSub sPrem IHSc. cbn [subb].
    unfold tyb in IHTy. unfold subb in IHSc. destruct IHSc as [Hsc [Hch Hca]].
    assert (HC : forall t, tmatch t Ψ = true ->
        forall ef k, fuelAt Δ (A `→ B) <= ef -> Ksc (CtxTrm e Σ) <= k ->
          In (C `→ D) (chainT infD scD tyD (k-1) ef Δ (A `→ B) e Σ t)).
    { intros t Ht ef k Hef Hk.
      destruct ef as [| ef']; [exfalso; pose proof (fuelAt_pos Δ (A `→ B)); lia|].
      destruct k as [| k']; [exfalso; pose proof (Ksc_pos (CtxTrm e Σ)); lia|].
      replace (S k' - 1) with k' by lia.
      assert (Hk' : Ksc Σ <= k').
      { pose proof (Ksc_tail_tm e Σ). lia. }
      assert (Hty : Fty CtxEmpty e <= k').
      { pose proof (FtyEmpty_le_Ksc e Σ). lia. }
      specialize (Hsc t Ht k' Hk'). specialize (IHTy k' Hty).
      rewrite chainT_arr. apply in_or_app. right.
      rewrite (openD_complete Δ A o). cbn.
      apply in_flat_map. exists C. split.
      + exact IHTy.
      + apply in_flat_map. exists Ω. split.
        * apply subAll_complete; [exact sSub | lia].
        * apply in_flat_map. exists D. split.
          { exact Hsc. }
          { cbn. left. reflexivity. } }
    split.
    + intros t Ht k Hk. destruct k as [| k']; [exfalso; pose proof (Ksc_pos (CtxTrm e Σ)); lia|].
      replace k' with (S k' - 1) by lia.
      cbn [scD]. apply (HC t Ht (fuelAt Δ (A `→ B)) (S k') (Nat.le_refl _) Hk).
    + split; [exact HC | exact I].
  - (* s_alll *)
    intros Δ A e Σ Ψ B C D sPrem IHSc. cbn [subb].
    unfold subb in IHSc. destruct IHSc as [Hsc [Hch Hca]].
    assert (HC : forall t, tmatch t Ψ = true ->
        forall ef k, fuelAt Δ (`∀ A) <= ef -> Ksc (CtxTrm e Σ) <= k ->
          In (C `→ D) (chainT infD scD tyD (k-1) ef Δ (`∀ A) e Σ t)).
    { intros t Ht ef k Hef Hk.
      induction ef as [| ef' IHef].
      - exfalso. pose proof (fuelAt_pos Δ (`∀ A)). lia.
      - assert (Hfa : fuelAt (Δ, ^) A <= ef')
          by (rewrite fuelAt_all in Hef; lia).
        assert (Hk' : Ksc (CtxTrm (ty_shift_tm e 0) (ty_shift_ctx Σ 0)) <= k).
        { rewrite Ksc_shift_tm. exact Hk. }
        specialize (Hch (tExTy t None) (tmatch_exy_none' t Ψ B Ht) ef' k Hfa Hk').
        rewrite chainT_all. apply in_or_app. left. apply in_flat_map.
        exists (ty_shift C 0 `→ ty_shift D 0). split.
        + exact Hch.
        + cbn [unshiftArrL]. rewrite !ty_unshift_shift. cbn. left. reflexivity. }
    split.
    + intros t Ht k Hk. destruct k as [| k']; [exfalso; pose proof (Ksc_pos (CtxTrm e Σ)); lia|].
      replace k' with (S k' - 1) by lia.
      cbn [scD]. apply (HC t Ht (fuelAt Δ (`∀ A)) (S k') (Nat.le_refl _) Hk).
    + split; [exact HC | exact I].
  - (* s_alll_no *)
    intros Δ A e Σ Ψ C D sPrem IHSc. cbn [subb].
    unfold subb in IHSc. destruct IHSc as [Hsc [Hch Hca]].
    assert (HC : forall t, tmatch t Ψ = true ->
        forall ef k, fuelAt Δ (`∀ A) <= ef -> Ksc (CtxTrm e Σ) <= k ->
          In (C `→ D) (chainT infD scD tyD (k-1) ef Δ (`∀ A) e Σ t)).
    { intros t Ht ef k Hef Hk.
      induction ef as [| ef' IHef].
      - exfalso. pose proof (fuelAt_pos Δ (`∀ A)). lia.
      - assert (Hfa : fuelAt (Δ, ^) A <= ef')
          by (rewrite fuelAt_all in Hef; lia).
        assert (Hk' : Ksc (CtxTrm (ty_shift_tm e 0) (ty_shift_ctx Σ 0)) <= k).
        { rewrite Ksc_shift_tm. exact Hk. }
        specialize (Hch (tEx t) (tmatch_ex' t Ψ Ht) ef' k Hfa Hk').
        rewrite chainT_all. apply in_or_app. right. apply in_flat_map.
        exists (ty_shift C 0 `→ ty_shift D 0). split.
        + exact Hch.
        + cbn [unshiftArrL]. rewrite !ty_unshift_shift. cbn. left. reflexivity. }
    split.
    + intros t Ht k Hk. destruct k as [| k']; [exfalso; pose proof (Ksc_pos (CtxTrm e Σ)); lia|].
      replace k' with (S k' - 1) by lia.
      cbn [scD]. apply (HC t Ht (fuelAt Δ (`∀ A)) (S k') (Nat.le_refl _) Hk).
    + split; [exact HC | exact I].
  - (* s_tapp *)
    intros Δ A B Σ Ψ C sPrem IHSc. cbn [subb].
    unfold subb in IHSc. destruct IHSc as [Hsc [Hch Hca]].
    assert (HD : forall t, tmatch t Ψ = true ->
        forall ef k, fuelAt Δ (`∀ A) <= ef -> Ksc (CtxTApp B Σ) <= k ->
          In (`∀ C) (chainA scD (k-1) ef Δ (`∀ A) B Σ t)).
    { intros t Ht ef k Hef Hk.
      destruct ef as [| ef']; [exfalso; pose proof (fuelAt_pos Δ (`∀ A)); lia|].
      destruct k as [| k']; [exfalso; pose proof (Ksc_pos (CtxTApp B Σ)); lia|].
      assert (Hk' : Ksc (ty_shift_ctx Σ 0) <= k').
      { rewrite Ksc_shift. pose proof (Ksc_tail_app B Σ). lia. }
      specialize (Hsc (tExTy t (Some B)) (tmatch_exy_some' t Ψ B Ht) k' Hk').
      rewrite chainA_all. cbn. apply in_flat_map. exists C. split.
      + replace (k' - 0) with k' by lia. exact Hsc.
      + cbn. left. reflexivity. }
    split.
    + intros t Ht k Hk. destruct k as [| k']; [exfalso; pose proof (Ksc_pos (CtxTApp B Σ)); lia|].
      replace k' with (S k' - 1) by lia.
      cbn [scD]. apply (HD t Ht (fuelAt Δ (`∀ A)) (S k') (Nat.le_refl _) Hk).
    + split; [exact I | exact HD].
  - (* s_svar_trm *)
    intros Δ x e Σ A B C l sPrem IHSc. cbn [subb].
    unfold subb in IHSc. destruct IHSc as [Hsc [Hch Hca]].
    assert (HC : forall t, tmatch t Δ = true ->
        forall ef k, fuelAt Δ (‶ x) <= ef -> Ksc (CtxTrm e Σ) <= k ->
          In (B `→ C) (chainT infD scD tyD (k-1) ef Δ (‶ x) e Σ t)).
    { intros t Ht ef k Hef Hk.
      induction ef as [| ef' IHef].
      - exfalso. pose proof (fuelAt_pos Δ (‶ x)). lia.
      - assert (Hfa : fuelAt Δ A <= ef') by (pose proof (fuelAt_tvar Δ x A l); lia).
        destruct k as [| k']; [exfalso; pose proof (Ksc_pos (CtxTrm e Σ)); lia|].
        specialize (Hch (tB Δ) (tmatch_base Δ) ef' (S k') Hfa Hk).
        rewrite chainT_tvar. apply in_or_app. right.
        rewrite Ht. cbn. rewrite (lookupExTyD_complete Δ x A l). cbn.
        apply in_flat_map. exists (B `→ C). split.
        + exact Hch.
        + cbn. left. reflexivity. }
    split.
    + intros t Ht k Hk. destruct k as [| k']; [exfalso; pose proof (Ksc_pos (CtxTrm e Σ)); lia|].
      replace k' with (S k' - 1) by lia.
      cbn [scD]. apply (HC t Ht (fuelAt Δ (‶ x)) (S k') (Nat.le_refl _) Hk).
    + split; [exact HC | exact I].
  - (* s_svar_tapp *)
    intros Δ x Σ A B C l sPrem IHSc. cbn [subb].
    unfold subb in IHSc. destruct IHSc as [Hsc [Hch Hca]].
    assert (HD : forall t, tmatch t Δ = true ->
        forall ef k, fuelAt Δ (‶ x) <= ef -> Ksc (CtxTApp B Σ) <= k ->
          In (`∀ C) (chainA scD (k-1) ef Δ (‶ x) B Σ t)).
    { intros t Ht ef k Hef Hk.
      induction ef as [| ef' IHef].
      - exfalso. pose proof (fuelAt_pos Δ (‶ x)). lia.
      - assert (Hfa : fuelAt Δ A <= ef') by (pose proof (fuelAt_tvar Δ x A l); lia).
        destruct k as [| k']; [exfalso; pose proof (Ksc_pos (CtxTApp B Σ)); lia|].
        specialize (Hca (tB Δ) (tmatch_base Δ) ef' (S k') Hfa Hk).
        rewrite chainA_tvar. rewrite Ht. cbn. rewrite (lookupExTyD_complete Δ x A l). cbn.
        apply in_flat_map. exists (`∀ C). split.
        + exact Hca.
        + cbn. left. reflexivity. }
    split.
    + intros t Ht k Hk. destruct k as [| k']; [exfalso; pose proof (Ksc_pos (CtxTApp B Σ)); lia|].
      replace k' with (S k' - 1) by lia.
      cbn [scD]. apply (HD t Ht (fuelAt Δ (‶ x)) (S k') (Nat.le_refl _) Hk).
    + split; [exact I | exact HD].
  - (* s_evar_infers *)
    intros Δ x e Σ Ψ A i IHInf sSub. cbn [subb].
    unfold infb in IHInf.
    assert (HC : forall t, tmatch t Ψ = true ->
        forall ef k, fuelAt Δ (‶ x) <= ef -> Ksc (CtxTrm e Σ) <= k ->
          In A (chainT infD scD tyD (k-1) ef Δ (‶ x) e Σ t)).
    { intros t Ht ef k Hef Hk.
      destruct ef as [| ef']; [exfalso; pose proof (fuelAt_pos Δ (‶ x)); lia|].
      destruct k as [| k']; [exfalso; pose proof (Ksc_pos (CtxTrm e Σ)); lia|].
      replace (S k' - 1) with k' by lia.
      assert (Hle : Finf (CtxTrm e Σ) <= k').
      { pose proof (Finf_ctx_le_Ksc e Σ). lia. }
      specialize (IHInf k' Hle).
      rewrite chainT_tvar. apply in_or_app. left.
      apply in_flat_map. exists A. split.
      + exact IHInf.
      + rewrite (substEnvD_complete A x Δ Ψ sSub). rewrite Ht. cbn. left. reflexivity. }
    split.
    + intros t Ht k Hk. destruct k as [| k']; [exfalso; pose proof (Ksc_pos (CtxTrm e Σ)); lia|].
      replace k' with (S k' - 1) by lia.
      cbn [scD]. apply (HC t Ht (fuelAt Δ (‶ x)) (S k') (Nat.le_refl _) Hk).
    + split; [exact HC | exact I].
  - (* infs_z *)
    intros Γ A t r. unfold infb. intros k Hk.
    destruct k as [| k']; [exfalso; pose proof (Finf_pos (CtxTyp A)); lia|].
    cbn [infD]. rewrite (TRegularD_complete Γ t). rewrite (RegularTypD_complete Γ A r).
    cbn. left. reflexivity.
  - (* infs_s *)
    intros Γ e Σ A B t IH i IHi. unfold tyb in IH. unfold infb in IHi. unfold infb. intros k Hk.
    destruct k as [| k']; [exfalso; pose proof (Finf_pos (CtxTrm e Σ)); lia|].
    assert (Hle1 : Fty CtxEmpty e <= k') by (pose proof (FtyEmpty_le_Finf e Σ); lia).
    assert (Hle2 : Finf Σ <= k') by (pose proof (Finf_tail_tm e Σ); lia).
    specialize (IH k' Hle1). specialize (IHi k' Hle2).
    cbn [infD]. apply in_flat_map. exists A. split.
    + exact IH.
    + apply in_flat_map. exists B. split.
      * exact IHi.
      * cbn. left. reflexivity.
Qed.

(* ============================================================ *)
(*   Decidability of typing                                     *)
(* ============================================================ *)

Theorem dec_ty : forall Γ Σ e,
  {A | ty Γ Σ e A} + {~ exists A, ty Γ Σ e A}.
Proof.
  intros Γ Σ e.
  destruct (tyD (Fty Σ e) Γ Σ e) as [| A L] eqn:E.
  - (* empty: no derivable type, by quantitative completeness *)
    right. intros [A HA].
    destruct completeness_bound as [Htyb _].
    unfold tyb in Htyb.
    pose proof (Htyb Γ Σ e A HA (Fty Σ e) (Nat.le_refl _)) as Hin.
    rewrite E in Hin. exact Hin.
  - (* nonempty: the head is a derivable type, by soundness *)
    left. exists A.
    destruct (tyD_scD_infD_sound (Fty Σ e)) as [Htyd _].
    unfold tyDs in Htyd.
    apply (Htyd Γ Σ e A). rewrite E. left. reflexivity.
Qed.
