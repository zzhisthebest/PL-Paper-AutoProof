Require Import strictness.cbpv.typing.

Require Export strictness.cbn.typing.
From Stdlib Require Import Logic.FunctionalExtensionality.
From Stdlib Require Import Logic.Eqdep_dec.
From Stdlib Require Import Arith PeanoNat.

Fixpoint translateType {n} (T : CbnTy n) : CompTy n * attrs n :=
    match T with
    | TUnit => (CF VUnit, lazyvector)
    | TSum γ1' T1 γ2' T2 =>
        let '(A1, γ1) := translateType T1 in
        let '(A2, γ2) := translateType T2 in
        (CF (VSum (VThunk (γ1' γ+ γ1) A1) (VThunk (γ2' γ+ γ2) A2)), lazyvector)
    | TProd γ1 T1 γ2 T2 =>
        let '(A1, γ1') := translateType T1 in
        let '(A2, γ2') := translateType T2 in
        (CF (VProd (VThunk (γ1 γ+ γ1') A1) (VThunk (γ2 γ+ γ2') A2)), lazyvector)
    | TArrow γInput q γ T1 T2 =>
        let '(A, γ1') := translateType T1 in
        let '(B, γ2') := translateType T2 in
        (CAbs (q C+ γ2' None) (VThunk (γInput γ+ γ1') A) (down_ty B), γ γ+ (γ↓ γ2'))
    end.

Definition translateContext {n} (Γ : cbnContext n) : context n :=
    fun (i : fin n) =>
        let '(τ, γ) := (Γ i) in
        let '(B, γ') := translateType τ in
        VThunk (γ γ+ γ') B.

Fixpoint translateTerm {n} (e : Term n) : Comp n :=
    match e with
    | tVar i => cForce (vVar i)
    | tAbs e => cAbs (translateTerm e)
    | tApp e1 e2 =>
        cApp (translateTerm e1) (vThunk (translateTerm e2))
    | tLet t1 t2 =>
        cLet (cRet (vThunk (translateTerm t1))) (translateTerm t2)
    | tUnit => cRet vUnit
    | tSeq e1 e2 =>
        cLet
            (translateTerm e1)
            (cSeq (vVar var_zero) ((ren_Comp shift) (translateTerm e2)))
    | tPair e1 e2 =>
        cRet (vPair (vThunk (translateTerm e1)) (vThunk (translateTerm e2)))
    | tInl e => cRet (vInl (vThunk (translateTerm e)))
    | tInr e => cRet (vInr (vThunk (translateTerm e)))
    | tSplit e1 e2 =>
        cLet
            (translateTerm e1)
            (cSplit
                (vVar var_zero)
                ((ren_Comp up2_ren') (translateTerm e2)))
    | tCase e e1 e2 =>
        cLet (translateTerm e)
            (cCase (vVar var_zero)
                ((ren_Comp up_ren') (translateTerm e1))
                ((ren_Comp up_ren') (translateTerm e2)))
    | tSub e => cSub (translateTerm e)
    end.

(* ---------- index & attribute insertion machinery ---------- *)
Fixpoint ins_ren (k : nat) {m} (i : fin m) {struct k} : fin (S m) :=
  match k with
  | 0 => Some i
  | S k' => match m as mm return fin mm -> fin (S mm) with
            | 0 => fun i => match i with end
            | S m' => fun i => match i with
                               | Some j => Some (@ins_ren k' m' j)
                               | None => None
                               end
            end i
  end.

Fixpoint ins_at (k : nat) {m} (γ : attrs m) {struct k} : attrs (S m) :=
  match k with
  | 0 => fun i => match i with Some j => γ j | None => Lazy end
  | S k' => match m as mm return attrs mm -> attrs (S mm) with
            | 0 => fun _ => fun _ => Lazy
            | S m' => fun δ => fun i => match i with
                                        | Some j => @ins_at k' m' (fun x => δ (Some x)) j
                                        | None => δ None
                                        end
            end γ
  end.

Lemma ins_ren_inj : forall b m (i j : fin m), @ins_ren b m i = @ins_ren b m j -> i = j.
Proof.
  induction b as [|b IH]; intros m i j H.
  - destruct m as [|m']; [destruct i|]. simpl in H. injection H as H. f_equal. exact H.
  - destruct m as [|m']; [destruct i|]. simpl in H.
    destruct i as [i'|], j as [j'|].
    + simpl in H. injection H as H. assert (i' = j') as -> by (apply IH; exact H). reflexivity.
    + simpl in H. discriminate.
    + simpl in H. discriminate.
    + reflexivity.
Qed.
Arguments ins_ren_inj {b m i j} _.

Lemma up_ren_ins_ren : forall b m, @up_ren m (S m) (@ins_ren b m) = @ins_ren (S b) (S m).
Proof.
  intros b m. apply functional_extensionality. intros i.
  destruct i as [i'|]; simpl; reflexivity.
Qed.

Lemma up2_ren_ins_ren : forall b m, @up_ren (S m) (S (S m)) (@up_ren m (S m) (@ins_ren b m)) = @ins_ren (S (S b)) (S (S m)).
Proof.
  intros b m. rewrite up_ren_ins_ren.
  apply functional_extensionality. intros i.
  destruct i as [i'|]; simpl; reflexivity.
Qed.

Lemma ins_at_image : forall k m (δ : attrs m) (i : fin m),
  ins_at k δ (ins_ren k i) = δ i.
Proof.
  induction k as [|k IH]; intros m δ i.
  - destruct m as [|m']; [destruct i|]. simpl. destruct i; reflexivity.
  - destruct m as [|m']; [destruct i|]. simpl. destruct i as [j|].
    + simpl. apply IH.
    + reflexivity.
Qed.

Lemma ins_at_head_pt : forall b m q (δ : attrs m) (j : fin (S (S m))),
  @ins_at (S b) (S m) (q .: δ) j = (q .: @ins_at b m δ) j.
Proof.
  intros b m q δ j. destruct m as [|m'].
  - destruct j as [j'|]; [|reflexivity].
    destruct j' as [j''|]; [destruct j''|reflexivity].
  - simpl. destruct j as [j'|]; reflexivity.
Qed.

Lemma ins_at_head : forall b m q (δ : attrs m),
  @ins_at (S b) (S m) (q .: δ) = q .: @ins_at b m δ.
Proof. intros. apply functional_extensionality. apply ins_at_head_pt. Qed.

Lemma ins_at_add_pt : forall b m (δ1 δ2 : attrs m) (j : fin (S m)),
  @ins_at b m (δ1 γ+ δ2) j = @ins_at b m δ1 j C+ @ins_at b m δ2 j.
Proof.
  induction b as [|b IH]; intros m δ1 δ2 j.
  - destruct m as [|m'].
    + destruct j; reflexivity.
    + simpl. destruct j as [j'|]; reflexivity.
  - destruct m as [|m'].
    + destruct j; reflexivity.
    + destruct j as [j'|].
      * simpl. apply IH.
      * simpl. reflexivity.
Qed.

Lemma ins_at_add : forall b m (δ1 δ2 : attrs m),
  @ins_at b m (δ1 γ+ δ2) = @ins_at b m δ1 γ+ @ins_at b m δ2.
Proof. intros. apply functional_extensionality. intros j. apply ins_at_add_pt. Qed.

Lemma ins_at_lazy_pt : forall b m (j : fin (S m)),
  @ins_at b m (@lazyvector m) j = Lazy.
Proof.
  induction b as [|b IH]; intros m j.
  - destruct m as [|m'].
    + destruct j; reflexivity.
    + simpl. destruct j as [j'|]; reflexivity.
  - destruct m as [|m'].
    + destruct j; reflexivity.
    + destruct j as [j'|]; simpl; [apply IH|reflexivity].
Qed.

Lemma ins_at_lazy : forall b m, @ins_at b m (@lazyvector m) = @lazyvector (S m).
Proof. intros. apply functional_extensionality. intros j. apply ins_at_lazy_pt. Qed.

Lemma ins_at_var_pt : forall b m (δ : attrs m) (i : fin m) (j : fin (S m)),
  @ins_at b m (env_set δ i Strict) j = env_set (@ins_at b m δ) (ins_ren b i) Strict j.
Proof.
  induction b as [|b IH]; intros m δ i j.
  - destruct m as [|m'].
    + destruct i.
    + simpl. destruct j as [j'|].
      * simpl. destruct (fin_eqb i j'); reflexivity.
      * simpl. reflexivity.
  - destruct m as [|m']; [destruct i|].
    destruct i as [i'|].
    + destruct j as [j'|].
      * simpl. apply IH.
      * simpl. reflexivity.
    + destruct j as [j'|].
      * simpl. reflexivity.
      * simpl. reflexivity.
Qed.

Lemma ins_at_var : forall b m (δ : attrs m) (i : fin m),
  @ins_at b m (env_set δ i Strict) = env_set (@ins_at b m δ) (ins_ren b i) Strict.
Proof. intros. apply functional_extensionality. intros j. apply ins_at_var_pt. Qed.

Lemma ins_at_le_pt : forall b m (δ1 δ2 : attrs m), δ1 γ<= δ2 -> forall j,
  @ins_at b m δ1 j C<= @ins_at b m δ2 j.
Proof.
  induction b as [|b IH]; intros m δ1 δ2 H j.
  - destruct m as [|m'].
    + destruct j as [j'|].
      * destruct j'.
      * simpl. exact I.
    + destruct j as [j'|]; simpl.
      * apply H.
      * exact I.
  - destruct m as [|m'].
    + destruct j as [j'|].
      * destruct j'.
      * simpl. exact I.
    + destruct j as [j'|].
      * simpl. apply IH. intros x. apply H.
      * simpl. apply H.
Qed.

Lemma ins_at_le : forall b m (δ1 δ2 : attrs m), δ1 γ<= δ2 ->
  @ins_at b m δ1 γ<= @ins_at b m δ2.
Proof. intros b m δ1 δ2 H. intros j. apply ins_at_le_pt; auto. Qed.

(* ---------- map_Ty lemmas ---------- *)
Lemma map_Ty_comp : forall {n m p k} (f : attrs m -> attrs p) (g : attrs n -> attrs m)
  (T : Ty n k), map_Ty f (map_Ty g T) = map_Ty (fun γ => f (g γ)) T.
Proof.
  intros n m p k f g T. induction T; simpl; try reflexivity; try (f_equal; auto).
Qed.

Lemma ins_at_down_pt : forall b m (δ : attrs (S m)) (j : fin (S m)),
  @ins_at (S b) (S m) δ (Some j) = @ins_at b m (fun x => δ (Some x)) j.
Proof. intros. reflexivity. Qed.

Lemma ins_at_down : forall b m (δ : attrs (S m)),
  @down_attrs (S m) (@ins_at (S b) (S m) δ) = @ins_at b m (fun i => δ (Some i)).
Proof.
  intros. apply functional_extensionality. intros i. apply ins_at_down_pt.
Qed.

Lemma map_Ty_down_ins : forall b m k (T : Ty (S m) k),
  down_ty (map_Ty (@ins_at (S b) (S m)) T) = map_Ty (@ins_at b m) (down_ty T).
Proof.
  intros b m k T. induction T.
  - reflexivity.
  - change (VThunk (@down_attrs (S m) (@ins_at (S b) (S m) γ))
                   (down_ty (map_Ty (@ins_at (S b) (S m)) T))
            = VThunk (@ins_at b m (ren_env γ shift))
                   (map_Ty (@ins_at b m) (down_ty T))).
    assert (H1 : @down_attrs (S m) (@ins_at (S b) (S m) γ) = @ins_at b m (ren_env γ shift)).
    { apply ins_at_down. }
    rewrite H1, IHT. reflexivity.
  - change (VProd (down_ty (map_Ty (@ins_at (S b) (S m)) T1))
                  (down_ty (map_Ty (@ins_at (S b) (S m)) T2))
            = VProd (map_Ty (@ins_at b m) (down_ty T1))
                    (map_Ty (@ins_at b m) (down_ty T2))).
    f_equal; assumption.
  - change (VSum (down_ty (map_Ty (@ins_at (S b) (S m)) T1))
                  (down_ty (map_Ty (@ins_at (S b) (S m)) T2))
            = VSum (map_Ty (@ins_at b m) (down_ty T1))
                    (map_Ty (@ins_at b m) (down_ty T2))).
    f_equal; assumption.
  - change (CAbs q (down_ty (map_Ty (@ins_at (S b) (S m)) T1))
                  (down_ty (map_Ty (@ins_at (S b) (S m)) T2))
            = CAbs q (map_Ty (@ins_at b m) (down_ty T1))
                    (map_Ty (@ins_at b m) (down_ty T2))).
    f_equal; assumption.
  - change (CF (down_ty (map_Ty (@ins_at (S b) (S m)) T))
            = CF (map_Ty (@ins_at b m) (down_ty T))).
    f_equal; assumption.
Qed.

(* ---------- up_map of ins_at ---------- *)
Lemma up_map_ins_at : forall b n, @up_map n (S n) (@ins_at b n) = @ins_at (S b) (S n).
Proof.
  intros b n. apply functional_extensionality. intros γ.
  apply functional_extensionality. intros i.
  destruct i as [j|]; reflexivity.
Qed.

Lemma ren_env_add : forall {n m} (ξ : ren m n) (a b : attrs n),
  ren_env (a γ+ b) ξ = ren_env a ξ γ+ ren_env b ξ.
Proof. intros. reflexivity. Qed.

Lemma down_ren_ty : forall {n m k} (ξ : ren m n) (T : Ty (S n) k),
  down_ty (ren_ty (@up_ren m n ξ) T) = ren_ty ξ (down_ty T).
Proof.
  intros n m k ξ T. induction T.
  - reflexivity.
  - change (VThunk (@down_attrs m (ren_env γ (@up_ren m n ξ)))
                   (down_ty (ren_ty (@up_ren m n ξ) T))
            = VThunk (ren_env (@down_attrs n γ) ξ)
                   (ren_ty ξ (down_ty T))).
    assert (H1 : @down_attrs m (ren_env γ (@up_ren m n ξ)) = ren_env (@down_attrs n γ) ξ).
    { reflexivity. }
    rewrite H1, IHT. reflexivity.
  - change (VProd (down_ty (ren_ty (@up_ren m n ξ) T1))
                  (down_ty (ren_ty (@up_ren m n ξ) T2))
            = VProd (ren_ty ξ (down_ty T1)) (ren_ty ξ (down_ty T2))).
    f_equal; assumption.
  - change (VSum (down_ty (ren_ty (@up_ren m n ξ) T1))
                  (down_ty (ren_ty (@up_ren m n ξ) T2))
            = VSum (ren_ty ξ (down_ty T1)) (ren_ty ξ (down_ty T2))).
    f_equal; assumption.
  - change (CAbs q (down_ty (ren_ty (@up_ren m n ξ) T1))
                  (down_ty (ren_ty (@up_ren m n ξ) T2))
            = CAbs q (ren_ty ξ (down_ty T1)) (ren_ty ξ (down_ty T2))).
    f_equal; assumption.
  - change (CF (down_ty (ren_ty (@up_ren m n ξ) T))
            = CF (ren_ty ξ (down_ty T))).
    f_equal; assumption.
Qed.

(* ---------- translateType commutation with renaming ---------- *)
Lemma translateType_ren_cbnTy : forall n (T : CbnTy n) m (ξ : ren m n),
  (fst (translateType (ren_cbnTy ξ T)) = ren_ty ξ (fst (translateType T))) /\
  (snd (translateType (ren_cbnTy ξ T)) = ren_env (snd (translateType T)) ξ).
Proof.
  intros n T. induction T; intros m ξ.
  - simpl. split; reflexivity.
  - (* TProd *)
    simpl.
    destruct (translateType T1) as [A1 g1] eqn:E1.
    destruct (translateType T2) as [A2 g2] eqn:E2.
    destruct (translateType (ren_cbnTy ξ T1)) as [A1' g1'] eqn:E1'.
    destruct (translateType (ren_cbnTy ξ T2)) as [A2' g2'] eqn:E2'.
    destruct (IHT1 m ξ) as [H1a H1b].
    destruct (IHT2 m ξ) as [H2a H2b].
    rewrite E1' in H1a; rewrite E1' in H1b.
    rewrite E2' in H2a; rewrite E2' in H2b.
    simpl in H1a, H1b, H2a, H2b.
    simpl. split.
    + rewrite H1a, H1b, H2a, H2b. reflexivity.
    + reflexivity.
  - (* TSum *)
    simpl.
    destruct (translateType T1) as [A1 g1] eqn:E1.
    destruct (translateType T2) as [A2 g2] eqn:E2.
    destruct (translateType (ren_cbnTy ξ T1)) as [A1' g1'] eqn:E1'.
    destruct (translateType (ren_cbnTy ξ T2)) as [A2' g2'] eqn:E2'.
    destruct (IHT1 m ξ) as [H1a H1b].
    destruct (IHT2 m ξ) as [H2a H2b].
    rewrite E1' in H1a; rewrite E1' in H1b.
    rewrite E2' in H2a; rewrite E2' in H2b.
    simpl in H1a, H1b, H2a, H2b.
    simpl. split.
    + rewrite H1a, H1b, H2a, H2b. reflexivity.
    + reflexivity.
  - (* TArrow *)
    simpl.
    destruct (translateType T1) as [A1 g1] eqn:E1.
    destruct (translateType T2) as [B2 g2] eqn:E2.
    destruct (translateType (ren_cbnTy ξ T1)) as [A1' g1'] eqn:E1'.
    destruct (translateType (ren_cbnTy (@up_ren m n ξ) T2)) as [B2' g2'] eqn:E2'.
    destruct (IHT1 m ξ) as [H1a H1b].
    destruct (IHT2 (S m) (@up_ren m n ξ)) as [H2a H2b].
    rewrite E1' in H1a; rewrite E1' in H1b.
    rewrite E2' in H2a; rewrite E2' in H2b.
    simpl in H1a, H1b, H2a, H2b.
    simpl. split.
    + rewrite H1a, H1b, H2a, H2b. rewrite down_ren_ty. reflexivity.
    + rewrite H2b. reflexivity.
Qed.

(* ---------- translateType commutation with ins_at ---------- *)
Lemma translateType_map_ins : forall n (T : CbnTy n) (b : nat),
  (fst (translateType (map_cbnTy (@ins_at b n) T)) = map_Ty (@ins_at b n) (fst (translateType T))) /\
  (snd (translateType (map_cbnTy (@ins_at b n) T)) = @ins_at b n (snd (translateType T))).
Proof.
  intros n T. induction T; intros b.
  - simpl. split; [reflexivity|]. rewrite ins_at_lazy. reflexivity.
  - (* TProd *)
    simpl.
    destruct (translateType T1) as [A1 g1] eqn:E1.
    destruct (translateType T2) as [A2 g2] eqn:E2.
    destruct (translateType (map_cbnTy (ins_at b) T1)) as [A1' g1'] eqn:E1'.
    destruct (translateType (map_cbnTy (ins_at b) T2)) as [A2' g2'] eqn:E2'.
    destruct (IHT1 b) as [H1a H1b].
    destruct (IHT2 b) as [H2a H2b].
    rewrite E1' in H1a; rewrite E1' in H1b.
    rewrite E2' in H2a; rewrite E2' in H2b.
    simpl in H1a, H1b, H2a, H2b.
    simpl. split.
    + rewrite H1a, H1b, H2a, H2b. rewrite <- !ins_at_add. reflexivity.
    + rewrite ins_at_lazy. reflexivity.
  - (* TSum *)
    simpl.
    destruct (translateType T1) as [A1 g1] eqn:E1.
    destruct (translateType T2) as [A2 g2] eqn:E2.
    destruct (translateType (map_cbnTy (ins_at b) T1)) as [A1' g1'] eqn:E1'.
    destruct (translateType (map_cbnTy (ins_at b) T2)) as [A2' g2'] eqn:E2'.
    destruct (IHT1 b) as [H1a H1b].
    destruct (IHT2 b) as [H2a H2b].
    rewrite E1' in H1a; rewrite E1' in H1b.
    rewrite E2' in H2a; rewrite E2' in H2b.
    simpl in H1a, H1b, H2a, H2b.
    simpl. split.
    + rewrite H1a, H1b, H2a, H2b. rewrite <- !ins_at_add. reflexivity.
    + rewrite ins_at_lazy. reflexivity.
  - (* TArrow *)
    simpl.
    rewrite up_map_ins_at.
    destruct (translateType T1) as [A1 g1] eqn:E1.
    destruct (translateType T2) as [B2 g2] eqn:E2.
    destruct (translateType (map_cbnTy (ins_at b) T1)) as [A1' g1'] eqn:E1'.
    destruct (translateType (map_cbnTy (@ins_at (S b) (S n)) T2)) as [B2' g2'] eqn:E2'.
    destruct (IHT1 b) as [H1a H1b].
    destruct (IHT2 (S b)) as [H2a H2b].
    rewrite E1' in H1a; rewrite E1' in H1b.
    rewrite E2' in H2a; rewrite E2' in H2b.
    simpl in H1a, H1b, H2a, H2b.
    change (B2' = map_Ty (@ins_at (S b) (S n)) B2) in H2a.
    change (g2' = @ins_at (S b) (S n) g2) in H2b.
    simpl. split.
    + rewrite H1a, H1b, H2a, H2b.
      rewrite <- ins_at_add.
      rewrite map_Ty_down_ins.
      reflexivity.
    + rewrite H2b. rewrite ins_at_down. rewrite <- ins_at_add. reflexivity.
Qed.

(* ---------- down_ty_until facts ---------- *)
Lemma S_sub_diag : forall n, S n - n = 1.
Proof. intros n. induction n; simpl; [reflexivity|exact IHn]. Qed.

Lemma SS_sub_diag : forall n, S (S n) - n = 2.
Proof. intros n. induction n; simpl; [reflexivity|]. simpl. exact IHn. Qed.

Fixpoint fin_to_nat {n} (i : fin n) : nat :=
  match n as nn return fin nn -> nat with
  | 0 => fun i => match i with end
  | S m => fun i => match i with Some j => S (fin_to_nat j) | None => 0 end
  end i.

Lemma fin_to_nat_inj : forall n (x y : fin n), fin_to_nat x = fin_to_nat y -> x = y.
Proof.
  induction n as [|n' IH]; intros x y H.
  - destruct x.
  - destruct x as [x'|], y as [y'|].
    + simpl in H. injection H as H. f_equal. apply IH. exact H.
    + simpl in H. discriminate.
    + simpl in H. discriminate.
    + reflexivity.
Qed.

Lemma fin_to_nat_eq_rect : forall X Y (e : X = Y) (x : fin X),
  fin_to_nat (@eq_rect nat X (fun k => fin k) x Y e) = fin_to_nat x.
Proof. intros. destruct e. reflexivity. Qed.

Lemma fin_to_nat_shift_p : forall k n (i : fin n),
  fin_to_nat (@shift_p k n i) = k + fin_to_nat i.
Proof.
  induction k; intros n i; simpl.
  - reflexivity.
  - rewrite IHk. reflexivity.
Qed.

Lemma up_fin_until_1 : forall m (H : m <= S m) i,
  @up_fin_until m (S m) H i = Some i.
Proof.
  intros m H i. apply fin_to_nat_inj.
  unfold up_fin_until.
  rewrite fin_to_nat_eq_rect.
  rewrite fin_to_nat_shift_p.
  rewrite S_sub_diag.
  reflexivity.
Qed.

Lemma up_fin_until_2 : forall m (H : m <= S (S m)) i,
  @up_fin_until m (S (S m)) H i = Some (Some i).
Proof.
  intros m H i. apply fin_to_nat_inj.
  unfold up_fin_until.
  rewrite fin_to_nat_eq_rect.
  rewrite fin_to_nat_shift_p.
  rewrite SS_sub_diag.
  reflexivity.
Qed.

Lemma ren_ty_comp : forall {n m p k} (ξ : ren n m) (σ : ren m p) (T : Ty p k),
  ren_ty ξ (ren_ty σ T) = ren_ty (fun i => σ (ξ i)) T.
Proof.
  intros n m p k ξ σ T. induction T; simpl.
  - reflexivity.
  - f_equal. exact IHT.
  - f_equal; assumption.
  - f_equal; assumption.
  - f_equal; assumption.
  - f_equal; assumption.
Qed.

Lemma down_ty_until_ren : forall n m k (B : Ty n k) (H : m <= n),
  down_ty_until B m H = ren_ty (@up_fin_until m n H) B.
Proof.
  intros n m k B. induction B; intros H; simpl.
  - reflexivity.
  - f_equal. exact (IHB H).
  - f_equal; [exact (IHB1 H)|exact (IHB2 H)].
  - f_equal; [exact (IHB1 H)|exact (IHB2 H)].
  - f_equal; [exact (IHB1 H)|exact (IHB2 H)].
  - f_equal. exact (IHB H).
Qed.

Lemma down_ty_until_1 : forall n k (B : Ty (S n) k) (H : n <= S n),
  down_ty_until B n H = down_ty B.
Proof.
  intros n k B H. rewrite down_ty_until_ren.
  assert (Hr : @up_fin_until n (S n) H = @shift n).
  { apply functional_extensionality. intros i. rewrite up_fin_until_1. reflexivity. }
  rewrite Hr. reflexivity.
Qed.

Lemma down_ty_until_2 : forall n k (B : Ty (S (S n)) k) (H : n <= S (S n)),
  down_ty_until B n H = down_ty (down_ty B).
Proof.
  intros n k B H. rewrite down_ty_until_ren.
  assert (Hr : @up_fin_until n (S (S n)) H = fun i => @shift (S n) (@shift n i)).
  { apply functional_extensionality. intros i. rewrite up_fin_until_2. reflexivity. }
  rewrite Hr. unfold down_ty. rewrite ren_ty_comp. reflexivity.
Qed.

Lemma down_compTy_until_1 : forall n (B : CompTy (S n)),
  down_compTy_until B n (Nat.le_succ_diag_r n) = down_ty B.
Proof. intros. apply down_ty_until_1. Qed.

Lemma down_compTy_until_2 : forall n (B : CompTy (S (S n))),
  down_compTy_until B n (le_S n (S n) (Nat.le_succ_diag_r n)) = down_ty (down_ty B).
Proof. intros. apply down_ty_until_2. Qed.

Lemma cons_add : forall q n (a b : attrs n), (q .: a) γ+ (q .: b) = q .: (a γ+ b).
Proof.
  intros q n a b. apply functional_extensionality. intros i.
  destruct i as [j|].
  - reflexivity.
  - destruct q; reflexivity.
Qed.

Lemma translateType_up_lazy : forall n (T : CbnTy n),
  (fst (translateType (up_cbnTy Lazy T)) = map_Ty (fun γ => Lazy .: γ) (fst (translateType T))) /\
  (snd (translateType (up_cbnTy Lazy T)) = Lazy .: (snd (translateType T))).
Proof.
  intros n T. exact (translateType_map_ins n T 0).
Qed.

Lemma translateContext_insert : forall n (T : CbnTy n) (γ : attrs n) (Γ : cbnContext n),
  translateContext (cbnContext_insert T γ Γ) =
  ctx_insert (VThunk (γ γ+ snd (translateType T)) (fst (translateType T))) (translateContext Γ).
Proof.
  intros n T γ Γ. apply functional_extensionality. intros i.
  unfold translateContext, cbnContext_insert, ctx_insert.
  destruct i as [j|].
  - (* Some j *)
    simpl. destruct (Γ j) as [τ γj] eqn:E. simpl.
    destruct (translateType_up_lazy n τ) as [Hf Hs].
    destruct (translateType (Lazy T↑ τ)) as [B γ'] eqn:E1.
    destruct (translateType τ) as [A γτ] eqn:E2.
    simpl in Hf, Hs.
    simpl. rewrite Hf, Hs. rewrite cons_add. reflexivity.
  - (* None: new head *)
    simpl.
    destruct (translateType_up_lazy n T) as [Hf Hs].
    destruct (translateType (Lazy T↑ T)) as [B γ'] eqn:E1.
    destruct (translateType T) as [A γτ] eqn:E2.
    simpl in Hf, Hs.
    simpl. rewrite Hf, Hs. rewrite cons_add. reflexivity.
Qed.



(* ---------- map_Ty up commutation ---------- *)
Lemma map_Ty_up : forall b n k (T : Ty n k),
  map_Ty (fun γ => Lazy .: γ) (map_Ty (@ins_at b n) T)
  = map_Ty (@ins_at (S b) (S n)) (map_Ty (fun γ => Lazy .: γ) T).
Proof.
  intros b n k T. rewrite map_Ty_comp. rewrite map_Ty_comp.
  reflexivity.
Qed.

Lemma map_Ty_up2 : forall b n k (T : Ty n k),
  map_Ty (fun γ => Lazy .: γ) (map_Ty (fun γ => Lazy .: γ) (map_Ty (@ins_at b n) T))
  = map_Ty (@ins_at (S (S b)) (S (S n)))
      (map_Ty (fun γ => Lazy .: γ) (map_Ty (fun γ => Lazy .: γ) T)).
Proof.
  intros b n k T.
  rewrite <- (map_Ty_up (S b) (S n) k (map_Ty (fun γ => Lazy .: γ) T)).
  rewrite <- (map_Ty_up b n k T).
  reflexivity.
Qed.

Lemma map_down_1 : forall b n (B : CompTy (S n)),
  map_Ty (@ins_at b n) (down_compTy_until B n (Nat.le_succ_diag_r n))
  = down_compTy_until (map_Ty (@ins_at (S b) (S n)) B) (S n) (Nat.le_succ_diag_r (S n)).
Proof.
  intros. rewrite down_compTy_until_1. rewrite down_compTy_until_1.
  symmetry. apply map_Ty_down_ins.
Qed.

Lemma map_down_2 : forall b n (B : CompTy (S (S n))),
  map_Ty (@ins_at b n) (down_compTy_until B n (le_S n (S n) (Nat.le_succ_diag_r n)))
  = down_compTy_until (map_Ty (@ins_at (S (S b)) (S (S n))) B) (S n)
      (le_S (S n) (S (S n)) (Nat.le_succ_diag_r (S n))).
Proof.
  intros. rewrite down_compTy_until_2. rewrite down_compTy_until_2.
  rewrite map_Ty_down_ins. rewrite map_Ty_down_ins. reflexivity.
Qed.

(* ---------- typing renaming lemma ---------- *)
Definition ins_ty (b n : nat) {k : Kind} (T : Ty n k) : Ty (S n) k := map_Ty (@ins_at b n) T.

Lemma corr_insert : forall b n (A : ValTy n) (Γ : context n) (Δ : context (S n)),
  (forall i : fin n, Δ (ins_ren b i) = ins_ty b n (Γ i)) ->
  forall i : fin (S n), ctx_insert (ins_ty b n A) Δ (ins_ren (S b) i) = ins_ty (S b) (S n) (ctx_insert A Γ i).
Proof.
  intros b n A Γ Δ Hc i. destruct i as [j|].
  - unfold ctx_insert, ins_ty. simpl. rewrite Hc. apply map_Ty_up.
  - unfold ctx_insert, ins_ty. simpl. apply map_Ty_up.
Qed.

Lemma corr_insert2 : forall b n (A1 A2 : ValTy n) (Γ : context n) (Δ : context (S n)),
  (forall i : fin n, Δ (ins_ren b i) = ins_ty b n (Γ i)) ->
  forall i : fin (S (S n)),
    ctx_insert (up_valTy Lazy (ins_ty b n A1)) (ctx_insert (ins_ty b n A2) Δ) (ins_ren (S (S b)) i)
    = ins_ty (S (S b)) (S (S n)) (ctx_insert (up_valTy Lazy A1) (ctx_insert A2 Γ) i).
Proof.
  intros b n A1 A2 Γ Δ Hc i. destruct i as [i1|].
  - destruct i1 as [j|].
    + unfold ctx_insert, ins_ty. simpl. rewrite Hc. apply map_Ty_up2.
    + unfold ctx_insert, ins_ty. simpl. apply map_Ty_up2.
  - unfold ctx_insert, ins_ty. simpl. apply map_Ty_up2.
Qed.

Lemma Wt_ins_mutual : forall n (γ : attrs n) (Γ : context n),
  (forall (V : Val n) (A : ValTy n), VWt γ Γ V A ->
     forall b (Δ : context (S n)),
       (forall i : fin n, Δ (ins_ren b i) = ins_ty b n (Γ i)) ->
       VWt (ins_at b γ) Δ (ren_Val (ins_ren b) V) (ins_ty b n A)) /\
  (forall (M : Comp n) (B : CompTy n), CWt γ Γ M B ->
     forall b (Δ : context (S n)),
       (forall i : fin n, Δ (ins_ren b i) = ins_ty b n (Γ i)) ->
       CWt (ins_at b γ) Δ (ren_Comp (ins_ren b) M) (ins_ty b n B)).
Proof.
  apply Wt_mutual with
    (P := fun n γ Γ V A _ => forall b (Δ : context (S n)),
        (forall i : fin n, Δ (ins_ren b i) = ins_ty b n (Γ i)) ->
        VWt (ins_at b γ) Δ (ren_Val (ins_ren b) V) (ins_ty b n A))
    (P0 := fun n γ Γ M B _ => forall b (Δ : context (S n)),
        (forall i : fin n, Δ (ins_ren b i) = ins_ty b n (Γ i)) ->
        CWt (ins_at b γ) Δ (ren_Comp (ins_ren b) M) (ins_ty b n B)).
  - (* T_Var *) intros n γ Γ i A e e0 b Δ Hc. subst A. subst γ.
    apply T_Var.
    + symmetry. apply Hc.
    + rewrite ins_at_var, ins_at_lazy. reflexivity.
  - (* T_Unit *) intros n γ Γ e b Δ Hc. subst γ.
    apply T_Unit. rewrite ins_at_lazy. reflexivity.
  - (* T_Thunk *) intros n γ Γ γ' M B c IH e b Δ Hc. subst γ.
    apply T_Thunk.
    + apply IH. exact Hc.
    + rewrite ins_at_lazy. reflexivity.
  - (* T_Pair *) intros n γ Γ γ1 γ2 V1 V2 A1 A2 v1 IH1 v2 IH2 e b Δ Hc. subst γ.
    rewrite ins_at_add. eapply T_Pair with (γ1 := ins_at b γ1) (γ2 := ins_at b γ2).
    + apply IH1. exact Hc.
    + apply IH2. exact Hc.
    + reflexivity.
  - (* T_Inl *) intros n γ Γ V1 A1 A2 v IH b Δ Hc. apply T_Inl. apply IH. exact Hc.
  - (* T_Inr *) intros n γ Γ V2 A1 A2 v IH b Δ Hc. apply T_Inr. apply IH. exact Hc.
  - (* T_Ret *) intros n γ Γ V A v IH b Δ Hc. apply T_Ret. apply IH. exact Hc.
  - (* T_Let *) intros n γ Γ q M M' A B B' γ1 γ2 c IH1 c' IH2 e e0 b Δ Hc. subst γ.
    rewrite ins_at_add. rewrite e0. unfold ins_ty. rewrite map_down_1.
    cbn [ren_Comp]. rewrite up_ren_ins_ren.
    eapply T_Let with (q := q) (A := ins_ty b n A) (B' := ins_ty (S b) (S n) B')
                      (γ1 := ins_at b γ1) (γ2 := ins_at b γ2).
    + apply IH1. exact Hc.
    + rewrite <- ins_at_head. apply IH2. apply corr_insert. exact Hc.
    + reflexivity.
    + reflexivity.
  - (* T_Force *) intros n γ Γ V B γ1 γ2 v IH e b Δ Hc. subst γ.
    rewrite ins_at_add. eapply T_Force with (γ1 := ins_at b γ1) (γ2 := ins_at b γ2).
    + apply IH. exact Hc.
    + reflexivity.
  - (* T_Seq *) intros n γ Γ V M B γ1 γ2 v IHv c IHc e b Δ Hc. subst γ.
    rewrite ins_at_add. eapply T_Seq with (γ1 := ins_at b γ1) (γ2 := ins_at b γ2).
    + apply IHv. exact Hc.
    + apply IHc. exact Hc.
    + reflexivity.
  - (* T_Split *) intros n γ Γ q1 q2 V M γ1 γ2 A1 A2 B B' v IHv c IHc e e0 b Δ Hc. subst γ.
    rewrite ins_at_add. rewrite e0. unfold ins_ty. rewrite map_down_2.
    cbn [ren_Comp]. rewrite up2_ren_ins_ren.
    eapply T_Split with (q1 := q1) (q2 := q2) (A1 := ins_ty b n A1) (A2 := ins_ty b n A2)
      (B' := ins_ty (S (S b)) (S (S n)) B') (γ1 := ins_at b γ1) (γ2 := ins_at b γ2).
    + apply IHv. exact Hc.
    + rewrite <- ins_at_head. rewrite <- ins_at_head. apply IHc. apply corr_insert2. exact Hc.
    + reflexivity.
    + reflexivity.
  - (* T_Case *) intros n γ Γ q1 q2 V M1 M2 γ1 γ2 A1 A2 B B1 B2 v IHv c1 IHc1 c2 IHc2 e e0 e1 b Δ Hc. subst γ.
    rewrite ins_at_add. rewrite e0. unfold ins_ty. rewrite map_down_1.
    cbn [ren_Comp]. rewrite up_ren_ins_ren.
    eapply T_Case with (q1 := q1) (q2 := q2) (A1 := ins_ty b n A1) (A2 := ins_ty b n A2)
      (B1 := ins_ty (S b) (S n) B1) (B2 := ins_ty (S b) (S n) B2)
      (γ1 := ins_at b γ1) (γ2 := ins_at b γ2).
    + apply IHv. exact Hc.
    + rewrite <- ins_at_head. apply IHc1. apply corr_insert. exact Hc.
    + rewrite <- ins_at_head. apply IHc2. apply corr_insert. exact Hc.
    + reflexivity.
    + reflexivity.
    + (* B_new = down (ins_ty B2) ; use e0,e1 *)
      assert (Hdd : down_compTy_until B1 n (Nat.le_succ_diag_r n)
                  = down_compTy_until B2 n (Nat.le_succ_diag_r n)).
      { rewrite <- e0. exact e1. }
      rewrite down_compTy_until_1 in Hdd. rewrite down_compTy_until_1 in Hdd.
      rewrite down_compTy_until_1. rewrite down_compTy_until_1.
      unfold ins_ty.
      rewrite map_Ty_down_ins. rewrite map_Ty_down_ins.
      rewrite Hdd. reflexivity.
  - (* T_Abs *) intros n γ Γ q M A B B' c IH e b Δ Hc.
    rewrite e. unfold ins_ty. cbn [map_Ty]. rewrite map_down_1.
    cbn [ren_Comp]. rewrite up_ren_ins_ren.
    eapply T_Abs with (q := q) (A := ins_ty b n A) (B' := ins_ty (S b) (S n) B').
    + rewrite <- ins_at_head. apply IH. apply corr_insert. exact Hc.
    + reflexivity.
  - (* T_App *) intros n γ Γ M q V γ1 γ2 A B c IHc v IHv e b Δ Hc. subst γ.
    rewrite ins_at_add. eapply T_App with (γ1 := ins_at b γ1) (γ2 := ins_at b γ2).
    + apply IHc. exact Hc.
    + apply IHv. exact Hc.
    + reflexivity.
  - (* T_CSub *) intros n γ Γ M γ' B c IH a b Δ Hc.
    eapply T_CSub with (γ' := ins_at b γ').
    + apply IH. exact Hc.
    + apply ins_at_le. exact a.
Qed.

(* ---------- individual renaming lemmas ---------- *)
Definition VWt_ins_gen := fun (b n : nat) (γ : attrs n) (Γ : context n) (V : Val n) (A : ValTy n)
  (h : VWt γ Γ V A) (Δ : context (S n))
  (Hc : forall i : fin n, Δ (ins_ren b i) = ins_ty b n (Γ i)) =>
  proj1 (Wt_ins_mutual n γ Γ) V A h b Δ Hc.

Definition CWt_ins_gen := fun (b n : nat) (γ : attrs n) (Γ : context n) (M : Comp n) (B : CompTy n)
  (h : CWt γ Γ M B) (Δ : context (S n))
  (Hc : forall i : fin n, Δ (ins_ren b i) = ins_ty b n (Γ i)) =>
  proj2 (Wt_ins_mutual n γ Γ) M B h b Δ Hc.

(* ---------- attribute helper lemmas ---------- *)
Lemma lazyvector_add : forall n, (@lazyvector n) γ+ (@lazyvector n) = @lazyvector n.
Proof.
  intros n. apply functional_extensionality. intros i. reflexivity.
Qed.

Lemma lazy_add : forall n (δ : attrs n), (@lazyvector n) γ+ δ = δ.
Proof.
  intros n δ. apply functional_extensionality. intros i.
  unfold attr_vector_add, lazyvector. simpl. destruct (δ i); reflexivity.
Qed.

Lemma add_lazy : forall n (δ : attrs n), δ γ+ (@lazyvector n) = δ.
Proof.
  intros n δ. apply functional_extensionality. intros i.
  unfold attr_vector_add, lazyvector. simpl. destruct (δ i); reflexivity.
Qed.

Lemma env_set_add : forall n (δ1 δ2 : attrs n) (i : fin n),
  ((δ1 γ+ δ2) <- Strict @ i) = (δ1 <- Strict @ i) γ+ δ2.
Proof.
  intros n δ1 δ2 i. apply functional_extensionality. intros j.
  unfold env_set, attr_vector_add. simpl. destruct (fin_eqb i j); simpl.
  - destruct (δ2 j); reflexivity.
  - reflexivity.
Qed.

Lemma lazy_env_set_add : forall n (δ : attrs n) (i : fin n),
  env_set (@lazyvector n) i Strict γ+ δ = env_set δ i Strict.
Proof.
  intros n δ i. apply functional_extensionality. intros j.
  unfold env_set, attr_vector_add, lazyvector. simpl.
  destruct (fin_eqb i j); simpl.
  - destruct (δ j); reflexivity.
  - destruct (δ j); reflexivity.
Qed.

Lemma cons_add_r : forall q n (a : attrs n) (b : attrs (S n)),
  (q .: a) γ+ b = (q C+ b None) .: (a γ+ @down_attrs n b).
Proof.
  intros q n a b. apply functional_extensionality. intros j.
  destruct j as [j|]; simpl; reflexivity.
Qed.

Lemma attr_add_le : forall c1 c2 a, c1 C<= c2 -> (c1 C+ a) C<= (c2 C+ a).
Proof.
  intros c1 c2 a H. destruct c1, c2, a; simpl in *; auto; try contradiction.
Qed.

Lemma attrs_add_le : forall n (γ1 γ2 δ : attrs n), γ1 γ<= γ2 -> (γ1 γ+ δ) γ<= (γ2 γ+ δ).
Proof. intros n γ1 γ2 δ H i. apply attr_add_le. apply H. Qed.

Lemma translateType_down : forall n (T : CbnTy (S n)),
  fst (translateType (down_cbnTy T)) = down_ty (fst (translateType T)) /\
  snd (translateType (down_cbnTy T)) = down_attrs (snd (translateType T)).
Proof.
  intros n T. apply translateType_ren_cbnTy.
Qed.

Lemma down_ty_up : forall n k (T : Ty n k), down_ty (up_Ty Lazy T) = T.
Proof.
  intros n k T. induction T.
  - reflexivity.
  - change (VThunk (@down_attrs n (Lazy .: γ)) (down_ty (up_Ty Lazy T))
            = VThunk γ T).
    assert (H1 : @down_attrs n (Lazy .: γ) = γ).
    { reflexivity. }
    rewrite H1, IHT. reflexivity.
  - change (VProd (down_ty (up_Ty Lazy T1)) (down_ty (up_Ty Lazy T2)) = VProd T1 T2).
    f_equal; assumption.
  - change (VSum (down_ty (up_Ty Lazy T1)) (down_ty (up_Ty Lazy T2)) = VSum T1 T2).
    f_equal; assumption.
  - change (CAbs q (down_ty (up_Ty Lazy T1)) (down_ty (up_Ty Lazy T2)) = CAbs q T1 T2).
    f_equal; assumption.
  - change (CF (down_ty (up_Ty Lazy T)) = CF T).
    f_equal; assumption.
Qed.

Lemma down_compTy_until_up : forall n (B : CompTy n),
  down_compTy_until (up_compTy Lazy B) n (Nat.le_succ_diag_r n) = B.
Proof.
  intros. rewrite down_compTy_until_1. apply down_ty_up.
Qed.

Lemma ins_ren_1 : forall n, @up_ren' n = @ins_ren 1 (S n).
Proof.
  intros n. apply functional_extensionality. intros i.
  destruct i as [j|]; reflexivity.
Qed.

Lemma ins_ren_2 : forall n, @up2_ren' n = @ins_ren 2 (S (S n)).
Proof.
  intros n. apply functional_extensionality. intros i.
  destruct i as [j|]; [destruct j as [k|]|]; reflexivity.
Qed.

Lemma ins_ren_0 : forall n, @shift n = @ins_ren 0 n.
Proof. intros n. reflexivity. Qed.

Lemma translateType_down2 : forall n (T : CbnTy (S (S n))),
  fst (translateType (down_cbnTy (down_cbnTy T))) = down_ty (down_ty (fst (translateType T))) /\
  snd (translateType (down_cbnTy (down_cbnTy T))) = down_attrs (down_attrs (snd (translateType T))).
Proof.
  intros n T.
  destruct (translateType_down n (down_cbnTy T)) as [H1 H1'].
  destruct (translateType_down (S n) T) as [H2 H2'].
  split.
  - rewrite H1, H2. reflexivity.
  - rewrite H1', H2'. reflexivity.
Qed.

Lemma CWt_shift_gen : forall n (γ : attrs n) (Γ : context n) (M : Comp n) (B : CompTy n) (A : ValTy n),
  CWt γ Γ M B ->
  CWt (ins_at 0 γ) (ctx_insert A Γ) (ren_Comp shift M) (ins_ty 0 n B).
Proof.
  intros n γ Γ M B A H.
  eapply CWt_ins_gen with (b := 0).
  - exact H.
  - intros i. reflexivity.
Qed.


Lemma attr_add_assoc : forall a b c : attr, (a C+ b) C+ c = a C+ (b C+ c).
Proof. intros a b c. destruct a, b, c; reflexivity. Qed.

Lemma attrs_add_assoc : forall n (a b c : attrs n), (a γ+ b) γ+ c = a γ+ (b γ+ c).
Proof. intros. apply functional_extensionality. intros i. apply attr_add_assoc. Qed.

Lemma down_attrs_add : forall n (a b : attrs (S n)), down_attrs (a γ+ b) = down_attrs a γ+ down_attrs b.
Proof. intros. reflexivity. Qed.

Lemma cons_lazy_down : forall n (δ : attrs (S n)), ((δ None) .: down_attrs δ) = δ.
Proof. intros n δ. apply functional_extensionality. intros j. destruct j as [j|]; reflexivity. Qed.

Lemma down_attrs_ins_at : forall b n (δ : attrs (S (S n))),
  down_attrs (@ins_at (S b) (S (S n)) δ) = @ins_at b (S n) (down_attrs δ).
Proof. intros. apply ins_at_down. Qed.

(* canonical cons decomposition *)
Lemma cons_down_decomp : forall n (δ : attrs (S n)), δ = (δ None) .: down_attrs δ.
Proof. intros n δ. symmetry. apply cons_lazy_down. Qed.

Lemma ins_at_0_cons : forall n (δ : attrs n), @ins_at 0 n δ = Lazy .: δ.
Proof.
  intros n δ. apply functional_extensionality. intros i.
  destruct i as [j|]; reflexivity.
Qed.

Lemma split_attrs_tail : forall n (q1 q2 : attr) (γ2 : attrs n) (gT : attrs (S (S n))),
  @down_attrs (S n) (@down_attrs (S (S n)) (@ins_at 2 (S (S n)) ((q1 .: (q2 .: γ2)) γ+ gT)))
  = Lazy .: (γ2 γ+ @down_attrs n (@down_attrs (S n) gT)).
Proof.
  intros n q1 q2 γ2 gT.
  assert (E : @down_attrs (S (S n)) (@ins_at 2 (S (S n)) ((q1 .: (q2 .: γ2)) γ+ gT))
            = @ins_at 1 (S n) (@down_attrs (S n) ((q1 .: (q2 .: γ2)) γ+ gT))).
  { apply ins_at_down. }
  rewrite E.
  assert (E2 : @down_attrs (S n) (@ins_at 1 (S n) (@down_attrs (S n) ((q1 .: (q2 .: γ2)) γ+ gT)))
             = @ins_at 0 n (@down_attrs n (@down_attrs (S n) ((q1 .: (q2 .: γ2)) γ+ gT)))).
  { apply ins_at_down. }
  rewrite E2.
  assert (E3 : @down_attrs n (@down_attrs (S n) ((q1 .: (q2 .: γ2)) γ+ gT))
             = γ2 γ+ @down_attrs n (@down_attrs (S n) gT)).
  { rewrite down_attrs_add. rewrite down_attrs_add. reflexivity. }
  rewrite E3. rewrite ins_at_0_cons. reflexivity.
Qed.

Lemma ins_ty_0_up : forall n k (T : Ty n k), ins_ty 0 n T = up_Ty Lazy T.
Proof.
  intros n k T. unfold ins_ty, up_Ty.
  assert (Hf : @ins_at 0 n = (fun γ : attrs n => Lazy .: γ)).
  { apply functional_extensionality. intros γ. apply ins_at_0_cons. }
  rewrite Hf. reflexivity.
Qed.

Lemma ins_ty_0_up_comp : forall n (T : CompTy n), ins_ty 0 n T = up_compTy Lazy T.
Proof. intros. apply ins_ty_0_up. Qed.


Lemma corr0_gen : forall n (A : ValTy n) (Γ' : context n),
  forall i : fin n, ctx_insert A Γ' (ins_ren 0 i) = ins_ty 0 n (Γ' i).
Proof.
  intros n A Γ' i. unfold ctx_insert. simpl.
  rewrite ins_ty_0_up. reflexivity.
Qed.

Lemma case_attrs_tail : forall n (q : attr) (γ2 : attrs n) (g : attrs (S n)),
  @down_attrs (S n) (@ins_at 1 (S n) ((q .: γ2) γ+ g)) = Lazy .: (γ2 γ+ @down_attrs n g).
Proof.
  intros n q γ2 g.
  assert (E : @down_attrs (S n) (@ins_at 1 (S n) ((q .: γ2) γ+ g))
            = @ins_at 0 n (@down_attrs n ((q .: γ2) γ+ g))).
  { apply ins_at_down. }
  rewrite E. rewrite down_attrs_add. rewrite ins_at_0_cons. reflexivity.
Qed.

Lemma ins_at_lazy3 : forall n (δ : attrs n),
  @ins_at 2 (S (S n)) (Lazy .: (Lazy .: δ)) = Lazy .: (Lazy .: (Lazy .: δ)).
Proof.
  intros n δ. apply functional_extensionality. intros i.
  destruct i as [i1|].
  - destruct i1 as [j|]; [|reflexivity].
    destruct j as [k|]; simpl; reflexivity.
  - reflexivity.
Qed.

Lemma map_Ty_ins2_lazy : forall n k (T : Ty n k),
  map_Ty (@ins_at 2 (S (S n))) (map_Ty (fun γ => Lazy .: γ) (map_Ty (fun γ => Lazy .: γ) T))
  = map_Ty (fun γ => Lazy .: γ) (map_Ty (fun γ => Lazy .: γ) (map_Ty (fun γ => Lazy .: γ) T)).
Proof.
  intros n k T.
  rewrite map_Ty_comp. rewrite map_Ty_comp. rewrite map_Ty_comp. rewrite map_Ty_comp.
  assert (Hf : (fun γ : attrs n => @ins_at 2 (S (S n)) (Lazy .: (Lazy .: γ)))
             = (fun γ : attrs n => Lazy .: (Lazy .: (Lazy .: γ)))).
  { apply functional_extensionality. intros γ. apply ins_at_lazy3. }
  rewrite Hf. reflexivity.
Qed.

Lemma corr_split_gen : forall n (Xo Xi A : ValTy n) (Γ' : context n) (i : fin (S (S n))),
  ctx_insert (up_valTy Lazy (up_valTy Lazy Xo)) (ctx_insert (up_valTy Lazy Xi) (ctx_insert A Γ')) (ins_ren 2 i)
  = ins_ty 2 (S (S n)) (ctx_insert (up_valTy Lazy Xo) (ctx_insert Xi Γ') i).
Proof.
  intros n Xo Xi A Γ' i. destruct i as [i1|].
  - destruct i1 as [j|].
    + simpl. unfold ins_ty.
      change (map_Ty (fun γ => Lazy .: γ) (map_Ty (fun γ => Lazy .: γ) (map_Ty (fun γ => Lazy .: γ) (Γ' j)))
              = map_Ty (@ins_at 2 (S (S n))) (map_Ty (fun γ => Lazy .: γ) (map_Ty (fun γ => Lazy .: γ) (Γ' j)))).
      rewrite map_Ty_ins2_lazy. reflexivity.
    + simpl. unfold ins_ty.
      change (map_Ty (fun γ => Lazy .: γ) (map_Ty (fun γ => Lazy .: γ) (map_Ty (fun γ => Lazy .: γ) Xi))
              = map_Ty (@ins_at 2 (S (S n))) (map_Ty (fun γ => Lazy .: γ) (map_Ty (fun γ => Lazy .: γ) Xi))).
      rewrite map_Ty_ins2_lazy. reflexivity.
  - simpl. unfold ins_ty.
    change (map_Ty (fun γ => Lazy .: γ) (map_Ty (fun γ => Lazy .: γ) (map_Ty (fun γ => Lazy .: γ) Xo))
            = map_Ty (@ins_at 2 (S (S n))) (map_Ty (fun γ => Lazy .: γ) (map_Ty (fun γ => Lazy .: γ) Xo))).
    rewrite map_Ty_ins2_lazy. reflexivity.
Qed.



Lemma translateTerm_gen : forall n (γ : attrs n) (Γ : cbnContext n) (e : Term n) (T : CbnTy n),
  cbnWt γ Γ e T ->
  CWt (γ γ+ snd (translateType T)) (translateContext Γ) (translateTerm e) (fst (translateType T)).
Proof.
  apply cbnWt_ind with
    (P := fun n γ Γ e T => CWt (γ γ+ snd (translateType T)) (translateContext Γ) (translateTerm e) (fst (translateType T))).
  - (* Var *)
    intros n γ Γ i A γ' He Hγ. rewrite Hγ.
    destruct (translateType A) as [B gA] eqn:EA.
    eapply T_Force with (V := vVar i) (B := B) (γ1 := (lazyvector <- Strict @ i)) (γ2 := γ' γ+ gA).
    + apply T_Var.
      * symmetry. unfold translateContext. simpl. rewrite <- He. rewrite EA. simpl. reflexivity.
      * reflexivity.
    + apply functional_extensionality. intros j.
      unfold env_set, attr_vector_add, lazyvector. simpl.
      destruct (fin_eqb i j); simpl; destruct (γ' j); destruct (gA j); reflexivity.
  - (* Unit *)
    intros n γ Γ Hγ. rewrite Hγ. simpl.
    apply T_Ret. apply T_Unit. apply lazyvector_add.
  - (* Let *)
    intros n γ Γ q γ1 t1 t2 T1 T2 T h1 IH1 h2 IH2 HT.
    rewrite HT.
    destruct (translateType T1) as [B1 g1] eqn:E1.
    destruct (translateType T2) as [B2 g2] eqn:E2.
    destruct (translateType_down n T2) as [Hdf Hds].
    simpl in IH1, IH2.
    rewrite E2 in Hdf, Hds. simpl in Hdf, Hds.
    rewrite Hdf, Hds.
    eapply T_Let with (q := q C+ g2 None) (A := VThunk (γ1 γ+ g1) B1) (B' := B2)
                     (γ1 := lazyvector) (γ2 := γ γ+ down_attrs g2).
    + apply T_Ret. apply T_Thunk. exact IH1. reflexivity.
    + assert (Hctx : translateContext (cbnContext_insert T1 γ1 Γ) = ctx_insert (VThunk (γ1 γ+ g1) B1) (translateContext Γ)).
      { rewrite translateContext_insert. rewrite E1. simpl. reflexivity. }
      rewrite <- Hctx. simpl. rewrite <- cons_add_r. apply IH2.
    + symmetry. apply lazy_add.
    + symmetry. apply down_compTy_until_1.
  - (* Pair *)
    intros n γ Γ γ1 γ2 t1 t2 T1 T2 h1 IH1 h2 IH2 Hγ. rewrite Hγ. cbn [translateType]. cbn [translateType] in IH1, IH2.
    destruct (translateType T1) as [A1 g1] eqn:E1.
    destruct (translateType T2) as [A2 g2] eqn:E2.
    simpl in IH1, IH2. cbn. apply T_Ret. eapply T_Pair with (γ1 := lazyvector) (γ2 := lazyvector).
    + apply T_Thunk. exact IH1. reflexivity.
    + apply T_Thunk. exact IH2. reflexivity.
    + reflexivity.
  - (* Inl *)
    intros n γ Γ γ' γ'' t1 T1 T2 h IH Hγ. rewrite Hγ. cbn [translateType]. cbn [translateType] in IH.
    destruct (translateType T1) as [A1 g1] eqn:E1.
    destruct (translateType T2) as [A2 g2] eqn:E2.
    simpl in IH. cbn. apply T_Ret. eapply T_Inl.
    apply T_Thunk. exact IH. apply lazyvector_add.
  - (* Inr *)
    intros n γ Γ γ' γ'' t2 T1 T2 h IH Hγ. rewrite Hγ. cbn [translateType]. cbn [translateType] in IH.
    destruct (translateType T1) as [A1 g1] eqn:E1.
    destruct (translateType T2) as [A2 g2] eqn:E2.
    simpl in IH. cbn. apply T_Ret. eapply T_Inr.
    apply T_Thunk. exact IH. apply lazyvector_add.
  - (* Seq *)
    intros n γ Γ t1 t2 T γ1 γ2 h1 IH1 h2 IH2 Hγ. rewrite Hγ. cbn [translateType]. cbn [translateType] in IH1, IH2.
    destruct (translateType T) as [B g] eqn:E.
    simpl in IH1.
    eapply T_Let with (q := Strict) (A := VUnit) (B' := up_compTy Lazy B)
                     (γ1 := γ1 γ+ lazyvector) (γ2 := γ2 γ+ g).
    + exact IH1.
    + eapply T_Seq with (γ1 := lazyvector <- Strict @ var_zero) (γ2 := @ins_at 0 n (γ2 γ+ g)).
      * apply T_Var. reflexivity. reflexivity.
      * eapply CWt_shift_gen. exact IH2.
      * apply functional_extensionality. intros j. destruct j as [j|].
        -- unfold env_set, attr_vector_add, lazyvector. simpl.
           destruct ((γ2 γ+ g) j); reflexivity.
        -- unfold env_set, attr_vector_add, lazyvector. simpl. reflexivity.
    + rewrite attrs_add_assoc. rewrite add_lazy. reflexivity.
    + symmetry. apply down_compTy_until_up.
  - (* Split *)
    intros n γ Γ t1 t2 q1 q2 γ1 γ2 γ1' γ2' T1 T2 T T' h1 IH1 h2 IH2 Hγ HT.
    rewrite Hγ, HT. cbn [translateType]. cbn [translateType] in IH1, IH2.
    destruct (translateType T1) as [A1 g1] eqn:E1.
    destruct (translateType T2) as [A2 g2] eqn:E2.
    destruct (translateType T') as [BT gT] eqn:ET.
    destruct (translateType_down2 n T') as [Hdf Hds].
    rewrite ET in Hdf, Hds. simpl in Hdf, Hds.
    rewrite Hdf, Hds.
    simpl in IH1, IH2.
    eapply T_Let with (q := Strict)
      (A := VProd (VThunk (γ1' γ+ g1) A1) (VThunk (γ2' γ+ g2) A2))
      (B' := up_compTy Lazy (down_ty (down_ty BT)))
      (γ1 := γ1 γ+ lazyvector) (γ2 := γ2 γ+ down_attrs (down_attrs gT)).
    + exact IH1.
    + (* CWt premise for cSplit *)
      rewrite translateContext_insert in IH2.
      rewrite translateContext_insert in IH2.
      rewrite (proj1 (translateType_up_lazy n T1)) in IH2.
      rewrite (proj2 (translateType_up_lazy n T1)) in IH2.
      rewrite cons_add in IH2.
      rewrite E1, E2 in IH2. simpl in IH2.
      (* now IH2 : CWt (ins_at 0 (...) ...) (ctx_insert (VThunk (Lazy.:(γ1'+g1)) (map_Ty lazy A1)) (ctx_insert (VThunk (γ2'+g2) A2) Γ')) (translateTerm t2) BT *)
      pose (E := @ins_at 2 (S (S n)) ((q1 .: (q2 .: γ2)) γ+ gT)).
      assert (Hdec1 : E = (E None) .: @down_attrs (S (S n)) E).
      { unfold E. apply cons_down_decomp. }
      pose (Ed := @down_attrs (S (S n)) E).
      assert (Hdec2 : Ed = (Ed None) .: @down_attrs (S n) Ed).
      { unfold Ed. apply cons_down_decomp. }
      assert (Hfull : E = (E None) .: ((Ed None) .: @down_attrs (S n) Ed)).
      { rewrite Hdec1. fold Ed. rewrite Hdec2. reflexivity. }
      assert (Hins : CWt E
                       (ctx_insert (up_valTy Lazy (up_valTy Lazy (VThunk (γ1' γ+ g1) A1)))
                          (ctx_insert (up_valTy Lazy (VThunk (γ2' γ+ g2) A2))
                             (ctx_insert (VProd (VThunk (γ1' γ+ g1) A1) (VThunk (γ2' γ+ g2) A2)) (translateContext Γ))))
                       (ren_Comp (ins_ren 2) (translateTerm t2)) (ins_ty 2 (S (S n)) BT)).
      { eapply CWt_ins_gen with (b := 2).
        - exact IH2.
        - apply corr_split_gen. }
      fold E in Hins.
      rewrite Hfull in Hins.
      rewrite (ins_ren_2 n).
      eapply T_Split with (q1 := E None) (q2 := Ed None)
        (γ1 := lazyvector <- Strict @ var_zero)
        (γ2 := @down_attrs (S n) Ed) (B' := ins_ty 2 (S (S n)) BT).
      * apply T_Var. reflexivity. reflexivity.
      * exact Hins.
      * unfold Ed, E. rewrite split_attrs_tail.
        apply functional_extensionality. intros j. destruct j as [j|].
        -- unfold env_set, attr_vector_add, lazyvector. simpl.
           destruct ((γ2 γ+ down_attrs (down_attrs gT)) j); reflexivity.
        -- unfold env_set, attr_vector_add, lazyvector. simpl. reflexivity.
      * rewrite down_compTy_until_2. unfold ins_ty.
        rewrite map_Ty_down_ins. rewrite map_Ty_down_ins. reflexivity.
    + rewrite attrs_add_assoc. rewrite add_lazy. reflexivity.
    + symmetry. apply down_compTy_until_up.
  - (* Case *)
    intros n γ Γ t1 t2 t3 q1 q2 γ1 γ2 γ1' γ2' TL1 TR1 T T2 T3 h1 IH1 h2 IH2 h3 IH3 Hγ HT2 HT3.
    rewrite Hγ, HT2. cbn [translateType]. cbn [translateType] in IH1, IH2, IH3.
    destruct (translateType TL1) as [A1 g1] eqn:E1.
    destruct (translateType TR1) as [A2 g2] eqn:E2.
    destruct (translateType T2) as [B1 h1g] eqn:E2b.
    destruct (translateType T3) as [B2 h2g] eqn:E3b.
    destruct (translateType_down n T2) as [Hdf1 Hds1].
    destruct (translateType_down n T3) as [Hdf2 Hds2].
    rewrite E2b in Hdf1, Hds1. simpl in Hdf1, Hds1.
    rewrite E3b in Hdf2, Hds2. simpl in Hdf2, Hds2.
    rewrite Hdf1, Hds1.
    simpl in IH1, IH2, IH3.
    assert (HTT : down_cbnTy T2 = down_cbnTy T3).
    { rewrite <- HT2. exact HT3. }
    assert (HB : @down_ty n CompFlag B1 = @down_ty n CompFlag B2).
    { rewrite <- Hdf1, <- Hdf2. rewrite HTT. reflexivity. }
    assert (Hg : @down_attrs n h1g = @down_attrs n h2g).
    { rewrite <- Hds1, <- Hds2. rewrite HTT. reflexivity. }
    eapply T_Let with (q := Strict)
      (A := VSum (VThunk (γ1' γ+ g1) A1) (VThunk (γ2' γ+ g2) A2))
      (B' := up_compTy Lazy (down_ty B1))
      (γ1 := γ1 γ+ lazyvector) (γ2 := γ2 γ+ down_attrs h1g).
    + exact IH1.
    + (* cCase premise *)
      assert (Hctx2 : translateContext (cbnContext_insert TL1 γ1' Γ) = ctx_insert (VThunk (γ1' γ+ g1) A1) (translateContext Γ)).
      { rewrite translateContext_insert. rewrite E1. simpl. reflexivity. }
      assert (Hctx3 : translateContext (cbnContext_insert TR1 γ2' Γ) = ctx_insert (VThunk (γ2' γ+ g2) A2) (translateContext Γ)).
      { rewrite translateContext_insert. rewrite E2. simpl. reflexivity. }
      rewrite Hctx2 in IH2. rewrite Hctx3 in IH3.
      pose (E1c := @ins_at 1 (S n) ((q1 .: γ2) γ+ h1g)).
      assert (Hd1 : E1c = (E1c None) .: @down_attrs (S n) E1c).
      { unfold E1c. apply cons_down_decomp. }
      pose (E2c := @ins_at 1 (S n) ((q2 .: γ2) γ+ h2g)).
      assert (Hd2 : E2c = (E2c None) .: @down_attrs (S n) E2c).
      { unfold E2c. apply cons_down_decomp. }
      assert (HdE : @down_attrs (S n) E2c = @down_attrs (S n) E1c).
      { unfold E1c, E2c. rewrite case_attrs_tail. rewrite case_attrs_tail. rewrite Hg. reflexivity. }
      assert (Hins2 : CWt E1c
                        (ctx_insert (up_valTy Lazy (VThunk (γ1' γ+ g1) A1))
                           (ctx_insert (VSum (VThunk (γ1' γ+ g1) A1) (VThunk (γ2' γ+ g2) A2)) (translateContext Γ)))
                        (ren_Comp (ins_ren 1) (translateTerm t2)) (ins_ty 1 (S n) B1)).
      { eapply CWt_ins_gen with (b := 1).
        - exact IH2.
        - apply corr_insert with (A := VThunk (γ1' γ+ g1) A1)
            (Δ := ctx_insert (VSum (VThunk (γ1' γ+ g1) A1) (VThunk (γ2' γ+ g2) A2)) (translateContext Γ)).
          apply corr0_gen. }
      assert (Hins3 : CWt E2c
                        (ctx_insert (up_valTy Lazy (VThunk (γ2' γ+ g2) A2))
                           (ctx_insert (VSum (VThunk (γ1' γ+ g1) A1) (VThunk (γ2' γ+ g2) A2)) (translateContext Γ)))
                        (ren_Comp (ins_ren 1) (translateTerm t3)) (ins_ty 1 (S n) B2)).
      { eapply CWt_ins_gen with (b := 1).
        - exact IH3.
        - apply corr_insert with (A := VThunk (γ2' γ+ g2) A2)
            (Δ := ctx_insert (VSum (VThunk (γ1' γ+ g1) A1) (VThunk (γ2' γ+ g2) A2)) (translateContext Γ)).
          apply corr0_gen. }
      fold E1c in Hins2. rewrite Hd1 in Hins2.
      fold E2c in Hins3. rewrite Hd2 in Hins3. rewrite HdE in Hins3.
      rewrite (ins_ren_1 n).
      eapply T_Case with (q1 := E1c None) (q2 := E2c None)
        (γ1 := lazyvector <- Strict @ var_zero) (γ2 := @down_attrs (S n) E1c)
        (B1 := ins_ty 1 (S n) B1) (B2 := ins_ty 1 (S n) B2).
      * apply T_Var. reflexivity. reflexivity.
      * exact Hins2.
      * exact Hins3.
      * unfold E1c. rewrite case_attrs_tail.
        apply functional_extensionality. intros j. destruct j as [j|].
        -- unfold env_set, attr_vector_add, lazyvector. simpl.
           destruct ((γ2 γ+ down_attrs h1g) j); reflexivity.
        -- unfold env_set, attr_vector_add, lazyvector. simpl. reflexivity.
      * rewrite down_compTy_until_1. unfold ins_ty. rewrite map_Ty_down_ins.
        change (map_Ty (@ins_at 0 n) (@down_ty n CompFlag B1) = up_compTy Lazy (@down_ty n CompFlag B1)).
        apply ins_ty_0_up.
      * rewrite down_compTy_until_1. unfold ins_ty. rewrite map_Ty_down_ins.
        rewrite <- HB. apply ins_ty_0_up.
    + rewrite attrs_add_assoc. rewrite add_lazy. reflexivity.
    + symmetry. apply down_compTy_until_up.
  - (* Abs *)
    intros n γ Γ q γInput γ' t T1 T2 h IH Hγ. rewrite Hγ. cbn [translateType]. cbn [translateType] in IH.
    destruct (translateType T1) as [A1 g1] eqn:E1.
    destruct (translateType T2) as [B2 g2] eqn:E2.
    simpl in IH.
    eapply T_Abs with (q := q C+ g2 None) (A := VThunk (γInput γ+ g1) A1) (B' := B2)
                     (γ := lazyvector γ+ (γ' γ+ down_attrs g2)).
    + assert (Hctx : translateContext (cbnContext_insert T1 γInput Γ) = ctx_insert (VThunk (γInput γ+ g1) A1) (translateContext Γ)).
      { rewrite translateContext_insert. rewrite E1. simpl. reflexivity. }
      rewrite <- Hctx. rewrite lazy_add. rewrite <- cons_add_r. apply IH.
    + symmetry. apply down_compTy_until_1.
  - (* App *)
    intros n γ Γ t1 t2 q γ1 γInput γ3 T1 T2 T2' h1 IH1 h2 IH2 Hγ HT2.
    rewrite Hγ, HT2. cbn [translateType]. cbn [translateType] in IH1.
    destruct (translateType T1) as [A1 g1] eqn:E1.
    destruct (translateType T2') as [B2 g2] eqn:E2.
    destruct (translateType_down n T2') as [Hdf Hds].
    rewrite E2 in Hdf, Hds. simpl in Hdf, Hds.
    rewrite Hdf, Hds.
    simpl in IH1, IH2.
    eapply T_App with (γ1 := γ1 γ+ (γ3 γ+ down_attrs g2)) (γ2 := lazyvector)
                     (A := VThunk (γInput γ+ g1) A1) (B := down_ty B2).
    + exact IH1.
    + apply T_Thunk. exact IH2. reflexivity.
    + rewrite attrs_add_assoc. rewrite add_lazy. reflexivity.
  - (* Sub *)
    intros n γ Γ γ' t T h IH Hle.
    eapply T_CSub with (γ' := γ' γ+ snd (translateType T)).
    + exact IH.
    + apply attrs_add_le. exact Hle.
Qed.

Theorem translation_correct_returner :
    forall n (γ : attrs n) (Γ : cbnContext n) e T A γ',
    cbnWt γ Γ e T ->
    (CF A, γ') = translateType T ->
    CWt γ (translateContext Γ) (translateTerm e) (CF A).
Proof.
  intros n γ Γ e T A γ' Hh Htr.
  pose proof (translateTerm_gen n γ Γ e T Hh) as Hgen.
  destruct T.
  - simpl in Htr. injection Htr as HA Hg. subst A. subst γ'.
    simpl in Hgen. rewrite add_lazy in Hgen. exact Hgen.
  - cbn [translateType] in Htr. cbn [translateType] in Hgen.
    destruct (translateType T1) as [B1 g1] eqn:E1.
    destruct (translateType T2) as [B2 g2] eqn:E2.
    simpl in Htr, Hgen. injection Htr as HA Hg. subst A. subst γ'.
    rewrite add_lazy in Hgen. exact Hgen.
  - cbn [translateType] in Htr. cbn [translateType] in Hgen.
    destruct (translateType T1) as [B1 g1] eqn:E1.
    destruct (translateType T2) as [B2 g2] eqn:E2.
    simpl in Htr, Hgen. injection Htr as HA Hg. subst A. subst γ'.
    rewrite add_lazy in Hgen. exact Hgen.
  - cbn [translateType] in Htr.
    destruct (translateType T1) as [B1 g1] eqn:E1.
    destruct (translateType T2) as [B2 g2] eqn:E2.
    simpl in Htr. discriminate Htr.
Qed.
