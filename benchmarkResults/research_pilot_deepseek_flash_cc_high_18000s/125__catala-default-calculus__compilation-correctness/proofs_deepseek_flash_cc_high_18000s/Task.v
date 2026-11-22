Require Import Syntax Sequences Reduction.

Definition process_exceptions :=
  (Lam (* x => *) (Lam (* y => *)
    (Match_ (Var 0 (* y *)) (* with *)
      (* | None => *)
        (Var 1 (* y *))
      (* | Some z => *)
        (Match_ (Var 2 (* x *)) (* with *)
          (* | None => *)
            (Var 1 (* y *))
          (* | Some w => *)
            (Conflict)
        )
      ))).


Fixpoint trans (t: term) : term :=
  match t with
  | Var x => Var x
  | App t1 t2 => App (trans t1) (trans t2)
  | Lam t => Lam (trans t)

  | Value v => Value (trans_value v)
  | Binop op t1 t2 => Binop op (trans t1) (trans t2)

  | Match_ u t1 t2 =>
    Match_ (trans u) (trans t1) (trans t2)
  | ENone => ENone
  | ESome t => ESome (trans t)

  | If t ta tb =>
    If (trans t) (trans ta) (trans tb)
  | Fold f ts acc =>
    Fold (trans f) (List.map trans ts) (trans acc)

  | ErrorOnEmpty t => Match_ (trans t) Conflict (Var 0)
  | DefaultPure t => ESome (trans t)
  | Default ts tj tc =>
    Match_
      (Fold
        process_exceptions
        (List.map trans ts) ENone)
      (If (trans tj) (trans tc) ENone)
      (ESome (Var 0))
  | Empty => ENone
  | Conflict => Conflict
  end

with trans_value v :=
  match v with
  | Bool b => Bool b
  | Int i => Int i
  | Closure t sigma => Closure (trans t) (List.map trans_value sigma)
  | VNone => VNone
  | VUnit => VUnit
  | VSome v => VSome (trans_value v)
  | VPure v => VSome (trans_value v)
  end
.

From Stdlib Require Import List Arith Lia Wellfounded.
Import List.ListNotations.
Open Scope list.

Fixpoint tsum (l:list nat) : nat :=
  match l with [] => 0 | x::xs => x + tsum xs end.

Fixpoint tsize (t:term) : nat :=
  match t with
  | Var _ => 1
  | App a b => S (tsize a + tsize b)
  | Lam a => S (tsize a)
  | ErrorOnEmpty a => S (tsize a)
  | DefaultPure a => S (tsize a)
  | Default ts tj tc => S (tsize tj + tsize tc + tsum (List.map tsize ts))
  | Empty => 1
  | Conflict => 1
  | Value v => 1
  | Binop _ a b => S (tsize a + tsize b)
  | Match_ u a b => S (tsize u + tsize a + tsize b)
  | ENone => 1
  | ESome a => S (tsize a)
  | Fold f ts a => S (tsize f + tsize a + tsum (List.map tsize ts))
  | If a b c => S (tsize a + tsize b + tsize c)
  end.

Lemma tsize_in : forall ts (t:term), In t ts -> tsize t <= tsum (List.map tsize ts).
Proof.
  intros ts t Hin. induction ts as [|a tl IH].
  - inversion Hin.
  - simpl in *. destruct Hin as [-> | Hin].
    + lia.
    + specialize (IH Hin). lia.
Qed.

Definition term_lt (x y:term) := tsize x < tsize y.

Lemma term_lt_wf : well_founded term_lt.
Proof. unfold term_lt. apply wf_inverse_image with (f:=tsize). apply lt_wf. Qed.

Lemma up_0 : forall (sigma:var->term), up sigma 0 = Var 0.
Proof. intros. unfold up. cbn. reflexivity. Qed.
Lemma up_S : forall (sigma:var->term) n, up sigma (S n) = rename (+1) (sigma n).
Proof. intros. unfold up. cbn. reflexivity. Qed.

Lemma ren_list_map : forall (ts:list term) (xi:var->var),
  mmap (rename xi) ts = List.map (fun t => rename xi t) ts.
Proof.
  intros. induction ts.
  - reflexivity.
  - change (rename xi a :: mmap (rename xi) ts = rename xi a :: List.map (fun t => rename xi t) ts).
    rewrite IHts. reflexivity.
Qed.

Lemma map_ren_trans_list : forall (ts:list term) (xi:var->var),
  (forall t, In t ts -> trans (rename xi t) = rename xi (trans t)) ->
  List.map trans (mmap (rename xi) ts) = mmap (rename xi) (List.map trans ts).
Proof.
  intros ts xi H. induction ts as [|a tl IH].
  - reflexivity.
  - change (trans (rename xi a) :: List.map trans (mmap (rename xi) tl)
            = rename xi (trans a) :: mmap (rename xi) (List.map trans tl)).
    rewrite H by (left; reflexivity).
    rewrite IH by (intros t Hin; apply H; right; exact Hin).
    reflexivity.
Qed.

Lemma trans_ren : forall t (xi:var->var), trans (rename xi t) = rename xi (trans t).
Proof.
  intros t. revert t.
  apply (well_founded_induction term_lt_wf (fun t => forall xi, trans (rename xi t) = rename xi (trans t))).
  intros t IH xi. destruct t; simpl.
  - reflexivity.
  - assert (H1 : forall xi, trans (rename xi t1) = rename xi (trans t1)).
    { intros; apply IH; unfold term_lt; simpl; lia. }
    assert (H2 : forall xi, trans (rename xi t2) = rename xi (trans t2)).
    { intros; apply IH; unfold term_lt; simpl; lia. }
    rewrite H1, H2. reflexivity.
  - f_equal. apply IH. unfold term_lt; simpl; lia.
  - f_equal. apply IH. unfold term_lt; simpl; lia.
  - f_equal. apply IH. unfold term_lt; simpl; lia.
  - (* Default *)
    assert (H1 : forall xi, trans (rename xi t1) = rename xi (trans t1)).
    { intros; apply IH; unfold term_lt; simpl; lia. }
    assert (H2 : forall xi, trans (rename xi t2) = rename xi (trans t2)).
    { intros; apply IH; unfold term_lt; simpl; lia. }
    assert (HL : forall xi, List.map trans (mmap (rename xi) ts) = mmap (rename xi) (List.map trans ts)).
    { intros xi0. apply map_ren_trans_list. intros t0 Hin.
      apply IH. unfold term_lt. simpl. pose proof (tsize_in _ _ Hin). lia. }
    (repeat f_equal); solve [apply HL | apply H1 | apply H2 | reflexivity].
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - assert (H1 : forall xi, trans (rename xi t1) = rename xi (trans t1)).
    { intros; apply IH; unfold term_lt; simpl; lia. }
    assert (H2 : forall xi, trans (rename xi t2) = rename xi (trans t2)).
    { intros; apply IH; unfold term_lt; simpl; lia. }
    rewrite H1, H2. reflexivity.
  - assert (H1 : forall xi, trans (rename xi t1) = rename xi (trans t1)).
    { intros; apply IH; unfold term_lt; simpl; lia. }
    assert (H2 : forall xi, trans (rename xi t2) = rename xi (trans t2)).
    { intros; apply IH; unfold term_lt; simpl; lia. }
    assert (H3 : forall xi, trans (rename xi t3) = rename xi (trans t3)).
    { intros; apply IH; unfold term_lt; simpl; lia. }
    (repeat f_equal); solve [apply H1 | apply H2 | apply H3 | reflexivity].
  - reflexivity.
  - f_equal. apply IH. unfold term_lt; simpl; lia.
  - (* Fold *)
    assert (H1 : forall xi, trans (rename xi t1) = rename xi (trans t1)).
    { intros; apply IH; unfold term_lt; simpl; lia. }
    assert (H2 : forall xi, trans (rename xi t2) = rename xi (trans t2)).
    { intros; apply IH; unfold term_lt; simpl; lia. }
    assert (HL : forall xi, List.map trans (mmap (rename xi) ts) = mmap (rename xi) (List.map trans ts)).
    { intros xi0. apply map_ren_trans_list. intros t0 Hin.
      apply IH. unfold term_lt. simpl. pose proof (tsize_in _ _ Hin). lia. }
    (repeat f_equal); solve [apply HL | apply H1 | apply H2 | reflexivity].
  - assert (H1 : forall xi, trans (rename xi t1) = rename xi (trans t1)).
    { intros; apply IH; unfold term_lt; simpl; lia. }
    assert (H2 : forall xi, trans (rename xi t2) = rename xi (trans t2)).
    { intros; apply IH; unfold term_lt; simpl; lia. }
    assert (H3 : forall xi, trans (rename xi t3) = rename xi (trans t3)).
    { intros; apply IH; unfold term_lt; simpl; lia. }
    rewrite H1, H2, H3. reflexivity.
Qed.

Lemma subst_list_map : forall (ts:list term) (sigma:var->term),
  ts..[sigma] = List.map (fun t => t.[sigma]) ts.
Proof.
  intros. induction ts.
  - reflexivity.
  - change (a.[sigma] :: ts..[sigma] = a.[sigma] :: List.map (fun t => t.[sigma]) ts).
    rewrite IHts. reflexivity.
Qed.

Lemma map_subst_trans_list : forall (ts:list term) sigma tau,
  (forall t, In t ts -> trans (t.[sigma]) = (trans t).[tau]) ->
  List.map trans (ts..[sigma]) = (List.map trans ts)..[tau].
Proof.
  intros ts sigma tau H. induction ts as [|a tl IH].
  - reflexivity.
  - change (trans (a.[sigma]) :: List.map trans (tl..[sigma])
            = (trans a).[tau] :: (List.map trans tl)..[tau]).
    rewrite H by (left; reflexivity).
    rewrite IH by (intros t Hin; apply H; right; exact Hin).
    reflexivity.
Qed.

Lemma up_trans : forall (sigma tau:var->term),
  (forall n, tau n = trans (sigma n)) ->
  forall n, up tau n = trans (up sigma n).
Proof.
  intros sigma tau H [|n].
  - rewrite up_0, up_0. reflexivity.
  - rewrite up_S, up_S, trans_ren, H. reflexivity.
Qed.

Lemma trans_subst_gen : forall t sigma tau,
  (forall n, tau n = trans (sigma n)) ->
  trans (t.[sigma]) = (trans t).[tau].
Proof.
  intros t. revert t.
  apply (well_founded_induction term_lt_wf (fun t => forall sigma tau,
     (forall n, tau n = trans (sigma n)) -> trans (t.[sigma]) = (trans t).[tau])).
  intros t IH sigma tau H. destruct t; simpl.
  - symmetry. apply H.
  - assert (H1 : trans (t1.[sigma]) = (trans t1).[tau]).
    { apply IH; [unfold term_lt; simpl; lia | exact H]. }
    assert (H2 : trans (t2.[sigma]) = (trans t2).[tau]).
    { apply IH; [unfold term_lt; simpl; lia | exact H]. }
    rewrite H1, H2. reflexivity.
  - f_equal. apply IH; [unfold term_lt; simpl; lia | apply up_trans; exact H].
  - f_equal. apply IH; [unfold term_lt; simpl; lia | exact H].
  - f_equal. apply IH; [unfold term_lt; simpl; lia | exact H].
  - (* Default *)
    assert (H1 : trans (t1.[sigma]) = (trans t1).[tau]).
    { apply IH; [unfold term_lt; simpl; lia | exact H]. }
    assert (H2 : trans (t2.[sigma]) = (trans t2).[tau]).
    { apply IH; [unfold term_lt; simpl; lia | exact H]. }
    assert (HL : List.map trans (ts..[sigma]) = (List.map trans ts)..[tau]).
    { apply map_subst_trans_list. intros t0 Hin.
      apply IH; [unfold term_lt; simpl; pose proof (tsize_in _ _ Hin); lia | exact H]. }
    (repeat f_equal); solve [apply HL | apply H1 | apply H2 | reflexivity].
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - assert (H1 : trans (t1.[sigma]) = (trans t1).[tau]).
    { apply IH; [unfold term_lt; simpl; lia | exact H]. }
    assert (H2 : trans (t2.[sigma]) = (trans t2).[tau]).
    { apply IH; [unfold term_lt; simpl; lia | exact H]. }
    rewrite H1, H2. reflexivity.
  - (* Match_ *)
    assert (H1 : trans (t1.[sigma]) = (trans t1).[tau]).
    { apply IH; [unfold term_lt; simpl; lia | exact H]. }
    assert (H2 : trans (t2.[sigma]) = (trans t2).[tau]).
    { apply IH; [unfold term_lt; simpl; lia | exact H]. }
    assert (H3 : trans (t3.[up sigma]) = (trans t3).[up tau]).
    { apply IH; [unfold term_lt; simpl; lia | apply up_trans; exact H]. }
    (repeat f_equal); solve [apply H1 | apply H2 | apply H3 | reflexivity].
  - reflexivity.
  - f_equal. apply IH; [unfold term_lt; simpl; lia | exact H].
  - (* Fold *)
    assert (H1 : trans (t1.[sigma]) = (trans t1).[tau]).
    { apply IH; [unfold term_lt; simpl; lia | exact H]. }
    assert (H2 : trans (t2.[sigma]) = (trans t2).[tau]).
    { apply IH; [unfold term_lt; simpl; lia | exact H]. }
    assert (HL : List.map trans (ts..[sigma]) = (List.map trans ts)..[tau]).
    { apply map_subst_trans_list. intros t0 Hin.
      apply IH; [unfold term_lt; simpl; pose proof (tsize_in _ _ Hin); lia | exact H]. }
    (repeat f_equal); solve [apply HL | apply H1 | apply H2 | reflexivity].
  - (* If *)
    assert (H1 : trans (t1.[sigma]) = (trans t1).[tau]).
    { apply IH; [unfold term_lt; simpl; lia | exact H]. }
    assert (H2 : trans (t2.[sigma]) = (trans t2).[tau]).
    { apply IH; [unfold term_lt; simpl; lia | exact H]. }
    assert (H3 : trans (t3.[sigma]) = (trans t3).[tau]).
    { apply IH; [unfold term_lt; simpl; lia | exact H]. }
    rewrite H1, H2, H3. reflexivity.
Qed.

Lemma trans_subst : forall t sigma,
  trans (t.[sigma]) = (trans t).[fun n => trans (sigma n)].
Proof. intros. apply trans_subst_gen. reflexivity. Qed.

Lemma up_ext : forall (sigma tau:var->term),
  (forall n, sigma n = tau n) -> forall n, up sigma n = up tau n.
Proof.
  intros sigma tau H [|n]; [rewrite up_0, up_0 | rewrite up_S, up_S, H]; reflexivity.
Qed.

Lemma subst_list_ext : forall (ts:list term) sigma tau,
  (forall t, In t ts -> t.[sigma] = t.[tau]) -> ts..[sigma] = ts..[tau].
Proof.
  intros ts sigma tau H. induction ts as [|a tl IH].
  - reflexivity.
  - change (a.[sigma] :: tl..[sigma] = a.[tau] :: tl..[tau]).
    rewrite H by (left; reflexivity).
    rewrite IH by (intros x Hin; apply H; right; exact Hin).
    reflexivity.
Qed.

Lemma subst_ext : forall t sigma tau,
  (forall n, sigma n = tau n) -> t.[sigma] = t.[tau].
Proof.
  intros t. revert t.
  apply (well_founded_induction term_lt_wf (fun t => forall sigma tau,
    (forall n, sigma n = tau n) -> t.[sigma] = t.[tau])).
  intros t IH sigma tau H. destruct t; simpl.
  - apply H.
  - assert (H1 : t1.[sigma] = t1.[tau]) by (apply IH; [unfold term_lt; simpl; lia | exact H]).
    assert (H2 : t2.[sigma] = t2.[tau]) by (apply IH; [unfold term_lt; simpl; lia | exact H]).
    rewrite H1, H2. reflexivity.
  - f_equal. apply IH; [unfold term_lt; simpl; lia | apply up_ext; exact H].
  - f_equal. apply IH; [unfold term_lt; simpl; lia | exact H].
  - f_equal. apply IH; [unfold term_lt; simpl; lia | exact H].
  - (* Default *)
    assert (H1 : t1.[sigma] = t1.[tau]) by (apply IH; [unfold term_lt; simpl; lia | exact H]).
    assert (H2 : t2.[sigma] = t2.[tau]) by (apply IH; [unfold term_lt; simpl; lia | exact H]).
    assert (HL : ts..[sigma] = ts..[tau]).
    { apply subst_list_ext. intros t0 Hin.
      apply IH; [unfold term_lt; simpl; pose proof (tsize_in _ _ Hin); lia | exact H]. }
    rewrite HL, H1, H2. reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - assert (H1 : t1.[sigma] = t1.[tau]) by (apply IH; [unfold term_lt; simpl; lia | exact H]).
    assert (H2 : t2.[sigma] = t2.[tau]) by (apply IH; [unfold term_lt; simpl; lia | exact H]).
    rewrite H1, H2. reflexivity.
  - (* Match_ *)
    assert (H1 : t1.[sigma] = t1.[tau]) by (apply IH; [unfold term_lt; simpl; lia | exact H]).
    assert (H2 : t2.[sigma] = t2.[tau]) by (apply IH; [unfold term_lt; simpl; lia | exact H]).
    assert (H3 : t3.[up sigma] = t3.[up tau]) by (apply IH; [unfold term_lt; simpl; lia | apply up_ext; exact H]).
    rewrite H1, H2, H3. reflexivity.
  - reflexivity.
  - f_equal. apply IH; [unfold term_lt; simpl; lia | exact H].
  - (* Fold *)
    assert (H1 : t1.[sigma] = t1.[tau]) by (apply IH; [unfold term_lt; simpl; lia | exact H]).
    assert (H2 : t2.[sigma] = t2.[tau]) by (apply IH; [unfold term_lt; simpl; lia | exact H]).
    assert (HL : ts..[sigma] = ts..[tau]).
    { apply subst_list_ext. intros t0 Hin.
      apply IH; [unfold term_lt; simpl; pose proof (tsize_in _ _ Hin); lia | exact H]. }
    rewrite HL, H1, H2. reflexivity.
  - assert (H1 : t1.[sigma] = t1.[tau]) by (apply IH; [unfold term_lt; simpl; lia | exact H]).
    assert (H2 : t2.[sigma] = t2.[tau]) by (apply IH; [unfold term_lt; simpl; lia | exact H]).
    assert (H3 : t3.[sigma] = t3.[tau]) by (apply IH; [unfold term_lt; simpl; lia | exact H]).
    rewrite H1, H2, H3. reflexivity.
Qed.

(* ---------- star lifting ---------- *)
Lemma star_trans : forall a b c, star sred a b -> star sred b c -> star sred a c.
Proof.
  intros a b c H1. revert c.
  induction H1 as [a0 | a0 b0 c0 Hab Hbc IH]; intros c H2.
  - exact H2.
  - eapply star_step; [exact Hab | apply IH; exact H2].
Qed.

Lemma star_app_left : forall t1 t2 u, star sred t1 t2 -> star sred (App t1 u) (App t2 u).
Proof.
  intros t1 t2 u H. induction H.
  - apply star_refl.
  - eapply star_step. apply sred_app_left. eassumption. eassumption.
Qed.

Lemma star_app_right_closure : forall t sigma u1 u2,
  star sred u1 u2 -> star sred (App (Value (Closure t sigma)) u1) (App (Value (Closure t sigma)) u2).
Proof.
  intros t sigma u1 u2 H. induction H.
  - apply star_refl.
  - eapply star_step. apply sred_app_right. eassumption. eassumption.
Qed.

Lemma star_binop_left : forall op t1 t2 u, star sred t1 t2 -> star sred (Binop op t1 u) (Binop op t2 u).
Proof.
  intros op t1 t2 u H. induction H.
  - apply star_refl.
  - eapply star_step. apply sred_binop_left. eassumption. eassumption.
Qed.

Lemma star_binop_right : forall op v u1 u2, star sred u1 u2 -> star sred (Binop op (Value v) u1) (Binop op (Value v) u2).
Proof.
  intros op v u1 u2 H. induction H.
  - apply star_refl.
  - eapply star_step. apply sred_binop_right. eassumption. eassumption.
Qed.

Lemma star_match_cond : forall u1 u2 t1 t2, star sred u1 u2 -> star sred (Match_ u1 t1 t2) (Match_ u2 t1 t2).
Proof.
  intros u1 u2 t1 t2 H. induction H.
  - apply star_refl.
  - eapply star_step. apply sred_match_cond. eassumption. eassumption.
Qed.

Lemma star_if_cond : forall u1 u2 ta tb, star sred u1 u2 -> star sred (If u1 ta tb) (If u2 ta tb).
Proof.
  intros u1 u2 ta tb H. induction H.
  - apply star_refl.
  - eapply star_step. apply sred_if_cond. eassumption. eassumption.
Qed.

Lemma star_esome : forall t1 t2, star sred t1 t2 -> star sred (ESome t1) (ESome t2).
Proof.
  intros t1 t2 H. induction H.
  - apply star_refl.
  - eapply star_step. apply sred_Some_context. eassumption. eassumption.
Qed.

Lemma star_fold_acc : forall f ts t1 t2, star sred t1 t2 -> star sred (Fold f ts t1) (Fold f ts t2).
Proof.
  intros f ts t1 t2 H. induction H.
  - apply star_refl.
  - eapply star_step. apply sred_Fold_step. eassumption. eassumption.
Qed.

Lemma star_default_J : forall tj1 tj2 tc, star sred tj1 tj2 -> star sred (Default [] tj1 tc) (Default [] tj2 tc).
Proof.
  intros tj1 tj2 tc H. induction H.
  - apply star_refl.
  - eapply star_step. apply sred_default_J. eassumption. eassumption.
Qed.

Lemma star_default_E_one : forall vi tj tj' ts j c, star sred tj tj' ->
  star sred (Default (Value (VPure vi) :: tj :: ts) j c) (Default (Value (VPure vi) :: tj' :: ts) j c).
Proof.
  intros vi tj tj' ts j c H. induction H.
  - apply star_refl.
  - eapply star_step. apply sred_default_E_one. eassumption. eassumption.
Qed.

Lemma star_default_E_zero : forall ti ti' ts j c, star sred ti ti' ->
  star sred (Default (ti :: ts) j c) (Default (ti' :: ts) j c).
Proof.
  intros ti ti' ts j c H. induction H.
  - apply star_refl.
  - eapply star_step. apply sred_default_E_zero. eassumption. eassumption.
Qed.

(* ---------- process_exceptions evaluation ---------- *)
Definition pbody := (Match_ (Var 0) (Var 1) (Match_ (Var 2) (Var 1) (Conflict))).
Definition pe_body (xv:value) := (Match_ (Var 0) (Value xv) (Match_ (Value xv) (Var 1) Conflict)).
Definition pe_res (xv yv:value) := (Match_ (Value yv) (Value xv) (Match_ (Value xv) (Value yv) Conflict)).

Lemma pe_beta1 : forall xv, (Lam pbody).[subst_of_env (xv :: [])] = Lam (pe_body xv).
Proof. intros. reflexivity. Qed.
Lemma pe_beta2 : forall xv yv, (pe_body xv).[subst_of_env (yv :: [])] = pe_res xv yv.
Proof. intros. reflexivity. Qed.

Lemma pe_res_none : forall xv, star sred (pe_res xv VNone) (Value xv).
Proof. intros. eapply star_step. apply sred_match_None. apply star_refl. Qed.

Lemma pe_res_some_none : forall v, star sred (pe_res VNone (VSome v)) (Value (VSome v)).
Proof.
  intros v.
  eapply star_step. apply sred_match_Some.
  change (star sred (Match_ (Value VNone) (Value (VSome v)) Conflict) (Value (VSome v))).
  eapply star_step. apply sred_match_None. apply star_refl.
Qed.

Lemma pe_res_some_some : forall w v, star sred (pe_res (VSome w) (VSome v)) Conflict.
Proof.
  intros w v.
  eapply star_step. apply sred_match_Some.
  change (star sred (Match_ (Value (VSome w)) (Value (VSome v)) Conflict) Conflict).
  eapply star_step. apply sred_match_Some.
  simpl. apply star_refl.
Qed.

Lemma closure_apply_any : forall xv yv,
  star sred (App (App (Value (Closure (Lam pbody) [])) (Value xv)) (Value yv)) (pe_res xv yv).
Proof.
  intros xv yv.
  eapply star_step. apply sred_app_left. apply sred_beta.
  rewrite pe_beta1.
  eapply star_step. apply sred_app_left. apply sred_lam.
  eapply star_step. apply sred_beta.
  rewrite pe_beta2. apply star_refl.
Qed.

Lemma pe_value_any : forall xv yv,
  star sred (App (App process_exceptions (Value xv)) (Value yv)) (pe_res xv yv).
Proof.
  intros xv yv.
  eapply star_step. apply sred_app_left. apply sred_app_left. apply sred_lam.
  apply closure_apply_any.
Qed.

Lemma pe_value_none_none : star sred (App (App process_exceptions (Value VNone)) (Value VNone)) (Value VNone).
Proof. eapply star_trans. apply pe_value_any. apply pe_res_none. Qed.

Lemma pe_value_some_none : forall w,
  star sred (App (App process_exceptions (Value (VSome w))) (Value VNone)) (Value (VSome w)).
Proof. intros. eapply star_trans. apply pe_value_any. apply pe_res_none. Qed.

Lemma pe_value_none_some : forall v,
  star sred (App (App process_exceptions (Value VNone)) (Value (VSome v))) (Value (VSome v)).
Proof. intros. eapply star_trans. apply pe_value_any. apply pe_res_some_none. Qed.

Lemma pe_value_some_some : forall w v,
  star sred (App (App process_exceptions (Value (VSome w))) (Value (VSome v))) Conflict.
Proof. intros. eapply star_trans. apply pe_value_any. apply pe_res_some_some. Qed.

Lemma pe_conflict_any : forall yv,
  star sred (App (App process_exceptions Conflict) (Value yv)) Conflict.
Proof.
  intros yv.
  assert (H : star sred (App process_exceptions Conflict) Conflict).
  { eapply star_step. apply sred_app_left. apply sred_lam.
    eapply star_step. apply sred_app_left_conflict. apply star_refl. }
  eapply star_trans.
  - apply star_app_left. exact H.
  - eapply star_step. apply sred_app_right_conflict. apply star_refl.
Qed.

Lemma G_common : forall x y c, star sred x y ->
  star sred (App (App process_exceptions x) c) (App (App (Value (Closure (Lam pbody) [])) y) c).
Proof.
  intros x y c Hxy.
  assert (H1 : star sred (App process_exceptions x) (App (Value (Closure (Lam pbody) [])) y)).
  { eapply star_trans.
    - eapply star_step. apply sred_app_left. apply sred_lam. apply star_refl.
    - apply star_app_right_closure. exact Hxy. }
  apply star_app_left. exact H1.
Qed.

Lemma pe_ENone_none : star sred (App (App process_exceptions ENone) (Value VNone)) (Value VNone).
Proof.
  eapply star_trans.
  - eapply G_common. eapply star_step. apply sred_None. apply star_refl.
  - eapply star_trans.
    + apply closure_apply_any.
    + apply pe_res_none.
Qed.

Lemma pe_ENone_some : forall v,
  star sred (App (App process_exceptions ENone) (Value (VSome v))) (Value (VSome v)).
Proof.
  intros v.
  eapply star_trans.
  - eapply G_common. eapply star_step. apply sred_None. apply star_refl.
  - eapply star_trans.
    + apply closure_apply_any.
    + apply pe_res_some_none.
Qed.

(* ---------- fold lemmas ---------- *)
Lemma fold_acc_none : forall ts, star sred (Fold process_exceptions ts ENone) (Fold process_exceptions ts (Value VNone)).
Proof. intros. eapply star_step. apply sred_Fold_step. apply sred_None. apply star_refl. Qed.

Lemma fold_nil_none : star sred (Fold process_exceptions [] ENone) (Value VNone).
Proof. eapply star_trans. apply fold_acc_none. eapply star_step. apply sred_Fold_init. apply star_refl. Qed.

Lemma fold_init : forall v, star sred (Fold process_exceptions [] (Value v)) (Value v).
Proof. intros. eapply star_step. apply sred_Fold_init. apply star_refl. Qed.

Lemma fold_conflict : forall ts, star sred (Fold process_exceptions ts Conflict) Conflict.
Proof. intros. eapply star_step. apply sred_Fold_Conflict. apply star_refl. Qed.

Lemma fold_head_none : forall a rest,
  star sred (Fold process_exceptions (a::rest) ENone) (Fold process_exceptions rest (App (App process_exceptions a) (Value VNone))).
Proof.
  intros. eapply star_step. apply sred_Fold_step. apply sred_None.
  eapply star_step. apply sred_Fold_rec. apply star_refl.
Qed.

Lemma fold_head_value : forall a rest v,
  star sred (Fold process_exceptions (a::rest) (Value v)) (Fold process_exceptions rest (App (App process_exceptions a) (Value v))).
Proof. intros. eapply star_step. apply sred_Fold_rec. apply star_refl. Qed.

Lemma fold_some_head : forall w rest,
  star sred (Fold process_exceptions (Value (VSome w) :: rest) ENone) (Fold process_exceptions rest (Value (VSome w))).
Proof.
  intros. eapply star_trans. apply fold_head_none. apply star_fold_acc. apply pe_value_some_none.
Qed.

Lemma fold_single_some : forall w,
  star sred (Fold process_exceptions [Value (VSome w)] ENone) (Value (VSome w)).
Proof. intros. eapply star_trans. apply fold_some_head. apply fold_init. Qed.

Lemma fold_two_some_conflict : forall w w' rest,
  star sred (Fold process_exceptions (Value (VSome w) :: Value (VSome w') :: rest) ENone) Conflict.
Proof.
  intros.
  eapply star_trans. apply fold_head_none.
  eapply star_trans.
  - apply star_fold_acc. apply pe_value_some_none.
  - eapply star_trans.
    + apply fold_head_value.
    + eapply star_trans.
      * apply star_fold_acc. apply pe_value_some_some.
      * apply fold_conflict.
Qed.

Lemma fold_enone_head : forall rest,
  star sred (Fold process_exceptions (ENone :: rest) ENone) (Fold process_exceptions rest (Value VNone)).
Proof.
  intros. eapply star_trans. apply fold_head_none. apply star_fold_acc. apply pe_ENone_none.
Qed.

Lemma fold_some_enone : forall w rest,
  star sred (Fold process_exceptions (Value (VSome w) :: ENone :: rest) ENone) (Fold process_exceptions rest (Value (VSome w))).
Proof.
  intros.
  eapply star_trans. apply fold_head_none.
  eapply star_trans.
  - apply star_fold_acc. apply pe_value_some_none.
  - eapply star_trans.
    + apply fold_head_value.
    + apply star_fold_acc. apply pe_ENone_some.
Qed.

Lemma fold_conflict_head : forall rest,
  star sred (Fold process_exceptions (Conflict :: rest) ENone) Conflict.
Proof.
  intros.
  eapply star_trans. apply fold_head_none.
  eapply star_trans.
  - apply star_fold_acc. apply pe_conflict_any.
  - apply fold_conflict.
Qed.

Lemma fold_some_conflict : forall w rest,
  star sred (Fold process_exceptions (Value (VSome w) :: Conflict :: rest) ENone) Conflict.
Proof.
  intros.
  eapply star_trans. apply fold_head_none.
  eapply star_trans.
  - apply star_fold_acc. apply pe_value_some_none.
  - eapply star_trans.
    + apply fold_head_value.
    + eapply star_trans.
      * apply star_fold_acc. apply pe_conflict_any.
      * apply fold_conflict.
Qed.

(* ---------- extra helpers for main theorem ---------- *)
Lemma subst_of_env_map_trans : forall (sigma:list value) n,
  subst_of_env (List.map trans_value sigma) n = trans (subst_of_env sigma n).
Proof.
  intros sigma. induction sigma as [|w rest IH]; intros n.
  - destruct n; reflexivity.
  - destruct n as [|k].
    + reflexivity.
    + simpl. apply IH.
Qed.

Lemma subst_of_env_cons_trans : forall (v:value) (sigma:list value) n,
  subst_of_env (trans_value v :: List.map trans_value sigma) n = trans (subst_of_env (v :: sigma) n).
Proof.
  intros v sigma [|k].
  - reflexivity.
  - unfold subst_of_env. cbn.
    rewrite nth_error_map.
    rewrite length_map.
    destruct (nth_error sigma k) as [w|]; reflexivity.
Qed.

Lemma trans_subst1 : forall t (v:value),
  trans (t.[Value v/]) = (trans t).[Value (trans_value v)/].
Proof.
  intros. erewrite trans_subst.
  apply subst_ext. intros [|n]; reflexivity.
Qed.

Lemma get_op_trans : forall op v1 v2 v,
  Some v = get_op op v1 v2 -> Some (trans_value v) = get_op op (trans_value v1) (trans_value v2).
Proof.
  intros op v1 v2 v H. destruct op; destruct v1; destruct v2; simpl in *; try discriminate;
    inversion H; subst; reflexivity.
Qed.

(* ================= main theorem ================= *)
Theorem correction_small_steps:
  forall s1 s2,
  sred s1 s2 ->
  exists target,
    star sred (trans s1) target /\
    star sred (trans s2) target.
Proof.
  intros s1 s2 H.
  induction H as [ t
    | t v sigma'
    | t sigma
    | u
    | t u1 u2 sigma _ IH
    | t1 t2 u _ IH
    | op v v1 v2 Hget
    | op u
    | op v
    | op v u1 u2 _ IH
    | op t1 t2 u _ IH
    | tc
    | tc
    | tc
    | tj1 tj2 tc _ IH
    | ts vi vj tjust tcons
    | vi tjust tcons
    | ts2 tjust tcons
    | vi ts2 tjust tcons
    | vi ts tjust tcons
    | ts2 tj tc
    | vi tj tj' ts3 tjust tcons _ IH
    | ti ti' ts2 tj tc _ IH
    | t1 t2
    | v t1 t2
    | t1 t2
    | u1 u2 t1 t2 _ IH
    |
    |
    | v
    | t1 t2 _ IH
    | ta tb
    | ta tb
    | ta tb
    | u1 u2 ta tb _ IH
    | ta tb _ IH
    |
    | v
    |
    | v
    | ta tb _ IH
    |
    | f h t v
    | f v
    | f ts t1 t2 _ IH
    | f ts
  ].
  - (* sred_lam *)
    exists (Value (Closure (trans t) [])).
    split.
    + eapply star_step. apply sred_lam. apply star_refl.
    + apply star_refl.
  - (* sred_beta *)
    exists ((trans t).[subst_of_env (trans_value v :: List.map trans_value sigma')]).
    split.
    + eapply star_step. apply sred_beta. apply star_refl.
    + rewrite trans_subst.
      assert (E : (trans t).[(fun n => trans (subst_of_env (v :: sigma') n))]
                = (trans t).[subst_of_env (trans_value v :: List.map trans_value sigma')]).
      { apply subst_ext. intros n. symmetry. apply subst_of_env_cons_trans. }
      rewrite E. apply star_refl.
  - (* sred_app_left_conflict *)
    exists Conflict. split.
    + eapply star_step. apply sred_app_left_conflict. apply star_refl.
    + apply star_refl.
  - (* sred_app_right_conflict *)
    exists Conflict. split.
    + eapply star_step. apply sred_app_right_conflict. apply star_refl.
    + apply star_refl.
  - (* sred_app_right *)
    destruct IH as (T & H1 & H2).
    exists (App (Value (Closure (trans t) (List.map trans_value sigma))) T).
    split; apply star_app_right_closure; assumption.
  - (* sred_app_left *)
    destruct IH as (T & H1 & H2).
    exists (App T (trans u)).
    split; apply star_app_left; assumption.
  - (* sred_binop_finish *)
    exists (Value (trans_value v)). split.
    + eapply star_step. eapply sred_binop_finish. apply get_op_trans. exact Hget.
      apply star_refl.
    + apply star_refl.
  - (* sred_binop_right_conflict *)
    exists Conflict. split.
    + eapply star_step. apply sred_binop_right_conflict. apply star_refl.
    + apply star_refl.
  - (* sred_binop_left_conflict *)
    exists Conflict. split.
    + eapply star_step. apply sred_binop_left_conflict. apply star_refl.
    + apply star_refl.
  - (* sred_binop_right *)
    destruct IH as (T & H1 & H2).
    exists (Binop op (Value (trans_value v)) T).
    split; apply star_binop_right; assumption.
  - (* sred_binop_left *)
    destruct IH as (T & H1 & H2).
    exists (Binop op T (trans u)).
    split; apply star_binop_left; assumption.
  - (* sred_default_JTrue *)
    exists (trans tc). split.
    + eapply star_trans. apply star_match_cond. apply fold_nil_none.
      eapply star_step. apply sred_match_None.
      eapply star_step. apply sred_if_true. apply star_refl.
    + apply star_refl.
  - (* sred_default_JFalse *)
    exists ENone. split.
    + eapply star_trans. apply star_match_cond. apply fold_nil_none.
      eapply star_step. apply sred_match_None.
      eapply star_step. apply sred_if_false. apply star_refl.
    + apply star_refl.
  - (* sred_default_JConflict *)
    exists Conflict. split.
    + eapply star_trans. apply star_match_cond. apply fold_nil_none.
      eapply star_step. apply sred_match_None.
      eapply star_step. apply sred_if_cond_conflict. apply star_refl.
    + apply star_refl.
  - (* sred_default_J *)
    destruct IH as (T & H1 & H2).
    exists (If T (trans tc) ENone).
    split.
    + eapply star_trans. apply star_match_cond. apply fold_nil_none.
      eapply star_trans. eapply star_step. apply sred_match_None. apply star_refl.
      apply star_if_cond. exact H1.
    + eapply star_trans. apply star_match_cond. apply fold_nil_none.
      eapply star_trans. eapply star_step. apply sred_match_None. apply star_refl.
      apply star_if_cond. exact H2.
  - (* sred_default_Conflict *)
    exists Conflict. split.
    + eapply star_trans. apply star_match_cond. apply fold_two_some_conflict.
      eapply star_step. apply sred_match_conflict. apply star_refl.
    + apply star_refl.
  - (* sred_default_E_value *)
    exists (Value (VSome (trans_value vi))). split.
    + eapply star_trans. apply star_match_cond. apply fold_single_some.
      eapply star_step. apply sred_match_Some.
      eapply star_step. apply sred_Some. apply star_refl.
    + apply star_refl.
  - (* sred_default_E_zero_conflict *)
    exists Conflict. split.
    + eapply star_trans. apply star_match_cond. apply fold_conflict_head.
      eapply star_step. apply sred_match_conflict. apply star_refl.
    + apply star_refl.
  - (* sred_default_E_one_conflict *)
    exists Conflict. split.
    + eapply star_trans. apply star_match_cond. apply fold_some_conflict.
      eapply star_step. apply sred_match_conflict. apply star_refl.
    + apply star_refl.
  - (* sred_default_E_one_empty *)
    exists (Match_ (Fold process_exceptions (List.map trans ts) (Value (VSome (trans_value vi))))
              (If (trans tjust) (trans tcons) ENone) (ESome (Var 0))).
    split.
    + apply star_match_cond. apply fold_some_enone.
    + apply star_match_cond. apply fold_some_head.
  - (* sred_default_E_zero_empty *)
    exists (Match_ (Fold process_exceptions (List.map trans ts2) (Value VNone))
              (If (trans tj) (trans tc) ENone) (ESome (Var 0))).
    split.
    + apply star_match_cond. apply fold_enone_head.
    + apply star_match_cond. apply fold_acc_none.
  - (* sred_default_E_one *)
    destruct IH as (T & H1 & H2).
    exists (Match_ (Fold process_exceptions (List.map trans ts3)
                    (App (App (Value (Closure (Lam pbody) [])) T) (Value (VSome (trans_value vi)))))
              (If (trans tjust) (trans tcons) ENone) (ESome (Var 0))).
    split.
    + apply star_match_cond.
      eapply star_trans. apply fold_some_head.
      eapply star_trans. apply fold_head_value.
      apply star_fold_acc. apply G_common. exact H1.
    + apply star_match_cond.
      eapply star_trans. apply fold_some_head.
      eapply star_trans. apply fold_head_value.
      apply star_fold_acc. apply G_common. exact H2.
  - (* sred_default_E_zero *)
    destruct IH as (T & H1 & H2).
    exists (Match_ (Fold process_exceptions (List.map trans ts2)
                    (App (App (Value (Closure (Lam pbody) [])) T) (Value VNone)))
              (If (trans tj) (trans tc) ENone) (ESome (Var 0))).
    split.
    + apply star_match_cond.
      eapply star_trans. apply fold_head_none.
      apply star_fold_acc. apply G_common. exact H1.
    + apply star_match_cond.
      eapply star_trans. apply fold_head_none.
      apply star_fold_acc. apply G_common. exact H2.
  - (* sred_match_None *)
    exists (trans t1). split.
    + eapply star_step. apply sred_match_None. apply star_refl.
    + apply star_refl.
  - (* sred_match_Some *)
    exists ((trans t2).[Value (trans_value v)/]). split.
    + eapply star_step. apply sred_match_Some. apply star_refl.
    + rewrite trans_subst1. apply star_refl.
  - (* sred_match_conflict *)
    exists Conflict. split.
    + eapply star_step. apply sred_match_conflict. apply star_refl.
    + apply star_refl.
  - (* sred_match_cond *)
    destruct IH as (T & H1 & H2).
    exists (Match_ T (trans t1) (trans t2)).
    split; apply star_match_cond; assumption.
  - (* sred_None *)
    exists (Value VNone). split.
    + eapply star_step. apply sred_None. apply star_refl.
    + apply star_refl.
  - (* sred_Some_conflict *)
    exists Conflict. split.
    + eapply star_step. apply sred_Some_conflict. apply star_refl.
    + apply star_refl.
  - (* sred_Some *)
    exists (Value (VSome (trans_value v))). split.
    + eapply star_step. apply sred_Some. apply star_refl.
    + apply star_refl.
  - (* sred_Some_context *)
    destruct IH as (T & H1 & H2).
    exists (ESome T).
    split; apply star_esome; assumption.
  - (* sred_if_cond_conflict *)
    exists Conflict. split.
    + eapply star_step. apply sred_if_cond_conflict. apply star_refl.
    + apply star_refl.
  - (* sred_if_true *)
    exists (trans ta). split.
    + eapply star_step. apply sred_if_true. apply star_refl.
    + apply star_refl.
  - (* sred_if_false *)
    exists (trans tb). split.
    + eapply star_step. apply sred_if_false. apply star_refl.
    + apply star_refl.
  - (* sred_if_cond *)
    destruct IH as (T & H1 & H2).
    exists (If T (trans ta) (trans tb)).
    split; apply star_if_cond; assumption.
  - (* sred_ErrorOnEmpty *)
    destruct IH as (T & H1 & H2).
    exists (Match_ T Conflict (Var 0)).
    split; apply star_match_cond; assumption.
  - (* sred_eoe_empty *)
    exists Conflict. split.
    + eapply star_trans. apply star_match_cond.
      eapply star_step. apply sred_None. apply star_refl.
      eapply star_step. apply sred_match_None. apply star_refl.
    + apply star_refl.
  - (* sred_eoe_value *)
    exists (Value (trans_value v)). split.
    + eapply star_step. apply sred_match_Some. apply star_refl.
    + apply star_refl.
  - (* sred_eoe_conflict *)
    exists Conflict. split.
    + eapply star_step. apply sred_match_conflict. apply star_refl.
    + apply star_refl.
  - (* sred_DefaultPure_value *)
    exists (Value (VSome (trans_value v))). split.
    + eapply star_step. apply sred_Some. apply star_refl.
    + apply star_refl.
  - (* sred_DefaultPure *)
    destruct IH as (T & H1 & H2).
    exists (ESome T).
    split; apply star_esome; assumption.
  - (* sred_DefaultPure_conflit *)
    exists Conflict. split.
    + eapply star_step. apply sred_Some_conflict. apply star_refl.
    + apply star_refl.
  - (* sred_Fold_rec *)
    exists (Fold (trans f) (List.map trans t) (App (App (trans f) (trans h)) (Value (trans_value v)))).
    split.
    + eapply star_step. apply sred_Fold_rec. apply star_refl.
    + apply star_refl.
  - (* sred_Fold_init *)
    exists (Value (trans_value v)). split.
    + eapply star_step. apply sred_Fold_init. apply star_refl.
    + apply star_refl.
  - (* sred_Fold_step *)
    destruct IH as (T & H1 & H2).
    exists (Fold (trans f) (List.map trans ts) T).
    split; apply star_fold_acc; assumption.
  - (* sred_Fold_Conflict *)
    exists Conflict. split.
    + eapply star_step. apply sred_Fold_Conflict. apply star_refl.
    + apply star_refl.
Qed.
