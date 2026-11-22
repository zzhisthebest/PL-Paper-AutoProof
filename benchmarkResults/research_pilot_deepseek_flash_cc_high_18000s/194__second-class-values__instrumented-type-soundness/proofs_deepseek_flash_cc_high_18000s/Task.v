Require Export Arith.EqNat.

From Stdlib Require Export PeanoNat.

Require Export stlc1.

Inductive wf_env : venv -> tenv -> Prop :=
| wfe_nil : forall n, wf_env (@Def vl nil nil n) (@Def ty nil nil n)
| wfe_cons : forall v t vs ts n,
    val_type (expand_env vs v n) v t ->
    wf_env vs ts ->
    get_inv_idx vs = get_inv_idx ts ->
    wf_env (expand_env vs v n) (expand_env ts t n)

with val_type : venv -> vl -> ty -> Prop :=
| v_bool: forall venv b,
    val_type venv (vbool b) TBool
| v_abs: forall env venv tenv y T1 T2 m retcl,
    wf_env venv tenv ->
    has_type (expand_env (expand_env tenv (TFun T1 m T2 retcl) Second) T1 m) y retcl T2 ->
    val_type env (vabs venv m y retcl) (TFun T1 m T2 retcl).

Inductive stp: venv -> ty -> venv -> ty -> Prop :=
| stp_refl: forall G1 G2 T,
   stp G1 T G2 T.

Inductive res_type: venv -> option vl -> ty -> Prop :=
| not_stuck: forall venv v T,
      val_type venv v T ->
      res_type venv (Some v) T.

(* ------------------------------------------------------------------ *)
(* Auxiliary machinery                                                *)
(* ------------------------------------------------------------------ *)

(* Mutual induction principle for the wf_env / val_type block.  Coq does
   not generate the individual schemes automatically because the two
   types are defined mutually. *)
Scheme wf_env_mut_ind := Induction for wf_env Sort Prop
  with val_type_mut_ind := Induction for val_type Sort Prop.

(* Accessors for the two components of an environment. *)
Definition fc {X : Type} (e : @env X) : list X :=
  match e with Def l _ _ => l end.

Definition sc {X : Type} (e : @env X) : list X :=
  match e with Def _ l _ => l end.

Lemma fc_expand_first : forall {X} (e : @env X) x,
  fc (expand_env e x First) = x :: fc e.
Proof. intros X e x. destruct e as [l1 l2 m]. reflexivity. Qed.

Lemma fc_expand_second : forall {X} (e : @env X) x,
  fc (expand_env e x Second) = fc e.
Proof. intros X e x. destruct e as [l1 l2 m]. reflexivity. Qed.

Lemma sc_expand_first : forall {X} (e : @env X) x,
  sc (expand_env e x First) = sc e.
Proof. intros X e x. destruct e as [l1 l2 m]. reflexivity. Qed.

Lemma sc_expand_second : forall {X} (e : @env X) x,
  sc (expand_env e x Second) = x :: sc e.
Proof. intros X e x. destruct e as [l1 l2 m]. reflexivity. Qed.

(* val_type does not actually depend on its first (venv) argument. *)
Lemma val_type_irrel : forall a b v t, val_type a v t -> val_type b v t.
Proof.
  intros a b v t H. inversion H; subst.
  - constructor.
  - econstructor; eauto.
Qed.

(* Inversion of a value of function type. *)
Lemma val_type_bool_inv : forall a b T, val_type a (vbool b) T -> T = TBool.
Proof. intros a b T H. inversion H. reflexivity. Qed.

Lemma vabs_inv_gen : forall a venv m y retcl T1 m' T2 retcl',
  val_type a (vabs venv m y retcl) (TFun T1 m' T2 retcl') ->
  m = m' /\ retcl = retcl' /\
  exists tenv, wf_env venv tenv /\
    has_type (expand_env (expand_env tenv (TFun T1 m' T2 retcl') Second) T1 m')
             y retcl' T2.
Proof.
  intros a venv m y retcl T1 m' T2 retcl' H. inversion H. subst.
  split; [reflexivity | split; [reflexivity | eauto]].
Qed.

Lemma sanitize_any_expand : forall {X} (e : @env X) x n k,
  sanitize_any (expand_env e x n) k = expand_env (sanitize_any e k) x n.
Proof.
  intros X e x n k. destruct e as [l1 l2 m]. destruct n; reflexivity.
Qed.

Lemma get_inv_idx_sanitize : forall {X} (e : @env X) k,
  get_inv_idx (sanitize_any e k) = k.
Proof. intros X e k. destruct e as [l1 l2 m]. reflexivity. Qed.

Lemma get_inv_idx_expand : forall {X} (e : @env X) x c,
  get_inv_idx (expand_env e x c) = get_inv_idx e.
Proof. intros X e x c. destruct e as [l1 l2 m]. destruct c; reflexivity. Qed.

(* Changing the sc_min index simultaneously in both environments
   preserves well-formedness. *)
Lemma wf_env_sanitize_any : forall vs ts, wf_env vs ts ->
  forall k, wf_env (sanitize_any vs k) (sanitize_any ts k).
Proof.
  intros vs ts H.
  refine (wf_env_mut_ind
            (fun vs ts _ => forall k, wf_env (sanitize_any vs k) (sanitize_any ts k))
            (fun _ _ _ _ => True) _ _ _ _ vs ts H).
  - intros n k. simpl. constructor.
  - intros v t vs0 ts0 n Hv IHv Hw IHw He k.
    rewrite sanitize_any_expand. rewrite sanitize_any_expand.
    apply wfe_cons with (v := v) (t := t) (vs := sanitize_any vs0 k)
                        (ts := sanitize_any ts0 k) (n := n).
    + eapply val_type_irrel. exact Hv.
    + apply IHw.
    + rewrite !get_inv_idx_sanitize. reflexivity.
  - intros. exact I.
  - intros. exact I.
Qed.

(* Indexed structural description of a list of values paired with a list
   of types. *)
Fixpoint lc (vs : list vl) (ts : list ty) : Prop :=
  match vs, ts with
  | [], [] => True
  | v :: vs', t :: ts' => val_type (@Def vl [] [] 0) v t /\ lc vs' ts'
  | _, _ => False
  end.

Lemma lc_length : forall vs ts, lc vs ts -> length vs = length ts.
Proof.
  intros vs. induction vs as [|v vs' IH]; intros ts H.
  - destruct ts; simpl in *; [reflexivity | contradiction].
  - destruct ts as [|t ts']; simpl in *; [contradiction |].
    destruct H as [Hv Htl]. simpl. f_equal. apply IH, Htl.
Qed.

Lemma index_Some_lt : forall {X} (l : list X) i a,
  index i l = Some a -> i < length l.
Proof.
  intros X l. induction l as [|a l' IH]; intros i b Hi; simpl in Hi.
  - discriminate.
  - destruct (Nat.eqb i (length l')) eqn:E.
    + apply Nat.eqb_eq in E. subst i. simpl. lia.
    + apply IH in Hi. simpl. lia.
Qed.

Lemma index_exists : forall {X} (l : list X) i,
  i < length l -> exists a, index i l = Some a.
Proof.
  intros X l. induction l as [|a l' IH]; intros i Hi.
  - simpl in Hi. lia.
  - simpl. destruct (Nat.eqb i (length l')) eqn:E.
    + exists a. reflexivity.
    + apply IH. apply Nat.eqb_neq in E. simpl in Hi. lia.
Qed.

Lemma lc_index : forall vs ts, lc vs ts ->
  forall i v, index i vs = Some v ->
    exists t, index i ts = Some t /\ val_type (@Def vl [] [] 0) v t.
Proof.
  intros vs. induction vs as [|v' vs' IH]; intros ts Hlc i v Hi.
  - destruct ts; simpl in *; [discriminate | contradiction].
  - destruct ts as [|t' ts']; simpl in *; [contradiction |].
    destruct Hlc as [Hv Htl].
    destruct (Nat.eqb i (length vs')) eqn:E.
    + injection Hi as Hveq. subst v.
      assert (Hlen : length vs' = length ts') by (apply lc_length, Htl).
      assert (E' : (i =? length ts') = true)
        by (apply Nat.eqb_eq; apply Nat.eqb_eq in E; lia).
      exists t'. simpl. rewrite E'. split; [reflexivity | exact Hv].
    + assert (E' : (i =? length ts') = false).
      { apply Nat.eqb_neq. apply Nat.eqb_neq in E.
        pose proof (lc_length _ _ Htl). lia. }
      rewrite E'. simpl. exact (IH ts' Htl i v Hi).
Qed.

Lemma lc_index_inv : forall vs ts, lc vs ts ->
  forall i t, index i ts = Some t ->
    exists v, index i vs = Some v /\ val_type (@Def vl [] [] 0) v t.
Proof.
  intros vs ts Hlc i t Hi.
  assert (Hlen : length vs = length ts) by (apply lc_length, Hlc).
  assert (Hlt : i < length vs)
    by (rewrite Hlen; exact (index_Some_lt ts i t Hi)).
  destruct (index_exists vs i Hlt) as [v Hv].
  destruct (lc_index vs ts Hlc i v Hv) as [t' [Ht' Hvt]].
  rewrite Hi in Ht'. injection Ht' as Heq. subst t'.
  exists v. split; [exact Hv | exact Hvt].
Qed.

(* Structural facts about well-formed environments. *)
Definition wf_facts (vs : venv) (ts : tenv) : Prop :=
  length (fc vs) = length (fc ts) /\
  length (sc vs) = length (sc ts) /\
  get_inv_idx vs = get_inv_idx ts /\
  lc (fc vs) (fc ts) /\
  lc (sc vs) (sc ts).

Lemma wf_env_facts : forall vs ts, wf_env vs ts -> wf_facts vs ts.
Proof.
  intros vs ts H.
  refine (wf_env_mut_ind
            (fun vs ts _ => wf_facts vs ts)
            (fun _ _ _ _ => True) _ _ _ _ vs ts H).
  - intros n. unfold wf_facts. simpl. repeat split; auto.
  - intros v t vs0 ts0 n Hv IHv Hw IHw He.
    unfold wf_facts in *.
    destruct IHw as (L1 & L2 & EI & C1 & C2).
    destruct vs0 as [vs1 vs2 vm]; destruct ts0 as [ts1 ts2 tm];
      destruct n; simpl in *.
    + split.
      * simpl. f_equal. exact L1.
      * split.
        -- exact L2.
        -- split.
           ++ exact EI.
           ++ split.
              ** split.
                 { eapply val_type_irrel. exact Hv. }
                 { exact C1. }
              ** exact C2.
    + split.
      * exact L1.
      * split.
        -- simpl. f_equal. exact L2.
        -- split.
           ++ exact EI.
           ++ split.
              ** exact C1.
              ** split.
                 { eapply val_type_irrel. exact Hv. }
                 { exact C2. }
  - intros. exact I.
  - intros. exact I.
Qed.

(* Sanitizing by a class preserves well-formedness. *)
Lemma wf_env_sanitize_env : forall c venv tenv,
  wf_env venv tenv -> wf_env (sanitize_env c venv) (sanitize_env c tenv).
Proof.
  intros c venv tenv H. destruct c.
  - destruct venv as [vs1 vs2 vm]; destruct tenv as [ts1 ts2 tm].
    pose proof (wf_env_facts _ _ H) as F.
    destruct F as (L1 & L2 & EI & C1 & C2).
    simpl in L2.
    simpl. rewrite <- L2.
    exact (wf_env_sanitize_any (Def vs1 vs2 vm) (Def ts1 ts2 tm) H (length vs2)).
  - exact H.
Qed.

(* Lookup correspondence between the two sides of a well-formed
   environment. *)
Lemma lookup_wf : forall venv tenv, wf_env venv tenv ->
  forall c x T, lookup x (sanitize_env c tenv) = Some T ->
    exists v, lookup x (sanitize_env c venv) = Some v /\ val_type venv v T.
Proof.
  intros venv tenv Hwf c x T Hlk.
  pose proof (wf_env_facts _ _ Hwf) as F.
  destruct F as (L1 & L2 & EI & C1 & C2).
  destruct venv as [vs1 vs2 vm]; destruct tenv as [ts1 ts2 tm].
  destruct x as [cl i]; destruct c; destruct cl; simpl in *.
  - (* sanitize First, V First *)
    destruct (lc_index_inv vs1 ts1 C1 i T Hlk) as [v [Hv Hvt]].
    exists v. split; [exact Hv | eapply val_type_irrel; exact Hvt].
  - (* sanitize First, V Second *)
    destruct (Nat.leb (length ts2) i) eqn:E; [| discriminate].
    destruct (lc_index_inv vs2 ts2 C2 i T Hlk) as [v [Hv Hvt]].
    exists v. split.
    + rewrite L2. rewrite E. simpl. exact Hv.
    + eapply val_type_irrel; exact Hvt.
  - (* sanitize Second, V First *)
    destruct (lc_index_inv vs1 ts1 C1 i T Hlk) as [v [Hv Hvt]].
    exists v. split; [exact Hv | eapply val_type_irrel; exact Hvt].
  - (* sanitize Second, V Second *)
    destruct (Nat.leb tm i) eqn:E; [| discriminate].
    destruct (lc_index_inv vs2 ts2 C2 i T Hlk) as [v [Hv Hvt]].
    exists v. split.
    + rewrite EI. rewrite E. simpl. exact Hv.
    + eapply val_type_irrel; exact Hvt.
Qed.

(* Extending a well-formed environment with a value of the argument type
   (and with the closure itself as a second-class member) stays
   well-formed. *)
Lemma wf_env_extend : forall (env2 : venv) (tenv0 : tenv) (vx : vl)
                             (T1 : ty) (m : class) (ey : tm) (retcl : class) (T2 : ty),
  wf_env env2 tenv0 ->
  has_type (expand_env (expand_env tenv0 (TFun T1 m T2 retcl) Second) T1 m)
           ey retcl T2 ->
  val_type env2 vx T1 ->
  wf_env (expand_env (expand_env env2 (vabs env2 m ey retcl) Second) vx m)
         (expand_env (expand_env tenv0 (TFun T1 m T2 retcl) Second) T1 m).
Proof.
  intros env2 tenv0 vx T1 m ey retcl T2 Hwf0 Hbody Hvx.
  pose proof (wf_env_facts _ _ Hwf0) as F.
  destruct F as (_ & _ & EI & _ & _).
  econstructor.
  - eapply val_type_irrel. exact Hvx.
  - econstructor.
    + apply v_abs with (tenv := tenv0); [ exact Hwf0 | exact Hbody ].
    + exact Hwf0.
    + exact EI.
  - rewrite !get_inv_idx_expand. exact EI.
Qed.

(* ------------------------------------------------------------------ *)
(* The semantic statement for expressions                             *)
(* ------------------------------------------------------------------ *)

Definition exp_type (k : nat) (venv : venv) (e : tm) (n : class) (T : ty) : Prop :=
  match teval k venv e n with
  | None => True
  | Some None => False
  | Some (Some v) => val_type venv v T
  end.

(* If an expression evaluates to a value of type T in one environment,
   then the same evaluation result is a value of type T in any other
   environment (values do not depend on the typing environment). *)
Lemma exp_type_res :
  forall (k : nat) (venv venv' : venv) (e : tm) (n : class) (T : ty),
  exp_type k venv' e n T ->
  match teval k venv' e n with
  | None => True
  | Some None => False
  | Some (Some v) => val_type venv v T
  end.
Proof.
  intros k venv venv' e n T H. unfold exp_type in H.
  destruct (teval k venv' e n) as [[v|]|]; simpl in *.
  - eapply val_type_irrel. exact H.
  - exact H.
  - exact I.
Qed.

(* Sequencing two evaluations: if the argument evaluates safely and,
   for every resulting value, the body evaluates safely, then the whole
   continuation is safe. *)
Lemma exp_type_app_bind :
  forall (k : nat) (venv : venv) (x : tm) (m : class) (T1 : ty)
         (F : vl -> @env vl) (ey : tm) (retcl : class) (T2 : ty),
  exp_type k venv x m T1 ->
  (forall vx, val_type venv vx T1 -> exp_type k (F vx) ey retcl T2) ->
  match
    match teval k venv x m with
    | Some (Some vx) => teval k (F vx) ey retcl
    | Some None => Some None
    | None => None
    end
  with
  | None => True
  | Some None => False
  | Some (Some v) => val_type venv v T2
  end.
Proof.
  intros k venv x m T1 F ey retcl T2 Hx Hbody.
  unfold exp_type in Hx.
  destruct (teval k venv x m) as [[vx|]|]; simpl in *.
  - exact (exp_type_res k venv (F vx) ey retcl T2 (Hbody vx Hx)).
  - exact Hx.
  - exact I.
Qed.

Lemma exp_type_fund : forall k venv tenv e n T,
  has_type tenv e n T -> wf_env venv tenv -> exp_type k venv e n T.
Proof.
  intros k. induction k as [|k' IH].
  - intros venv tenv e n T Hty Hwf. unfold exp_type. simpl. exact I.
  - intros venv tenv e n T Hty Hwf. unfold exp_type. simpl.
    destruct Hty as [n0 env0
                   | n0 env0
                   | n0 x env0 T1 Hlk
                   | m retcl q env0 f x T1 T2 Hf Hx Hsub
                   | m n0 retcl env0 y T1 T2 Hbody].
    -- (* t_true *)
       simpl. constructor.
    -- (* t_false *)
       simpl. constructor.
    -- (* t_var *)
       simpl.
       destruct (lookup_wf venv env0 Hwf n0 x T1 Hlk) as [v [Hv Hvt]].
       rewrite Hv. simpl. exact Hvt.
    -- (* t_app *)
       remember (teval k' venv f Second) as Ef eqn:HEf.
       assert (IHf := IH venv env0 f Second (TFun T1 m T2 retcl) Hf Hwf).
       assert (IHx := IH venv env0 x m T1 Hx Hwf).
       unfold exp_type in IHf, IHx.
       rewrite <- HEf in IHf.
       destruct Ef as [[vf|]|].
       --- (* f returns a value *)
           simpl in IHf.
           destruct vf as [b | env2 m0 ey retcl0].
           ---- (* a boolean cannot have a function type *)
                simpl. pose proof (val_type_bool_inv _ _ _ IHf) as E.
                discriminate E.
           ---- (* a closure *)
                destruct (vabs_inv_gen _ env2 _ ey _ _ _ _ _ IHf)
                  as [Hm [Hr Hx0]].
                destruct Hx0 as [tenv0 [Hwf2 Hbody2]].
                subst m0. subst retcl0.
                destruct retcl; destruct q.
                ----- (* return class First, used at class First *)
                      simpl.
                      apply (exp_type_app_bind k' venv x m T1
                               (fun vx => expand_env
                                            (expand_env env2 (vabs env2 m ey First) Second)
                                            vx m)
                               ey First T2);
                        [ exact IHx
                        | intros vx Hvx;
                          apply (IH
                                   (expand_env (expand_env env2 (vabs env2 m ey First) Second) vx m)
                                   (expand_env (expand_env tenv0 (TFun T1 m T2 First) Second) T1 m)
                                   ey First T2 Hbody2);
                          apply wf_env_extend;
                          [ exact Hwf2 | exact Hbody2
                          | eapply val_type_irrel; exact Hvx ] ].
                ----- (* return class First, used at class Second *)
                      simpl.
                      apply (exp_type_app_bind k' venv x m T1
                               (fun vx => expand_env
                                            (expand_env env2 (vabs env2 m ey First) Second)
                                            vx m)
                               ey First T2);
                        [ exact IHx
                        | intros vx Hvx;
                          apply (IH
                                   (expand_env (expand_env env2 (vabs env2 m ey First) Second) vx m)
                                   (expand_env (expand_env tenv0 (TFun T1 m T2 First) Second) T1 m)
                                   ey First T2 Hbody2);
                          apply wf_env_extend;
                          [ exact Hwf2 | exact Hbody2
                          | eapply val_type_irrel; exact Hvx ] ].
                ----- (* return class Second, used at class First: rejected *)
                      exfalso. simpl in Hsub. discriminate Hsub.
                ----- (* return class Second, used at class Second *)
                      simpl.
                      apply (exp_type_app_bind k' venv x m T1
                               (fun vx => expand_env
                                            (expand_env env2 (vabs env2 m ey Second) Second)
                                            vx m)
                               ey Second T2);
                        [ exact IHx
                        | intros vx Hvx;
                          apply (IH
                                   (expand_env (expand_env env2 (vabs env2 m ey Second) Second) vx m)
                                   (expand_env (expand_env tenv0 (TFun T1 m T2 Second) Second) T1 m)
                                   ey Second T2 Hbody2);
                          apply wf_env_extend;
                          [ exact Hwf2 | exact Hbody2
                          | eapply val_type_irrel; exact Hvx ] ].
       --- (* f returns an error *) simpl in IHf. simpl. exact IHf.
       --- (* f times out *) simpl. exact I.
    -- (* t_abs *)
       simpl.
       apply v_abs with (venv := sanitize_env n0 venv) (tenv := sanitize_env n0 env0).
       --- apply wf_env_sanitize_env. exact Hwf.
       --- exact Hbody.
Qed.

Theorem full_safety : forall k e n tenv venv res T,
  teval k venv e n = Some res -> has_type tenv e n T -> wf_env venv tenv ->
  res_type venv res T.
Proof.
  intros k e n tenv venv res T Hevt Hty Hwf.
  pose proof (exp_type_fund k venv tenv e n T Hty Hwf) as H.
  unfold exp_type in H.
  rewrite Hevt in H.
  destruct res as [v|].
  - simpl in H. apply not_stuck. exact H.
  - simpl in H. exfalso. exact H.
Qed.
