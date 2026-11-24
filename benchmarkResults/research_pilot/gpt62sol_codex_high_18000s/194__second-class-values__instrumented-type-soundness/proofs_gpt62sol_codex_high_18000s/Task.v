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

Local Lemma val_type_change_env : forall G G' v T,
  val_type G v T -> val_type G' v T.
Proof.
  intros G G' v T Hv.
  destruct Hv.
  - apply v_bool.
  - eapply v_abs; eassumption.
Qed.

Local Lemma wf_env_inv_idx : forall vs ts,
  wf_env vs ts -> get_inv_idx vs = get_inv_idx ts.
Proof.
  intros vs ts Hwf.
  destruct Hwf as [i | v t vs ts c Hv Hwf Hidx].
  - reflexivity.
  - destruct vs, ts, c; exact Hidx.
Qed.

Local Lemma wf_env_length : forall vs ts,
  wf_env vs ts -> forall c, length_env c vs = length_env c ts.
Proof.
  intros vs ts Hwf.
  induction Hwf as [i | v t vs ts c Hv Hwf IH Hidx]; intro d.
  - destruct d; reflexivity.
  - specialize (IH d).
    destruct vs, ts, c, d; cbn in *; congruence.
Qed.

Local Lemma wf_env_extend : forall vs ts,
  wf_env vs ts -> forall G v T c,
  val_type G v T -> wf_env (expand_env vs v c) (expand_env ts T c).
Proof.
  intros vs ts Hwf G v T c Hv.
  apply wfe_cons.
  - eapply val_type_change_env. exact Hv.
  - exact Hwf.
  - apply wf_env_inv_idx. exact Hwf.
Qed.

Local Lemma sanitize_any_expand : forall X (env : @env X) x c i,
  sanitize_any (expand_env env x c) i =
  expand_env (sanitize_any env i) x c.
Proof.
  intros X env x c i.
  destruct env, c; reflexivity.
Qed.

Local Lemma wf_env_sanitize_any : forall vs ts,
  wf_env vs ts -> forall i, wf_env (sanitize_any vs i) (sanitize_any ts i).
Proof.
  intros vs ts Hwf.
  induction Hwf as [j | v t vs ts c Hv Hwf IH Hidx]; intro i.
  - apply wfe_nil.
  - rewrite !sanitize_any_expand.
    eapply wf_env_extend.
    + apply IH.
    + exact Hv.
Qed.

Local Lemma wf_env_sanitize : forall vs ts,
  wf_env vs ts -> forall c, wf_env (sanitize_env c vs) (sanitize_env c ts).
Proof.
  intros vs ts Hwf c.
  destruct c.
  - pose proof (wf_env_length vs ts Hwf Second) as Hlen.
    destruct vs as [vs1 vs2 vi], ts as [ts1 ts2 ti].
    cbn in Hlen |- *.
    rewrite Hlen.
    exact (wf_env_sanitize_any _ _ Hwf (length ts2)).
  - exact Hwf.
Qed.

Local Lemma wf_env_lookup : forall vs ts,
  wf_env vs ts -> forall G x T,
  lookup x ts = Some T -> res_type G (lookup x vs) T.
Proof.
  intros vs ts Hwf.
  induction Hwf as [i | v t vs ts c Hv Hwf IH Hidx].
  - intros G [d idx] T Hlookup.
    destruct d; cbn in Hlookup.
    + discriminate.
    + destruct (i <=? idx); discriminate.
  - intros G [d idx] T Hlookup.
    pose proof (wf_env_length vs ts Hwf c) as Hlen.
    destruct vs as [vs1 vs2 vi], ts as [ts1 ts2 ti], c, d;
      cbn in Hlookup, Hlen, Hidx |- *; subst ti.
    + rewrite <- Hlen in Hlookup.
      destruct (idx =? length vs1).
      * injection Hlookup as ->.
        constructor. eapply val_type_change_env. exact Hv.
      * exact (IH G (V First idx) T Hlookup).
    + exact (IH G (V Second idx) T Hlookup).
    + exact (IH G (V First idx) T Hlookup).
    + destruct (vi <=? idx) eqn:Hvisible; [| discriminate].
      rewrite <- Hlen in Hlookup.
      destruct (idx =? length vs2).
      * injection Hlookup as ->.
        constructor. eapply val_type_change_env. exact Hv.
      * specialize (IH G (V Second idx) T).
        cbn in IH. rewrite Hvisible in IH.
        exact (IH Hlookup).
Qed.

Theorem full_safety : forall k e n tenv venv res T,
  teval k venv e n = Some res -> has_type tenv e n T -> wf_env venv tenv ->
  res_type venv res T.
Proof.
  induction k as [|k IH]; intros e n tenv venv res T Heval Htype Hwf.
  - discriminate.
  - destruct Htype as
      [n tenv | n tenv | n x tenv T Hlookup
      | m retcl q tenv f x T1 T2 Hf Hx Hsub
      | m n retcl tenv body T1 T2 Hbody].
    + cbn in Heval. injection Heval as <-. constructor. constructor.
    + cbn in Heval. injection Heval as <-. constructor. constructor.
    + cbn in Heval. injection Heval as <-.
      eapply wf_env_lookup.
      * apply wf_env_sanitize. exact Hwf.
      * exact Hlookup.
    + cbn in Heval.
      destruct (teval k venv f Second) as [rf |] eqn:Hef; [| discriminate].
      pose proof (IH _ _ _ _ _ _ Hef Hf Hwf) as Hrf.
      inversion Hrf as [G vf Tf Hvf]; subst.
      inversion Hvf as
        [| G captured captured_types body A B argcl bodycl Hcaptured Hbody]; subst.
      destruct (teval k venv x m) as [rx |] eqn:Hex.
      2: destruct retcl, q; discriminate.
      pose proof (IH _ _ _ _ _ _ Hex Hx Hwf) as Hrx.
      inversion Hrx as [G vx Tx Hvx]; subst.
      assert (Hcall :
        teval k (expand_env
          (expand_env captured (vabs captured m body retcl) Second) vx m)
          body retcl = Some res).
      { destruct retcl, q; cbn in Hsub, Heval; try discriminate; exact Heval. }
      assert (Hself :
        wf_env (expand_env captured (vabs captured m body retcl) Second)
               (expand_env captured_types (TFun T1 m T2 retcl) Second)).
      { eapply wf_env_extend; eassumption. }
      pose proof (wf_env_extend _ _ Hself _ _ _ m Hvx) as Hcall_env.
      pose proof (IH _ _ _ _ _ _ Hcall Hbody Hcall_env) as Hr.
      inversion Hr; subst.
      constructor. eapply val_type_change_env. eassumption.
    + cbn in Heval. injection Heval as <-.
      constructor. eapply v_abs.
      * apply wf_env_sanitize. exact Hwf.
      * exact Hbody.
Qed.
