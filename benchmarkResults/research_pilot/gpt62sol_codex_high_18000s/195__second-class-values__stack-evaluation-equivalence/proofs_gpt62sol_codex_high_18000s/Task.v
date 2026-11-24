Require Export Arith.EqNat.

From Stdlib Require Export PeanoNat.

Require Export stlc1.

Require Export stlc2.

Inductive equiv_val : stack vl_stack -> vl -> vl_stack -> Prop :=
  | equiv_const : forall b st, equiv_val st (vbool b) (vbool_stack b)
  | equiv_abs : forall H1 H2 idx lS i t c1 c2 H fr,
                      get_stack_frame lS i = Some (fr, idx) ->
                      equiv_env lS (Def H1 H2 idx) (H, (fr, idx)) ->
                      equiv_val lS (vabs (Def H1 H2 idx) c1 t c2) (vabs_stack H i c1 t c2)
with equiv_env : stack vl_stack -> venv -> venv_stack -> Prop :=
  | eqv_forall : forall lS H1 H1s H2 H2s H20,
                      Forall2(fun v vs => equiv_val lS v vs) H1 H1s ->
                      Forall2(fun v vs => equiv_val lS v vs) H2 H2s ->
                      equiv_env lS (Def H1 (H2++H20) (length H20)) (H1s, (H2s, length H20))
.

Definition eqv_nested_ind := fun
  (Pv : stack vl_stack -> vl -> vl_stack -> Prop)
  (Pe : stack vl_stack -> venv -> venv_stack -> Prop)
  (fconst : forall (b : bool) (st : stack vl_stack),
       Pv st (vbool b) (vbool_stack b))
  (fabs : forall (H1 H2 : list vl) (idx : nat) (lS : stack vl_stack)
          (i : st_ptr) (t : tm) (c1 c2 : class) (H : heap vl_stack)
          (fr : list vl_stack),
        get_stack_frame lS i = Some (fr, idx) ->
        Pe lS (Def H1 H2 idx) (H, (fr, idx)) ->
        Pv lS (vabs (Def H1 H2 idx) c1 t c2) (vabs_stack H i c1 t c2))
  (fenv : forall (lS : stack vl_stack) (H1 : list vl)
         (H1s : list vl_stack) (H2 : list vl) (H2s : list vl_stack)
         (H20 : list vl),
       Forall2 (fun (v : vl) (vs : vl_stack) => Pv lS v vs) H1 H1s ->
       Forall2 (fun (v : vl) (vs : vl_stack) => Pv lS v vs) H2 H2s ->
       Pe lS (Def H1 (H2 ++ H20) (length H20)) (H1s, (H2s, length H20)))
=>
  fix F (s : stack vl_stack) (v : vl) (v0 : vl_stack) (e : equiv_val s v v0): Pv s v v0 :=
match e in (equiv_val s0 v1 v2) return (Pv s0 v1 v2) with
| equiv_const x x0 => fconst x x0
| equiv_abs x x0 x1 x2 x3 x4 c1 c2 x6 x7 x8 x9 =>
  fabs x x0 x1 x2 x3 x4 c1 c2 x6 x7 x8 (
         match x9 in (equiv_env s0 v1 v2) return (Pe s0 v1 v2) with
           | eqv_forall x x0 x1 x2 x3 x4 x5 x6 =>
             fenv x x0 x1 x2 x3 x4
                  ((fix G l l' (fa: Forall2 (fun v v' => equiv_val x v v') l l') := match fa in (Forall2 _ l1 l2) return Forall2 _ l1 l2 with
                                | Forall2_nil _ => Forall2_nil _
                                | @Forall2_cons _ _ _ a b x1 x2 r x4 =>
                                  Forall2_cons a b (F x a b r) (G x1 x2 x4)
                              end) x0 x1 x5)
                  ((fix G l l' (fa: Forall2 (fun v v' => equiv_val x v v') l l') := match fa in (Forall2 _ l1 l2) return Forall2 _ l1 l2 with
                                | Forall2_nil _ => Forall2_nil _
                                | @Forall2_cons _ _ _ a b x1 x2 r x4 =>
                                  Forall2_cons a b (F x a b r) (G x1 x2 x4)
                              end) x2 x3 x6)
         end)
end.

Inductive equiv_opt: stack vl_stack -> option (vl) -> option (vl_stack) -> Prop :=
| e_stuck : forall lS, equiv_opt lS None None
| e_val : forall lS v v_stack, equiv_val lS v v_stack -> equiv_opt lS (Some v) ((Some v_stack)).

Inductive equiv_res: stack vl_stack -> option (option vl) -> option (option vl_stack) -> Prop :=
| e_time : forall lS, equiv_res lS None None
| e_res : forall lS v v_stack, equiv_opt lS v v_stack -> equiv_res lS ((Some v)) ((Some v_stack)).

Definition get_fenv (vs : option (option vl_stack)) :=
  match vs with
  | Some (Some (vabs_stack h _ _ _ _)) => h
  | _ => []
  end.

Local Lemma index_past_end {X : Type} (xs : list X) i :
  length xs <= i -> index i xs = None.
Proof.
  induction xs as [|x xs IH]; cbn; intros Hi; [reflexivity|].
  destruct (i =? length xs) eqn:Heq.
  - apply Nat.eqb_eq in Heq. lia.
  - apply IH. lia.
Qed.

Local Lemma index_app_offset {X : Type} (xs tail : list X) i :
  index (length tail + i) (xs ++ tail) = index i xs.
Proof.
  induction xs as [|x xs IH]; cbn.
  - apply index_past_end. lia.
  - rewrite length_app.
    destruct (i =? length xs) eqn:Heq.
    + apply Nat.eqb_eq in Heq.
      replace (length tail + i) with (length xs + length tail) by lia.
      now rewrite Nat.eqb_refl.
    + apply Nat.eqb_neq in Heq.
      assert ((length tail + i =? length xs + length tail) = false)
        as Hneq by (apply Nat.eqb_neq; lia).
      rewrite Hneq. now apply IH.
Qed.

Local Lemma index_under_prefix {X : Type} (prefix xs : list X) i :
  i < length xs -> index i (prefix ++ xs) = index i xs.
Proof.
  induction prefix as [|x prefix IH]; cbn; intros Hi; [reflexivity|].
  assert ((i =? length (prefix ++ xs)) = false) as Hneq.
  { apply Nat.eqb_neq. rewrite length_app. lia. }
  rewrite Hneq. now apply IH.
Qed.

Local Lemma get_frame_under_prefix {X : Type} (prefix st : stack X) ptr fr :
  get_stack_frame st ptr = Some fr ->
  get_stack_frame (prefix ++ st) ptr = Some fr.
Proof.
  destruct ptr as [i|i]; cbn; intros Hfr; [exact Hfr|].
  rewrite index_under_prefix; [exact Hfr|].
  destruct (lt_dec i (length st)) as [Hi|Hi]; [exact Hi|].
  rewrite index_past_end in Hfr by lia. discriminate.
Qed.

Local Lemma split_at_suffix prefix (fr : stack_frame vl_stack) st :
  stack_split (prefix ++ fr :: st) (length (fr :: st)) =
    Some (prefix, fr :: st).
Proof.
  induction prefix as [|p prefix IH]; cbn.
  - now rewrite Nat.eqb_refl.
  - assert ((length (prefix ++ fr :: st) =? length st) = false)
      as Hneq by (apply Nat.eqb_neq; rewrite length_app; cbn; lia).
    cbn in IH. now rewrite Hneq, IH.
Qed.

(* Stack pointers count from the bottom, so adding frames preserves captures. *)
Local Lemma equiv_val_under_prefix st v vs :
  equiv_val st v vs -> forall prefix, equiv_val (prefix ++ st) v vs.
Proof.
  refine (eqv_nested_ind
    (fun st v vs => forall prefix, equiv_val (prefix ++ st) v vs)
    (fun st e es => forall prefix, equiv_env (prefix ++ st) e es)
    _ _ _ st v vs).
  - intros. constructor.
  - intros H1 H2 idx lS i t c1 c2 H fr Hget Henv prefix.
    eapply equiv_abs; [eapply get_frame_under_prefix; exact Hget|apply Henv].
  - intros lS H1 H1s H2 H2s H20 Hfirst Hsecond prefix.
    constructor.
    + induction Hfirst; constructor; auto.
    + induction Hsecond; constructor; auto.
Qed.

Local Lemma equiv_env_under_prefix st e h fr prefix :
  equiv_env st e (h, fr) -> equiv_env (prefix ++ st) e (h, fr).
Proof.
  intros He. inversion He; subst. constructor.
  - eapply Forall2_impl; [|eassumption].
    intros; now apply equiv_val_under_prefix.
  - eapply Forall2_impl; [|eassumption].
    intros; now apply equiv_val_under_prefix.
Qed.

(* A first-class closure has an empty captured frame and a first-class heap. *)
Local Lemma equiv_first_any_stack st v vs :
  equiv_val st v vs -> wf_val First vs ->
  forall st', equiv_val st' v vs.
Proof.
  refine (eqv_nested_ind
    (fun st v vs => wf_val First vs -> forall st', equiv_val st' v vs)
    (fun st e es => fc_env (fst es) -> fst (snd es) = [] ->
       forall st', equiv_env st' e es)
    _ _ _ st v vs).
  - intros. constructor.
  - intros H1 H2 idx lS i t c1 c2 H fr Hget Henv Hwf st'.
    inversion Hwf; subst. cbn in Hget. inversion Hget; subst.
    eapply equiv_abs; [reflexivity|]. apply Henv; auto.
  - intros lS H1 H1s H2 H2s H20 Hfirst Hsecond Hheap Hempty st'.
    cbn in Hheap, Hempty. subst H2s. inversion Hsecond; subst.
    constructor; [|constructor].
    clear Hsecond. induction Hfirst; [constructor|].
    inversion Hheap; subst. constructor; auto.
Qed.

Local Lemma wf_first_is_second vs : wf_val First vs -> wf_val Second vs.
Proof.
  intros Hwf. inversion Hwf; subst; constructor; auto.
Qed.

Local Lemma wf_first_result_is_second r : wf First r -> wf Second r.
Proof.
  intros Hwf. inversion Hwf; subst; constructor.
  now apply wf_first_is_second.
Qed.

Local Lemma equiv_first_result_any_stack st r rs :
  equiv_res st r rs -> wf First rs ->
  forall st', equiv_res st' r rs.
Proof.
  intros Hrel Hwf st'. destruct Hrel as [|st v vs Hopt]; [constructor|].
  destruct Hopt; [repeat constructor|].
  inversion Hwf; subst. do 2 constructor. eapply equiv_first_any_stack; eauto.
Qed.

Local Lemma equiv_index st xs ys i :
  Forall2 (equiv_val st) xs ys -> equiv_opt st (index i xs) (index i ys).
Proof.
  intros Hrel. induction Hrel; cbn; [constructor|].
  assert (length l = length l') as Hlen by (now apply Forall2_length in Hrel).
  rewrite Hlen. destruct (i =? length l'); [now constructor|exact IHHrel].
Qed.

Local Lemma wf_index c xs i :
  Forall (wf_val c) xs -> wf c (Some (index i xs)).
Proof.
  intros Hwf. induction Hwf; cbn; [constructor|].
  destruct (i =? length l); [now constructor|exact IHHwf].
Qed.

Local Lemma wf_heap_forall h : fc_env h -> Forall (wf_val First) h.
Proof.
  intros Hwf. induction Hwf; constructor; assumption.
Qed.

Local Lemma wf_frame_under_prefix prefix st fr off :
  sc_env (prefix ++ (fr, off) :: st) -> Forall (wf_val Second) fr.
Proof.
  induction prefix; cbn; intros Hwf; inversion Hwf; subst; auto.
Qed.

Local Lemma wf_get_frame st ptr fr off :
  sc_env st -> get_stack_frame st ptr = Some (fr, off) ->
  Forall (wf_val Second) fr.
Proof.
  intros Hsc. destruct ptr as [i|i]; cbn.
  - intros Hget. inversion Hget; constructor.
  - induction Hsc as [|st frame idx Hsc IH Hframe]; cbn; [discriminate|].
    destruct (i =? length st); [|exact IH].
    intros Hget. now inversion Hget; subst.
Qed.

Local Lemma equiv_lookup_stack st env h fr off x n tail :
  equiv_env st env (h, (fr, off)) ->
  equiv_opt st (lookup x (sanitize_env n env))
    (match x, n with
     | V Second _, First => None
     | _, _ => lookup_stack x h ((fr, off) :: tail)
     end).
Proof.
  intros Henv. inversion Henv; subst.
  destruct x as [c i], c, n; cbn; try (apply equiv_index; assumption).
  - destruct (length (H2 ++ H20) <=? i) eqn:Hbound.
    + apply Nat.leb_le in Hbound. rewrite index_past_end by exact Hbound.
      constructor.
    + constructor.
  - destruct (length H20 <=? i) eqn:Hbound; [|constructor].
    apply Nat.leb_le in Hbound.
    replace i with (length H20 + (i - length H20)) at 1 by lia.
    rewrite index_app_offset. now apply equiv_index.
Qed.

Local Lemma equiv_expand st env h fr x xs c :
  equiv_env st env (h, fr) -> equiv_val st x xs ->
  equiv_env st (expand_env env x c) (expand_env_stack (h, fr) xs c).
Proof.
  intros Henv Hx. inversion Henv; subst. destruct c; cbn.
  - constructor; now try constructor.
  - apply (eqv_forall st H1 h (x :: H2) (xs :: H2s) H20);
      auto using Forall2_cons.
Qed.

Local Lemma wf_lookup_stack st h fr off x n :
  fc_env h -> Forall (wf_val Second) fr ->
  wf n (Some (match x, n with
              | V Second _, First => None
              | _, _ => lookup_stack x h ((fr, off) :: st)
              end)).
Proof.
  intros Hheap Hframe. destruct x as [c i], c, n; cbn.
  - apply wf_index. now apply wf_heap_forall.
  - apply wf_first_result_is_second, wf_index. now apply wf_heap_forall.
  - constructor.
  - destruct (off <=? i); [now apply wf_index|constructor].
Qed.

Local Lemma equiv_abs_first st env h fr off m t ret :
  equiv_env st env (h, (fr, off)) ->
  equiv_val st (vabs (sanitize_env First env) m t ret)
    (vabs_stack h (S0 (off + length fr)) m t ret).
Proof.
  intros Henv. inversion Henv as [s H1 H1s H2 H2s H20 Hfirst Hsecond]; subst. cbn.
  assert (length H2 = length fr) as Hlen by (now apply Forall2_length in Hsecond).
  replace (length H20 + length fr) with (length (H2 ++ H20))
    by (rewrite length_app, Hlen; lia).
  eapply equiv_abs; [reflexivity|].
  apply (eqv_forall st H1 h [] [] (H2 ++ H20)); [assumption|constructor].
Qed.

(* Recursive calls preserve the input as a suffix even when they delay popping. *)
Local Definition eval_agrees n input r rs st :=
  (exists added, st = added ++ input) /\
  sc_env st /\ equiv_res st r rs /\ wf n rs.

Local Lemma eval_agrees_unchanged n st r rs :
  sc_env st -> equiv_res st r rs -> wf n rs -> eval_agrees n st r rs st.
Proof.
  intros Hsc Hrel Hwf. split; [now exists []|auto].
Qed.

Local Lemma eval_agrees_return n ret input frames r rs st :
  subcl ret n = true -> sc_env input ->
  (exists pre, frames = pre ++ input) ->
  eval_agrees ret frames r rs st ->
  eval_agrees n input r rs
    (match rs, ret with
     | Some (Some _), Second => st
     | _, _ => input
     end).
Proof.
  intros Hclass Hsc [pre Hframes] [[added Hst] [Hsc' [Hrel Hwf]]].
  destruct ret.
  - destruct rs as [[v|]|]; apply eval_agrees_unchanged; auto;
      try (eapply equiv_first_result_any_stack; eauto);
      destruct n; auto using wf_first_result_is_second.
  - destruct n; [discriminate|].
    destruct rs as [[v|]|].
    + split.
      * exists (added ++ pre). now rewrite Hst, Hframes, <- app_assoc.
      * auto.
    + apply eval_agrees_unchanged; auto.
      inversion Hrel as [|s v1 v2 Hopt]; subst.
      inversion Hopt; subst. repeat constructor.
    + apply eval_agrees_unchanged; auto. inversion Hrel; constructor.
Qed.

Local Lemma teval_equiv_invariants : forall k n t env lS prefix fr h rs st,
  teval_stack k (length (fr :: lS)) (prefix ++ fr :: lS) h t n = (rs, st) ->
  equiv_env (fr :: lS) env (h, fr) ->
  fc_env h -> sc_env (prefix ++ fr :: lS) ->
  eval_agrees n (prefix ++ fr :: lS) (teval k env t n) rs st.
Proof.
  induction k as [|k IH]; intros n t env lS prefix [fr off] h rs st
    Hrun Henv Hheap Hsc.
  - cbn in Hrun. inversion Hrun; subst.
    apply eval_agrees_unchanged; [assumption|constructor|constructor].
  - cbn [teval_stack] in Hrun. rewrite split_at_suffix in Hrun.
    pose proof (equiv_env_under_prefix _ _ _ _ prefix Henv) as Henv_full.
    destruct t as [| |x|f a|m body ret]; cbn [teval] in *.
    + inversion Hrun; subst. apply eval_agrees_unchanged; repeat constructor; assumption.
    + inversion Hrun; subst. apply eval_agrees_unchanged; repeat constructor; assumption.
    + pose proof (equiv_lookup_stack _ _ _ _ _ x n lS Henv_full) as Hrel.
      pose proof (wf_lookup_stack lS h fr off x n Hheap
        (wf_frame_under_prefix prefix lS fr off Hsc)) as Hwf.
      destruct x as [c i], c, n; inversion Hrun; subst;
        apply eval_agrees_unchanged; auto using e_res.
    + destruct (teval_stack k (length (@cons (stack_frame vl_stack) (fr, off) lS))
        (prefix ++ @cons (stack_frame vl_stack) (fr, off) lS) h f Second)
        as [rf stf] eqn:HrunF in Hrun.
      destruct (IH Second f env lS prefix (fr, off) h rf stf HrunF
        Henv Hheap Hsc) as [[pf Hstf] [HscF [HrelF HwfF]]].
      remember (teval k env f Second) as vf in HrelF |- *.
      clear Heqvf.
      destruct HrelF as [|stf vf rf HoptF].
      * inversion Hrun; subst. apply eval_agrees_unchanged; auto using e_time, wf_timeout.
      * destruct HoptF as [|stf vf rf HvalF].
        -- inversion Hrun; subst; apply eval_agrees_unchanged;
             auto using e_res, e_stuck, wf_stuck.
        -- destruct HvalF as
             [b stf|H1 H2 idx stf ptr body m ret hf frame Hget Hcapt].
           ++ inversion Hrun; subst; apply eval_agrees_unchanged;
                auto using e_res, e_stuck, wf_stuck.
           ++ assert (Hstf' : stf = (pf ++ prefix) ++ (fr, off) :: lS)
                by (rewrite Hstf; apply app_assoc).
              assert (HscF' : sc_env ((pf ++ prefix) ++ (fr, off) :: lS))
                by (rewrite <- Hstf'; exact HscF).
              destruct (teval_stack k (length (@cons (stack_frame vl_stack) (fr, off) lS))
                stf h a m) as [ra sta] eqn:HrunA in Hrun.
              pose proof HrunA as HrunA'. rewrite Hstf' in HrunA'.
              destruct (IH m a env lS (pf ++ prefix) (fr, off) h ra sta
                HrunA' Henv Hheap HscF') as [[pa Hsta] [HscA [HrelA HwfA]]].
              assert (Hsta' : sta = pa ++ stf) by (rewrite Hstf'; exact Hsta).
              clear Hsta. rename Hsta' into Hsta.
              remember (teval k env a m) as va in HrelA |- *.
              clear Heqva.
              destruct HrelA as [|sta va ra HoptA].
              ** destruct ret, n; inversion Hrun; subst; apply eval_agrees_unchanged;
                   auto using e_time, wf_timeout, e_res, e_stuck, wf_stuck.
              ** destruct HoptA as [|sta va ra HvalA].
                 --- destruct ret, n; inversion Hrun; subst; apply eval_agrees_unchanged;
                       auto using e_res, e_stuck, wf_stuck.
                 --- rewrite Hget in Hrun.
                     pose (vf := vabs (Def H1 H2 idx) m body ret).
                     pose (vfs := vabs_stack hf ptr m body ret).
                     assert (HvalF : equiv_val stf vf vfs) by (eapply equiv_abs; eassumption).
                     assert (HheapF : fc_env hf).
                     { inversion HwfF as [v c Hclosure| |]; subst.
                       now inversion Hclosure. }
                     assert (HwfSelf : wf_val Second vfs) by (constructor; exact HheapF).
                     assert (HwfArg : wf_val m ra) by (now inversion HwfA).
                     assert (Hframe : Forall (wf_val Second) frame)
                       by exact (wf_get_frame stf ptr frame idx HscF Hget).
                     pose (callee := expand_env (expand_env (Def H1 H2 idx) vf Second) va m).
                     pose (callee_stack := expand_env_stack (hf, (vfs :: frame, idx)) ra m).
                     (* The captured environment is valid through argument evaluation. *)
                     assert (Hcallee : equiv_env sta callee callee_stack).
                     {
                       unfold callee, callee_stack.
                       apply (equiv_expand sta _ hf (vfs :: frame, idx)); [|exact HvalA].
                       rewrite Hsta. apply equiv_env_under_prefix.
                       exact (equiv_expand stf _ hf (frame, idx) vf vfs Second Hcapt HvalF).
                     }
                     assert (HwfCallee : fc_env (fst callee_stack) /\
                       Forall (wf_val Second) (fst (snd callee_stack))).
                     {
                       unfold callee_stack. destruct m; cbn; split;
                         auto using heap_cons, Forall_cons.
                     }
                     change (expand_env_stack
                       (expand_env_stack (hf, (frame, idx))
                         (vabs_stack hf ptr m body ret) Second) ra m)
                       with callee_stack in Hrun.
                     destruct callee_stack as [hb fb].
                     destruct HwfCallee as [HheapB HframeB].
                     destruct fb as [fb offb].
                     assert (HscB : sc_env ((fb, offb) :: sta)) by (now constructor).
                     lazymatch type of Hrun with
                     | context [teval_stack k ?depth ?frames hb body ret] =>
                         destruct (teval_stack k depth frames hb body ret)
                           as [rb stb] eqn:HrunB in Hrun
                     end.
                     pose proof (IH ret body callee sta [] (fb, offb) hb rb stb HrunB
                       (equiv_env_under_prefix _ _ _ _ [(fb, offb)] Hcallee)
                       HheapB HscB) as Hbody.
                     assert (Hframes : exists pre, (fb, offb) :: sta =
                       pre ++ (prefix ++ (fr, off) :: lS)).
                     {
                       exists ((fb, offb) :: (pa ++ pf)).
                       rewrite Hsta, Hstf. cbn. now rewrite <- app_assoc.
                     }
                     fold vf callee.
                     pose proof (fun Hclass => eval_agrees_return n ret _ _ _ _ _
                       Hclass Hsc Hframes Hbody) as Hreturn.
                     destruct ret, n; try solve
                       [inversion Hrun; subst; apply eval_agrees_unchanged;
                        auto using e_res, e_stuck, wf_stuck].
                     all: specialize (Hreturn eq_refl);
                       destruct rb as [[vb|]|]; inversion Hrun; subst; exact Hreturn.
    + destruct n; inversion Hrun; subst; apply eval_agrees_unchanged.
      * exact Hsc.
      * do 2 constructor. now apply equiv_abs_first.
      * do 2 constructor. exact Hheap.
      * exact Hsc.
      * do 2 constructor. unfold sanitize_env.
        inversion Henv_full; subst. eapply equiv_abs; [|exact Henv_full].
        apply get_frame_under_prefix. cbn. now rewrite Nat.eqb_refl.
      * do 2 constructor. exact Hheap.
Qed.

Theorem teval_equiv : forall k n t env v lS lS' fr env_stack v_stack st,
     teval k env t n = v ->
     teval_stack k (length (fr::lS)) (lS' ++ fr::lS) env_stack t n = (v_stack, st) ->

     equiv_env (fr::lS) env (env_stack,fr) ->
     fc_env env_stack -> sc_env (lS' ++ fr::lS) ->
     equiv_res st v v_stack.
Proof.
  intros k n t env v lS lS' fr env_stack v_stack st Hval Hrun Henv Hheap Hsc.
  destruct (teval_equiv_invariants k n t env lS lS' fr env_stack v_stack st
    Hrun Henv Hheap Hsc) as [_ [_ [Hrel _]]].
  now rewrite Hval in Hrel.
Qed.
