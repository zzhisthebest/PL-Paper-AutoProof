Require Import Typing.
Open Scope string_scope.

Definition G0 := Scope [] [] [].
Definition unit_fn := TyFn 0 [] [] unit_type.
Definition return_unit :=
  IFun "main" [] "ret" (FLet "r" (INew 0) (FJump "ret" ["r"])).

Ltac wf :=
  cbv [well_formed wf_external wf_local wf_cont_context wf_cont
       wf_context wf_entry wf_lifetime named empty bind_terms bind_lifetimes
       term_names lft_names type_names cont_name cont_lfts cont_args cont_types
       instantiate own type_size unit_type G0] in *;
  repeat first [solve [simpl; intuition congruence] | constructor].

Example return_unit_is_a_typed_main :
  typed_instruction G0 [] [] [] return_unit "m" [named "m" unit_fn].
Proof.
  unfold return_unit, unit_fn.
  eapply S_fn with (params := []) (call := "call") (y := "answer").
  - reflexivity.
  - wf.
  - unfold fresh_lifetimes. wf.
  - wf.
  - constructor.
  - cbn [named owned_args instantiate instantiate_requirements].
    eapply F_let with (before := []).
    + wf.
    + simpl. intuition congruence.
    + apply S_new.
    + cbn [List.app].
      eapply F_jump.
      * wf.
      * reflexivity.
      * wf.
      * cbn [rename_context rename_path named own type_size unit_type].
        eapply C_trans with (U := [named "r" (TyOwn 0 (TyUninit 0))]).
        -- wf.
        -- apply (C_weaken _ _ _ [named "r" (TyOwn 0 (TyUninit 0))] [named "main" (TyFn 0 [] [] unit_type)]).
        -- apply C_subtype. split; [wf|split; [wf|]].
           apply T_own. exact (T_uninit_prod _ _ _ _ []).
Qed.

Example return_unit_erases_to_closed_core : is_closed [] (erase_instruction return_unit) = true.
Proof. vm_compute. reflexivity. Qed.

Example closed_main_can_start :
  reducible (App (erase_instruction return_unit) [Rec BAnon [BAnon] poison])
            (∅ : state).
Proof.
  unfold reducible.
  eexists _, (∅ : state), [].
  refine (Ectx_step [] _ _ _ _ _ _).
  unfold return_unit. cbn [erase_instruction].
  eapply BetaS.
  - constructor; last constructor.
    cbn [to_val cons_binder app_binder].
    destruct (decide (Closed [] poison)) as [Hclosed|Hopen].
    + eexists. reflexivity.
    + exfalso. apply Hopen. reflexivity.
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
Qed.

(* The polymorphic signature from Appendix Example 1:
   one lifetime parameter, a call that requires it to be alive,
   and a mutable Point argument with a shared int result. *)
Definition point := TyProd [TyInt; TyInt].
Definition get_x_type :=
  TyFn 1 [(LftBound 0, LftBound 1)]
    [TyBorrow (LftBound 0) Mutable point] (TyBorrow (LftBound 0) Shared TyInt).

Example get_x_signature_well_formed : wf_type G0 0 0 get_x_type.
Proof. unfold get_x_type, point. wf. Qed.

Example get_x_instantiates_both_lifetime_scopes :
  instantiate_requirements (LftFree "call") [LftFree "a"] [(LftBound 0, LftBound 1)]
    = [(LftFree "call", LftFree "a")] /\
  instantiate [LftFree "a"] (TyBorrow (LftBound 0) Shared TyInt) =
    TyBorrow (LftFree "a") Shared TyInt.
Proof. split; reflexivity. Qed.

Example borrow_can_be_shared_and_unblocked :
  let G := Scope ["p"] ["a"] [] in
  let L := [(LftFree "a", [])] in
  let before := [named "p" (TyOwn 1 TyInt)] in
  let loan := named "p" (TyBorrow (LftFree "a") Shared TyInt) in
  let blocked := Blocked (PVar "p") (LftFree "a") (TyOwn 1 TyInt) in
  context_includes G [] L before [blocked; loan] /\
  unblock (LftFree "a") [blocked] = before.
Proof.
  simpl. split; last reflexivity.
  eapply C_trans with (U := [named "p" (TyBorrow (LftFree "a") Mutable TyInt);
                            Blocked (PVar "p") (LftFree "a") (TyOwn 1 TyInt)]).
  - wf.
  - apply C_borrow. left. reflexivity.
  - eapply C_trans with (U := [Blocked (PVar "p") (LftFree "a") (TyOwn 1 TyInt);
                              named "p" (TyBorrow (LftFree "a") Mutable TyInt)]).
    + wf.
    + apply C_perm, perm_swap.
    + eapply C_frame with (frame := [Blocked (PVar "p") (LftFree "a") (TyOwn 1 TyInt)]).
      apply C_share.
      apply AliveLocal with (parents := []); [left; reflexivity | constructor].
Qed.

Example call_instantiates_a_lifetime :
  let G := Scope ["k"; "f"; "p"; "keep"] ["a"] [] in
  let a := LftFree "a" in
  let L := [(a, [])] in
  let sig := TyFn 1 [(LftBound 0, LftBound 1)]
                  [TyBorrow (LftBound 0) Shared TyInt] unit_type in
  let T := [named "p" (own (TyBorrow a Shared TyInt)); named "keep" TyInt] in
  typed_body G [] L [Cont "k" L ["y"] [named "y" (own unit_type); named "keep" TyInt]]
    (T ++ [named "f" sig])%list (FCall "f" [PVar "p"] "k").
Proof.
  simpl.
  eapply F_call with
    (T := [named "p" (own (TyBorrow (LftFree "a") Shared TyInt)); named "keep" TyInt])
    (frame := [named "keep" TyInt]) (r := unit_type) (params := [LftFree "a"])
    (call := "short") (limits := [LftFree "a"]).
  - wf.
  - unfold return_fresh. simpl. intuition congruence.
  - reflexivity.
  - wf.
  - reflexivity.
  - wf.
  - apply C_perm, Permutation_refl.
  - constructor; last constructor.
    apply AliveLocal with (parents := []); [left; reflexivity | constructor].
  - simpl. intuition congruence.
  - constructor; last constructor.
    apply LftExternal. left. reflexivity.
Qed.

Example double_free_call_cannot_supply_a_fresh_return_frame :
  forall (returned : ty) (frame : type_context),
    named "p" returned :: frame =
      [named "p" (own (TyUninit 1)); named "p" (own (TyUninit 1))] ->
    ~ return_fresh "p" frame.
Proof.
  intros returned frame H. injection H as _ Hframe. subst frame.
  unfold return_fresh. simpl. tauto.
Qed.

Example return_binding_cannot_capture_a_projected_blocked_path :
  ~ return_fresh "p"
    [Blocked (POffset (PVar "p") 1) (LftFree "a") (own TyInt)].
Proof. unfold return_fresh. simpl. tauto. Qed.

Example function_subtyping_instantiates_left_parameters :
  subtype G0 [] []
    (TyFn 1 [] [TyBorrow (LftBound 0) Shared TyInt] unit_type)
    (TyFn 0 [] [TyBorrow Static Shared TyInt] unit_type).
Proof.
  split; [wf|split; [wf|]].
  eapply T_fn with (names := []) (call := "call") (actuals := [Static]).
  - unfold fresh_lifetimes. wf.
  - reflexivity.
  - wf.
  - constructor.
  - constructor; [apply T_refl | constructor].
  - apply T_refl.
Qed.

Example recursive_subtyping_uses_a_scoped_hypothesis :
  let t := TyRec (TyOwn 1 (TyBound 0)) in subtype G0 [] [] t t.
Proof.
  simpl. split.
  - constructor; [exact I|wf].
  - split.
    + constructor; [exact I|wf].
    + eapply T_rec with (x := "X") (y := "Y").
      * wf.
      * apply T_own.
        eapply T_hyp with (E0 := []) (L0 := []).
        -- left. reflexivity.
        -- apply incl_refl.
        -- apply incl_refl.
Qed.

Example reborrow_restores_the_original_reference :
  let G := Scope ["p"] ["child"; "parent"] [] in
  let parent := LftFree "parent" in
  let child := LftFree "child" in
  let L := [(parent, []); (child, [parent])] in
  let original := TyBorrow parent Mutable TyInt in
  let active := named "p" (TyBorrow child Mutable TyInt) in
  let blocked := Blocked (PVar "p") child original in
  context_includes G [] L [named "p" original] [active; blocked] /\
  unblock child [active; blocked] = [active; named "p" original].
Proof.
  simpl. split; last reflexivity.
  apply C_reborrow.
  eapply LftLocal with (parents := [LftFree "parent"]); simpl; auto.
Qed.

Lemma empty_context_lifetime_order k k' :
  lft_le [] [] k k' -> k' = Static \/ k' = k.
Proof.
  intro H. induction H; simpl in *; intuition congruence.
Qed.

Example a_lifetime_cannot_be_used_after_its_end a : ~ alive [] [] (LftFree a).
Proof.
  assert (H : forall k, alive [] [] k -> k = Static).
  { intros k Hk. induction Hk; simpl in *; try contradiction; auto.
    destruct (empty_context_lifetime_order _ _ H) as [-> | ->]; auto. }
  intro Hlive. specialize (H _ Hlive). discriminate.
Qed.
