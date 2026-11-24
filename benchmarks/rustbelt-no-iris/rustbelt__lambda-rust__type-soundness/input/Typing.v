Require Export Surface.

Definition well_formed G E L K T :=
  wf_external G 0 E /\ wf_local G L /\ wf_cont_context G K /\ wf_context G T.

Definition named (x : string) := Available (PVar x).

Definition owned_args (paths : list path) (ts : list ty) : type_context :=
  map (fun '(p, t) => Available p (own t)) (combine paths ts).

Fixpoint rename_path (names : list (string * string)) (p : path) : path :=
  match p with
  | PVar x =>
      match find (fun '(a, _) => String.eqb x a) names with
      | Some (_, y) => PVar y
      | None => PVar x
      end
  | POffset p0 n => POffset (rename_path names p0) n
  end.

Definition rename_context (formals actuals : list string) (T : type_context) :=
  let rename := rename_path (combine formals actuals) in
  map (fun e => match e with
          | Available p t => Available (rename p) t
          | Blocked p k t => Blocked (rename p) k t
          end) T.

Fixpoint path_root (p : path) : string :=
  match p with
  | PVar x => x
  | POffset base _ => path_root base
  end.

Definition entry_root (e : entry) : string :=
  match e with
  | Available p _ | Blocked p _ _ => path_root p
  end.

(* Binding the result must not capture a path in the caller's retained resources. *)
Definition return_fresh (y : string) (frame : type_context) : Prop :=
  ~ In y (map entry_root frame).

Definition case_owned (p : path) (n : nat) (all : list ty) (t : ty) :=
  let padding := (type_size (TySum all) - S (type_size t))%nat in
  [Available (POffset p 0) (TyOwn n (TyUninit 1));
   Available (POffset p 1) (TyOwn n t);
   Available (POffset p (S (type_size t))) (TyOwn n (TyUninit padding))].

(* Appendix §1.4.5. The explicit well-formedness premises implement the
   appendix's convention that every typing judgement is well formed. *)
Inductive typed_body : scope -> external -> local -> cont_context -> type_context -> body -> Prop :=
| F_consequence G E L L' K K' T T' code :
    well_formed G E L K T ->
    Permutation L L' -> context_includes G E L T T' ->
    continuations_include G E K K' ->
    typed_body G E L' K' T' code ->
    typed_body G E L K T code
| F_equalize G E L K T a k code :
    well_formed G E (L ++ [(LftFree a, [k])]) K T ->
    typed_body G (E ++ [(LftFree a, k); (k, LftFree a)]) L K T code ->
    typed_body G E (L ++ [(LftFree a, [k])]) K T code
| F_let G E L K before after frame x i code :
    well_formed G E L K (before ++ frame) ->
    ~ In x (term_names G) ->
    typed_instruction G E L before i x after ->
    typed_body (bind_terms [x] G) E L K (after ++ frame) code ->
    typed_body G E L K (before ++ frame) (FLet x i code)
| F_letcont G E L1 L2 K T captured k xs code next :
    well_formed G E L2 K T ->
    NoDup (k :: xs ++ term_names G) ->
    let K' := K ++ [Cont k L1 xs captured] in
    typed_body (bind_terms (k :: xs) G) E L1 K' captured code ->
    typed_body (bind_terms [k] G) E L2 K' T next ->
    typed_body G E L2 K T (FLetCont k xs code next)
| F_if G E L K T p yes no :
    well_formed G E L K (T ++ [Available p TyBool]) ->
    typed_body G E L K T yes -> typed_body G E L K T no ->
    typed_body G E L K (T ++ [Available p TyBool]) (FIf p yes no)
| F_jump G E L T U k formals actuals :
    well_formed G E L [Cont k L formals U] T ->
    length actuals = length formals ->
    Forall (fun x => In x (term_names G)) actuals ->
    context_includes G E L T (rename_context formals actuals U) ->
    typed_body G E L [Cont k L formals U] T (FJump k actuals)
| F_call G E L T frame f k y n requires arg_types r params call limits args :
    well_formed G E L
      [Cont k L [y] (named y (own (instantiate params r)) :: frame)]
      (T ++ [named f (TyFn n requires arg_types r)]) ->
    return_fresh y frame ->
    length params = n -> Forall (wf_lifetime G 0) params ->
    length args = length arg_types -> Forall (wf_path G) args ->
    context_includes G E L T (owned_args args (map (instantiate params) arg_types) ++ frame) ->
    Forall (alive E L) limits ->
    ~ In call (lft_names G) ->
    external_satisfied (E ++ map (fun l => (LftFree call, l)) limits) L
      (instantiate_requirements (LftFree call) params requires) ->
    typed_body G E L
      [Cont k L [y] (named y (own (instantiate params r)) :: frame)]
      (T ++ [named f (TyFn n requires arg_types r)]) (FCall f args k)
| F_newlft G E L K T name parents code :
    well_formed G E L K T ->
    ~ In name (lft_names G) -> Forall (wf_lifetime G 0) parents ->
    typed_body (bind_lifetimes [name] G) E (L ++ [(LftFree name, parents)]) K T code ->
    typed_body G E L K T (FNewLft code)
| F_endlft G E L K T k parents code :
    well_formed G E (L ++ [(k, parents)]) K T ->
    typed_body G E L K (unblock k T) code ->
    typed_body G E (L ++ [(k, parents)]) K T (FEndLft code)
| F_case_own G E L K T p n ts branches :
    well_formed G E L K (T ++ [Available p (TyOwn n (TySum ts))]) ->
    Forall2 (fun t branch =>
      typed_body G E L K (T ++ case_owned p n ts t) branch \/
      typed_body G E L K (T ++ [Available p (TyOwn n (TySum ts))]) branch) ts branches ->
    typed_body G E L K (T ++ [Available p (TyOwn n (TySum ts))]) (FCase p branches)
| F_case_bor G E L K T p k m ts branches :
    well_formed G E L K (T ++ [Available p (TyBorrow k m (TySum ts))]) ->
    alive E L k ->
    Forall2 (fun t branch =>
      typed_body G E L K (T ++ [Available (POffset p 1) (TyBorrow k m t)]) branch \/
      typed_body G E L K (T ++ [Available p (TyBorrow k m (TySum ts))]) branch) ts branches ->
    typed_body G E L K (T ++ [Available p (TyBorrow k m (TySum ts))]) (FCase p branches)
with typed_instruction : scope -> external -> local -> type_context ->
    instruction -> string -> type_context -> Prop :=
| S_true G E L x : typed_instruction G E L [] ITrue x [named x TyBool]
| S_false G E L x : typed_instruction G E L [] IFalse x [named x TyBool]
| S_num G E L z x : typed_instruction G E L [] (INum z) x [named x TyInt]
| S_fn G E L captured f xs k code x y n req ts r params call :
    length xs = length ts -> NoDup (f :: k :: xs ++ term_names G) ->
    fresh_lifetimes G n params call ->
    wf_type G 0 0 (TyFn n req ts r) ->
    Forall (fun b => match b with
      | Available _ t => type_has Copy t /\ type_has Send t
      | Blocked _ _ _ => False
      end) captured ->
    let as_lfts := map LftFree params in
    let call_lfts := [(LftFree call, [])] in
    let K := [Cont k call_lfts [y] [named y (own (instantiate as_lfts r))]] in
    let G' := bind_terms (f :: k :: xs) (bind_lifetimes (call :: params) G) in
    let E' := instantiate_requirements (LftFree call) as_lfts req ++ E in
    let T := captured ++ owned_args (map PVar xs) (map (instantiate as_lfts) ts)
                      ++ [named f (TyFn n req ts r)] in
    typed_body G' E' call_lfts K T code ->
    typed_instruction G E L captured (IFun f xs k code) x [named x (TyFn n req ts r)]
| S_path G E L p t x :
    typed_instruction G E L [Available p t] (IPath p) x [named x t]
| S_add G E L p q x :
    typed_instruction G E L [Available p TyInt; Available q TyInt] (IAdd p q) x [named x TyInt]
| S_sub G E L p q x :
    typed_instruction G E L [Available p TyInt; Available q TyInt] (ISub p q) x [named x TyInt]
| S_leq G E L p q x :
    typed_instruction G E L [Available p TyInt; Available q TyInt] (ILe p q) x [named x TyBool]
| S_new G E L n x :
    typed_instruction G E L [] (INew n) x [named x (TyOwn n (TyUninit n))]
| S_delete G E L n p t x :
    type_size t = n ->
    typed_instruction G E L [Available p (TyOwn n t)] (IDelete n p) x []
| S_deref G E L p before t after x :
    type_read G E L before t after -> type_size t = 1%nat ->
    typed_instruction G E L [Available p before] (IRead p) x [Available p after; named x t]
| S_deref_bor_own G E L p k m n t x :
    alive E L k ->
    typed_instruction G E L [Available p (TyBorrow k m (TyOwn n t))] (IRead p) x
      [named x (TyBorrow k m t)]
| S_deref_bor_bor G E L p k k' m t x :
    alive E L k -> lft_le E L k k' ->
    typed_instruction G E L [Available p (TyBorrow k m (TyBorrow k' Mutable t))] (IRead p) x
      [named x (TyBorrow k m t)]
| S_assign G E L p q before t after x :
    type_write G E L before t after ->
    typed_instruction G E L [Available p before; Available q t] (IWrite p q) x [Available p after]
| S_sum_assign_unit G E L p before ts after tag x :
    nth_error ts tag = Some unit_type -> type_write G E L before (TySum ts) after ->
    typed_instruction G E L [Available p before] (ISumUnit tag p) x [Available p after]
| S_sum_assign G E L p q before ts t after tag x :
    nth_error ts tag = Some t -> type_write G E L before (TySum ts) after ->
    typed_instruction G E L [Available p before; Available q t] (ISumWrite tag p q) x [Available p after]
| S_memcpy G E L p q before_src before_dst t after_src after_dst n x :
    type_size t = n ->
    type_write G E L before_dst t after_dst -> type_read G E L before_src t after_src ->
    typed_instruction G E L [Available p before_dst; Available q before_src] (ICopy n p q) x
      [Available p after_dst; Available q after_src]
| S_sum_memcpy G E L p q before_src before_dst ts t after_src after_dst tag n x :
    type_size t = n -> nth_error ts tag = Some t ->
    type_write G E L before_dst (TySum ts) after_dst -> type_read G E L before_src t after_src ->
    typed_instruction G E L [Available p before_dst; Available q before_src] (ISumCopy tag n p q) x
      [Available p after_dst; Available q after_src].
