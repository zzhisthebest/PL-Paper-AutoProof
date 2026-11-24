Require Export Types.

Definition fresh_lifetimes (G : scope) n (params : list string) (call : string) :=
  length params = n /\ NoDup (call :: params ++ lft_names G).

Definition instantiate (params : list lifetime) (t : ty) := open_type_lfts 0 params t.
Definition instantiate_requirements call params E := open_external 0 (call :: params) E.

(* An explicit hypothesis context reifies the hypothetical premise of T-rec.
   Assumptions are scoped to a lifetime context and to the two fresh type names. *)
Definition type_hypotheses := list (external * local * string * string).

Inductive subtype_under :
    scope -> type_hypotheses -> external -> local -> ty -> ty -> Prop :=
| T_hyp G H E L E0 L0 x y :
    In (E0, L0, x, y) H -> incl E0 E -> incl L0 L ->
    subtype_under G H E L (TyFree x) (TyFree y)
| T_refl G H E L t : subtype_under G H E L t t
| T_trans G H E L a b c :
    wf_type G 0 0 b ->
    subtype_under G H E L a b -> subtype_under G H E L b c ->
    subtype_under G H E L a c
| T_bor_lft G H E L k k' m t :
    lft_le E L k k' ->
    subtype_under G H E L (TyBorrow k m t) (TyBorrow k' m t)
| T_uninit_prod G H E L ns :
    subtype_under G H E L (TyUninit (fold_right Nat.add 0%nat ns)) (TyProd (map TyUninit ns))
| T_uninit_prod_inv G H E L ns :
    subtype_under G H E L (TyProd (map TyUninit ns)) (TyUninit (fold_right Nat.add 0%nat ns))
| T_rec_unfold G H E L t :
    subtype_under G H E L (TyRec t) (open_type_var 0 0 (TyRec t) t)
| T_rec_fold G H E L t :
    subtype_under G H E L (open_type_var 0 0 (TyRec t) t) (TyRec t)
| T_rec G H E L x y a b :
    NoDup (x :: y :: type_names G) ->
    subtype_under (bind_types [x; y] G) ((E, L, x, y) :: H) E L
      (open_type_var 0 0 (TyFree x) a) (open_type_var 0 0 (TyFree y) b) ->
    subtype_under G H E L (TyRec a) (TyRec b)
| T_own G H E L n a b :
    subtype_under G H E L a b ->
    subtype_under G H E L (TyOwn n a) (TyOwn n b)
| T_bor_shr G H E L k a b :
    subtype_under G H E L a b ->
    subtype_under G H E L (TyBorrow k Shared a) (TyBorrow k Shared b)
| T_bor_mut G H E L k a b :
    subtype_under G H E L a b -> subtype_under G H E L b a ->
    subtype_under G H E L (TyBorrow k Mutable a) (TyBorrow k Mutable b)
| T_prod G H E L ts us :
    Forall2 (subtype_under G H E L) ts us ->
    subtype_under G H E L (TyProd ts) (TyProd us)
| T_sum G H E L ts us :
    Forall2 (subtype_under G H E L) ts us ->
    subtype_under G H E L (TySum ts) (TySum us)
| T_fn G H E L na nb Ea Eb as_ bs a b names call actuals :
    fresh_lifetimes G nb names call ->
    let params := map LftFree names in
    let G' := bind_lifetimes (call :: names) G in
    let E' := E ++ instantiate_requirements (LftFree call) params Eb in
    length actuals = na -> Forall (wf_lifetime G' 0) actuals ->
    external_satisfied E' L (instantiate_requirements (LftFree call) actuals Ea) ->
    Forall2 (subtype_under G' H E' L) (map (instantiate params) bs) (map (instantiate actuals) as_) ->
    subtype_under G' H E' L (instantiate actuals a) (instantiate params b) ->
    subtype_under G H E L (TyFn na Ea as_ a) (TyFn nb Eb bs b).

(* Section 1.4 assumes well-formedness implicitly. *)
Definition subtype (G : scope) E L a b :=
  wf_type G 0 0 a /\ wf_type G 0 0 b /\ subtype_under G [] E L a b.

Fixpoint split_product (p : path) (offset : nat) (wrap : ty -> ty) (ts : list ty) :=
  match ts with
  | [] => []
  | t :: rest =>
      Available (POffset p offset) (wrap t) ::
      split_product p (offset + type_size t) wrap rest
  end.

Inductive context_includes (G : scope) (E : external) (L : local) :
    type_context -> type_context -> Prop :=
| C_perm T T' : Permutation T T' -> context_includes G E L T T'
| C_trans T U V :
    wf_context G U ->
    context_includes G E L T U -> context_includes G E L U V -> context_includes G E L T V
| C_weaken T T' : context_includes G E L (T ++ T') T
| C_frame T T' frame :
    context_includes G E L T T' -> context_includes G E L (frame ++ T) (frame ++ T')
| C_copy p t :
    type_has Copy t -> context_includes G E L [Available p t] [Available p t; Available p t]
| C_subtype p t u :
    subtype G E L t u -> context_includes G E L [Available p t] [Available p u]
| C_share p k t :
    alive E L k ->
    context_includes G E L [Available p (TyBorrow k Mutable t)] [Available p (TyBorrow k Shared t)]
| C_split_own p n ts :
    ts <> [] ->
    context_includes G E L [Available p (TyOwn n (TyProd ts))] (split_product p 0 (TyOwn n) ts)
| C_join_own p n ts :
    ts <> [] ->
    context_includes G E L (split_product p 0 (TyOwn n) ts) [Available p (TyOwn n (TyProd ts))]
| C_split_bor p k m ts :
    ts <> [] ->
    context_includes G E L [Available p (TyBorrow k m (TyProd ts))] (split_product p 0 (TyBorrow k m) ts)
| C_join_bor p k m ts :
    ts <> [] ->
    context_includes G E L (split_product p 0 (TyBorrow k m) ts) [Available p (TyBorrow k m (TyProd ts))]
| C_borrow p n k t :
    wf_lifetime G 0 k ->
    context_includes G E L [Available p (TyOwn n t)]
      [Available p (TyBorrow k Mutable t); Blocked p k (TyOwn n t)]
| C_reborrow p k k' m t :
    lft_le E L k' k ->
    context_includes G E L [Available p (TyBorrow k m t)]
      [Available p (TyBorrow k' m t); Blocked p k' (TyBorrow k m t)].

Definition unblock (k : lifetime) (T : type_context) : type_context :=
  map (fun e =>
    match e with
    | Blocked p k' t =>
        if match k, k' with
           | Static, Static => true
           | LftFree x, LftFree y => String.eqb x y
           | LftBound i, LftBound j => Nat.eqb i j
           | _, _ => false
           end
        then Available p t else e
    | _ => e
    end) T.

Inductive continuations_include (G : scope) (E : external) :
    cont_context -> cont_context -> Prop :=
| K_perm K K' : Permutation K K' -> continuations_include G E K K'
| K_trans K K' K'' :
    wf_cont_context G K' ->
    continuations_include G E K K' -> continuations_include G E K' K'' ->
    continuations_include G E K K''
| K_weaken K K' : continuations_include G E (K ++ K') K
| K_subtype K K' k L xs T T' :
    continuations_include G E K K' -> context_includes (bind_terms xs G) E L T' T ->
    continuations_include G E (K ++ [Cont k L xs T]) (K' ++ [Cont k L xs T']).

Inductive type_write (G : scope) (E : external) (L : local) : ty -> ty -> ty -> Prop :=
| WriteOwn n before value :
    type_size before = type_size value ->
    type_write G E L (TyOwn n before) value (TyOwn n value)
| WriteBorrow k t :
    alive E L k -> type_write G E L (TyBorrow k Mutable t) t (TyBorrow k Mutable t).

Inductive type_read (G : scope) (E : external) (L : local) : ty -> ty -> ty -> Prop :=
| ReadOwnCopy n t :
    type_has Copy t -> type_read G E L (TyOwn n t) t (TyOwn n t)
| ReadOwnMove n t :
    type_read G E L (TyOwn n t) t (TyOwn n (TyUninit (type_size t)))
| ReadBorrow k m t :
    alive E L k -> type_has Copy t ->
    type_read G E L (TyBorrow k m t) t (TyBorrow k m t).
