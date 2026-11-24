Require Export Core.
From Stdlib Require Export List Permutation.

(* Appendix §1.4. Free names are used in typing derivations; indices
   represent bound variables in function and recursive types. *)
Inductive lifetime :=
| Static
| LftFree (name : string)
| LftBound (index : nat).

Definition external := list (lifetime * lifetime).
Definition local := list (lifetime * list lifetime).

Inductive borrow_mode := Mutable | Shared.

Inductive ty :=
| TyFree (name : string)
| TyBound (index : nat)
| TyBool
| TyInt
| TyUninit (words : nat)
| TyOwn (block_size : nat) (content : ty)
| TyBorrow (k : lifetime) (mode : borrow_mode) (content : ty)
| TySum (branches : list ty)
| TyProd (fields : list ty)
| TyFn (arity_lfts : nat) (requires : external) (args : list ty) (result : ty)
| TyRec (body : ty).

(* In a TyFn signature, args and result bind the lifetime parameters.
   The external context additionally binds the call lifetime at index 0. *)
Definition open_lifetime (depth : nat) (args : list lifetime) (k : lifetime) :=
  match k with
  | LftBound i =>
      if Nat.ltb i depth then LftBound i
      else
        let j := (i - depth)%nat in
        match nth_error args j with
        | Some (LftBound n) => LftBound (depth + n)
        | Some a => a
        | None => LftBound (i - length args)
        end
  | _ => k
  end.

Definition open_external depth args (E : external) : external :=
  map (fun '(k, k') => (open_lifetime depth args k, open_lifetime depth args k')) E.

Fixpoint open_type_lfts (depth : nat) (args : list lifetime) (t : ty) : ty :=
  match t with
  | TyOwn n t0 => TyOwn n (open_type_lfts depth args t0)
  | TyBorrow k m t0 => TyBorrow (open_lifetime depth args k) m (open_type_lfts depth args t0)
  | TySum ts => TySum (map (open_type_lfts depth args) ts)
  | TyProd ts => TyProd (map (open_type_lfts depth args) ts)
  | TyFn n E ts r =>
      TyFn n (open_external (S (depth + n)) args E)
             (map (open_type_lfts (depth + n) args) ts)
             (open_type_lfts (depth + n) args r)
  | TyRec b => TyRec (open_type_lfts depth args b)
  | _ => t
  end.

Fixpoint shift_type_vars (cutoff count : nat) (t : ty) : ty :=
  match t with
  | TyBound i => if Nat.ltb i cutoff then t else TyBound (count + i)
  | TyOwn n t0 => TyOwn n (shift_type_vars cutoff count t0)
  | TyBorrow k m t0 => TyBorrow k m (shift_type_vars cutoff count t0)
  | TySum ts => TySum (map (shift_type_vars cutoff count) ts)
  | TyProd ts => TyProd (map (shift_type_vars cutoff count) ts)
  | TyFn n E ts r =>
      TyFn n E (map (shift_type_vars cutoff count) ts) (shift_type_vars cutoff count r)
  | TyRec b => TyRec (shift_type_vars (S cutoff) count b)
  | _ => t
  end.

Fixpoint shift_type_lfts (cutoff count : nat) (t : ty) : ty :=
  let shift depth k :=
    match k with
    | LftBound i => if Nat.ltb i depth then k else LftBound (count + i)
    | _ => k
    end in
  match t with
  | TyOwn n t0 => TyOwn n (shift_type_lfts cutoff count t0)
  | TyBorrow k m t0 => TyBorrow (shift cutoff k) m (shift_type_lfts cutoff count t0)
  | TySum ts => TySum (map (shift_type_lfts cutoff count) ts)
  | TyProd ts => TyProd (map (shift_type_lfts cutoff count) ts)
  | TyFn n E ts r =>
      TyFn n (map (fun '(k, k') => (shift (S (cutoff + n)) k, shift (S (cutoff + n)) k')) E)
        (map (shift_type_lfts (cutoff + n) count) ts) (shift_type_lfts (cutoff + n) count r)
  | TyRec b => TyRec (shift_type_lfts cutoff count b)
  | _ => t
  end.

Fixpoint open_type_var (depth lft_depth : nat) (a t : ty) : ty :=
  match t with
  | TyBound i =>
      match Nat.compare i depth with
      | Lt => t
      | Eq => shift_type_lfts 0 lft_depth (shift_type_vars 0 depth a)
      | Gt => TyBound (Nat.pred i)
      end
  | TyOwn n t0 => TyOwn n (open_type_var depth lft_depth a t0)
  | TyBorrow k m t0 => TyBorrow k m (open_type_var depth lft_depth a t0)
  | TySum ts => TySum (map (open_type_var depth lft_depth a) ts)
  | TyProd ts => TyProd (map (open_type_var depth lft_depth a) ts)
  | TyFn n E ts r =>
      TyFn n E (map (open_type_var depth (lft_depth + n) a) ts)
               (open_type_var depth (lft_depth + n) a r)
  | TyRec b => TyRec (open_type_var (S depth) lft_depth a b)
  | _ => t
  end.

Inductive path :=
| PVar (name : string)
| POffset (base : path) (words : nat).

Inductive entry :=
| Available (p : path) (t : ty)
| Blocked (p : path) (k : lifetime) (t : ty).

Definition type_context := list entry.

Record continuation := Cont {
  cont_name : string;
  cont_lfts : local;
  cont_args : list string;
  cont_types : type_context
}.
Definition cont_context := list continuation.

Record scope := Scope {
  term_names : list string;
  lft_names : list string;
  type_names : list string
}.

Definition bind_terms (xs : list string) (G : scope) : scope :=
  Scope (xs ++ term_names G) (lft_names G) (type_names G).
Definition bind_lifetimes (ks : list string) (G : scope) : scope :=
  Scope (term_names G) (ks ++ lft_names G) (type_names G).
Definition bind_types (xs : list string) (G : scope) : scope :=
  Scope (term_names G) (lft_names G) (xs ++ type_names G).

Inductive wf_path (G : scope) : path -> Prop :=
| WfVar x : In x (term_names G) -> wf_path G (PVar x)
| WfOffset p n : wf_path G p -> wf_path G (POffset p n).

Definition wf_lifetime (G : scope) (bound : nat) (k : lifetime) : Prop :=
  match k with
  | Static => True
  | LftFree x => In x (lft_names G)
  | LftBound i => (i < bound)%nat
  end.

Definition wf_external G bound (E : external) :=
  Forall (fun '(k, k') => wf_lifetime G bound k /\ wf_lifetime G bound k') E.

Definition wf_local G (L : local) :=
  Forall (fun '(k, parents) => wf_lifetime G 0 k /\ Forall (wf_lifetime G 0) parents) L.

(* The size computation never visits a recursive variable in a well-formed
   type: a pointer stops the computation. *)
Fixpoint guarded (index : nat) (t : ty) : Prop :=
  let all ts := fold_right (fun t ok => guarded index t /\ ok) True ts in
  match t with
  | TyBound i => i <> index
  | TyProd ts | TySum ts => all ts
  | TyFn _ _ ts r => all ts /\ guarded index r
  | TyRec b => guarded (S index) b
  | _ => True
  end.

Inductive wf_type (G : scope) : nat -> nat -> ty -> Prop :=
| WfTypeFree d a x : In x (type_names G) -> wf_type G d a (TyFree x)
| WfTypeBound d a i : (i < a)%nat -> wf_type G d a (TyBound i)
| WfBool d a : wf_type G d a TyBool
| WfInt d a : wf_type G d a TyInt
| WfUninit d a n : wf_type G d a (TyUninit n)
| WfOwn d a n t : wf_type G d a t -> wf_type G d a (TyOwn n t)
| WfBorrow d a k m t :
    wf_lifetime G d k -> wf_type G d a t -> wf_type G d a (TyBorrow k m t)
| WfSum d a ts : Forall (wf_type G d a) ts -> wf_type G d a (TySum ts)
| WfProd d a ts : Forall (wf_type G d a) ts -> wf_type G d a (TyProd ts)
| WfFn d a n E ts r :
    wf_external G (S (d + n)) E ->
    Forall (wf_type G (d + n) a) ts -> wf_type G (d + n) a r ->
    wf_type G d a (TyFn n E ts r)
| WfRec d a t :
    guarded 0 t -> wf_type G d (S a) t -> wf_type G d a (TyRec t).

Definition wf_entry G (b : entry) :=
  match b with
  | Available p t => wf_path G p /\ wf_type G 0 0 t
  | Blocked p k t => wf_path G p /\ wf_lifetime G 0 k /\ wf_type G 0 0 t
  end.
Definition wf_context G := Forall (wf_entry G).

Definition wf_cont G (k : continuation) :=
  In (cont_name k) (term_names G) /\ wf_local G (cont_lfts k) /\
  NoDup (cont_args k) /\
  wf_context (bind_terms (cont_args k) G) (cont_types k).
Definition wf_cont_context G := Forall (wf_cont G).

Fixpoint type_size (t : ty) : nat :=
  match t with
  | TyBool | TyInt | TyOwn _ _ | TyBorrow _ _ _ | TyFn _ _ _ _ => 1
  | TyUninit n => n
  | TyProd ts => fold_right (fun t n => Nat.add (type_size t) n) 0%nat ts
  | TySum ts => S (fold_right (fun t n => Nat.max (type_size t) n) 0%nat ts)
  | TyRec t0 => type_size t0
  | TyFree _ | TyBound _ => 0
  end.

Definition own (t : ty) := TyOwn (type_size t) t.
Definition unit_type := TyProd [].

(* Appendix §1.4.2. The three properties have the same structural clauses,
   except for pointer capabilities. *)
Inductive property := Copy | Send | Sync.

Inductive type_has : property -> ty -> Prop :=
| HasBool p : type_has p TyBool
| HasInt p : type_has p TyInt
| HasUninit p n : type_has p (TyUninit n)
| HasFree p x : type_has p (TyFree x)
| HasBound p i : type_has p (TyBound i)
| HasFn p n E ts r : type_has p (TyFn n E ts r)
| HasProd p ts : Forall (type_has p) ts -> type_has p (TyProd ts)
| HasSum p ts : Forall (type_has p) ts -> type_has p (TySum ts)
| HasRec p t : type_has p t -> type_has p (TyRec t)
| HasOwnSend n t : type_has Send t -> type_has Send (TyOwn n t)
| HasOwnSync n t : type_has Sync t -> type_has Sync (TyOwn n t)
| HasMutSend k t : type_has Send t -> type_has Send (TyBorrow k Mutable t)
| HasMutSync k t : type_has Sync t -> type_has Sync (TyBorrow k Mutable t)
| HasSharedCopy k t : type_has Copy (TyBorrow k Shared t)
| HasSharedSend k t : type_has Sync t -> type_has Send (TyBorrow k Shared t)
| HasSharedSync k t : type_has Sync t -> type_has Sync (TyBorrow k Shared t).

(* Appendix §1.4.3: these are typing judgments, not lifetime logic assertions. *)
(* [lft_le E L k k'] means k is no longer than k'. *)
Inductive lft_le (E : external) (L : local) : lifetime -> lifetime -> Prop :=
| LftStatic k : lft_le E L k Static
| LftLocal k parents k' :
    In (k, parents) L -> In k' parents -> lft_le E L k k'
| LftExternal k k' : In (k, k') E -> lft_le E L k k'
| LftRefl k : lft_le E L k k
| LftTrans k k' k'' :
    lft_le E L k k' -> lft_le E L k' k'' -> lft_le E L k k''.

Inductive alive (E : external) (L : local) : lifetime -> Prop :=
| AliveStatic : alive E L Static
| AliveLocal k parents : In (k, parents) L -> Forall (alive E L) parents -> alive E L k
| AliveIncluded k k' : alive E L k -> lft_le E L k k' -> alive E L k'.

Definition external_satisfied E L (requires : external) :=
  Forall (fun '(k, k') => lft_le E L k k') requires.
