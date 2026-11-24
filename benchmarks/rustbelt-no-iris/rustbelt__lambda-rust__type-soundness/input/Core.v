From stdpp Require Export strings gmap relations.

Declare Scope expr_scope.
Delimit Scope expr_scope with E.
Declare Scope val_scope.
Declare Scope loc_scope.
Declare Scope lrust_binder_scope.
Set Default Proof Using "Type".

Open Scope Z_scope.

(** Expressions and vals. *)
Definition block : Set := positive.
Definition loc : Set := block * Z.

Bind Scope loc_scope with loc.
Delimit Scope loc_scope with L.
Open Scope loc_scope.

Inductive base_lit : Set :=
| LitPoison | LitLoc (l : loc) | LitInt (n : Z).
Inductive bin_op : Set :=
| PlusOp | MinusOp | LeOp | EqOp | OffsetOp.
Inductive order : Set :=
| ScOrd | Na1Ord | Na2Ord.

Inductive binder := BAnon | BNamed : string → binder.
Delimit Scope lrust_binder_scope with RustB.
Bind Scope lrust_binder_scope with binder.

Notation "[ ]" := (@nil binder) : lrust_binder_scope.
Notation "a :: b" := (@cons binder a%RustB b%RustB)
  (at level 60, right associativity) : lrust_binder_scope.
Notation "[ x1 ; x2 ; .. ; xn ]" :=
  (@cons binder x1%RustB (@cons binder x2%RustB
        (..(@cons binder xn%RustB (@nil binder))..))) : lrust_binder_scope.
Notation "[ x ]" := (@cons binder x%RustB (@nil binder)) : lrust_binder_scope.

Definition cons_binder (mx : binder) (X : list string) : list string :=
  match mx with BAnon => X | BNamed x => x :: X end.
Infix ":b:" := cons_binder (at level 60, right associativity).
Fixpoint app_binder (mxl : list binder) (X : list string) : list string :=
  match mxl with [] => X | b :: mxl => b :b: app_binder mxl X end.
Infix "+b+" := app_binder (at level 60, right associativity).
Instance binder_dec_eq : EqDecision binder.
Proof. solve_decision. Defined.

Inductive expr :=
| Var (x : string)
| Lit (l : base_lit)
| Rec (f : binder) (xl : list binder) (e : expr)
| BinOp (op : bin_op) (e1 e2 : expr)
| App (e : expr) (el : list expr)
| Read (o : order) (e : expr)
| Write (o : order) (e1 e2: expr)
| CAS (e0 e1 e2 : expr)
| Alloc (e : expr)
| Free (e1 e2 : expr)
| Case (e : expr) (el : list expr)
| Fork (e : expr).

Arguments App _%_E _%_E.
Arguments Case _%_E _%_E.

Fixpoint is_closed (X : list string) (e : expr) : bool :=
  match e with
  | Var x => bool_decide (x ∈ X)
  | Lit _ => true
  | Rec f xl e => is_closed (f :b: xl +b+ X) e
  | BinOp _ e1 e2 | Write _ e1 e2 | Free e1 e2 =>
    is_closed X e1 && is_closed X e2
  | App e el | Case e el => is_closed X e && forallb (is_closed X) el
  | Read _ e | Alloc e | Fork e => is_closed X e
  | CAS e0 e1 e2 => is_closed X e0 && is_closed X e1 && is_closed X e2
  end.

Class Closed (X : list string) (e : expr) := closed : is_closed X e.
Instance closed_proof_irrel env e : ProofIrrel (Closed env e).
Proof. unfold Closed. apply _. Qed.
Instance closed_decision env e : Decision (Closed env e).
Proof. unfold Closed. apply _. Qed.

Inductive val :=
| LitV (l : base_lit)
| RecV (f : binder) (xl : list binder) (e : expr) `{Closed (f :b: xl +b+ []) e}.

Bind Scope val_scope with val.

Definition of_val (v : val) : expr :=
  match v with
  | RecV f x e => Rec f x e
  | LitV l => Lit l
  end.

Definition to_val (e : expr) : option val :=
  match e with
  | Rec f xl e =>
    if decide (Closed (f :b: xl +b+ []) e) then Some (RecV f xl e) else None
  | Lit l => Some (LitV l)
  | _ => None
  end.

(** The state: heaps of vals*lockstate. *)
Inductive lock_state :=
| WSt | RSt (n : nat).
Definition state := gmap loc (lock_state * val).

(** Evaluation contexts *)
Inductive ectx_item :=
| BinOpLCtx (op : bin_op) (e2 : expr)
| BinOpRCtx (op : bin_op) (v1 : val)
| AppLCtx (e2 : list expr)
| AppRCtx (v : val) (vl : list val) (el : list expr)
| ReadCtx (o : order)
| WriteLCtx (o : order) (e2 : expr)
| WriteRCtx (o : order) (v1 : val)
| CasLCtx (e1 e2: expr)
| CasMCtx (v0 : val) (e2 : expr)
| CasRCtx (v0 : val) (v1 : val)
| AllocCtx
| FreeLCtx (e2 : expr)
| FreeRCtx (v1 : val)
| CaseCtx (el : list expr).

Definition fill_item (Ki : ectx_item) (e : expr) : expr :=
  match Ki with
  | BinOpLCtx op e2 => BinOp op e e2
  | BinOpRCtx op v1 => BinOp op (of_val v1) e
  | AppLCtx e2 => App e e2
  | AppRCtx v vl el => App (of_val v) ((of_val <$> vl) ++ e :: el)
  | ReadCtx o => Read o e
  | WriteLCtx o e2 => Write o e e2
  | WriteRCtx o v1 => Write o (of_val v1) e
  | CasLCtx e1 e2 => CAS e e1 e2
  | CasMCtx v0 e2 => CAS (of_val v0) e e2
  | CasRCtx v0 v1 => CAS (of_val v0) (of_val v1) e
  | AllocCtx => Alloc e
  | FreeLCtx e2 => Free e e2
  | FreeRCtx v1 => Free (of_val v1) e
  | CaseCtx el => Case e el
  end.

(** Substitution *)
Fixpoint subst (x : string) (es : expr) (e : expr)  : expr :=
  match e with
  | Var y => if bool_decide (y = x) then es else Var y
  | Lit l => Lit l
  | Rec f xl e =>
    Rec f xl $ if bool_decide (BNamed x ≠ f ∧ BNamed x ∉ xl) then subst x es e else e
  | BinOp op e1 e2 => BinOp op (subst x es e1) (subst x es e2)
  | App e el => App (subst x es e) (map (subst x es) el)
  | Read o e => Read o (subst x es e)
  | Write o e1 e2 => Write o (subst x es e1) (subst x es e2)
  | CAS e0 e1 e2 => CAS (subst x es e0) (subst x es e1) (subst x es e2)
  | Alloc e => Alloc (subst x es e)
  | Free e1 e2 => Free (subst x es e1) (subst x es e2)
  | Case e el => Case (subst x es e) (map (subst x es) el)
  | Fork e => Fork (subst x es e)
  end.

Definition subst' (mx : binder) (es : expr) : expr → expr :=
  match mx with BNamed x => subst x es | BAnon => id end.

Fixpoint subst_l (xl : list binder) (esl : list expr) (e : expr) : option expr :=
  match xl, esl with
  | [], [] => Some e
  | x::xl, es::esl => subst' x es <$> subst_l xl esl e
  | _, _ => None
  end.
Arguments subst_l _%_RustB _ _%_E.

Definition Z_of_bool (b : bool) : Z :=
  if b then 1 else 0.

Definition lit_of_bool (b : bool) : base_lit :=
  LitInt $ Z_of_bool b.

Definition shift_loc (l : loc) (z : Z) : loc := (l.1, l.2 + z).

Notation "l +ₗ z" := (shift_loc l%L z%Z)
  (at level 50, left associativity) : loc_scope.

Fixpoint init_mem (l:loc) (n:nat) (σ:state) : state :=
  match n with
  | O => σ
  | S n => <[l:=(RSt 0, LitV LitPoison)]>(init_mem (l +ₗ 1) n σ)
  end.

Fixpoint free_mem (l:loc) (n:nat) (σ:state) : state :=
  match n with
  | O => σ
  | S n => delete l (free_mem (l +ₗ 1) n σ)
  end.

Inductive lit_eq (σ : state) : base_lit → base_lit → Prop :=
(* No refl case for poison *)
| IntRefl z : lit_eq σ (LitInt z) (LitInt z)
| LocRefl l : lit_eq σ (LitLoc l) (LitLoc l)
(* Comparing unallocated pointers can non-deterministically say they are equal
   even if they are not.  Given that our `free` actually makes addresses
   re-usable, this may not be strictly necessary, but it is the most
   conservative choice that avoids UB (and we cannot use UB as this operation is
   possible in safe Rust).  See
   <https://internals.rust-lang.org/t/comparing-dangling-pointers/3019> for some
   more background. *)
| LocUnallocL l1 l2 :
    σ !! l1 = None →
    lit_eq σ (LitLoc l1) (LitLoc l2)
| LocUnallocR l1 l2 :
    σ !! l2 = None →
    lit_eq σ (LitLoc l1) (LitLoc l2).

Inductive lit_neq (σ : state) : base_lit → base_lit → Prop :=
| IntNeq z1 z2 :
    z1 ≠ z2 → lit_neq σ (LitInt z1) (LitInt z2)
| LocNeq l1 l2 :
    l1 ≠ l2 → lit_neq σ (LitLoc l1) (LitLoc l2)
| LocNeqNullR l :
    lit_neq σ (LitLoc l) (LitInt 0)
| LocNeqNullL l :
    lit_neq σ (LitInt 0) (LitLoc l).

Inductive bin_op_eval (σ : state) : bin_op → base_lit → base_lit → base_lit → Prop :=
| BinOpPlus z1 z2 :
    bin_op_eval σ PlusOp (LitInt z1) (LitInt z2) (LitInt (z1 + z2))
| BinOpMinus z1 z2 :
    bin_op_eval σ MinusOp (LitInt z1) (LitInt z2) (LitInt (z1 - z2))
| BinOpLe z1 z2 :
    bin_op_eval σ LeOp (LitInt z1) (LitInt z2) (lit_of_bool $ bool_decide (z1 ≤ z2))
| BinOpEqTrue l1 l2 :
    lit_eq σ l1 l2 → bin_op_eval σ EqOp l1 l2 (lit_of_bool true)
| BinOpEqFalse l1 l2 :
    lit_neq σ l1 l2 → bin_op_eval σ EqOp l1 l2 (lit_of_bool false)
| BinOpOffset l z :
    bin_op_eval σ OffsetOp (LitLoc l) (LitInt z) (LitLoc $ l +ₗ z).

Definition stuck_term := App (Lit $ LitInt 0) [].

Inductive head_step : expr → state → expr → state → list expr → Prop :=
| BinOpS op l1 l2 l' σ :
    bin_op_eval σ op l1 l2 l' →
    head_step (BinOp op (Lit l1) (Lit l2)) σ (Lit l') σ []
| BetaS f xl e e' el σ:
    Forall (λ ei, is_Some (to_val ei)) el →
    Closed (f :b: xl +b+ []) e →
    subst_l (f::xl) (Rec f xl e :: el) e = Some e' →
    head_step (App (Rec f xl e) el) σ e' σ []
| ReadScS l n v σ:
    σ !! l = Some (RSt n, v) →
    head_step (Read ScOrd (Lit $ LitLoc l)) σ (of_val v) σ []
| ReadNa1S l n v σ:
    σ !! l = Some (RSt n, v) →
    head_step (Read Na1Ord (Lit $ LitLoc l)) σ
              (Read Na2Ord (Lit $ LitLoc l)) (<[l:=(RSt $ S n, v)]>σ)
              []
| ReadNa2S l n v σ:
    σ !! l = Some (RSt $ S n, v) →
    head_step (Read Na2Ord (Lit $ LitLoc l)) σ
              (of_val v) (<[l:=(RSt n, v)]>σ)
              []
| WriteScS l e v v' σ:
    to_val e = Some v →
    σ !! l = Some (RSt 0, v') →
    head_step (Write ScOrd (Lit $ LitLoc l) e) σ
              (Lit LitPoison) (<[l:=(RSt 0, v)]>σ)
              []
| WriteNa1S l e v v' σ:
    to_val e = Some v →
    σ !! l = Some (RSt 0, v') →
    head_step (Write Na1Ord (Lit $ LitLoc l) e) σ
              (Write Na2Ord (Lit $ LitLoc l) e) (<[l:=(WSt, v')]>σ)
              []
| WriteNa2S l e v v' σ:
    to_val e = Some v →
    σ !! l = Some (WSt, v') →
    head_step (Write Na2Ord (Lit $ LitLoc l) e) σ
              (Lit LitPoison) (<[l:=(RSt 0, v)]>σ)
              []
| CasFailS l n e1 lit1 e2 lit2 litl σ :
    to_val e1 = Some $ LitV lit1 → to_val e2 = Some $ LitV lit2 →
    σ !! l = Some (RSt n, LitV litl) →
    lit_neq σ lit1 litl →
    head_step (CAS (Lit $ LitLoc l) e1 e2) σ (Lit $ lit_of_bool false) σ  []
| CasSucS l e1 lit1 e2 lit2 litl σ :
    to_val e1 = Some $ LitV lit1 → to_val e2 = Some $ LitV lit2 →
    σ !! l = Some (RSt 0, LitV litl) →
    lit_eq σ lit1 litl →
    head_step (CAS (Lit $ LitLoc l) e1 e2) σ
              (Lit $ lit_of_bool true) (<[l:=(RSt 0, LitV lit2)]>σ)
              []
(* A succeeding CAS has to detect concurrent non-atomic read accesses, and
   trigger UB if there is one.  In lambdaRust, succeeding and failing CAS are
   not mutually exclusive, so it could happen that a CAS can both fail (and
   hence not be stuck) but also succeed (and hence be racing with a concurrent
   non-atomic read).  In that case, we have to explicitly reduce to a stuck
   state; due to the possibility of failing CAS, we cannot rely on the current
   state being stuck like we could in a language where failing and succeeding
   CAS are mutually exclusive.

   This means that CAS is atomic (it always reducs to an irreducible
   expression), but not strongly atomic (it does not always reduce to a value).

   If there is a concurrent non-atomic write, the CAS itself is stuck: All its
   reductions are blocked.  *)
| CasStuckS l n e1 lit1 e2 lit2 litl σ :
    to_val e1 = Some $ LitV lit1 → to_val e2 = Some $ LitV lit2 →
    σ !! l = Some (RSt n, LitV litl) → (0 < n)%nat →
    lit_eq σ lit1 litl →
    head_step (CAS (Lit $ LitLoc l) e1 e2) σ
              stuck_term σ
              []
| AllocS n l σ :
    0 < n →
    (∀ m, σ !! (l +ₗ m) = None) →
    head_step (Alloc $ Lit $ LitInt n) σ
              (Lit $ LitLoc l) (init_mem l (Z.to_nat n) σ) []
| FreeS n l σ :
    0 < n →
    (∀ m, is_Some (σ !! (l +ₗ m)) ↔ 0 ≤ m < n) →
    head_step (Free (Lit $ LitInt n) (Lit $ LitLoc l)) σ
              (Lit LitPoison) (free_mem l (Z.to_nat n) σ)
              []
| CaseS i el e σ :
    0 ≤ i →
    el !! (Z.to_nat i) = Some e →
    head_step (Case (Lit $ LitInt i) el) σ e σ []
| ForkS e σ:
    head_step (Fork e) σ (Lit LitPoison) σ [e].



(* The POPL'18 evaluation-context and thread-pool closures, specialized to λRust. *)
Definition fill (K : list ectx_item) (e : expr) : expr :=
  foldl (flip fill_item) e K.

Inductive prim_step : expr -> state -> expr -> state -> list expr -> Prop :=
| Ectx_step K e e' σ σ' spawned :
    head_step e σ e' σ' spawned ->
    prim_step (fill K e) σ (fill K e') σ' spawned.

Definition reducible (e : expr) (σ : state) : Prop :=
  exists e' σ' spawned, prim_step e σ e' σ' spawned.

Inductive pool_step : (list expr * state) -> (list expr * state) -> Prop :=
| Step_thread before after e e' σ σ' spawned :
    prim_step e σ e' σ' spawned ->
    pool_step (before ++ e :: after, σ)
              (before ++ e' :: after ++ spawned, σ').

Inductive access_kind : Type := ReadAcc | WriteAcc | FreeAcc.

(* This is a crucial definition; if we forget to sync it with head_step,
   the results proven here are worthless. *)
Inductive next_access_head : expr → state → access_kind * order → loc → Prop :=
| Access_read ord l σ :
    next_access_head (Read ord (Lit $ LitLoc l)) σ (ReadAcc, ord) l
| Access_write ord l e σ :
    is_Some (to_val e) →
    next_access_head (Write ord (Lit $ LitLoc l) e) σ (WriteAcc, ord) l
| Access_cas_fail l st e1 lit1 e2 lit2 litl σ :
    to_val e1 = Some $ LitV lit1 → to_val e2 = Some $ LitV lit2 →
    lit_neq σ lit1 litl → σ !! l = Some (st, LitV litl) →
    next_access_head (CAS (Lit $ LitLoc l) e1 e2) σ (ReadAcc, ScOrd) l
| Access_cas_suc l st e1 lit1 e2 lit2 litl σ :
    to_val e1 = Some $ LitV lit1 → to_val e2 = Some $ LitV lit2 →
    lit_eq σ lit1 litl → σ !! l = Some (st, LitV litl) →
    next_access_head (CAS (Lit $ LitLoc l) e1 e2) σ (WriteAcc, ScOrd) l
| Access_free n l σ i :
    0 ≤ i < n →
    next_access_head (Free (Lit $ LitInt n) (Lit $ LitLoc l))
                     σ (FreeAcc, Na2Ord) (l +ₗ i).

Definition next_access_thread (e: expr) (σ : state)
           (a : access_kind * order) (l : loc) : Prop :=
  ∃ K e', next_access_head e' σ a l ∧ e = fill K e'.

Definition next_accesses_threadpool (el: list expr) (σ : state)
           (a1 a2 : access_kind * order) (l : loc): Prop :=
  ∃ t1 e1 t2 e2 t3, el = t1 ++ e1 :: t2 ++ e2 :: t3 ∧
                    next_access_thread e1 σ a1 l ∧ next_access_thread e2 σ a2 l.

Definition nonracing_accesses (a1 a2 : access_kind * order) : Prop :=
  match a1, a2 with
  | (_, ScOrd), (_, ScOrd) => True
  | (ReadAcc, _), (ReadAcc, _) => True
  | _, _ => False
  end.

Definition nonracing_threadpool (el : list expr) (σ : state) : Prop :=
  ∀ l a1 a2, next_accesses_threadpool el σ a1 a2 l →
             nonracing_accesses a1 a2.
