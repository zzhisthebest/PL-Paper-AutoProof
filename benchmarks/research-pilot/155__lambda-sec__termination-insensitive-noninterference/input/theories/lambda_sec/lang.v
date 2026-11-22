From logrel_ifc.prelude Require Export base.

From stdpp Require Import gmap countable.

Module lambda_sec.

Inductive binop := Add | Sub | Mult | Eq | Le | Lt.

Record loc := { loc_car : Z }.

Global Instance loc_eq_decision : EqDecision loc := ltac:(solve_decision).

Global Instance loc_countable : Countable loc :=
  ltac:(apply (inj_countable' loc_car (λ i, {| loc_car := i |})); intros []; done).

Inductive expr :=
  | Var (x : var)
  | Lam (e : {bind expr})
  | App (e1 e2 : expr)
  | LetIn (e1 : expr) (e2 : {bind expr})
  | Seq (e1 e2 : expr)

  | Unit
  | Bool (b : bool)
  | Nat (n : nat)
  | BinOp (op : binop) (e1 e2 : expr)
  | If (e0 e1 e2 : expr)

  | Pair (e1 e2 : expr)
  | Proj1 (e : expr)
  | Proj2 (e : expr)

  | InjL (e : expr)
  | InjR (e : expr)
  | Case (e0 : expr) (e1 e2 : {bind expr})

  | Loc (l : loc)
  | Alloc (e : expr)
  | Store (e1 e2 : expr)
  | Load (e : expr)

  | TLam (e : expr)
  | TApp (e : expr)

  | TLLam (e : expr)
  | TLApp (e : expr)

  | Pack (e : expr)
  | Unpack (e1 : expr) (e2 : {bind expr})

  | Fold (e : expr)
  | Unfold (e : expr)
  .

Instance Ids_expr : Ids expr := ltac:(derive).
Instance Rename_expr : Rename expr := ltac:(derive).
Instance Subst_expr : Subst expr := ltac:(derive).

Inductive val :=
  | UnitV
  | BoolV (b : bool)
  | NatV (n : nat)
  | LamV (e : expr)
  | TLamV (e : expr)
  | TLLamV (e : expr)
  | PairV (l r: val)
  | InjLV (v: val)
  | InjRV (v: val)
  | LocV (l : loc)
  | FoldV (v : val)
  | PackV (v : val).

Fixpoint of_val (v : val) : expr :=
    match v with
    | UnitV => Unit
    | BoolV b => Bool b
    | NatV n => Nat n
    | LamV e => Lam e
    | TLamV e => TLam e
    | TLLamV e => TLLam e
    | PairV v1 v2 => Pair (of_val v1) (of_val v2)
    | InjLV v => InjL (of_val v)
    | InjRV v => InjR (of_val v)
    | LocV l => Loc l
    | FoldV v => Fold (of_val v)
    | PackV v => Pack (of_val v)
    end.

Notation "# v" := (of_val v) (at level 20).

Definition binop_eval (op : binop) (a b : nat) : val :=
    match op with
    | Add => NatV (a + b)
    | Sub => NatV (a - b)
    | Mult => NatV (a * b)
    | Eq => BoolV $ bool_decide (a = b)
    | Le => BoolV $ bool_decide (a ≤ b)
    | Lt => BoolV $ bool_decide (a < b)
    end.

Fixpoint to_val (e : expr) : option val :=
    match e with
    | Unit => Some UnitV
    | Bool b => Some $ BoolV b
    | Nat n => Some $ NatV n
    | Lam e => Some $ LamV e
    | TLam e => Some $ TLamV e
    | TLLam e => Some $ TLLamV e
    | Pair e1 e2 => v1 ← to_val e1; v2 ← to_val e2; Some $ PairV v1 v2
    | InjL e => InjLV <$> to_val e
    | InjR e => InjRV <$> to_val e
    | Loc l => Some $ LocV l
    | Fold e => v ← to_val e; Some (FoldV v)
    | Pack e => v ← to_val e; Some (PackV v)
    | _ => None
    end.

Inductive ectx_item :=
  | AppLCtx (e2 : expr)
  | AppRCtx (v1 : val)
  | LetInCtx (e2 : expr)
  | SeqCtx (e2 : expr)
  | TAppCtx
  | TLAppCtx
  | BinOpLCtx (op : binop) (e2 : expr)
  | BinOpRCtx (op : binop) (v1 : val)
  | IfCtx (e1 : {bind expr}) (e2 : {bind expr})
  | PairLCtx (e2 : expr)
  | PairRCtx (v1 : val)
  | InjLCtx | InjRCtx
  | Proj1Ctx | Proj2Ctx
  | CaseCtx (e1 : {bind expr}) (e2 : {bind expr})
  | AllocCtx | LoadCtx
  | StoreLCtx (e2 : expr)
  | StoreRCtx (v1 : val)
  | FoldCtx
  | UnfoldCtx
  | PackCtx
  | UnpackCtx (e : expr)
  .

Definition fill_item (Ki : ectx_item) (e : expr) : expr :=
    match Ki with
    | AppLCtx e2 => App e e2
    | AppRCtx v1 => App (# v1) e
    | LetInCtx e2 => LetIn e e2
    | SeqCtx e2 => Seq e e2
    | TAppCtx => TApp e
    | TLAppCtx => TLApp e
    | BinOpLCtx op e2 => BinOp op e e2
    | BinOpRCtx op v1 => BinOp op (# v1) e
    | IfCtx e1 e2 => If e e1 e2
    | PairLCtx e2 => Pair e e2
    | PairRCtx v1 => Pair (# v1) e
    | InjLCtx => InjL e | InjRCtx => InjR e
    | Proj1Ctx => Proj1 e | Proj2Ctx => Proj2 e
    | CaseCtx e1 e2 => Case e e1 e2
    | AllocCtx => Alloc e
    | LoadCtx => Load e
    | StoreLCtx e2 => Store e e2
    | StoreRCtx v1 => Store (# v1) e
    | FoldCtx => Fold e
    | UnfoldCtx => Unfold e
    | PackCtx => Pack e
    | UnpackCtx e' => Unpack e e'
    end.

Definition state : Type := gmap loc val.

Inductive head_step : expr → state → list Empty_set → expr → state → list expr → Prop :=

  | BetaS e1 e2 v2 σ :
      to_val e2 = Some v2 →
      head_step (App (Lam e1) e2) σ [] e1.[e2/] σ []

  | TBeta e σ :
      head_step (TApp (TLam e)) σ [] e σ []

  | LetInBetaS e1 e2 v2 σ :
      to_val e1 = Some v2 →
      head_step (LetIn e1 e2) σ [] e2.[e1/] σ []

  | SeqBetaS e1 e2 v2 σ :
      to_val e1 = Some v2 →
      head_step (Seq e1 e2) σ [] e2 σ []

  | LBeta e σ :
      head_step (TLApp (TLLam e)) σ [] e σ []

  | BinOpS op n1 n2 σ :
      head_step (BinOp op (Nat n1) (Nat n2)) σ [] (# (binop_eval op n1 n2)) σ []

  | IfFalseS e1 e2 σ :
      head_step (If (Bool false) e1 e2) σ [] e2 σ []
  | IfTrueS e1 e2 σ :
      head_step (If (Bool true) e1 e2) σ [] e1 σ []

  | Proj1S e1 e2 v1 v2 σ :
      to_val e1 = Some v1 →
      to_val e2 = Some v2 →
      head_step (Proj1 $ Pair e1 e2) σ [] (of_val v1) σ []
  | Proj2S e1 e2 v1 v2 σ :
      to_val e1 = Some v1 →
      to_val e2 = Some v2 →
      head_step (Proj2 $ Pair e1 e2) σ [] (of_val v2) σ []

  | CaseLS e0 e1 e2 v0 σ :
      to_val e0 = Some v0 →
      head_step (Case (InjL e0) e1 e2) σ [] (e1.[e0/]) σ []
  | CaseRS e0 e1 e2 v0 σ :
      to_val e0 = Some v0 →
      head_step (Case (InjR e0) e1 e2) σ [] (e2.[e0/]) σ []

  | AllocS e v l σ :
      to_val e = Some v →
      σ !! l = None →
      head_step (Alloc e) σ [] (Loc l) (<[l := v]>σ) []
  | StoreS e v l σ :
      to_val e = Some v →
      is_Some $ σ !! l →
      head_step (Store (Loc l) e) σ [] Unit (<[l := v]>σ) []
  | LoadS l v σ :
      σ !! l = Some v →
      head_step (Load $ Loc l) σ [] (of_val v) σ []

  | UnpackPackS e1 e2 v1 σ :
      to_val e1 = Some v1 →
      head_step (Unpack (Pack e1) e2) σ [] (e2.[e1/]) σ []

  | UnfoldFoldS e v σ :
      to_val e = Some v →
      head_step (Unfold (Fold e)) σ [] e σ []
  .

(* The Iris evaluation-context construction specialized to lambda_sec. *)
Definition fill (K : list ectx_item) (e : expr) : expr :=
  foldl (flip fill_item) e K.

Inductive prim_step (e1 : expr) (σ1 : state) (κ : list Empty_set)
    (e2 : expr) (σ2 : state) (efs : list expr) : Prop :=
| Ectx_step K e1' e2' :
    e1 = fill K e1' → e2 = fill K e2' →
    head_step e1' σ1 κ e2' σ2 efs →
    prim_step e1 σ1 κ e2 σ2 efs.

Notation pstep := (λ x1 x2, prim_step (fst x1) (snd x1) [] (fst x2) (snd x2) []).

End lambda_sec.

Export lambda_sec.

Definition is_atomic (e : expr) : Prop :=
  match e with
  | Alloc e => is_Some (to_val e)
  | Load e =>  is_Some (to_val e)
  | Store e1 e2 => is_Some (to_val e1) ∧ is_Some (to_val e2)
  | _ => False
  end.
