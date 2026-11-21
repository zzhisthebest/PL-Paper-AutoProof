From Stdlib Require Export Strings.String FunctionalExtensionality.
From stdpp Require Export gmap fin.

Open Scope string_scope.

(* Expressions and values *)
(* ---------------------- *)

Inductive expr :=
  | Val : val -> expr
  | Var : string -> expr
  | Fun : string -> expr -> expr
  | App : expr -> expr -> expr
  | Unit : expr
  | Pair : expr -> expr -> expr
  | LetPair : expr -> expr -> expr
  | Sum : nat -> expr -> expr
  | MatchSum n : expr -> (fin n -> expr) -> expr
  | Fork : expr -> expr
with val :=
  | FunV : string -> expr -> val
  | UnitV : val
  | PairV : val -> val -> val
  | SumV : nat -> val -> val
  | BarrierV : nat -> val.


(* Type system *)
(* ----------- *)

Inductive linearity := Lin | Unr.

CoInductive type :=
  | FunT : linearity -> type -> type -> type
  | UnitT : type
  | PairT : type -> type -> type
  | SumT n : (fin n -> type) -> type.

CoInductive unr : type -> Prop :=
  | Fun_unr t1 t2 : unr (FunT Unr t1 t2)
  | Unit_unr : unr UnitT
  | Pair_unr t1 t2 : unr t1 -> unr t2 -> unr (PairT t1 t2)
  | Sum_unr n ts : (∀ i, unr (ts i)) -> unr (SumT n ts).

(* We define linear environment splitting here.
   On paper this is implicit in Γ1,Γ2 ⊢ e : A.
   In Coq we have to explicitly say env_split Γ Γ1 Γ2, and typed Γ e A. *)
Definition env := gmap string type.

Definition env_unr (Γ : env) :=
  ∀ x t, Γ !! x = Some t -> unr t.

Definition disj (Γ1 Γ2 : env) :=
  ∀ i t1 t2, Γ1 !! i = Some t1 -> Γ2 !! i = Some t2 -> t1 = t2 ∧ unr t1.

Definition env_split (Γ : env) (Γ1 : env) (Γ2 : env) :=
  Γ = Γ1 ∪ Γ2 ∧ disj Γ1 Γ2.

Definition env_bind (Γ' : env) (x : string) (t : type) (Γ : env) :=
  Γ' = <[ x := t ]> Γ ∧ ∀ t', Γ !! x = Some t' -> unr t'.

Definition env_var (Γ : env) (x : string) (t : type) :=
  ∃ Γ', Γ = <[ x := t ]> Γ' ∧ env_unr Γ'.


Inductive typed : env -> expr -> type -> Prop :=
  | Var_typed Γ x t :
    env_var Γ x t ->
    typed Γ (Var x) t
  | Fun_typed Γ Γ' x e t1 t2 l :
    env_bind Γ' x t1 Γ ->
    (l = Unr -> env_unr Γ) ->
    typed Γ' e t2 ->
    typed Γ (Fun x e) (FunT l t1 t2)
  | App_typed Γ Γ1 Γ2 e1 e2 t1 t2 l :
    env_split Γ Γ1 Γ2 ->
    typed Γ1 e1 (FunT l t1 t2) ->
    typed Γ2 e2 t1 ->
    typed Γ (App e1 e2) t2
  | Unit_typed Γ :
    env_unr Γ ->
    typed Γ Unit UnitT
  | Pair_typed Γ Γ1 Γ2 e1 e2 t1 t2 :
    env_split Γ Γ1 Γ2 ->
    typed Γ1 e1 t1 ->
    typed Γ2 e2 t2 ->
    typed Γ (Pair e1 e2) (PairT t1 t2)
  | LetPair_typed Γ Γ1 Γ2 e1 e2 t1 t2 t :
    env_split Γ Γ1 Γ2 ->
    typed Γ1 e1 (PairT t1 t2) ->
    typed Γ2 e2 (FunT Lin t1 (FunT Lin t2 t)) ->
    typed Γ (LetPair e1 e2) t
  | Sum_typed Γ n (ts : fin n -> type) i e :
    typed Γ e (ts i) ->
    typed Γ (Sum i e) (SumT n ts)
  | MatchSumN_typed n Γ Γ1 Γ2 t (ts : fin n -> type) es e :
    env_split Γ Γ1 Γ2 ->
    (n = 0 -> env_unr Γ2) ->
    typed Γ1 e (SumT n ts) ->
    (∀ i, typed Γ2 (es i) (FunT Lin (ts i) t)) ->
    typed Γ (MatchSum n e es) t
  | Fork_typed Γ e t1 t2 :
    typed Γ e (FunT Lin (FunT Lin t2 t1) UnitT) ->
    typed Γ (Fork e) (FunT Lin t1 t2).
