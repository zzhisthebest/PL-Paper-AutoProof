Require Export strictness.cbpv.syntax strictness.cbpv.typing.

From Coq Require Export PeanoNat.

From Coq Require Export Bool.

Require Import Coq.Program.Equality.

From Coq Require Import FunctionalExtensionality.

Require Import Psatz.

Inductive Clos : Kind ->  Type :=
| Absent : Clos ValFlag
| Unit : Clos ValFlag
| Thunk (mOuter : nat) mInner (γ' : attrs mOuter)  (ρ : fin mInner -> Clos ValFlag) (M : Comp mInner) : Clos ValFlag
| Pair (W1 W2 : Clos ValFlag) : Clos ValFlag
| Inl (W : Clos ValFlag) : Clos ValFlag
| Inr (W : Clos ValFlag) : Clos ValFlag
| Return (W : Clos ValFlag) : Clos CompFlag
| Closure (mOuter : nat) mInner (γ' : attrs mOuter) (ρ : fin mInner -> Clos ValFlag) (M : Comp (S mInner)) : Clos CompFlag.

Definition ClosValue := Clos ValFlag.

Definition ClosComp := Clos CompFlag.

Definition env n := fin n -> ClosValue.

Definition min_le : forall m n, min m n <= m := ltac:(lia).

Fixpoint down_clos {k} scope (C : Clos k) : Clos k :=
  match C with
  | Absent => Absent
  | Unit => Unit
  | Thunk n m γ' ρ M => Thunk (min n scope) m (down_env_until γ' (min n scope) (min_le n scope)) ρ M
  | Pair W1 W2 => Pair (down_clos scope W1) (down_clos scope W2)
  | Inl W => Inl (down_clos scope W)
  | Inr W => Inr (down_clos scope W)
  | Return W => Return (down_clos scope W)
  | Closure n m γ' ρ M => Closure (min n scope) m (down_env_until γ' (min n scope) (min_le n scope)) ρ M
  end.

Definition down_value := @down_clos ValFlag.

Definition down_comp := @down_clos CompFlag.

Notation "scope 'W↓' W" := (down_value scope W) (at level 85).

Notation "scope 'T↓' T" := (down_comp scope T) (at level 85).

Fixpoint well_scoped_clos {k} (C : Clos k) max_scope :=
  match C with
  | Absent => True
  | Unit => True
  | Thunk n m γ ρ M => n <= max_scope
  | Pair W1 W2 => well_scoped_clos W1 max_scope /\ well_scoped_clos W2 max_scope
  | Inl W => well_scoped_clos W max_scope
  | Inr W => well_scoped_clos W max_scope
  | Return W => well_scoped_clos W max_scope
  | Closure n _ _ ρ _  => n <= max_scope
end.

Definition well_scoped_value := @well_scoped_clos ValFlag.

Definition well_scoped_env {n} (ρ : env n) m := forall i, well_scoped_value (ρ i) m.

Definition well_scoped_comp := @well_scoped_clos CompFlag.

Inductive EvalVal {n} (γ : attrs n) (ρ : env n) : Val n -> ClosValue -> Prop :=
  | E_Var i W :
    W = ρ i ->
    γ = (lazyvector <- Strict @ i) ->
    W <> Absent ->

    EvalVal γ ρ (vVar i) W

  | E_Unit :
    γ = lazyvector ->

    EvalVal γ ρ vUnit Unit

  | E_Thunk M γ' :
    γ = lazyvector ->

    EvalVal γ ρ (vThunk M) (Thunk n n γ' ρ M)

  | E_VPair γ1 γ2 V1 V2 W1 W2 :
    EvalVal γ1 ρ V1 W1 ->
    EvalVal γ2 ρ V2 W2 ->
    γ = γ1 γ+ γ2 ->

    EvalVal γ ρ (vPair V1 V2) (Pair W1 W2)

  | E_Inl V W :
    EvalVal γ ρ V W ->

    EvalVal γ ρ (vInl V) (Inl W)

  | E_Inr V W :
    EvalVal γ ρ V W ->

    EvalVal γ ρ (vInr V) (Inr W)
.

Inductive EvalComp {n} (γ : attrs n) (ρ : env n) : Comp n -> ClosComp -> Prop :=
| E_Abs M :

  EvalComp γ ρ (cAbs M) (Closure n n γ ρ M)

| E_AppAbs n' m q γ1 γ2 γ' γUp H M M' V T T' W ρ':
  EvalComp γ1 ρ M (Closure n' m γ' ρ' M') ->
  EvalVal γ2 ρ V W ->
  γ' = down_env_until γUp n' H ->
  EvalComp (q .: γUp) ((n' W↓ W) .: ρ') M' T' ->
  γ = γ1 γ+ γ2 ->
  T = (n' T↓ T') ->

  EvalComp γ ρ (cApp M V) T

| E_Split q1 q2 γ1 γ2 V N W1 W2 T T' :
  EvalVal γ1 ρ V (Pair W1 W2) ->
  EvalComp (q1 .: (q2 .: γ2)) (W1 .: (W2 .: ρ)) N T' ->
  γ = γ1 γ+ γ2 ->
  T = (n T↓ T') ->

  EvalComp γ ρ (cSplit V N) T

| E_Ret V W :
  EvalVal γ ρ V W ->

  EvalComp γ ρ (cRet V) (Return W)

| E_LetRet γ1 γ2 q M N W T T' :
  EvalComp γ1 ρ M (Return W) ->
  EvalComp (q .: γ2) (W .: ρ) N T' ->
  γ = γ1 γ+ γ2 ->
  T = (n T↓ T') ->

  EvalComp γ ρ (cLet M N) T

| E_Force mInner mOuter (γ2'' : attrs n) γ1 (γ2 : attrs mOuter) γ2' V M T T' ρ' Hn HInner :
  EvalVal γ1 ρ V (Thunk mOuter mInner γ2 ρ' M) ->
  EvalComp γ2' ρ' M T' ->
  down_env_until γ2' mOuter HInner = γ2 ->
  down_env_until γ2'' mOuter Hn = γ2 ->
  γ = γ1 γ+ γ2'' ->
  T = (mOuter T↓ T') ->

  EvalComp γ ρ (cForce V) T

| E_Seq γ1 γ2 V N T :
  EvalVal γ1 ρ V Unit ->
  EvalComp γ2 ρ N T ->
  γ = γ1 γ+ γ2 ->

  EvalComp γ ρ (cSeq V N) T

| E_Casel γ1 γ2 q V M1 M2 W T T' :
  EvalVal γ1 ρ V (Inl W) ->
  EvalComp (q .: γ2) (W .: ρ) M1 T' ->
  γ = γ1 γ+ γ2 ->
  T = (n T↓ T') ->

  EvalComp γ ρ (cCase V M1 M2) T

| E_Caser γ1 γ2 q V M1 M2 W T T' :
  EvalVal γ1 ρ V (Inr W) ->
  EvalComp (q .: γ2) (W .: ρ) M2 T' ->
  γ = γ1 γ+ γ2 ->
  T = (n T↓ T') ->

  EvalComp γ ρ (cCase V M1 M2) T

| E_CSub M γ' B:
  EvalComp γ' ρ M B ->
  γ γ<= γ' ->

  EvalComp γ ρ (cSub M) B
.

Inductive eq_up_to_attrs : forall (k : Kind), Clos k -> Clos k -> Prop :=
  | Eq_Absent : eq_up_to_attrs ValFlag Absent Absent
  | Eq_Unit : eq_up_to_attrs ValFlag Unit Unit
  | Eq_Thunk n m γ γ' ρ ρ' M :
    (forall i, eq_up_to_attrs ValFlag (ρ i) (ρ' i)) ->
    eq_up_to_attrs ValFlag (Thunk n m γ ρ M) (Thunk n m γ' ρ' M)

  | Eq_Pair W1 W2 W1' W2' :
    eq_up_to_attrs ValFlag W1 W1' ->
    eq_up_to_attrs ValFlag W2 W2' ->
    eq_up_to_attrs ValFlag (Pair W1 W2) (Pair W1' W2')

  | Eq_Inl W W' :
    eq_up_to_attrs ValFlag W W' ->
    eq_up_to_attrs ValFlag (Inl W) (Inl W')

  | Eq_Inr W W' :
    eq_up_to_attrs ValFlag W W' ->
    eq_up_to_attrs ValFlag (Inr W) (Inr W')

  | Eq_Return W W' :
    eq_up_to_attrs ValFlag W W' ->
    eq_up_to_attrs CompFlag (Return W) (Return W')

  | Eq_Closure n m γ γ' ρ ρ' M :
    (forall i, eq_up_to_attrs ValFlag (ρ i) (ρ' i)) ->
    eq_up_to_attrs CompFlag (Closure n m γ ρ M) (Closure n m γ' ρ' M)
.

Arguments eq_up_to_attrs {k}.

Definition eq_env_up_to_attrs {n} (ρ1 ρ2 : env n) :=
  forall i, eq_up_to_attrs (ρ1 i) (ρ2 i).

Definition EvalValFail {n} (ρ : env n) V :=
  forall γ W ρ', eq_env_up_to_attrs ρ ρ' -> ~ EvalVal γ ρ' V W.

Definition EvalCompFail {n} (ρ : env n) M :=
  forall γ T ρ', eq_env_up_to_attrs ρ ρ' -> ~ EvalComp γ ρ' M T.
