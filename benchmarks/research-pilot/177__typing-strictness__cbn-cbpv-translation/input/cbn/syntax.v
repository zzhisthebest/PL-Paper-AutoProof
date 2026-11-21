Require Export strictness.autosubst2.fintype.

Require Export strictness.common.attributes.

Inductive CbnTy (n : nat) : Type :=
  | TUnit : CbnTy n
  | TProd (γ1 : attrs n) (T1 : CbnTy n) (γ2 : attrs n) (T2 : CbnTy n) : CbnTy n
  | TSum  (γ1 : attrs n) (T1 : CbnTy n) (γ2 : attrs n) (T2 : CbnTy n) : CbnTy n
  | TArrow (γInput : attrs n) (q : attr) (γ : attrs n) (T1 : CbnTy n) (T2 : CbnTy (S n)) : CbnTy n
.

Arguments TUnit {n}.

Arguments TProd {n}.

Arguments TSum {n}.

Arguments TArrow {n}.

Definition up_map {n m} (ξ : attrs n -> attrs m) : attrs (S n) -> attrs (S m) :=
  fun (γ : attrs (S n)) => fun (fn : fin (S m)) => match fn with
  | None => γ None
  | Some f => ξ (ren_env γ shift) f
  end.

Fixpoint map_cbnTy {n m} (ξ : attrs n -> attrs m) (T : CbnTy n) : CbnTy m :=
  match T with
  | TUnit => TUnit
  | TProd γ1 T1 γ2 T2 => TProd (ξ γ1) (map_cbnTy ξ T1) (ξ γ2) (map_cbnTy ξ T2)
  | TSum γ1 T1 γ2 T2 => TSum (ξ γ1) (map_cbnTy ξ T1)  (ξ γ2) (map_cbnTy ξ T2)
  | TArrow γInput q' γ T1 T2 => TArrow (ξ γInput) q' (ξ γ) (map_cbnTy ξ T1) (map_cbnTy (up_map ξ) T2)
  end.

Definition up_cbnTy {n} q (T : CbnTy n) := map_cbnTy (fun γ => q .: γ) T.

Infix "T↑" := (up_cbnTy) (at level 85).

Fixpoint ren_cbnTy {n m} (ξ : ren m n) (T : CbnTy n) : CbnTy m :=
  match T with
  | TUnit => TUnit
  | TProd γ1 T1 γ2 T2 => TProd (ren_env γ1 ξ) (ren_cbnTy ξ T1) (ren_env γ2 ξ) (ren_cbnTy ξ T2)
  | TSum γ1 T1 γ2 T2 => TSum (ren_env γ1 ξ) (ren_cbnTy ξ T1) (ren_env γ2 ξ) (ren_cbnTy ξ T2)
  | TArrow γInput q γ T1 T2 => TArrow (ren_env γInput ξ) q (ren_env γ ξ) (ren_cbnTy ξ T1) (ren_cbnTy (up_ren ξ) T2)
  end.

Definition down_cbnTy {n} (T : CbnTy (S n)) : CbnTy n := ren_cbnTy shift T.

Notation "'T↓' T" := (down_cbnTy T) (at level 85).

Inductive Term (n : nat) : Type :=
  | tVar (x : fin n) : Term n

  | tUnit : Term n

  | tLet (t1 : Term n) (t2: Term (S n)) : Term n

  | tPair (t1 : Term n) (t2: Term n) : Term n

  | tInl (t : Term n) : Term n
  | tInr (t : Term n) : Term n

  | tSeq (t1 : Term n) (t1 : Term n) : Term n

  | tAbs (t : Term (S n)) : Term n

  | tApp (t1 : Term n) (t2: Term n) : Term n

  | tSplit (t1 : Term n) (t2: Term (S (S (n)))) : Term n

  | tCase (t1 : Term n) (t2 : Term (S n)) (t3 : Term (S n)) : Term n

  | tSub (t : Term n) : Term n
.

Arguments tVar {n}.

Arguments tUnit {n}.

Arguments tPair {n}.

Arguments tLet {n}.

Arguments tInl {n}.

Arguments tInr {n}.

Arguments tSeq {n}.

Arguments tAbs {n}.

Arguments tApp {n}.

Arguments tSplit {n}.

Arguments tCase {n}.

Arguments tSub {n}.
