Require Export strictness.common.attributes.

Require Export strictness.autosubst2.fintype.

Require Import Psatz.

From Coq Require Export PeanoNat.

From Coq Require Export Bool.

From Coq Require Import FunctionalExtensionality.

Require Import Coq.Program.Equality.

Inductive Kind := ValFlag : Kind | CompFlag : Kind.

Inductive Ty (n : nat) : Kind -> Type :=
  | VUnit : Ty n ValFlag
  | VThunk (γ : attrs n) (B : Ty n CompFlag) : Ty n ValFlag
  | VProd (A1 : Ty n ValFlag) (A2 : Ty n ValFlag) : Ty n ValFlag
  | VSum (A1 : Ty n ValFlag ) (A2 : Ty n ValFlag) : Ty n ValFlag
  | CAbs (q : attr) (A : Ty n ValFlag) (B : Ty n CompFlag) : Ty n CompFlag
  | CF (A : Ty n ValFlag) : Ty n CompFlag
.

Definition ValTy n := Ty n ValFlag.

Definition CompTy n := Ty n CompFlag.

Arguments VUnit {n}.

Arguments VThunk {n}.

Arguments VProd {n}.

Arguments VSum {n}.

Arguments CF {n}.

Arguments CAbs {n}.

Fixpoint ren_ty {n m k} (ξ : fin m -> fin n) (T : Ty n k) : Ty m k :=
  match T with
  | VUnit => VUnit
  | VProd A1 A2 => VProd (ren_ty ξ A1) (ren_ty ξ A2)
  | VSum A1 A2 => VSum (ren_ty ξ A1) (ren_ty ξ A2)
  | VThunk γ B => VThunk (ren_env γ ξ) (ren_ty ξ B)
  | CF A => CF (ren_ty ξ A)
  | CAbs q A B => CAbs q (ren_ty ξ A) (ren_ty ξ B)
  end
.

Definition down_ty {n k} (T : Ty (S n) k) : Ty n k := ren_ty shift T.

Definition down_valTy {n} := @down_ty n ValFlag.

Definition down_compTy {n} := @down_ty n CompFlag.

Notation "'A↓' A" := (down_valTy A) (at level 85).

Notation "'B↓' B" := (down_compTy B) (at level 85).

Fixpoint map_Ty {n m k} (ξ : attrs n -> attrs m) (T : Ty n k) : Ty m k :=
  match T with
  | VUnit => VUnit
  | VThunk γ B => VThunk (ξ γ) (map_Ty ξ B)
  | VProd A1 A2 => VProd (map_Ty ξ A1) (map_Ty ξ A2)
  | VSum A1 A2 => VSum (map_Ty ξ A1) (map_Ty ξ A2)
  | CF A => CF (map_Ty ξ A)
  | CAbs q' A B => CAbs q' (map_Ty ξ A) (map_Ty ξ B)
  end
.

Definition up_Ty {n k} q (T : Ty n k) : Ty (S n) k := map_Ty (fun γ => q .: γ) T.

Definition up_valTy {n} := @up_Ty n ValFlag.

Definition up_compTy {n} := @up_Ty n CompFlag.

Infix "A↑" := (up_valTy) (at level 85).

Infix "B↑" := (up_compTy) (at level 85).

Fixpoint down_ty_until {n k} (A : Ty n k) m (H : m <= n) : Ty m k :=
  match A with
  | VUnit => VUnit
  | VProd A1 A2 => VProd (down_ty_until A1 m H) (down_ty_until A2 m H)
  | VSum A1 A2 => VSum (down_ty_until A1 m H) (down_ty_until A2 m H)
  | VThunk γ B => VThunk (down_env_until γ m H) (down_ty_until B m H)
  | CF A => CF (down_ty_until A m H)
  | CAbs q A B =>
    CAbs q (down_ty_until A m H) (down_ty_until B m H)
  end
.

Definition down_valTy_until {n} := @down_ty_until n ValFlag.

Definition down_compTy_until {n} := @down_ty_until n CompFlag.

Inductive Val (n : nat) : Type :=
  | vVar (x : fin n) : Val n


  | vUnit : Val n


  | vThunk (M : Comp n) : Val n


  | vPair (V1 :Val n) (V2: Val n) : Val n


  | vInl (V : Val n) : Val n
  | vInr (V : Val n) : Val n

 with Comp (n : nat) : Type :=

  | cRet (V : Val n) : Comp n

  | cLet (M : Comp n) (M' : Comp (S n)) : Comp n


  | cForce (V : Val n) : Comp n


  | cSeq (V : Val n) (M : Comp n) : Comp n


  | cAbs (M : Comp (S n)) : Comp n

  | cApp (M : Comp n) (V : Val n) : Comp n


  | cSplit (V : Val n) (M : Comp (S (S (n)))) : Comp n


  | cCase (V : Val n) (M1 : Comp (S n)) (M2 : Comp (S n)) : Comp n


  | cSub (V : Comp n) : Comp n
.

Arguments vVar {n}.

Arguments vUnit {n}.

Arguments vThunk {n}.

Arguments vPair {n}.

Arguments vInl {n}.

Arguments vInr {n}.

Arguments cRet {n}.

Arguments cLet {n}.

Arguments cForce {n}.

Arguments cSeq {n}.

Arguments cAbs {n}.

Arguments cApp {n}.

Arguments cSplit {n}.

Arguments cCase {n}.

Arguments cSub {n}.

Scheme Val_ind' := Induction for Val Sort Prop
    with Comp_ind' := Induction for Comp Sort Prop.

Combined Scheme ValComp_mutual from Val_ind', Comp_ind'.

Definition upRen_Val_Val { m n : nat } (ξ : fin m -> fin n) : fin (S m) -> fin (S n) :=
  up_ren ξ.

Fixpoint ren_Val { m n } (ξ : fin m -> fin n) (s : Val m) : Val n :=
    match s return Val n with
    | vVar s => vVar (ξ s)
    | vUnit => vUnit
    | vThunk s0 => vThunk (ren_Comp ξ s0)
    | vPair s0 s1 => vPair (ren_Val ξ s0) (ren_Val ξ s1)
    | vInl s0 => vInl (ren_Val ξ s0)
    | vInr s0 => vInr (ren_Val ξ s0)
    end
 with ren_Comp { m n } (ξ : fin m -> fin n) (s : Comp m) : Comp n :=
    match s return Comp n with
    | cAbs s1 => cAbs (ren_Comp (upRen_Val_Val ξ) s1)
    | cApp s0 s1 => cApp (ren_Comp ξ s0) (ren_Val ξ s1)
    | cForce s0 => cForce (ren_Val ξ s0)
    | cSplit s1 s2 => cSplit (ren_Val ξ s1)
      (ren_Comp (upRen_Val_Val (upRen_Val_Val ξ)) s2)
    | cRet s1 => cRet (ren_Val ξ s1)
    | cLet s1 s2 => cLet (ren_Comp ξ s1) (ren_Comp (upRen_Val_Val ξ) s2)
    | cSeq s0 s1 => cSeq (ren_Val ξ s0) (ren_Comp ξ s1)
    | cCase s1 s2 s3 => cCase (ren_Val ξ s1)
        (ren_Comp (upRen_Val_Val ξ) s2)
        (ren_Comp (upRen_Val_Val ξ) s3)
    | cSub s1 => cSub (ren_Comp ξ s1)
    end.
