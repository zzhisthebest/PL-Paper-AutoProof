Require Export cbpv.common.effects cbpv.common.coeffects cbpv.autosubst2.fintype.

Section Tm.

Inductive Tm (nTm : nat) : Type :=
  | var_Tm : (fin) (nTm) -> Tm (nTm)
  | abs : Q   -> Tm  ((S) nTm) -> Tm (nTm)
  | app : Q   -> Tm  (nTm) -> Tm  (nTm) -> Tm (nTm)
  | unit : Tm (nTm)
  | seq : Tm  (nTm) -> Tm  (nTm) -> Tm (nTm)
  | pair : Tm  (nTm) -> Tm  (nTm) -> Tm (nTm)
  | split : Q   -> Tm  (nTm) -> Tm  ((S) ((S) nTm)) -> Tm (nTm)
  | inl : Tm  (nTm) -> Tm (nTm)
  | inr : Tm  (nTm) -> Tm (nTm)
  | case : Q   -> Tm  (nTm) -> Tm  ((S) nTm) -> Tm  ((S) nTm) -> Tm (nTm)
  | box : Q   -> Tm  (nTm) -> Tm (nTm)
  | unbox : Q   -> Tm  (nTm) -> Tm  ((S) nTm) -> Tm (nTm)
  | ret : Tm  (nTm) -> Tm (nTm)
  | bind : Q   -> Tm  (nTm) -> Tm  ((S) nTm) -> Tm (nTm)
  | coerce : Tm  (nTm) -> Tm (nTm)
  | tickT : Tm (nTm).

Definition upRen_Tm_Tm { m : nat } { n : nat } (xi : (fin) (m) -> (fin) (n)) : (fin) ((S) (m)) -> (fin) ((S) (n)) :=
  (up_ren) xi.

Fixpoint ren_Tm { mTm : nat } { nTm : nat } (xiTm : (fin) (mTm) -> (fin) (nTm)) (s : Tm (mTm)) : Tm (nTm) :=
    match s return Tm (nTm) with
    | var_Tm (_) s => (var_Tm (nTm)) (xiTm s)
    | abs (_) s0 s1 => abs (nTm) ((fun x => x) s0) ((ren_Tm (upRen_Tm_Tm xiTm)) s1)
    | app (_) s0 s1 s2 => app (nTm) ((fun x => x) s0) ((ren_Tm xiTm) s1) ((ren_Tm xiTm) s2)
    | unit (_)  => unit (nTm)
    | seq (_) s0 s1 => seq (nTm) ((ren_Tm xiTm) s0) ((ren_Tm xiTm) s1)
    | pair (_) s0 s1 => pair (nTm) ((ren_Tm xiTm) s0) ((ren_Tm xiTm) s1)
    | split (_) s0 s1 s2 => split (nTm) ((fun x => x) s0) ((ren_Tm xiTm) s1) ((ren_Tm (upRen_Tm_Tm (upRen_Tm_Tm xiTm))) s2)
    | inl (_) s0 => inl (nTm) ((ren_Tm xiTm) s0)
    | inr (_) s0 => inr (nTm) ((ren_Tm xiTm) s0)
    | case (_) s0 s1 s2 s3 => case (nTm) ((fun x => x) s0) ((ren_Tm xiTm) s1) ((ren_Tm (upRen_Tm_Tm xiTm)) s2) ((ren_Tm (upRen_Tm_Tm xiTm)) s3)
    | box (_) s0 s1 => box (nTm) ((fun x => x) s0) ((ren_Tm xiTm) s1)
    | unbox (_) s0 s1 s2 => unbox (nTm) ((fun x => x) s0) ((ren_Tm xiTm) s1) ((ren_Tm (upRen_Tm_Tm xiTm)) s2)
    | ret (_) s0 => ret (nTm) ((ren_Tm xiTm) s0)
    | bind (_) s0 s1 s2 => bind (nTm) ((fun x => x) s0) ((ren_Tm xiTm) s1) ((ren_Tm (upRen_Tm_Tm xiTm)) s2)
    | coerce (_) s0 => coerce (nTm) ((ren_Tm xiTm) s0)
    | tickT (_)  => tickT (nTm)
    end.

Definition up_Tm_Tm { m : nat } { nTm : nat } (sigma : (fin) (m) -> Tm (nTm)) : (fin) ((S) (m)) -> Tm ((S) nTm) :=
  (scons) ((var_Tm ((S) nTm)) (var_zero)) ((funcomp) (ren_Tm (shift)) sigma).

Fixpoint subst_Tm { mTm : nat } { nTm : nat } (sigmaTm : (fin) (mTm) -> Tm (nTm)) (s : Tm (mTm)) : Tm (nTm) :=
    match s return Tm (nTm) with
    | var_Tm (_) s => sigmaTm s
    | abs (_) s0 s1 => abs (nTm) ((fun x => x) s0) ((subst_Tm (up_Tm_Tm sigmaTm)) s1)
    | app (_) s0 s1 s2 => app (nTm) ((fun x => x) s0) ((subst_Tm sigmaTm) s1) ((subst_Tm sigmaTm) s2)
    | unit (_)  => unit (nTm)
    | seq (_) s0 s1 => seq (nTm) ((subst_Tm sigmaTm) s0) ((subst_Tm sigmaTm) s1)
    | pair (_) s0 s1 => pair (nTm) ((subst_Tm sigmaTm) s0) ((subst_Tm sigmaTm) s1)
    | split (_) s0 s1 s2 => split (nTm) ((fun x => x) s0) ((subst_Tm sigmaTm) s1) ((subst_Tm (up_Tm_Tm (up_Tm_Tm sigmaTm))) s2)
    | inl (_) s0 => inl (nTm) ((subst_Tm sigmaTm) s0)
    | inr (_) s0 => inr (nTm) ((subst_Tm sigmaTm) s0)
    | case (_) s0 s1 s2 s3 => case (nTm) ((fun x => x) s0) ((subst_Tm sigmaTm) s1) ((subst_Tm (up_Tm_Tm sigmaTm)) s2) ((subst_Tm (up_Tm_Tm sigmaTm)) s3)
    | box (_) s0 s1 => box (nTm) ((fun x => x) s0) ((subst_Tm sigmaTm) s1)
    | unbox (_) s0 s1 s2 => unbox (nTm) ((fun x => x) s0) ((subst_Tm sigmaTm) s1) ((subst_Tm (up_Tm_Tm sigmaTm)) s2)
    | ret (_) s0 => ret (nTm) ((subst_Tm sigmaTm) s0)
    | bind (_) s0 s1 s2 => bind (nTm) ((fun x => x) s0) ((subst_Tm sigmaTm) s1) ((subst_Tm (up_Tm_Tm sigmaTm)) s2)
    | coerce (_) s0 => coerce (nTm) ((subst_Tm sigmaTm) s0)
    | tickT (_)  => tickT (nTm)
    end.

End Tm.

Section Ty.

Inductive Ty  : Type :=
  | Unit : Ty
  | Pair : Ty   -> Ty   -> Ty
  | Sum : Ty   -> Ty   -> Ty
  | Abs : Q   -> Ty   -> Ty   -> Ty
  | Box : Q   -> Ty   -> Ty
  | Mon : E   -> Ty   -> Ty .

End Ty.

Arguments var_Tm {nTm}.

Arguments abs {nTm}.

Arguments app {nTm}.

Arguments unit {nTm}.

Arguments seq {nTm}.

Arguments pair {nTm}.

Arguments split {nTm}.

Arguments inl {nTm}.

Arguments inr {nTm}.

Arguments case {nTm}.

Arguments box {nTm}.

Arguments unbox {nTm}.

Arguments ret {nTm}.

Arguments bind {nTm}.

Arguments coerce {nTm}.

Arguments tickT {nTm}.

Global Instance Subst_Tm { mTm : nat } { nTm : nat } : Subst1 ((fin) (mTm) -> Tm (nTm)) (Tm (mTm)) (Tm (nTm)) := @subst_Tm (mTm) (nTm) .

Global Instance Ren_Tm { mTm : nat } { nTm : nat } : Ren1 ((fin) (mTm) -> (fin) (nTm)) (Tm (mTm)) (Tm (nTm)) := @ren_Tm (mTm) (nTm) .

Global Instance VarInstance_Tm { mTm : nat } : Var ((fin) (mTm)) (Tm (mTm)) := @var_Tm (mTm) .

Notation "x '__Tm'" := (var_Tm x) (at level 5, format "x __Tm") : subst_scope.

Notation "x '__Tm'" := (@ids (_) (_) VarInstance_Tm x) (at level 5, only printing, format "x __Tm") : subst_scope.

Notation "'var'" := (var_Tm) (only printing, at level 1) : subst_scope.

Class Up_Tm X Y := up_Tm : X -> Y.

Notation "↑__Tm" := (up_Tm) (only printing) : subst_scope.

Notation "↑__Tm" := (up_Tm_Tm) (only printing) : subst_scope.

Global Instance Up_Tm_Tm { m : nat } { nTm : nat } : Up_Tm (_) (_) := @up_Tm_Tm (m) (nTm) .

Notation "s [ sigmaTm ]" := (subst_Tm sigmaTm s) (at level 7, left associativity, only printing) : subst_scope.

Notation "[ sigmaTm ]" := (subst_Tm sigmaTm) (at level 1, left associativity, only printing) : fscope.

Notation "s ⟨ xiTm ⟩" := (ren_Tm xiTm s) (at level 7, left associativity, only printing) : subst_scope.

Notation "⟨ xiTm ⟩" := (ren_Tm xiTm) (at level 1, left associativity, only printing) : fscope.
