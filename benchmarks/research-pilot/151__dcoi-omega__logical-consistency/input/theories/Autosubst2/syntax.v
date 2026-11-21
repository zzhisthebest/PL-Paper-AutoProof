Require Export Lattice.All.

Require Export unscoped.

Module Type syntax_sig
  (Export lattice : Lattice).

Section tm.

Inductive tm  : Type :=
  | var_tm : ( fin ) -> tm
  | tAbs : ( T   ) -> ( tm   ) -> tm
  | tApp : ( tm   ) -> ( T   ) -> ( tm   ) -> tm
  | tPi : ( T   ) -> ( tm   ) -> ( tm   ) -> tm
  | tUniv : ( nat   ) -> tm
  | tVoid : tm
  | tAbsurd : ( tm   ) -> tm
  | tEq : ( T   ) -> ( tm   ) -> ( tm   ) -> tm
  | tJ : ( T   ) -> ( tm   ) -> ( tm   ) -> tm
  | tRefl : tm
  | tSig : ( T   ) -> ( tm   ) -> ( tm   ) -> tm
  | tPack : ( T   ) -> ( tm   ) -> ( tm   ) -> tm
  | tLet : ( T   ) -> ( T   ) -> ( tm   ) -> ( tm   ) -> tm
  | tZero : tm
  | tSuc : ( tm   ) -> tm
  | tInd : ( T   ) -> ( tm   ) -> ( tm   ) -> ( tm   ) -> tm
  | tNat : tm
  | tTT : tm
  | tSeq : ( T   ) -> ( tm   ) -> ( tm   ) -> tm
  | tUnit : tm .

Definition upRen_tm_tm   (xi : ( fin ) -> fin) : ( fin ) -> fin :=
  (up_ren) xi.

Fixpoint ren_tm   (xitm : ( fin ) -> fin) (s : tm ) : tm  :=
    match s return tm  with
    | var_tm  s => (var_tm ) (xitm s)
    | tAbs  s0 s1 => tAbs  ((fun x => x) s0) ((ren_tm (upRen_tm_tm xitm)) s1)
    | tApp  s0 s1 s2 => tApp  ((ren_tm xitm) s0) ((fun x => x) s1) ((ren_tm xitm) s2)
    | tPi  s0 s1 s2 => tPi  ((fun x => x) s0) ((ren_tm xitm) s1) ((ren_tm (upRen_tm_tm xitm)) s2)
    | tUniv  s0 => tUniv  ((fun x => x) s0)
    | tVoid   => tVoid
    | tAbsurd  s0 => tAbsurd  ((ren_tm xitm) s0)
    | tEq  s0 s1 s2 => tEq  ((fun x => x) s0) ((ren_tm xitm) s1) ((ren_tm xitm) s2)
    | tJ  s0 s1 s2 => tJ  ((fun x => x) s0) ((ren_tm xitm) s1) ((ren_tm xitm) s2)
    | tRefl   => tRefl
    | tSig  s0 s1 s2 => tSig  ((fun x => x) s0) ((ren_tm xitm) s1) ((ren_tm (upRen_tm_tm xitm)) s2)
    | tPack  s0 s1 s2 => tPack  ((fun x => x) s0) ((ren_tm xitm) s1) ((ren_tm xitm) s2)
    | tLet  s0 s1 s2 s3 => tLet  ((fun x => x) s0) ((fun x => x) s1) ((ren_tm xitm) s2) ((ren_tm (upRen_tm_tm (upRen_tm_tm xitm))) s3)
    | tZero   => tZero
    | tSuc  s0 => tSuc  ((ren_tm xitm) s0)
    | tInd  s0 s1 s2 s3 => tInd  ((fun x => x) s0) ((ren_tm xitm) s1) ((ren_tm (upRen_tm_tm (upRen_tm_tm xitm))) s2) ((ren_tm xitm) s3)
    | tNat   => tNat
    | tTT   => tTT
    | tSeq  s0 s1 s2 => tSeq  ((fun x => x) s0) ((ren_tm xitm) s1) ((ren_tm xitm) s2)
    | tUnit   => tUnit
    end.

Definition up_tm_tm   (sigma : ( fin ) -> tm ) : ( fin ) -> tm  :=
  (scons) ((var_tm ) (var_zero)) ((funcomp) (ren_tm (shift)) sigma).

Fixpoint subst_tm   (sigmatm : ( fin ) -> tm ) (s : tm ) : tm  :=
    match s return tm  with
    | var_tm  s => sigmatm s
    | tAbs  s0 s1 => tAbs  ((fun x => x) s0) ((subst_tm (up_tm_tm sigmatm)) s1)
    | tApp  s0 s1 s2 => tApp  ((subst_tm sigmatm) s0) ((fun x => x) s1) ((subst_tm sigmatm) s2)
    | tPi  s0 s1 s2 => tPi  ((fun x => x) s0) ((subst_tm sigmatm) s1) ((subst_tm (up_tm_tm sigmatm)) s2)
    | tUniv  s0 => tUniv  ((fun x => x) s0)
    | tVoid   => tVoid
    | tAbsurd  s0 => tAbsurd  ((subst_tm sigmatm) s0)
    | tEq  s0 s1 s2 => tEq  ((fun x => x) s0) ((subst_tm sigmatm) s1) ((subst_tm sigmatm) s2)
    | tJ  s0 s1 s2 => tJ  ((fun x => x) s0) ((subst_tm sigmatm) s1) ((subst_tm sigmatm) s2)
    | tRefl   => tRefl
    | tSig  s0 s1 s2 => tSig  ((fun x => x) s0) ((subst_tm sigmatm) s1) ((subst_tm (up_tm_tm sigmatm)) s2)
    | tPack  s0 s1 s2 => tPack  ((fun x => x) s0) ((subst_tm sigmatm) s1) ((subst_tm sigmatm) s2)
    | tLet  s0 s1 s2 s3 => tLet  ((fun x => x) s0) ((fun x => x) s1) ((subst_tm sigmatm) s2) ((subst_tm (up_tm_tm (up_tm_tm sigmatm))) s3)
    | tZero   => tZero
    | tSuc  s0 => tSuc  ((subst_tm sigmatm) s0)
    | tInd  s0 s1 s2 s3 => tInd  ((fun x => x) s0) ((subst_tm sigmatm) s1) ((subst_tm (up_tm_tm (up_tm_tm sigmatm))) s2) ((subst_tm sigmatm) s3)
    | tNat   => tNat
    | tTT   => tTT
    | tSeq  s0 s1 s2 => tSeq  ((fun x => x) s0) ((subst_tm sigmatm) s1) ((subst_tm sigmatm) s2)
    | tUnit   => tUnit
    end.

End tm.

Global Instance Subst_tm   : Subst1 (( fin ) -> tm ) (tm ) (tm ) := @subst_tm   .

Global Instance Ren_tm   : Ren1 (( fin ) -> fin) (tm ) (tm ) := @ren_tm   .

Global Instance VarInstance_tm  : Var (fin) (tm ) := @var_tm  .

Notation "x '__tm'" := (var_tm x) (at level 5, format "x __tm") : subst_scope.

Notation "x '__tm'" := (@ids (_) (_) VarInstance_tm x) (at level 5, only printing, format "x __tm") : subst_scope.

Notation "'var'" := (var_tm) (only printing, at level 1) : subst_scope.

Class Up_tm X Y := up_tm : ( X ) -> Y.

Notation "↑__tm" := (up_tm) (only printing) : subst_scope.

Notation "↑__tm" := (up_tm_tm) (only printing) : subst_scope.

Global Instance Up_tm_tm   : Up_tm (_) (_) := @up_tm_tm   .

Notation "s [ sigmatm ]" := (subst_tm sigmatm s) (at level 7, left associativity, only printing) : subst_scope.

Notation "[ sigmatm ]" := (subst_tm sigmatm) (at level 1, left associativity, only printing) : fscope.

Notation "s ⟨ xitm ⟩" := (ren_tm xitm s) (at level 7, left associativity, only printing) : subst_scope.

Notation "⟨ xitm ⟩" := (ren_tm xitm) (at level 1, left associativity, only printing) : fscope.

Notation "s [ sigmatm ]" := (subst_tm sigmatm s) (at level 7, left associativity) : subst_scope.

Notation "s ⟨ xitm ⟩" := (ren_tm xitm s) (at level 7, left associativity) : subst_scope.

Global Open Scope subst_scope.

End syntax_sig.
