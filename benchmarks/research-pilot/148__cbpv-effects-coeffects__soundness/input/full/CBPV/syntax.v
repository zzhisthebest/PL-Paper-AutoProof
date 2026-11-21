Require Export cbpv.common.effects cbpv.common.coeffects cbpv.autosubst2.fintype.

Section ValTyCompTy.

Inductive ValTy  : Type :=
  | VUnit : ValTy
  | VThunk : E   -> CompTy   -> ValTy
  | VPair : ValTy   -> ValTy   -> ValTy
  | VSum : ValTy   -> ValTy   -> ValTy
 with CompTy  : Type :=
  | CAbs : Q   -> ValTy   -> CompTy   -> CompTy
  | CF : Q   -> ValTy   -> CompTy
  | CPair : CompTy   -> CompTy   -> CompTy .

End ValTyCompTy.

Section ValComp.

Inductive Val (nVal : nat) : Type :=
  | var_Val : (fin) (nVal) -> Val (nVal)
  | vUnit : Val (nVal)
  | vThunk : Comp  (nVal) -> Val (nVal)
  | vPair : Val  (nVal) -> Val  (nVal) -> Val (nVal)
  | vInl : Val  (nVal) -> Val (nVal)
  | vInr : Val  (nVal) -> Val (nVal)
 with Comp (nVal : nat) : Type :=
  | cAbs : Q   -> Comp  ((S) nVal) -> Comp (nVal)
  | cApp : Comp  (nVal) -> Val  (nVal) -> Comp (nVal)
  | cForce : Val  (nVal) -> Comp (nVal)
  | cSplit : Q   -> Val  (nVal) -> Comp  ((S) ((S) nVal)) -> Comp (nVal)
  | cRet : Q   -> Val  (nVal) -> Comp (nVal)
  | cLet : Q   -> Comp  (nVal) -> Comp  ((S) nVal) -> Comp (nVal)
  | cPair : Comp  (nVal) -> Comp  (nVal) -> Comp (nVal)
  | cFst : Comp  (nVal) -> Comp (nVal)
  | cSnd : Comp  (nVal) -> Comp (nVal)
  | cSeq : Val  (nVal) -> Comp  (nVal) -> Comp (nVal)
  | cCase : Q   -> Val  (nVal) -> Comp  ((S) nVal) -> Comp  ((S) nVal) -> Comp (nVal)
  | cTick : Comp (nVal)
  | cLet0 : Comp  (nVal) -> Comp  ((S) nVal) -> Comp (nVal).

Definition upRen_Val_Val { m : nat } { n : nat } (xi : (fin) (m) -> (fin) (n)) : (fin) ((S) (m)) -> (fin) ((S) (n)) :=
  (up_ren) xi.

Fixpoint ren_Val { mVal : nat } { nVal : nat } (xiVal : (fin) (mVal) -> (fin) (nVal)) (s : Val (mVal)) : Val (nVal) :=
    match s return Val (nVal) with
    | var_Val (_) s => (var_Val (nVal)) (xiVal s)
    | vUnit (_)  => vUnit (nVal)
    | vThunk (_) s0 => vThunk (nVal) ((ren_Comp xiVal) s0)
    | vPair (_) s0 s1 => vPair (nVal) ((ren_Val xiVal) s0) ((ren_Val xiVal) s1)
    | vInl (_) s0 => vInl (nVal) ((ren_Val xiVal) s0)
    | vInr (_) s0 => vInr (nVal) ((ren_Val xiVal) s0)
    end
 with ren_Comp { mVal : nat } { nVal : nat } (xiVal : (fin) (mVal) -> (fin) (nVal)) (s : Comp (mVal)) : Comp (nVal) :=
    match s return Comp (nVal) with
    | cAbs (_) s0 s1 => cAbs (nVal) ((fun x => x) s0) ((ren_Comp (upRen_Val_Val xiVal)) s1)
    | cApp (_) s0 s1 => cApp (nVal) ((ren_Comp xiVal) s0) ((ren_Val xiVal) s1)
    | cForce (_) s0 => cForce (nVal) ((ren_Val xiVal) s0)
    | cSplit (_) s0 s1 s2 => cSplit (nVal) ((fun x => x) s0) ((ren_Val xiVal) s1) ((ren_Comp (upRen_Val_Val (upRen_Val_Val xiVal))) s2)
    | cRet (_) s0 s1 => cRet (nVal) ((fun x => x) s0) ((ren_Val xiVal) s1)
    | cLet (_) s0 s1 s2 => cLet (nVal) ((fun x => x) s0) ((ren_Comp xiVal) s1) ((ren_Comp (upRen_Val_Val xiVal)) s2)
    | cPair (_) s0 s1 => cPair (nVal) ((ren_Comp xiVal) s0) ((ren_Comp xiVal) s1)
    | cFst (_) s0 => cFst (nVal) ((ren_Comp xiVal) s0)
    | cSnd (_) s0 => cSnd (nVal) ((ren_Comp xiVal) s0)
    | cSeq (_) s0 s1 => cSeq (nVal) ((ren_Val xiVal) s0) ((ren_Comp xiVal) s1)
    | cCase (_) s0 s1 s2 s3 => cCase (nVal) ((fun x => x) s0) ((ren_Val xiVal) s1) ((ren_Comp (upRen_Val_Val xiVal)) s2) ((ren_Comp (upRen_Val_Val xiVal)) s3)
    | cTick (_)  => cTick (nVal)
    | cLet0 (_) s0 s1 => cLet0 (nVal) ((ren_Comp xiVal) s0) ((ren_Comp (upRen_Val_Val xiVal)) s1)
    end.

Definition up_Val_Val { m : nat } { nVal : nat } (sigma : (fin) (m) -> Val (nVal)) : (fin) ((S) (m)) -> Val ((S) nVal) :=
  (scons) ((var_Val ((S) nVal)) (var_zero)) ((funcomp) (ren_Val (shift)) sigma).

Fixpoint subst_Val { mVal : nat } { nVal : nat } (sigmaVal : (fin) (mVal) -> Val (nVal)) (s : Val (mVal)) : Val (nVal) :=
    match s return Val (nVal) with
    | var_Val (_) s => sigmaVal s
    | vUnit (_)  => vUnit (nVal)
    | vThunk (_) s0 => vThunk (nVal) ((subst_Comp sigmaVal) s0)
    | vPair (_) s0 s1 => vPair (nVal) ((subst_Val sigmaVal) s0) ((subst_Val sigmaVal) s1)
    | vInl (_) s0 => vInl (nVal) ((subst_Val sigmaVal) s0)
    | vInr (_) s0 => vInr (nVal) ((subst_Val sigmaVal) s0)
    end
 with subst_Comp { mVal : nat } { nVal : nat } (sigmaVal : (fin) (mVal) -> Val (nVal)) (s : Comp (mVal)) : Comp (nVal) :=
    match s return Comp (nVal) with
    | cAbs (_) s0 s1 => cAbs (nVal) ((fun x => x) s0) ((subst_Comp (up_Val_Val sigmaVal)) s1)
    | cApp (_) s0 s1 => cApp (nVal) ((subst_Comp sigmaVal) s0) ((subst_Val sigmaVal) s1)
    | cForce (_) s0 => cForce (nVal) ((subst_Val sigmaVal) s0)
    | cSplit (_) s0 s1 s2 => cSplit (nVal) ((fun x => x) s0) ((subst_Val sigmaVal) s1) ((subst_Comp (up_Val_Val (up_Val_Val sigmaVal))) s2)
    | cRet (_) s0 s1 => cRet (nVal) ((fun x => x) s0) ((subst_Val sigmaVal) s1)
    | cLet (_) s0 s1 s2 => cLet (nVal) ((fun x => x) s0) ((subst_Comp sigmaVal) s1) ((subst_Comp (up_Val_Val sigmaVal)) s2)
    | cPair (_) s0 s1 => cPair (nVal) ((subst_Comp sigmaVal) s0) ((subst_Comp sigmaVal) s1)
    | cFst (_) s0 => cFst (nVal) ((subst_Comp sigmaVal) s0)
    | cSnd (_) s0 => cSnd (nVal) ((subst_Comp sigmaVal) s0)
    | cSeq (_) s0 s1 => cSeq (nVal) ((subst_Val sigmaVal) s0) ((subst_Comp sigmaVal) s1)
    | cCase (_) s0 s1 s2 s3 => cCase (nVal) ((fun x => x) s0) ((subst_Val sigmaVal) s1) ((subst_Comp (up_Val_Val sigmaVal)) s2) ((subst_Comp (up_Val_Val sigmaVal)) s3)
    | cTick (_)  => cTick (nVal)
    | cLet0 (_) s0 s1 => cLet0 (nVal) ((subst_Comp sigmaVal) s0) ((subst_Comp (up_Val_Val sigmaVal)) s1)
    end.

End ValComp.

Arguments var_Val {nVal}.

Arguments vUnit {nVal}.

Arguments vThunk {nVal}.

Arguments vPair {nVal}.

Arguments vInl {nVal}.

Arguments vInr {nVal}.

Arguments cAbs {nVal}.

Arguments cApp {nVal}.

Arguments cForce {nVal}.

Arguments cSplit {nVal}.

Arguments cRet {nVal}.

Arguments cLet {nVal}.

Arguments cPair {nVal}.

Arguments cFst {nVal}.

Arguments cSnd {nVal}.

Arguments cSeq {nVal}.

Arguments cCase {nVal}.

Arguments cTick {nVal}.

Arguments cLet0 {nVal}.

Global Instance Subst_Val { mVal : nat } { nVal : nat } : Subst1 ((fin) (mVal) -> Val (nVal)) (Val (mVal)) (Val (nVal)) := @subst_Val (mVal) (nVal) .

Global Instance Subst_Comp { mVal : nat } { nVal : nat } : Subst1 ((fin) (mVal) -> Val (nVal)) (Comp (mVal)) (Comp (nVal)) := @subst_Comp (mVal) (nVal) .

Global Instance Ren_Val { mVal : nat } { nVal : nat } : Ren1 ((fin) (mVal) -> (fin) (nVal)) (Val (mVal)) (Val (nVal)) := @ren_Val (mVal) (nVal) .

Global Instance Ren_Comp { mVal : nat } { nVal : nat } : Ren1 ((fin) (mVal) -> (fin) (nVal)) (Comp (mVal)) (Comp (nVal)) := @ren_Comp (mVal) (nVal) .

Global Instance VarInstance_Val { mVal : nat } : Var ((fin) (mVal)) (Val (mVal)) := @var_Val (mVal) .

Notation "x '__Val'" := (var_Val x) (at level 5, format "x __Val") : subst_scope.

Notation "x '__Val'" := (@ids (_) (_) VarInstance_Val x) (at level 5, only printing, format "x __Val") : subst_scope.

Notation "'var'" := (var_Val) (only printing, at level 1) : subst_scope.

Class Up_Val X Y := up_Val : X -> Y.

Notation "↑__Val" := (up_Val) (only printing) : subst_scope.

Notation "↑__Val" := (up_Val_Val) (only printing) : subst_scope.

Global Instance Up_Val_Val { m : nat } { nVal : nat } : Up_Val (_) (_) := @up_Val_Val (m) (nVal) .

Notation "s [ sigmaVal ]" := (subst_Val sigmaVal s) (at level 7, left associativity, only printing) : subst_scope.

Notation "[ sigmaVal ]" := (subst_Val sigmaVal) (at level 1, left associativity, only printing) : fscope.

Notation "s ⟨ xiVal ⟩" := (ren_Val xiVal s) (at level 7, left associativity, only printing) : subst_scope.

Notation "⟨ xiVal ⟩" := (ren_Val xiVal) (at level 1, left associativity, only printing) : fscope.

Notation "s [ sigmaVal ]" := (subst_Comp sigmaVal s) (at level 7, left associativity, only printing) : subst_scope.

Notation "[ sigmaVal ]" := (subst_Comp sigmaVal) (at level 1, left associativity, only printing) : fscope.

Notation "s ⟨ xiVal ⟩" := (ren_Comp xiVal s) (at level 7, left associativity, only printing) : subst_scope.

Notation "⟨ xiVal ⟩" := (ren_Comp xiVal) (at level 1, left associativity, only printing) : fscope.
