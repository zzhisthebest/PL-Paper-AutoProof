Set Implicit Arguments.

Require Import LibExtra SyntaxClasses.

Inductive avar : Set :=
  | avar_b : nat -> avar
  | avar_f : var -> avar.

Notation avars := (list avar).

Instance VarSubstVar : SubstVar var :=
  fun x y z => If z = x then y else z.

Instance VarSealable: Sealable var :=
  fun n x y => y.

Instance VarOpenable : Openable var :=
  fun n x a => a.

Instance VarFreeVar : FreeVar var := singleton (A:=var).

Instance VarAbstractSyntax :
  AbstractSyntax VarOpenable VarFreeVar VarSubstVar := {}.

Instance AvarOpenable : Openable avar :=
  fun n x a =>
    match a with
    | avar_b i => If n = i then avar_f x else avar_b i
    | avar_f y => avar_f y
    end.

Instance AvarFreeVar : FreeVar avar :=
  fun a =>
    match a with
    | avar_b i => \{}
    | avar_f x => \{x}
    end.

Instance AvarSubstVar : SubstVar avar :=
  fun (x: var) (y: var) (a: avar) =>
    match a with
    | avar_b i => avar_b i
    | avar_f z => (avar_f (If z = x then y else z))
    end.

Instance AvarAbstractSyntax :
  AbstractSyntax AvarOpenable AvarFreeVar AvarSubstVar := {}.

Instance AvarSealable : Sealable avar :=
  fun n x a =>
    match a with
    | avar_b i => If n <= i then avar_f x else avar_b i
    | avar_f y => avar_f y
    end.

Instance AvarDecideFv : DecideFv AvarAbstractSyntax :=
  fun x a =>
    match a with
    | avar_b i => false
    | avar_f y => (If x = y then true else false)
    end.

Instance AvarClosing : Closing AvarAbstractSyntax :=
  fun (n : nat) (x : var) (a : avar) =>
    match a with
    | avar_b i => avar_b i
    | avar_f y => (If y = x then avar_b n else avar_f y)
    end.

Section VarSubstVar.

Context `{AS: AbstractSyntax}.

Context {SF: SubstFresh AS}.

Context {FS: FvSubstCases AS}.

Context {SC: SubstCommut AS}.

Context {ASOC: SubstOpenCommut AS}.

Context {SI: SubstId AS}.

End VarSubstVar.

Inductive varkind: Set :=
| v_loc: varkind
| v_ref: varkind
| v_par: varkind
| v_self: varkind
| v_let: varkind
| v_recv: varkind
.

Inductive varkind_abstract: varkind -> Prop :=
| v_abstract_let: varkind_abstract v_let
| v_abstract_par: varkind_abstract v_par
| v_abstract_self: varkind_abstract v_self
| v_abstract_recv: varkind_abstract v_recv
.
