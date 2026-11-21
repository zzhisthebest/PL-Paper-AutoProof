Set Implicit Arguments.

Require Import LibExtra SyntaxClasses.

Inductive avar : Set :=
  | avar_b : nat -> avar
  | avar_f : var -> avar.

Notation avars := (list avar).

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

Inductive vars_of_avars : list var -> list avar -> Prop :=
| vars_of_avars_nil : vars_of_avars nil nil
| vars_of_avars_cons : forall x vs avs,
    vars_of_avars vs avs ->
    vars_of_avars (cons x vs) (cons (avar_f x) avs).

Require Import TransformCollect.

Instance AvarsCollect : Collect AvarAbstractSyntax ListAbstractSyntax :=
  fun {C} df f comb => List.fold_right (fun a acc => comb (f a) acc) df.

Instance AvarsTransform : Transform AvarAbstractSyntax ListAbstractSyntax :=
  fun f a n => List.map (fun b => (f b n)) a.
