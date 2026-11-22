Require Export Autosubst.Autosubst.
From Stdlib Require Import List ZArith.

Inductive op :=
  | Add
  | Eq
.


Inductive term :=
  (* Lambda calculus part of the language*)
  | Var (x: var)
  | App (t1 t2: term)
  | Lam (t: {bind term})

  (* Default fragment of the language. *)
  | ErrorOnEmpty (arg: term)
  | DefaultPure (arg: term)
  | Default (ts: list term) (tj tc: term)
  | Empty
  | Conflict

  (* value computating fragment of the language*)
  | Value (v: value)
  | Binop (op: op) (t1 t2: term)

  | Match_ (u t1: term) (t2: {bind term})
  | ENone
  | ESome (t: term)
  | Fold (f: term) (ts: list term) (t: term)

  | If (t ta tb: term)

with value :=
  | Bool (b: bool)
  | Int (i: Z)
  | Closure (t: {bind term}) (sigma: list value)
  | VNone
  | VUnit
  | VSome (v: value)
  | VPure (v: value)
.

#[export] Instance Ids_term : Ids term := ltac:(derive).
#[export] Instance Rename_term : Rename term := ltac:(derive).
#[export] Instance Subst_term : Subst term := ltac:(derive).

Definition get_op op i1 i2 :=
  match op, i1, i2 with
  | Add, Int i1, Int i2 => Some (Int (Z.add i1 i2))
  | Eq, Int i1, Int i2 => Some (Bool (Z.eqb i1 i2))
  | _, _, _ => None
  end.

Import List.ListNotations.
Open Scope list.

Definition subst_of_env sigma :=
  fun n =>
  match List.nth_error sigma n with
  | None => ids (n - List.length sigma)
  | Some t => Value t
  end
.
