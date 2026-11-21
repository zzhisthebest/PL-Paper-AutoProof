Require Export Syntax.

From Stdlib Require Import List.

Import ListNotations.

Require Export Notations.

Require Export ssreflect ssrbool Stdlib.Sets.Finite_sets_facts.

Definition gget {X: Type} (l : list X)  : Loc -> option X := nth_error l.

Definition runtime_getObj (l : heap)    : Loc -> option Obj := nth_error l.

Definition getVal (l : list value)  : Loc -> option value := nth_error l.

Definition runtime_getVal (rΓ : r_env): Loc -> option value := nth_error (rΓ.(vars)).

Definition static_getType (sΓ: s_env): Loc -> option qualified_type := nth_error sΓ.

Fixpoint mapM {A B : Type} (f : A -> option B) (l : list A) : option (list B) :=
  match l with
  | [] => Some []
  | x :: xs =>
      match f x, mapM f xs with
      | Some y, Some ys => Some (y :: ys)
      | _, _ => None
      end
  end.

Definition static_getType_list (sΓ: s_env): list Loc -> option (list qualified_type) :=
  fun l => mapM (fun x => static_getType sΓ x) l.

Definition runtime_lookup_list (rΓ: r_env): list Loc -> option (list value) :=
  fun l => mapM (fun x => runtime_getVal rΓ x) l.

Fixpoint forallb2 {A B} (f : A -> B -> bool) (l1 : list A) (l2 : list B) : bool :=
  match l1, l2 with
  | [], [] => true
  | x1 :: xs1, x2 :: xs2 => f x1 x2 && forallb2 f xs1 xs2
  | _, _ => false
  end.

Fixpoint update {X : Type} (position : nat) (value : X) (l : list X) : list X :=
  match l, position with
  | [], _ => []
  | _::t, 0 => value :: t
  | h::l', S n => h :: update n value l'
  end.

Notation "[ x ↦  v ] l" := (update x v l) (at level 0).

Definition update_r_env_value (rΓ : r_env) (l : Loc) (v : value) : r_env :=
  match rΓ with
  {| vars := vars; |} =>
      {| vars := update l v vars;|}
  end.

Definition find_class (CT : class_table) (C : class_name) : option class_def :=
    gget CT C.

Definition bound (CT : class_table) (C : class_name) : option q_c :=
  match find_class CT C with
  | Some decl => Some (class_qualifier (signature decl))
  | None => None
  end.
