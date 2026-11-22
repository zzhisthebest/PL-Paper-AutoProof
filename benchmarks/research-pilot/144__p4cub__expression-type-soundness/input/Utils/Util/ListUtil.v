Require Import Coq.Strings.String.

From Poulet4 Require Export Utils.Util.FunUtil Utils.Util.StringUtil Monads.Result.

From Coq Require Export Lists.List micromega.Lia.

Export ListNotations.

Require VST.zlist.sublist.

Section NthUpdate.

Context {A : Type}.

Fixpoint nth_update (n : nat) (a : A) (l : list A) : list A :=
    match n, l with
    | O, _::t   => a::t
    | S n, h::t => h :: nth_update n a t
    | O, []
    | S _, []  => []
  end.

Variable a : A.

End NthUpdate.

Section FoldLeftProp.

Context {A B : Type}.

Variable (R : A -> B -> B -> Prop).

Inductive FoldLeft : list A -> B -> B -> Prop :=
  | FoldLeft_nil (b: B) :
      FoldLeft [] b b
  | FoldLeft_cons (a: A) (l: list A) (b b' b'': B) :
      R a b b' ->
      FoldLeft l b' b'' ->
      FoldLeft (a :: l) b b''.

End FoldLeftProp.

Import String.

Definition opt_snd { A B : Type } (p : A * option B ) : option (A * B) :=
  match p with
  | (_, None) => None
  | (a, Some b) => Some (a,b)
  end.

Fixpoint string_member (x : string) (l1 : list string) : bool :=
  match l1 with
  | [] => false
  | y::ys =>
    if String.eqb x y
    then true
    else string_member x ys
  end.

Fixpoint list_eq {A : Type} (eq : A -> A -> bool) (s1 s2 : list A) : bool  :=
  match s1,s2 with
  | [], [] => true
  | _, [] => false
  | [], _ => false
  | x::xs, y::ys => andb (eq x y) (list_eq eq xs ys)
  end.

Import Result ResultNotations.

Fixpoint zip {A B : Type} (xs : list A) (ys : list B) : result string (list (A * B)) :=
  match xs, ys with
  | [],[] => ok []
  | [], _ => error "First zipped list was shorter than the second"%string
  | _, [] => error "First zipped list was longer than the second"%string
  | x::xs, y::ys =>
    let+ xys := zip xs ys in
    cons (x,y) xys
  end.

Fixpoint ith { A : Type } (xs : list A) (i : nat) : result string A :=
  match xs with
  | [] => error ("ListAccessFailure: list had " ++ StringUtil.string_of_nat i ++ " too few elements")%string
  | x::xs =>
    match i with
    | O => ok x
    | S i =>  ith xs i
    end
  end.

Section FoldRighti.

Context {A B : Type}.

Variable f : nat -> A -> B -> B.

Variable init : B.

Definition fold_righti (xs : list A) : B :=
    snd (List.fold_right (fun a '(i, b) => (i + 1, f i a b )) (O, init) xs).

End FoldRighti.

Section FoldLefti.

Context {A B : Type}.

Variable f : nat -> A -> B -> B.

Definition fold_lefti (init : B) (lst : list A) : B :=
    snd (fold_left (fun '(n, b) a => (S n, f n a b)) lst (O, init)).

End FoldLefti.

Definition findi { A : Type } (select : A -> bool) (l : list A) : option nat :=
  fold_lefti (fun i a found_at_n =>
                match found_at_n with
                | Some _ => found_at_n
                | None => if select a
                          then Some i
                          else None
                end
             ) None l.

Definition union_map_snd {Err A B C : Type} (f : B -> result Err C) (xs : list (A * B)) : result Err (list (A * C)) :=
  rred (List.map (snd_res_map f) xs).

Definition map_snd {A B C : Type} (f : B -> C) (ps : list (A * B)) : list (A * C) :=
  List.map (fun '(a, b) => (a, f b)) ps.

Fixpoint intersect_string_list_aux (xs ys acc : list string) : list string :=
  match xs with
  | [] => acc
  | x::xs =>
    if string_member x ys
    then intersect_string_list_aux xs ys (x::acc)
    else intersect_string_list_aux xs ys acc
  end.

Definition intersect_string_list (xs ys : list string) : list string :=
  rev' (intersect_string_list_aux xs ys []).

Definition Znth_default {A : Type} (x : A) (n : BinInt.Z) (l : list A) : A :=
  @VST.zlist.sublist.Znth A x n l.

Section IndexOf.

Context {A : Set}.

Variable eqA_dec : forall (x y : A), {x = y} + {x <> y}.

Variable a : A.

Fixpoint index_of (l : list A) : option nat :=
    match l with
    | [] => None
    | h :: t => if eqA_dec h a then Some 0 else option_map S (index_of t)
    end.

End IndexOf.

Section Mapi.

Context {A B : Type}.

Variable f : nat -> A -> B.

Fixpoint mapi_help (i : nat) (l : list A) : list B :=
    match l with
    | [] => []
    | a :: l => f i a :: mapi_help (S i) l
    end.

Definition mapi : list A -> list B := mapi_help 0.

End Mapi.
