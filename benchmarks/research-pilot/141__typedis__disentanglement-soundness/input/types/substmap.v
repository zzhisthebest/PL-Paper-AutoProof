From Coq Require Import ssreflect.

From stdpp Require Import base binders list sets gmap mapset ssreflect.

From dislog.utils Require Import more_stdpp.

From dislog.lang Require Import substitution.

Section binders.

Definition binders_set (xs:list binder) : gset string := ⋃ (binder_set <$> xs).

End binders.

Section delete.

Context {A:Type}.

Implicit Type (e:gmap string A).

Definition bdelete (b:binder) (e:gmap string A) : gmap string A :=
  match b with
  | BAnon => e
  | BNamed s => delete s e end.

Definition bdeletes (bs:list binder) (e:gmap string A) : gmap string A :=
  foldr bdelete e bs.

End delete.

Section binserts.

Context {A:Type}.

Definition binsert b x (e:gmap string A) :=
  match b with
  | BAnon => e
  | BNamed b => <[b:=x]> e end.

Definition binserts (xs:list (binder * A)) (e:gmap string A) :=
  foldr (fun '(b,x) acc => binsert b x acc) e xs.

End binserts.

Definition extend {A} xs ys (e:gmap string A) :=
  binserts (rev (zip xs ys)) e.

Section extend.

Context {A:Type}.

Implicit Type (e:gmap string A).

Definition bmap (xs:list binder) (ys:list A) :=
  extend xs ys ∅.

End extend.

Definition find_opt `{Countable A} (m:gmap A A) (a:A) :=
  default a (m !! a).

Section mextend.

Context `{Inhabited A}.

Definition mextend xs ys (e:gmap string A) :=
  extend xs ((fun x => e !!! x) <$> ys) e.

End mextend.
