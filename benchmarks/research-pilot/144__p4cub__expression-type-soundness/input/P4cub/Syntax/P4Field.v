Require Export Poulet4.Utils.Util.Utiliser.

Module Field.

Section FieldSets.

Variables K V : Set.

Definition f : Set := K * V.

Definition fs : Set := list f.

End FieldSets.

Section FieldLibrary.

Definition key {K V : Set} : f K V -> K := fst.

Definition value {K V : Set} : f K V -> V := snd.

Definition keys {K V : Set} : fs K V -> list K := List.map key.

Definition values {K V : Set} : fs K V -> list V := List.map value.

Definition predf_data {K T : Set} (P : T -> Prop) : f K T -> Prop := P ∘ snd.

Definition predfs_data {K T : Set} (P : T -> Prop) : fs K T -> Prop :=
      Forall (predf_data P).

Definition filter {K U : Set} (pred : U -> bool) : fs K U -> fs K U :=
      List.filter (pred ∘ snd).

Definition map {K U V : Set} (f : U -> V) : fs K U -> fs K V :=
      List.map (fun '(x,u) => (x, f u)).

Definition fold {K U V : Set} (f : K -> U -> V -> V)
               (fds : fs K U) (init : V) : V :=
      List.fold_right (fun '(x,u) acc => f x u acc) init fds.

Fixpoint find_value {K V : Set} (f : K -> bool) (fds : fs K V) : option V :=
      match fds with
      | [] => None
      | (k, v) :: fds => if f k then Some v else find_value f fds
      end.

Section GetUpdate.

Context {K U : Set}.

Context {keq : K -> K -> Prop}.

Context `{Equivalence K keq}.

Context `{EqDec K keq}.

Fixpoint get (k : K) (fds : fs K U) : option U :=
        match fds with
        | []            => None
        | (k',u') :: fds => if equiv_dec k k' then Some u'
                          else get k fds
        end.

Fixpoint get_index_rec (k: K) (fds : fs K U) (current : nat) : option nat :=
        match fds with
        | [] => None
        | (k',u') :: fds => if equiv_dec k k' then Some (current)
                            else get_index_rec k fds (S current)
        end.

Definition get_index (k: K) (fds : fs K U) : option nat :=
        get_index_rec k fds 0.

Fixpoint update (k : K) (u : U) (fds : fs K U) : fs K U :=
        match fds with
        | [] => []
        | (k',u') :: fds => (k', if equiv_dec k k' then u else u') :: update k u fds
        end.

End GetUpdate.

Section FieldRelations.

Context {K U V : Set}.

Context {keq : K -> K -> Prop}.

Context `{HK : Equivalence K keq}.

Variable R : U -> V -> Prop.

Definition relf : f K U -> f K V -> Prop :=
        fun u v => equiv (fst u) (fst v) /\ R (snd u) (snd v).

Definition relfs : fs K U -> fs K V -> Prop := Forall2 relf.

Context `{EqDec K keq}.

End FieldRelations.

Section DecEq.

Context {K U : Set}.

Context {keq : K -> K -> Prop}.

Context `{Equivalence K keq}.

Context `{EqDec K keq}.

Variable feq : U -> U -> bool.

Definition eqb_f : f K U -> f K U -> bool :=
        fun '(x1, u1) '(x2, u2) => equiv_dec x1 x2 &&&& feq u1 u2.

Fixpoint eqb_fs (fs1 fs2 : fs K U) : bool :=
        match fs1, fs2 with
        | [], _::_ | _::_, [] => false
        | [], [] => true
        | f1::fs1, f2::fs2 => eqb_f f1 f2 && eqb_fs fs1 fs2
        end.

Section ReflxEqb.

End ReflxEqb.

End DecEq.

End FieldLibrary.


Module FieldTactics.

End FieldTactics.

End Field.
