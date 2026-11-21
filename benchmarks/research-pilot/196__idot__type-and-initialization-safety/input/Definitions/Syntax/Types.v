Set Implicit Arguments.

Require Import Coq.Bool.Bool.

Require Import LibExtra SyntaxClasses.

Require Import Vars TransformCollect.

Inductive init_typ : Set :=
  | committed : init_typ
  | free : init_typ
  | unspecified : init_typ.

Notation inits := (list init_typ).

Notation init_ctx := (env init_typ).

Inductive typ : Set :=
  | typ_top  : typ
  | typ_bot  : typ
  | typ_rcd  : dec -> typ
  | typ_and  : typ -> typ -> typ
  | typ_sel  : avar -> typ_label -> typ
  | typ_bnd  : typ -> typ
  | typ_all  : typ -> typ -> typ
  | typ_con  : typs -> inits -> typ -> typ

with typs : Set :=
  | typs_nil : typs
  | typs_cons : typ -> typs -> typs

with dec : Set :=
  | dec_typ  : typ_label -> typ -> typ -> dec
  | dec_trm  : trm_label -> typ -> typ -> dec.

Scheme typ_mut  := Induction for typ Sort Prop
with   typs_mut := Induction for typs Sort Prop
with   dec_mut  := Induction for dec Sort Prop.

Combined Scheme typ_mutind from typ_mut, typs_mut, dec_mut.

Fixpoint typs_to_list (Ts : typs) : list typ :=
  match Ts with
  | typs_nil => nil
  | typs_cons T Ts' => (T :: typs_to_list Ts')%list
  end.

Instance TypsToList : ToList typ typs := typs_to_list.

Arguments TypsToList _ /.

Fixpoint typs_of_list (xs : list typ) : typs :=
  match xs with
  | nil => typs_nil
  | (T :: Ts')%list => typs_cons T (typs_of_list Ts')
  end.

Instance TypsOfList : OfList typ typs := typs_of_list.

Arguments TypsOfList _ /.

Fixpoint open_rec_typ (k: nat) (u: var) (T: typ) {struct T} : typ :=
  match T with
  | typ_top        => typ_top
  | typ_bot        => typ_bot
  | typ_rcd D      => typ_rcd (open_rec_dec k u D)
  | typ_and T1 T2  => typ_and (open_rec_typ k u T1)
                             (open_rec_typ k u T2)
  | typ_sel x L    => typ_sel (open_rec k u x) L
  | typ_bnd T      => typ_bnd (open_rec_typ (S k) u T)
  | typ_all T1 T2  => typ_all (open_rec_typ k u T1)
                             (open_rec_typ (S k) u T2)
  | typ_con Ts is' T =>
    typ_con
      (open_rec_typs k u Ts)
      is'
      (open_rec_typ (S (length_s Ts) + k) u T)

  end with
open_rec_typs (k : nat) (u : var) (Ts : typs) : typs :=
  match Ts with
  | typs_nil => typs_nil
  | typs_cons T Ts =>
    typs_cons (open_rec_typ k u T)
              (open_rec_typs k u Ts)
  end with
open_rec_dec (k: nat) (u: var) (D: dec): dec :=
  match D with
  | dec_typ L T U => dec_typ L (open_rec_typ k u T)
                            (open_rec_typ k u U)
  | dec_trm m T U => dec_trm m (open_rec_typ k u T)
                            (open_rec_typ k u U)
  end.

Instance TypOpenable : Openable typ := open_rec_typ.

Instance TypsOpenable : Openable typs := open_rec_typs.

Instance DecOpenable : Openable dec := open_rec_dec.

Fixpoint fv_typ (T: typ) : vars :=
  match T with
  | typ_top        => \{}
  | typ_bot        => \{}
  | typ_rcd D      => (fv_dec D)
  | typ_and T U    => (fv_typ T) \u (fv_typ U)
  | typ_sel x L    => (fv x)
  | typ_bnd T      => (fv_typ T)
  | typ_all T1 T2  => (fv_typ T1) \u (fv_typ T2)
  | typ_con Ts is' T   => (fv_typs Ts) \u (fv_typ T)
  end with
fv_typs (Ts : typs) : vars :=
  match Ts with
  | typs_nil => \{}
  | typs_cons T Ts => (fv_typ T) \u (fv_typs Ts)
  end with
fv_dec (D: dec) : vars :=
  match D with
  | dec_typ L T U => (fv_typ T) \u (fv_typ U)
  | dec_trm m T U => (fv_typ T) \u (fv_typ U)
  end.

Instance TypFreeVar : FreeVar typ := fv_typ.

Instance TypsFreeVar : FreeVar typs := fv_typs.

Instance DecFreeVar : FreeVar dec := fv_dec.

Fixpoint subst_typ (z: var) (u: var) (T: typ) { struct T } : typ :=
  match T with
  | typ_top        => typ_top
  | typ_bot        => typ_bot
  | typ_rcd D      => typ_rcd (subst_dec z u D)
  | typ_and T1 T2  => typ_and (subst_typ z u T1) (subst_typ z u T2)
  | typ_sel x L    => typ_sel (subst_var z u x) L
  | typ_bnd T      => typ_bnd (subst_typ z u T)
  | typ_all T U    => typ_all (subst_typ z u T) (subst_typ z u U)
  | typ_con Ts is' T   => typ_con (subst_typs z u Ts) is' (subst_typ z u T)
  end with
subst_typs (z: var) (u: var) (Ts: typs) { struct Ts } : typs :=
  match Ts with
  | typs_nil => typs_nil
  | typs_cons T Ts => typs_cons (subst_typ z u T) (subst_typs z u Ts)
  end with
subst_dec (z: var) (u: var) (D: dec) { struct D } : dec :=
  match D with
  | dec_typ L T U => dec_typ L (subst_typ z u T) (subst_typ z u U)
  | dec_trm L T U => dec_trm L (subst_typ z u T) (subst_typ z u U)
  end.

Instance TypSubstVar : SubstVar typ := subst_typ.

Instance TypsSubstVar : SubstVar typs := subst_typs.

Instance DecSubstVar : SubstVar dec := subst_dec.

Instance TypAbstractSyntax :
  AbstractSyntax TypOpenable TypFreeVar TypSubstVar := {}.

Instance TypsAbstractSyntax :
  AbstractSyntax TypsOpenable TypsFreeVar TypsSubstVar := {}.

Instance DecAbstractSyntax :
  AbstractSyntax DecOpenable DecFreeVar DecSubstVar := {}.

Instance DecLabelOf : LabelOf dec :=
  fun D =>
      match D with
      | dec_typ L _ _ => label_typ L
      | dec_trm m _ _ => label_trm m
      end.

Fixpoint collect_typ {C: Type} (df : C) (f : avar -> C) (comb: C -> C -> C) (T: typ) : C :=
  match T with
  | typ_top        => df
  | typ_bot        => df
  | typ_rcd D      => (collect_dec df f comb D)
  | typ_and T U    => comb (collect_typ df f comb T) (collect_typ df f comb U)
  | typ_sel x L    => (f x)
  | typ_bnd T      => (collect_typ df f comb T)
  | typ_all T1 T2  => comb (collect_typ df f comb T1) (collect_typ df f comb T2)
  | typ_con Ts is' T => comb (collect_typs df f comb Ts) (collect_typ df f comb T)
  end with
collect_typs {C: Type} (df : C) (f : avar -> C) (comb: C -> C -> C) (Ts: typs) : C :=
  match Ts with
  | typs_nil => df
  | typs_cons T Ts => comb (collect_typ df f comb T) (collect_typs df f comb Ts)
  end with
collect_dec {C: Type} (df : C) (f : avar -> C) (comb: C -> C -> C) (D: dec) : C :=
  match D with
  | dec_typ L T U => comb (collect_typ df f comb T) (collect_typ df f comb U)
  | dec_trm m T U => comb (collect_typ df f comb T) (collect_typ df f comb U)
  end.

Instance TypCollect : Collect AvarAbstractSyntax TypAbstractSyntax
  := @collect_typ.

Instance TypsCollect : Collect AvarAbstractSyntax TypsAbstractSyntax :=
  @collect_typs.

Instance DecCollect : Collect AvarAbstractSyntax DecAbstractSyntax :=
  @collect_dec.

Fixpoint transform_typ (f : avar -> nat -> avar) (T : typ) (n : nat) : typ :=
  match T with
  | typ_top        => typ_top
  | typ_bot        => typ_bot
  | typ_rcd D      => typ_rcd (transform_dec f D n)
  | typ_and T1 T2  => typ_and (transform_typ f T1 n) (transform_typ f T2 n)
  | typ_sel x L    => typ_sel (f x n) L
  | typ_bnd T      => typ_bnd (transform_typ f T (S n))
  | typ_all T1 T2  => typ_all (transform_typ f T1 n) (transform_typ f T2 (S n))
  | typ_con Ts is' T   => typ_con
                       (transform_typs f Ts n) is'
                       (transform_typ f T (S (length_s Ts) + n))
  end with
transform_typs (f : avar -> nat -> avar) (Ts : typs) (n : nat) : typs :=
  match Ts with
  | typs_nil => typs_nil
  | typs_cons T Ts =>
    typs_cons (transform_typ f T n) (transform_typs f Ts n)
  end with
transform_dec (f : avar -> nat -> avar) (D : dec) (n : nat) : dec :=
  match D with
  | dec_typ L T U => dec_typ L (transform_typ f T n) (transform_typ f U n)
  | dec_trm m T U => dec_trm m (transform_typ f T n) (transform_typ f U n)
  end.

Instance TypTransform : Transform AvarAbstractSyntax TypAbstractSyntax :=
  @transform_typ.

Instance TypsTransform : Transform AvarAbstractSyntax TypsAbstractSyntax :=
  @transform_typs.

Instance DecTransform : Transform AvarAbstractSyntax DecAbstractSyntax :=
  @transform_dec.
