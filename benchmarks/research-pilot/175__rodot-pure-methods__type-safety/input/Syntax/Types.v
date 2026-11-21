Set Implicit Arguments.

Require Import Coq.Bool.Bool.

Require Import LibExtra SyntaxClasses.

Require Import Vars Labels TransformCollect.

Inductive typ : Set :=
  | typ_top  : typ
  | typ_bot  : typ
  | typ_rcd  : dec -> typ
  | typ_and  : typ -> typ -> typ
  | typ_or   : typ -> typ -> typ
  | typ_sel  : avar -> typ_label -> avar -> typ
  | typ_bnd  : typ -> typ
  | typ_fun  : typ -> typ -> typ
  | typ_nocap: typ

with dec : Set :=
  | dec_typ: typ_label -> typ -> typ -> dec
  | dec_fld: fld_label -> typ -> typ -> dec
  | dec_met: met_label ->  typ -> typ -> typ -> dec
.

Notation typ_cap_marker C T := (typ_rcd (dec_typ (typ_label_refcap C) typ_bot T)) (only parsing).

Notation typ_mut_marker T := (typ_cap_marker typ_refcap_mutability T) (only parsing).

Scheme typ_mut  := Induction for typ Sort Prop
with   dec_mut  := Induction for dec Sort Prop.

Combined Scheme typ_mutind from typ_mut, dec_mut.

Fixpoint open_rec_typ (k: nat) (u: var) (T: typ) {struct T} : typ :=
  match T with
  | typ_top        => typ_top
  | typ_bot        => typ_bot
  | typ_rcd D      => typ_rcd (open_rec_dec k u D)
  | typ_and T1 T2  => typ_and (open_rec_typ k u T1)
                             (open_rec_typ k u T2)
  | typ_or T1 T2  => typ_or (open_rec_typ k u T1)
                             (open_rec_typ k u T2)
  | typ_sel x L y => typ_sel (open_rec k u x) L (open_rec k u y)
  | typ_bnd T      => typ_bnd (open_rec_typ (S k) u T)
  | typ_fun T1 T2  => typ_fun (open_rec_typ k u T1)
                             (open_rec_typ (S k) u T2)
  | typ_nocap => typ_nocap
  end with
open_rec_dec (k: nat) (u: var) (D: dec): dec :=
  match D with
  | dec_typ L T U => dec_typ L (open_rec_typ (S k) u T)
                            (open_rec_typ (S k) u U)
  | dec_fld m T U => dec_fld m (open_rec_typ k u T)
                            (open_rec_typ k u U)
  | dec_met m TC TZ TR =>
    dec_met m (open_rec_typ (S k) u TC) (open_rec_typ k u TZ) (open_rec_typ (S (S k)) u TR)
  end.

Instance TypOpenable : Openable typ := open_rec_typ.

Instance DecOpenable : Openable dec := open_rec_dec.

Fixpoint fv_typ (T: typ) : vars :=
  match T with
  | typ_top        => \{}
  | typ_bot        => \{}
  | typ_rcd D      => (fv_dec D)
  | typ_and T U    => (fv_typ T) \u (fv_typ U)
  | typ_or T U    => (fv_typ T) \u (fv_typ U)
  | typ_sel x L y   => (fv x) \u (fv y)
  | typ_bnd T      => (fv_typ T)
  | typ_fun T1 T2  => (fv_typ T1) \u (fv_typ T2)
  | typ_nocap => \{}
  end with
fv_dec (D: dec) : vars :=
  match D with
  | dec_typ L T U => (fv_typ T) \u (fv_typ U)
  | dec_fld m T U => (fv_typ T) \u (fv_typ U)
  | dec_met m TC TZ TR => (fv_typ TC) \u (fv_typ TZ) \u (fv_typ TR)
  end.

Instance TypFreeVar : FreeVar typ := fv_typ.

Instance DecFreeVar : FreeVar dec := fv_dec.

Fixpoint subst_typ (z: var) (u: var) (T: typ) { struct T } : typ :=
  match T with
  | typ_top        => typ_top
  | typ_bot        => typ_bot
  | typ_rcd D      => typ_rcd (subst_dec z u D)
  | typ_and T1 T2  => typ_and (subst_typ z u T1) (subst_typ z u T2)
  | typ_or T1 T2  => typ_or (subst_typ z u T1) (subst_typ z u T2)
  | typ_sel x L y    => typ_sel (subst_var z u x) L (subst_var z u y)
  | typ_bnd T      => typ_bnd (subst_typ z u T)
  | typ_fun T U    => typ_fun (subst_typ z u T) (subst_typ z u U)
  | typ_nocap => typ_nocap
  end with
subst_dec (z: var) (u: var) (D: dec) { struct D } : dec :=
  match D with
  | dec_typ L T U => dec_typ L (subst_typ z u T) (subst_typ z u U)
  | dec_fld L T U => dec_fld L (subst_typ z u T) (subst_typ z u U)
  | dec_met m TC TZ TR => dec_met m (subst_typ z u TC) (subst_typ z u TZ) (subst_typ z u TR)
  end.

Instance TypSubstVar : SubstVar typ := subst_typ.

Instance DecSubstVar : SubstVar dec := subst_dec.

Fixpoint seal_rec_typ (k: nat) (u: var) (T: typ) {struct T} : typ :=
  match T with
  | typ_top        => typ_top
  | typ_bot        => typ_bot
  | typ_rcd D      => typ_rcd (seal_rec_dec k u D)
  | typ_and T1 T2  => typ_and (seal_rec_typ k u T1)
                             (seal_rec_typ k u T2)
  | typ_or T1 T2  => typ_or (seal_rec_typ k u T1)
                             (seal_rec_typ k u T2)
  | typ_sel x L y => typ_sel (seal_rec k u x) L (seal_rec k u y)
  | typ_bnd T      => typ_bnd (seal_rec_typ (S k) u T)
  | typ_fun T1 T2  => typ_fun (seal_rec_typ k u T1)
                             (seal_rec_typ (S k) u T2)
  | typ_nocap => typ_nocap
  end with
seal_rec_dec (k: nat) (u: var) (D: dec): dec :=
  match D with
  | dec_typ L T U => dec_typ L (seal_rec_typ (S k) u T)
                            (seal_rec_typ (S k) u U)
  | dec_fld m T U => dec_fld m (seal_rec_typ k u T)
                            (seal_rec_typ k u U)
  | dec_met m TC TZ TR =>
    dec_met m (seal_rec_typ (S k) u TC) (seal_rec_typ k u TZ) (seal_rec_typ (S (S k)) u TR)
  end.

Instance TypSealable : Sealable typ := seal_rec_typ.

Instance DecSealable : Sealable dec := seal_rec_dec.

Instance TypAbstractSyntax :
  AbstractSyntax TypOpenable TypFreeVar TypSubstVar := {}.

Instance DecAbstractSyntax :
  AbstractSyntax DecOpenable DecFreeVar DecSubstVar := {}.

Instance DecLabelOf : LabelOf dec :=
  fun D =>
      match D with
      | dec_typ L _ _ => label_typ L
      | dec_fld m _ _ => label_fld m
      | dec_met m _ _ _ => label_met m
      end.

Fixpoint collect_typ {C: Type} (df : C) (f : avar -> C) (comb: C -> C -> C) (T: typ) : C :=
  match T with
  | typ_top        => df
  | typ_bot        => df
  | typ_rcd D      => (collect_dec df f comb D)
  | typ_and T U    => comb (collect_typ df f comb T) (collect_typ df f comb U)
  | typ_or T U    => comb (collect_typ df f comb T) (collect_typ df f comb U)
  | typ_sel x L y    => comb (f x) (f y)
  | typ_bnd T      => (collect_typ df f comb T)
  | typ_fun T1 T2  => comb (collect_typ df f comb T1) (collect_typ df f comb T2)
  | typ_nocap => df
  end with
collect_dec {C: Type} (df : C) (f : avar -> C) (comb: C -> C -> C) (D: dec) : C :=
  match D with
  | dec_typ L T U => comb (collect_typ df f comb T) (collect_typ df f comb U)
  | dec_fld m T U => comb (collect_typ df f comb T) (collect_typ df f comb U)
  | dec_met m TC TZ TR => comb (comb (collect_typ df f comb TC) (collect_typ df f comb TZ)) (collect_typ df f comb TR)
  end.

Instance TypCollect : Collect AvarAbstractSyntax TypAbstractSyntax
  := @collect_typ.

Instance DecCollect : Collect AvarAbstractSyntax DecAbstractSyntax :=
  @collect_dec.

Fixpoint transform_typ (f : avar -> nat -> avar) (T : typ) (n : nat) : typ :=
  match T with
  | typ_top        => typ_top
  | typ_bot        => typ_bot
  | typ_rcd D      => typ_rcd (transform_dec f D n)
  | typ_and T1 T2  => typ_and (transform_typ f T1 n) (transform_typ f T2 n)
  | typ_or T1 T2  => typ_or (transform_typ f T1 n) (transform_typ f T2 n)
  | typ_sel x L y    => typ_sel (f x n) L (f y n)
  | typ_bnd T      => typ_bnd (transform_typ f T (S n))
  | typ_fun T1 T2  => typ_fun (transform_typ f T1 n) (transform_typ f T2 (S n))
  | typ_nocap => typ_nocap
  end with
transform_dec (f : avar -> nat -> avar) (D : dec) (n : nat) : dec :=
  match D with
  | dec_typ L T U => dec_typ L (transform_typ f T (S n)) (transform_typ f U (S n))
  | dec_fld m T U => dec_fld m (transform_typ f T n) (transform_typ f U n)
  | dec_met m TC TZ TR => dec_met m (transform_typ f TC (S n)) (transform_typ f TZ n) (transform_typ f TR (S (S n)))
  end.

Instance TypTransform : Transform AvarAbstractSyntax TypAbstractSyntax :=
  @transform_typ.

Instance DecTransform : Transform AvarAbstractSyntax DecAbstractSyntax :=
  @transform_dec.

Inductive typ_nulary: typ -> Prop :=
| typ_nulary_top: typ_nulary typ_top
| typ_nulary_bot: typ_nulary typ_bot
| typ_nulary_nocap: typ_nulary typ_nocap
.

Inductive typ_andor: (typ -> typ -> typ) -> Prop :=
| typ_andor_and: typ_andor typ_and
| typ_andor_or: typ_andor typ_or
.

Notation typ_binary_rcd_typ_ctor A :=
  (fun t1 t2 => typ_rcd (dec_typ A t1 t2)).

Notation typ_binary_rcd_fld_ctor A :=
  (fun t1 t2 => typ_rcd (dec_fld A t1 t2)).

Inductive typ_binary: (typ -> typ -> typ) -> Prop :=
| typ_binary_and: typ_binary typ_and
| typ_binary_or: typ_binary typ_or
| typ_binary_fun: typ_binary typ_fun
| typ_binary_rcd_typ(A: typ_label): typ_binary (typ_binary_rcd_typ_ctor A)
| typ_binary_rcd_fld(A: fld_label): typ_binary (typ_binary_rcd_fld_ctor A)
.

Notation typ_notor B := (forall T U, B <> typ_or T U) (only parsing).

Notation typ_notand T := (forall S1 S2, T <> typ_and S1 S2) (only parsing).

Definition typ_notlog T := typ_notor T /\ typ_notand T.
