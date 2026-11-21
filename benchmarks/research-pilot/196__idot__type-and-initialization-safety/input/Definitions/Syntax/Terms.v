Set Implicit Arguments.

Require Import Coq.Bool.Bool.

Require Import LibExtra SyntaxClasses.

Require Import Vars TransformCollect Types.

Inductive def : Set :=
  | def_typ  : typ_label -> typ -> def
  | def_trm  : trm_label -> def.

Notation defs := (list def).

Inductive trm : Set :=
  | trm_var  : avar -> trm
  | trm_sel  : avar -> trm_label -> trm
  | trm_app  : avar -> avar -> trm
  | trm_let  : typ -> trm -> trm -> trm
  | trm_lit  : typ -> lit -> trm -> trm
  | trm_asn  : avar -> trm_label -> avar -> trm
  | trm_new  : avar -> list avar -> trm
with lit : Set :=
  | lit_fun : typ -> trm -> lit
  | lit_con  : typs -> inits -> typ -> defs -> trm -> lit.

Scheme trm_mut  := Induction for trm  Sort Prop
with   lit_mut  := Induction for lit  Sort Prop.

Combined Scheme trm_mutind from trm_mut, lit_mut.

Definition open_rec_def (k: nat) (u: var) (d: def) : def :=
  match d with
  | def_typ L T => def_typ L (open_rec k u T)
  | def_trm m   => def_trm m
  end.

Instance DefOpenable : Openable def := open_rec_def.

Fixpoint open_rec_trm (k: nat) (u: var) (t: trm): trm :=
  match t with
  | trm_var a      => trm_var (open_rec k u a)
  | trm_sel v m    => trm_sel (open_rec k u v) m
  | trm_app f a    => trm_app (open_rec k u f) (open_rec k u a)
  | trm_let T t1 t2 =>
    trm_let (open_rec k u T) (open_rec_trm k u t1) (open_rec_trm (S k) u t2)
  | trm_lit T l t =>
    trm_lit (open_rec k u T) (open_rec_lit k u l) (open_rec_trm (S k) u t)
  | trm_asn v m v2 => trm_asn (open_rec k u v) m (open_rec k u v2)
  | trm_new a avs  => trm_new (open_rec k u a) (open_rec k u avs)
  end with
open_rec_lit (k: nat) (u: var) (l: lit): lit :=
  match l with
  | lit_fun T t => lit_fun (open_rec k u T) (open_rec_trm (S k) u t)
  | lit_con Ts is' T ds t =>
    lit_con
      (open_rec k u Ts)
      is'
      (open_rec (S (length_s Ts) + k) u T)
      (open_rec (S (length_s Ts) + k) u ds)
      (open_rec_trm (S (length_s Ts) + k) u t)

  end.

Instance TrmOpenable : Openable trm := open_rec_trm.

Instance LitOpenable : Openable lit := open_rec_lit.

Definition fv_def (d: def) : vars :=
  match d with
  | def_typ _ T     => (fv T)
  | def_trm _       => \{}
  end.

Instance DefFreeVar : FreeVar def := fv_def.

Fixpoint fv_trm (t: trm) : vars :=
  match t with
  | trm_var a         => (fv a)
  | trm_sel x m       => (fv x)
  | trm_app f a       => (fv f) \u (fv a)
  | trm_let T t1 t2   => (fv T) \u (fv_trm t1) \u (fv_trm t2)
  | trm_lit T l t     => (fv T) \u (fv_lit l) \u (fv_trm t)
  | trm_asn x m y     => (fv x) \u (fv y)
  | trm_new a avs     => (fv a) \u (fv avs)
  end with
fv_lit (l: lit) : vars :=
  match l with
  | lit_fun T e    => (fv T) \u (fv_trm e)
  | lit_con Ts is' T ds t => (fv Ts) \u (fv T) \u (fv ds) \u (fv_trm t)
  end.

Instance TrmFreeVar : FreeVar trm := fv_trm.

Instance LitFreeVar : FreeVar lit := fv_lit.

Definition subst_def (z: var) (u: var) (d: def) : def :=
  match d with
  | def_typ l t => def_typ l (subst_var z u t)
  | def_trm l   => def_trm l
  end.

Instance DefSubstVar : SubstVar def := subst_def.

Fixpoint subst_trm (z: var) (u: var) (t: trm) : trm :=
  match t with
  | trm_var x        => trm_var (subst_var z u x)
  | trm_sel x1 L     => trm_sel (subst_var z u x1) L
  | trm_app x1 x2    => trm_app (subst_var z u x1) (subst_var z u x2)
  | trm_let T t1 t2  =>
    trm_let (subst_var z u T) (subst_trm z u t1) (subst_trm z u t2)
  | trm_lit T l t    =>
    trm_lit (subst_var z u T) (subst_lit z u l) (subst_trm z u t)
  | trm_asn x1 L x2  => trm_asn (subst_var z u x1) L (subst_var z u x2)
  | trm_new x xs     =>
    trm_new (subst_var z u x) (subst_var z u xs)
  end with
subst_lit (z: var) (u: var) (l: lit) : lit :=
  match l with
  | lit_fun T t   => lit_fun (subst_var z u T) (subst_trm z u t)
  | lit_con Ts is' T ds t =>
    lit_con (subst_var z u Ts)
            is'
            (subst_var z u T)
            (subst_var z u ds)
            (subst_trm z u t)
  end.

Instance TrmSubstVar : SubstVar trm := subst_trm.

Instance LitSubstVar : SubstVar lit := subst_lit.

Instance TrmAbstractSyntax :
  AbstractSyntax TrmOpenable TrmFreeVar TrmSubstVar := {}.

Instance LitAbstractSyntax :
  AbstractSyntax LitOpenable LitFreeVar LitSubstVar := {}.

Instance DefAbstractSyntax :
  AbstractSyntax DefOpenable DefFreeVar DefSubstVar := {}.

Instance DefLabelOf : LabelOf def :=
  fun D =>
      match D with
      | def_typ L _ => label_typ L
      | def_trm m   => label_trm m
      end.

Definition collect_def {C: Type} (df : C) (f : avar -> C) (comb: C -> C -> C) (d: def) : C :=
  match d with
  | def_typ _ T     => (collect df f comb T)
  | def_trm _       => df
  end.

Instance DefCollect : Collect AvarAbstractSyntax DefAbstractSyntax :=
  @collect_def.

Fixpoint collect_trm {C: Type} (df : C) (f : avar -> C) (comb: C -> C -> C) (t: trm) : C :=
  match t with
  | trm_var a        => (f a)
  | trm_sel x m      => (f x)
  | trm_app f' a     => comb (f f') (f a)
  | trm_let T t1 t2  =>
    comb (collect df f comb T)
         (comb (collect_trm df f comb t1) (collect_trm df f comb t2))
  | trm_lit T l t    =>
    comb (collect df f comb T)
         (comb (collect_lit df f comb l) (collect_trm df f comb t))
  | trm_asn x m y    => comb (f x) (f y)
  | trm_new a avs    => comb (f a) (collect df f comb avs)
  end with
collect_lit {C: Type} (df : C) (f : avar -> C) (comb: C -> C -> C) (l: lit) : C :=
  match l with
  | lit_fun T e  => comb (collect df f comb T) (collect_trm df f comb e)
  | lit_con Ts is' T ds t =>
    comb (collect df f comb Ts)
         (comb (collect df f comb T)
               (comb (collect df f comb ds) (collect_trm df f comb t)))
  end.

Instance TrmCollect : Collect AvarAbstractSyntax TrmAbstractSyntax :=
  @collect_trm.

Instance LitCollect : Collect AvarAbstractSyntax LitAbstractSyntax :=
  @collect_lit.

Definition transform_def (f : avar -> nat -> avar) (d : def) (n : nat) : def :=
  match d with
  | def_typ L T => def_typ L (transform f T n)
  | def_trm m   => def_trm m
  end.

Instance DefTransform : Transform AvarAbstractSyntax DefAbstractSyntax :=
  @transform_def.

Fixpoint transform_trm (f : avar -> nat -> avar) (t : trm) (n : nat) : trm :=
  match t with
  | trm_var a      => trm_var (f a n)
  | trm_sel v m    => trm_sel (f v n) m
  | trm_app f' a    => trm_app (f f' n) (f a n)
  | trm_let T t1 t2 =>
    trm_let (transform f T n) (transform_trm f t1 n) (transform_trm f t2 (S n))
  | trm_lit T l t  =>
    trm_lit (transform f T n) (transform_lit f l n) (transform_trm f t (S n))
  | trm_asn v m v2 => trm_asn (f v n) m (f v2 n)
  | trm_new a avs  => trm_new (f a n) (transform f avs n)
  end with
transform_lit (f : avar -> nat -> avar) (l : lit) (n : nat) : lit :=
  match l with
  | lit_fun T t => lit_fun (transform f T n) (transform_trm f t (S n))
  | lit_con Ts is' T ds t =>
    lit_con
      (transform f Ts n)
      is'
      (transform f T (S (length_s Ts) + n))
      (transform f ds (S (length_s Ts) + n))
      (transform_trm f t (S (length_s Ts) + n))

  end.

Instance TrmTransform : Transform AvarAbstractSyntax TrmAbstractSyntax :=
  @transform_trm.

Instance LitTransform : Transform AvarAbstractSyntax LitAbstractSyntax :=
  @transform_lit.
