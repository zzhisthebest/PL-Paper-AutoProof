Set Implicit Arguments.

Require Import Coq.Bool.Bool.

Require Import LibExtra SyntaxClasses.

Require Import Vars Labels TransformCollect Types.

Inductive trm : Set :=
  | trm_var  : avar -> trm
  | trm_read  : avar -> fld_label -> trm
  | trm_apply  : avar -> avar -> trm
  | trm_let  : trm -> trm -> trm
  | trm_lit  : lit -> trm -> trm
  | trm_write  : avar -> fld_label -> avar -> trm
  | trm_call: avar -> met_label -> avar -> trm

with lit : Set :=
  | lit_fun : typ -> trm -> lit
  | lit_obj  : typ -> defs -> lit

with def : Set :=
  | def_typ  : typ_label -> typ -> def
  | def_fld  : fld_label -> avar -> def
  | def_met  : met_label -> trm -> def

with defs : Set :=
  | defs_nil : defs
  | defs_cons : defs -> def -> defs.

Scheme trm_mut  := Induction for trm  Sort Prop
with   lit_mut  := Induction for lit  Sort Prop
with   def_mut  := Induction for def  Sort Prop
with   defs_mut := Induction for defs Sort Prop.

Combined Scheme trm_mutind from trm_mut, lit_mut, def_mut, defs_mut.

Fixpoint open_rec_trm (k: nat) (u: var) (t: trm): trm :=
  match t with
  | trm_var a      => trm_var (open_rec k u a)
  | trm_read v m    => trm_read (open_rec k u v) m
  | trm_apply f a    => trm_apply (open_rec k u f) (open_rec k u a)
  | trm_let t1 t2  => trm_let (open_rec_trm k u t1) (open_rec_trm (S k) u t2)
  | trm_lit l t => trm_lit (open_rec_lit k u l) (open_rec_trm (S k) u t)
  | trm_write v m v2 => trm_write (open_rec k u v) m (open_rec k u v2)
  | trm_call v m v2 => trm_call (open_rec k u v) m (open_rec k u v2)
  end with
open_rec_lit (k: nat) (u: var) (l: lit): lit :=
  match l with
  | lit_fun T t => lit_fun (open_rec k u T) (open_rec_trm (S k) u t)
  | lit_obj T ds =>
    lit_obj
      (open_rec (S k) u T)
      (open_rec_defs (S k) u ds)

  end with
open_rec_def (k: nat) (u: var) (d: def): def :=
  match d with
  | def_typ L T => def_typ L (open_rec (S k) u T)
  | def_fld m v => def_fld m (open_rec k u v)
  | def_met m e => def_met m (open_rec_trm (S (S k)) u e)
  end with
open_rec_defs (k: nat) (u: var) (ds: defs): defs :=
  match ds with
  | defs_nil       => defs_nil
  | defs_cons tl d => defs_cons (open_rec_defs k u tl) (open_rec_def k u d)
  end.

Instance TrmOpenable : Openable trm := open_rec_trm.

Instance LitOpenable : Openable lit := open_rec_lit.

Instance DefOpenable : Openable def := open_rec_def.

Instance DefsOpenable : Openable defs := open_rec_defs.

Fixpoint fv_trm (t: trm) : vars :=
  match t with
  | trm_var a         => (fv a)
  | trm_read x m       => (fv x)
  | trm_apply f a       => (fv f) \u (fv a)
  | trm_let t1 t2     => (fv_trm t1) \u (fv_trm t2)
  | trm_lit l t       => (fv_lit l) \u (fv_trm t)
  | trm_write x m y     => (fv x) \u (fv y)
  | trm_call x m y => (fv x) \u (fv y)
  end with
fv_lit (l: lit) : vars :=
  match l with
  | lit_fun T e    => (fv T) \u (fv_trm e)
  | lit_obj T ds => (fv T) \u (fv_defs ds)
  end with
fv_def (d: def) : vars :=
  match d with
  | def_typ _ T     => (fv T)
  | def_fld _ v     => (fv v)
  | def_met _ t     => (fv_trm t)
  end with
fv_defs(ds: defs) : vars :=
  match ds with
  | defs_nil         => \{}
  | defs_cons tl d   => (fv_defs tl) \u (fv_def d)
  end.

Instance TrmFreeVar : FreeVar trm := fv_trm.

Instance LitFreeVar : FreeVar lit := fv_lit.

Instance DefFreeVar : FreeVar def := fv_def.

Instance DefsFreeVar : FreeVar defs := fv_defs.

Fixpoint subst_trm (z: var) (u: var) (t: trm) : trm :=
  match t with
  | trm_var x        => trm_var (subst_var z u x)
  | trm_read x1 L     => trm_read (subst_var z u x1) L
  | trm_apply x1 x2    => trm_apply (subst_var z u x1) (subst_var z u x2)
  | trm_let t1 t2    => trm_let (subst_trm z u t1) (subst_trm z u t2)
  | trm_lit l t      => trm_lit (subst_lit z u l) (subst_trm z u t)
  | trm_write x1 L x2  => trm_write (subst_var z u x1) L (subst_var z u x2)
  | trm_call x1 L x2  => trm_call (subst_var z u x1) L (subst_var z u x2)
  end with
subst_lit (z: var) (u: var) (l: lit) : lit :=
  match l with
  | lit_fun T t   => lit_fun (subst_var z u T) (subst_trm z u t)
  | lit_obj T ds =>
    lit_obj (subst_var z u T)
            (subst_defs z u ds)
  end with
subst_def (z: var) (u: var) (d: def) : def :=
  match d with
  | def_typ l t => def_typ l (subst_var z u t)
  | def_fld l v => def_fld l (subst_var z u v)
  | def_met l t => def_met l (subst_trm z u t)
  end with
subst_defs (z: var) (u: var) (ds: defs) : defs :=
  match ds with
  | defs_nil => defs_nil
  | defs_cons rest d => defs_cons (subst_defs z u rest) (subst_def z u d)
  end.

Instance TrmSubstVar : SubstVar trm := subst_trm.

Instance LitSubstVar : SubstVar lit := subst_lit.

Instance DefSubstVar : SubstVar def := subst_def.

Instance DefsSubstVar : SubstVar defs := subst_defs.

Fixpoint seal_rec_trm (k: nat) (u: var) (t: trm): trm :=
  match t with
  | trm_var a      => trm_var (seal_rec k u a)
  | trm_read v m    => trm_read (seal_rec k u v) m
  | trm_apply f a    => trm_apply (seal_rec k u f) (seal_rec k u a)
  | trm_let t1 t2  => trm_let (seal_rec_trm k u t1) (seal_rec_trm (S k) u t2)
  | trm_lit l t => trm_lit (seal_rec_lit k u l) (seal_rec_trm (S k) u t)
  | trm_write v m v2 => trm_write (seal_rec k u v) m (seal_rec k u v2)
  | trm_call v m v2 => trm_call (seal_rec k u v) m (seal_rec k u v2)
  end with
seal_rec_lit (k: nat) (u: var) (l: lit): lit :=
  match l with
  | lit_fun T t => lit_fun (seal_rec k u T) (seal_rec_trm (S k) u t)
  | lit_obj T ds =>
    lit_obj
      (seal_rec (S k) u T)
      (seal_rec_defs (S k) u ds)

  end with
seal_rec_def (k: nat) (u: var) (d: def): def :=
  match d with
  | def_typ L T => def_typ L (seal_rec (S k) u T)
  | def_fld m v => def_fld m (seal_rec k u v)
  | def_met m e => def_met m (seal_rec_trm (S (S k)) u e)
  end with
seal_rec_defs (k: nat) (u: var) (ds: defs): defs :=
  match ds with
  | defs_nil       => defs_nil
  | defs_cons tl d => defs_cons (seal_rec_defs k u tl) (seal_rec_def k u d)
  end.

Instance TrmSealable : Sealable trm := seal_rec_trm.

Instance LitSealable : Sealable lit := seal_rec_lit.

Instance DefSealable : Sealable def := seal_rec_def.

Instance DefsSealable : Sealable defs := seal_rec_defs.

Instance TrmAbstractSyntax :
  AbstractSyntax TrmOpenable TrmFreeVar TrmSubstVar := {}.

Instance LitAbstractSyntax :
  AbstractSyntax LitOpenable LitFreeVar LitSubstVar := {}.

Instance DefAbstractSyntax :
  AbstractSyntax DefOpenable DefFreeVar DefSubstVar := {}.

Instance DefsAbstractSyntax :
  AbstractSyntax DefsOpenable DefsFreeVar DefsSubstVar := {}.

Instance DefLabelOf : LabelOf def :=
  fun D =>
      match D with
      | def_typ L _ => label_typ L
      | def_fld m _ => label_fld m
      | def_met m _ => label_met m
      end.

Fixpoint collect_trm {C: Type} (df : C) (f : avar -> C) (comb: C -> C -> C) (t: trm) : C :=
  match t with
  | trm_var a       => (f a)
  | trm_read x m      => (f x)
  | trm_apply f' a      => comb (f f') (f a)
  | trm_let t1 t2    => comb (collect_trm df f comb t1) (collect_trm df f comb t2)
  | trm_lit l t      => comb (collect_lit df f comb l) (collect_trm df f comb t)
  | trm_write x m y    => comb (f x) (f y)
  | trm_call x m y    => comb (f x) (f y)
  end with
collect_lit {C: Type} (df : C) (f : avar -> C) (comb: C -> C -> C) (l: lit) : C :=
  match l with
  | lit_fun T e  => comb (collect df f comb T) (collect_trm df f comb e)
  | lit_obj T ds => comb (collect df f comb T) (collect_defs df f comb ds)
  end with
collect_def {C: Type} (df : C) (f : avar -> C) (comb: C -> C -> C) (d: def) : C :=
  match d with
  | def_typ _ T     => (collect df f comb T)
  | def_fld _ v     => (f v)
  | def_met _ t     => (collect_trm df f comb t)
  end with
collect_defs {C: Type} (df : C) (f : avar -> C) (comb: C -> C -> C) (ds : defs) : C  :=
  match ds with
  | defs_nil         => df
  | defs_cons tl d   => comb (collect_defs df f comb tl) (collect_def df f comb d)
  end.

Instance TrmCollect : Collect AvarAbstractSyntax TrmAbstractSyntax :=
  @collect_trm.

Instance LitCollect : Collect AvarAbstractSyntax LitAbstractSyntax :=
  @collect_lit.

Instance DefCollect : Collect AvarAbstractSyntax DefAbstractSyntax :=
  @collect_def.

Instance DefsCollect : Collect AvarAbstractSyntax DefsAbstractSyntax :=
  @collect_defs.

Fixpoint transform_trm (f : avar -> nat -> avar) (t : trm) (n : nat) : trm :=
  match t with
  | trm_var a      => trm_var (f a n)
  | trm_read v m    => trm_read (f v n) m
  | trm_apply f' a    => trm_apply (f f' n) (f a n)
  | trm_let t1 t2  => trm_let (transform_trm f t1 n) (transform_trm f t2 (S n))
  | trm_lit l t    => trm_lit (transform_lit f l n) (transform_trm f t (S n))
  | trm_write v m v2 => trm_write (f v n) m (f v2 n)
  | trm_call v m v2 => trm_call (f v n) m (f v2 n)
  end with
transform_lit (f : avar -> nat -> avar) (l : lit) (n : nat) : lit :=
  match l with
  | lit_fun T t => lit_fun (transform f T n) (transform_trm f t (S n))
  | lit_obj T ds =>
    lit_obj
      (transform f T (S n))
      (transform_defs f ds (S n))
  end with
transform_def (f : avar -> nat -> avar) (d : def) (n : nat) : def :=
  match d with
  | def_typ L T => def_typ L (transform f T (S n))
  | def_fld m e => def_fld m (f e n)
  | def_met m e => def_met m (transform_trm f e (S (S n)))
  end with
transform_defs (f : avar -> nat -> avar) (ds : defs) (n : nat) : defs :=
  match ds with
  | defs_nil       => defs_nil
  | defs_cons tl d => defs_cons (transform_defs f tl n) (transform_def f d n)
  end.

Instance TrmTransform : Transform AvarAbstractSyntax TrmAbstractSyntax :=
  @transform_trm.

Instance LitTransform : Transform AvarAbstractSyntax LitAbstractSyntax :=
  @transform_lit.

Instance DefTransform : Transform AvarAbstractSyntax DefAbstractSyntax :=
  @transform_def.

Instance DefsTransform : Transform AvarAbstractSyntax DefsAbstractSyntax :=
  @transform_defs.
