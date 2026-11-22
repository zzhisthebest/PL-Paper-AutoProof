Set Implicit Arguments.

Require Import Coq.Bool.Bool.

Require Import LibExtra SyntaxClasses.

Require Import Vars TransformCollect Types Terms Envs.

Inductive item : Set :=
  | item_obj: defs -> item
  | item_fun: trm -> item.

Definition fv_item (v: item) : vars :=
  match v with
  | item_obj ds => (fv ds)
  | item_fun t => (fv t)
  end.

Instance ItemFreeVar : FreeVar item := fv_item.

Definition open_rec_item (n: nat) (x: var) (v: item) : item :=
  match v with
  | item_obj ds => item_obj (open_rec n x ds)
  | item_fun t => item_fun (open_rec (S n) x t)
  end.

Instance ItemOpenable : Openable item := open_rec_item.

Definition subst_item x y (v: item) : item :=
  match v with
  | item_obj ds => item_obj (subst_var x y ds)
  | item_fun t => item_fun (subst_var x y t)
  end.

Instance ItemSubstVar : SubstVar item := subst_item.

Instance ItemAbstractSyntax :
  AbstractSyntax ItemOpenable ItemFreeVar ItemSubstVar := {}.

Definition seal_rec_item (n: nat) (x: var) (v: item) : item :=
  match v with
  | item_obj ds => item_obj (seal_rec n x ds)
  | item_fun t => item_fun (seal_rec (S n) x t)
  end.

Instance ItemSealable : Sealable item := seal_rec_item.

Definition collect_item {C: Type} (df : C) (f : avar -> C) (comb: C -> C -> C) (it: item) : C :=
  match it with
  | item_obj ds => (collect df f comb ds)
  | item_fun t => (collect df f comb t)
  end.

Instance ItemCollect : Collect AvarAbstractSyntax ItemAbstractSyntax :=
  @collect_item.

Definition transform_item (f : avar -> nat -> avar) (it : item) (n : nat) : item :=
  match it with
  | item_obj ds => (item_obj (transform f ds n))
  | item_fun t => (item_fun (transform f t (S n)))
  end.

Instance ItemTransform : Transform AvarAbstractSyntax ItemAbstractSyntax :=
  @transform_item.

Notation heap := (env item).

Notation fv_heap Sigma := ((@dom item Sigma) \u (fv_env Sigma)).

Definition subst_heap x y : heap -> heap := map (subst_var x y).

Notation subheap_unchanged S1 S2 :=
  (forall y itm, binds y itm S1 -> binds y itm S2) (only parsing).

Class Fields (A: Type) :=
  fields: A -> vars.

Definition fields_def d: vars :=
  match d with
    | def_typ A T => \{}
    | def_met a t => \{}
    | def_fld a (avar_f x) => \{x}
    | def_fld a (avar_b n) => \{}
  end.

Instance FieldsDef: Fields def := fields_def.

Fixpoint fields_defs ds: vars :=
  match ds with
    | defs_nil => \{}
    | defs_cons ds d => (fields_defs ds) \u (fields d)
  end.

Instance FieldsDefs: Fields defs := fields_defs.

Fixpoint fields_item it: vars :=
  match it with
    | item_fun f => \{}
    | item_obj ds => (fields ds)
  end.

Instance FieldsItem: Fields item := fields_item.

Fixpoint fields_heap (S: heap) : vars :=
  match S with
    | nil%list => \{}
    | ((y,ds)::E)%list => (fields_heap E) \u (fields ds)
  end.

Instance FieldsHeap: Fields heap := fields_heap.

Class FieldsInFv (A: Set) {AF: Fields A}{AV: FreeVar A} :=
  fields_in_fv (a: A): fields a \c fv a.
