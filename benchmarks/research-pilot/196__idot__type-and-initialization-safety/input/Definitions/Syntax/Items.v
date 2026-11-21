Set Implicit Arguments.

Require Import Coq.Bool.Bool.

Require Import LibExtra SyntaxClasses.

Require Import Vars TransformCollect Types Terms.

Inductive heap_def : Set :=
  | heap_def_typ  : typ_label -> typ -> heap_def
  | heap_def_trm  : trm_label -> option var -> heap_def.

Notation heap_defs := (list heap_def).

Inductive item : Set :=
  | item_obj : typ -> heap_defs -> item
  | item_lit : lit -> item.

Definition heap_def_of_def (d : def) : heap_def :=
  match d with
  | def_typ A T => heap_def_typ A T
  | def_trm a   => heap_def_trm a None
  end.

Definition heap_defs_of_defs (ds : defs) : heap_defs :=
  List.map heap_def_of_def ds.

Instance HeapDefLabelOf : LabelOf heap_def | 1 :=
  fun hd =>
      match hd with
      | heap_def_typ L _ => label_typ L
      | heap_def_trm m _ => label_trm m
      end.

Definition fv_heap_def (hd: heap_def) : vars :=
  match hd with
  | heap_def_typ _ T        => (fv T)
  | heap_def_trm _ None     => \{}
  | heap_def_trm _ (Some x) => \{ x}
  end.

Instance HeapDefFreeVar : FreeVar heap_def := fv_heap_def.

Fixpoint open_rec_heap_def (k: nat) (u: var) (hd: heap_def)
         {struct hd} : heap_def :=
  match hd with
  | heap_def_typ L T     => heap_def_typ L (open_rec k u T)
  | heap_def_trm m opt_x => heap_def_trm m opt_x
  end.

Instance HeapDefOpenable : Openable heap_def := open_rec_heap_def.

Definition fv_item (v: item) : vars :=
  match v with
  | item_obj T hds    => (fv T) \u (fv hds)
  | item_lit l => (fv l)
  end.

Instance ItemFreeVar : FreeVar item := fv_item.

Definition subst_heap_def (z: var) (u: var) (hd: heap_def)
  : heap_def :=
  match hd with
  | heap_def_typ l t        => heap_def_typ l (subst_var z u t)
  | heap_def_trm l None     => heap_def_trm l None
  | heap_def_trm l (Some x) =>
    heap_def_trm l (Some (subst_fvar z u x))
  end.

Instance HeapDefSubstVar : SubstVar heap_def := subst_heap_def.

Instance HeapDefAbstractSyntax :
  AbstractSyntax HeapDefOpenable HeapDefFreeVar HeapDefSubstVar := {}.

Definition open_rec_item (n: nat) (x: var) (v: item) : item :=
  match v with
  | item_obj T ds    => item_obj (open_rec n x T)
                              (open_rec (S n) x ds)
  | item_lit l => item_lit (open_rec n x l)
  end.

Instance ItemOpenable : Openable item := open_rec_item.

Definition subst_item x y (v: item) : item :=
  match v with
  | item_obj T ds    => item_obj (subst_var x y T) (subst_var x y ds)
  | item_lit l => item_lit (subst_var x y l)
  end.

Instance ItemSubstVar : SubstVar item := subst_item.

Instance ItemAbstractSyntax :
  AbstractSyntax ItemOpenable ItemFreeVar ItemSubstVar := {}.
