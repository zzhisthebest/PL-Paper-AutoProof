Set Implicit Arguments.

Require Import LibExtra.

Require Export SyntaxClasses TransformCollect.

Require Export Vars Context Labels Types Terms Stack Objctx Envs Heap Env AbstractMachine.

Fixpoint get_def(l: label)(ds: defs): option def :=
match ds with
| defs_nil => None
| defs_cons ds' d => If label_of d = l then Some d else get_def l ds'
end.

Definition defs_has(ds: defs)(d: def) := get_def (label_of d) ds = Some d.

Definition defs_hasnt(ds: defs)(l: label) := get_def l ds = None.

Inductive lit_item_fun : item -> lit -> Prop :=
  | lit_item_fun_c : forall T t,
    lit_item_fun (item_fun t) (lit_fun T t).

Inductive lit_item_obj : item -> lit -> Prop :=
  | lit_item_obj_c : forall T ds,
    lit_item_obj (item_obj ds) (lit_obj T ds).
