Set Implicit Arguments.

Require Import Definitions.

Inductive wf_env : env -> Prop :=

| wf_nil : wf_env nil

| wf_cons : forall {x T G}, x \notin fv T \u fv G ->
                       fv T [<=] dom G ->
                       wf_env G ->
                       lc T ->
                       wf_env (x ~ T ++ G).

Definition is_sel (T : typ) :=
    match T with
    | typ_sel _ => True
    | _ => False
    end.
