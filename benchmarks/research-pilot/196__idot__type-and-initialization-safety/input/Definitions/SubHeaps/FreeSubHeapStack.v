Set Implicit Arguments.

Require Import LibExtra AbstractSyntax.

Require Import Effects CommittedSubHeap FreeSubHeapSingle.

Definition all_notin {A} (xs ys : fset A) :=
  forall x, x \in xs -> x \notin ys.

Fixpoint list_dom_union {A} (Es : list (env A)) :=
  match Es with
  | nil => \{}
  | (E :: Es)%list => dom E \u list_dom_union Es
  end.

Inductive free_sub_heaps :
  ctx -> init_ctx -> heap -> list eff_ctx -> Prop :=

| free_sub_heaps_nil : forall Gamma Delta Sigma,
    well_committed_heap Gamma Delta Sigma ->
    free_sub_heaps Gamma Delta Sigma nil

| free_sub_heaps_cons : forall Gamma Delta Sigma ℰ ℰs,
    all_notin (dom ℰ) (list_dom_union ℰs) ->
    free_sub_heap ℰ Sigma Delta ->
    free_sub_heaps Gamma Delta Sigma ℰs ->
    free_sub_heaps Gamma Delta Sigma (ℰ :: ℰs).
