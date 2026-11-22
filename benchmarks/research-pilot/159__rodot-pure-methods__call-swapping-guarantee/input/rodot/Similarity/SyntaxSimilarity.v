Set Implicit Arguments.

Require Import Coq.Init.Datatypes.

Require Import LibExtra DotTactics.

Require Import Coq.Program.Equality.

Require Import AbstractSyntax Similarity Defs.

Require Import HeapUpdate Deref.

Instance similar_var: Similar var := similar_by_subst.
Instance similar_avar: Similar avar := (@similar_by_subst avar _ _).
Instance similar_typ: Similar typ := (@similar_by_subst typ _ _).
Instance similar_dec: Similar dec := (@similar_by_subst dec _ _).
Instance similar_trm: Similar trm := (@similar_by_subst trm _ _).
Instance similar_defs: Similar defs := (@similar_by_subst defs _ _).
Instance similar_def: Similar def := (@similar_by_subst def _ _).
Instance similar_lit: Similar lit := (@similar_by_subst lit _ _).
Instance similar_item: Similar item := (@similar_by_subst item _ _).
Instance similar_frame: Similar frame := similar_by_subst.
Instance similar_stack: Similar stack := (@similar_by_subst stack _ _).

Instance similar_with_heap: SimilarWith heap := similar_env_with similar_item.
Instance similar_heap: Similar heap := similar_env.
Instance similar_with_renv: SimilarWith renv := similar_env_with similar_var.
Instance similar_renv: Similar renv := similar_env.

Section SimilarOpen.

Context {A: Set}
  {AS: SubstVar A}{AF: FreeVar A}{AO: Openable A}{AAS: AbstractSyntax AO AF AS}
  {ASC: SubstCommut AAS}{ASOC: SubstOpenCommut AAS}
  {AFOC: FvOpenCases AAS}{AFC: FvSubstCases AAS}{ASF: SubstFresh AAS}.

Let SA: Similar A := similar_by_subst.

Context {ASI: SubstId AAS}.

End SimilarOpen.
