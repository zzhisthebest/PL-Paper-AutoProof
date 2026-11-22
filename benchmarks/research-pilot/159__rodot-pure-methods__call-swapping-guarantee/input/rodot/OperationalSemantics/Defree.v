Set Implicit Arguments.

Require Import LibExtra DotTactics.

Require Import AbstractSyntax TypingMode GeneralTyping TightTyping RecordTypes InertContext PreciseTyping UnboundSubstitution Weakening Narrowing EWeakening Sealing ConfigTyping TFree Deref Closedness.

Section WithTypingMode.

Context (typing_mode: Mode).

Inductive defree_spec: Type :=


| defree_spec_empty
| defree_spec_subst (d: defree_spec) (x: var) (y: var)
| defree_spec_seal (d: defree_spec) (y: var)
.

Inductive defree_ctx: Type :=
  defree_ctx_with_null (G: ctx) (e: renv) (L: vars) (null: var): defree_ctx.

Definition defree_ctx_fv dfc :=
  match dfc with
  | (defree_ctx_with_null G e L null) =>
    ctx_dom G \u ctx_fv G \u dom e \u fv_env e \u L \u \{ null }
  end.

Inductive defree_ctx_ok: defree_ctx -> Prop :=
  defree_ctx_ok_null G e L null:
    ctx_ok G ->
    ctx_weakens G ->
    ok e ->
    defree_ctx_ok (defree_ctx_with_null G e L null)
with defree_ctx_get: defree_ctx -> ctx -> renv -> Prop :=
  defree_ctx_get_null G e L null:
    defree_ctx_get (defree_ctx_with_null G e L null) G e
with defree_ctx_closed: defree_ctx -> Prop :=
  defree_ctx_closed_null G e L null:
    sealed G ->
    defree_ctx_closed (defree_ctx_with_null G e L null).

Inductive defree_ctx_replacement: defree_ctx -> var -> var -> Prop :=
  defree_ctx_replacement_with_null (G: ctx) (e: renv) (L: vars) (null: var) x:
    x §# G ->
    x \notin (ctx_fv G) ->
    renv_notin x e ->
    x \notin L ->
    x <> null ->
    defree_ctx_replacement (defree_ctx_with_null G e L null) x null
with defree_ctx_null: defree_ctx -> var -> Prop :=
  defree_ctx_null_with_null (G: ctx) (e: renv) (L: vars) (null: var):
    defree_ctx_null (defree_ctx_with_null G e L null) null
with defree_spec_valid: defree_ctx -> defree_spec -> Prop :=
| dfree_spec_valid_empty dfc: defree_spec_valid dfc defree_spec_empty
| dfree_spec_valid_subst (dfc: defree_ctx) (dfs: defree_spec) (x y: var):
    defree_spec_valid dfc dfs ->
    defree_ctx_replacement dfc x y ->
    defree_spec_valid dfc (defree_spec_subst dfs x y)
|   dfree_spec_valid_seal (dfc: defree_ctx) (dfs: defree_spec) (null: var):
    defree_spec_valid dfc dfs ->
    defree_ctx_closed dfc ->
    defree_ctx_null dfc null ->
    defree_spec_valid dfc (defree_spec_seal dfs null)
.

Fixpoint defree_by_rec {A} {SU: SubstVar A} {AO: Sealable A} (n: nat) (dfs: defree_spec) (a: A) :=
  match dfs with

  | defree_spec_empty => a

  | defree_spec_subst dfs x y => ((defree_by_rec n dfs a) /[x -> y])
  | defree_spec_seal dfs y => (seal_rec n y (defree_by_rec n dfs a))
  end.

Notation defree_by:= (defree_by_rec 0) (only parsing).

Fixpoint defree_spec_concat (dfs1 dfs2: defree_spec):=
  match dfs2 with
  | defree_spec_empty => dfs1
  | defree_spec_subst dfs x y => (defree_spec_subst (defree_spec_concat dfs1 dfs) x y)
  | defree_spec_seal dfs y => (defree_spec_seal (defree_spec_concat dfs1 dfs) y)
  end.

Inductive defree {A} {SU: SubstVar A} {AO: Sealable A}: defree_ctx->A->A->Prop :=
| defree_by_spec dfc dfs T1:
    defree_spec_valid dfc dfs ->
    defree dfc T1 (defree_by dfs T1).

Section Defree.

Context {A: Set} {SU: SubstVar A} {ASl: Sealable A} {AF: FreeVar A} {AO: Openable A}.

Context {AS : AbstractSyntax AO AF SU} {AFSC: FvSubstCases AS} {AFSlC: FvSealCases AS ASl} {ASF: SubstFresh AS}.

Context {AOT: OpenTwice AO} {AOC: OpenCommut AO} {ASO: SealOpen AS ASl} {ASC: SealClosed AS ASl} {AFOC: FvOpenCases AS}.

End Defree.

End WithTypingMode.
