Set Implicit Arguments.

Require Import LibExtra DotTactics.

Require Import AbstractSyntax TypingMode GeneralTyping Env.

Require Import Coq.Program.Equality.

Class Subctx := subctx: renv -> ctx -> ctx -> Prop.

Notation "e ⊢ G1 ⪯  G2" := (subctx e G1 G2) (at level 40, G1 at level 59).

Section WithTypingMode.

Context (typing_mode: Mode).

Inductive subctx0: Subctx :=
| subctx_empty e: e ⊢ ctx_empty ⪯  ctx_empty
| subctx_grow: forall e G G' x vk T T',
    e ⊢ G ⪯ G' ->
    ctx_ok (G § x / vk ~ T) ->
    (G⁏e ⊢ T <: T') ->
    e ⊢ G § x / vk ~ T ⪯ G' § x / vk ~ T'
| subctx_stop: forall e G G',
    e ⊢ G ⪯ G' ->
    e ⊢ ctx_stop G ⪯ ctx_stop G'
| subctx_hide: forall e G G',
    e ⊢ G ⪯ G' ->
    e ⊢ ctx_hide G ⪯ ctx_hide G'
.

End WithTypingMode.

#[export] Existing Instance subctx0.

Section WithTypingMode.

Context (typing_mode: Mode).

End WithTypingMode.
