Set Implicit Arguments.

Require Import LibExtra DotTactics AbstractSyntax.

Require Import Context Equivalence Indep GeneralTyping.

Require Import Weakening.

Require Import Transformation Subenvironments.

Inductive TrfContextTy :=
  trfctx_ty (G: ctx)(e: renv): TrfContextTy.

Inductive TrfContextObjTy :=
  trfctx_objty (G: ctx)(Go: objctx)(e: renv): TrfContextObjTy.

Notation "'〈' G '⁏' e '⊢' a '∶' T '〉'" :=
  (typed_elem (trfctx_ty G e) T a) (at level 41, G at level 32, e at level 32).

Notation "'〈' G '§§' Go '⁏' e '⊢' a '∶' T '〉'" :=
  (typed_elem (trfctx_objty G Go e) T a) (at level 41, G at level 32, Go at level 32, e at level 32).

Definition TermTransform := Transform TrfContextTy typ trm.

Definition LitTransform := Transform TrfContextTy typ lit.

Definition DefTransform := Transform TrfContextObjTy dec def.

Definition DefsTransform := Transform TrfContextObjTy typ defs.

Definition TransformCondOk T A (TEa: TypedElement TrfContextTy T A) :=
  match TEa with
    〈Ga⁏ea ⊢ a ∶ Ta〉 => (ctx_ok Ga /\ ok ea)
  end.

Definition TransformCondObjOk T A (TEa: TypedElement TrfContextObjTy T A) :=
  match TEa with
    〈Ga§§Goa⁏ea ⊢ a ∶ Ta〉 => (ctx_ok (Ga §§& Goa) /\ ok ea)
  end.

Definition TransformIsAnswerTerm (TEa: TypedElement TrfContextTy typ trm) :=
  match TEa with
    〈_ ⊢ t ∶ _〉 => exists vb, t = (trm_var (avar_f vb))
  end.

Definition TransformCondTyping AT (A:Set) (TY: TypingProperty A AT) (TEa: TypedElement TrfContextTy AT A) :=
  match TEa with
    〈G⁏e ⊢ t ∶ T〉 => TY G objctx_empty e t T
  end.

Definition TransformCondObjTyping AT (A:Set) (TY: TypingProperty A AT) (TEa: TypedElement TrfContextObjTy AT A) :=
  match TEa with
    〈G§§Go⁏e ⊢ t ∶ T〉 => TY G Go e t T
  end.

Section WithTypingMode.

Context (typing_mode: Mode).

Definition TransformCondTermTyped := TransformCondTyping (@obj_typing trm _).

Definition TransformCondLitTyped := TransformCondTyping (@obj_typing lit _).

Definition TransformCondDefTyped := TransformCondObjTyping (@obj_dec_typing def _).

Definition TransformCondDefsTyped := TransformCondObjTyping (@obj_typing defs _).

End WithTypingMode.

Inductive TransformWeakening T A: Transform TrfContextTy T A :=
  trf_weaken Ga1 Ga2 Ga3 ea (a: A) Ta:
    ctx_weakens Ga2 ->
    ctx_ok (Ga1 §& Ga2 §& Ga3) ->
    ok ea ->
    TransformWeakening (〈Ga1 §& Ga3⁏ea ⊢ a ∶ Ta〉) (〈Ga1 §& Ga2 §& Ga3⁏ea ⊢ a ∶ Ta〉).

Inductive TransformObjWeakening T A: Transform TrfContextObjTy T A :=
  trf_obj_weaken Ga1 Ga2 Ga3 Go ea (a: A) Ta:
    ctx_weakens Ga2 ->
    ctx_ok (Ga1 §& Ga2 §& Ga3 §§& Go) ->
    ok ea ->
    TransformObjWeakening (〈Ga1 §& Ga3 §§ Go⁏ea ⊢ a ∶ Ta〉) (〈Ga1 §& Ga2 §& Ga3 §§ Go⁏ea ⊢ a ∶ Ta〉).

Notation TransformWeakeningCompat T A trf := (@TransformCondCompat  TrfContextTy T A (@TransformCondTypeIdentical TrfContextTy T A ) trf (@TransformWeakening T A)).

Notation TransformObjWeakeningCompat T A trf := (@TransformCondCompat  TrfContextObjTy T A (@TransformCondTypeIdentical TrfContextObjTy T A ) trf (@TransformObjWeakening T A)).

Inductive TransformEWeakening T A: Transform TrfContextTy T A :=
  trf_eweaken Ga (e1 e2 e3: renv) (a: A) Ta:
    ctx_ok Ga ->
    ok (e1 & e2 & e3) ->
    TransformEWeakening (〈Ga⁏(e1 & e3) ⊢ a ∶ Ta〉) (〈Ga⁏(e1 & e2 & e3) ⊢ a ∶ Ta〉).

Inductive TransformObjEWeakening T A: Transform TrfContextObjTy T A :=
  trf_obj_eweaken Ga Go (e1 e2 e3: renv) (a: A) Ta:
    ctx_ok (Ga §§& Go) ->
    ok (e1 & e2 & e3) ->
    TransformObjEWeakening (〈Ga §§ Go⁏(e1 & e3) ⊢ a ∶ Ta〉) (〈Ga §§ Go⁏(e1 & e2 & e3) ⊢ a ∶ Ta〉).

Notation TransformEWeakeningCompat T A trf := (@TransformCondCompat  TrfContextTy T A (@TransformCondTypeIdentical TrfContextTy T A ) trf (@TransformEWeakening T A)).

Notation TransformObjEWeakeningCompat T A trf := (@TransformCondCompat  TrfContextObjTy T A (@TransformCondTypeIdentical TrfContextObjTy T A ) trf (@TransformObjEWeakening T A)).

Inductive TransformWknCtxPush T A: Transform TrfContextTy T A :=
  trf_wkn_ctx_push Ga ea (a: A) Ta x vk Tx:
    ctx_ok Ga ->
    x §# Ga ->
    ok ea ->
    TransformWknCtxPush (〈Ga⁏ea ⊢ a ∶ Ta〉) (〈Ga  § x / vk ~ Tx⁏ea ⊢ a ∶ Ta〉).

Inductive TransformWknEnvPush T A: Transform TrfContextTy T A :=
  trf_wkn_env_push Ga ea (a: A) Ta x xy:
    ctx_ok Ga ->
    ok ea ->
    x # ea ->
    TransformWknEnvPush (〈Ga⁏ea ⊢ a ∶ Ta〉) (〈Ga⁏ea & x ~ xy ⊢ a ∶ Ta〉).

Notation TransformWknCtxPushCompat T A trf := (@TransformCondCompat  TrfContextTy T A (@TransformCondTypeIdentical TrfContextTy T A ) trf (@TransformWknCtxPush T A)).

Notation TransformWknEnvPushCompat T A trf := (@TransformCondCompat  TrfContextTy T A (@TransformCondTypeIdentical TrfContextTy T A ) trf (@TransformWknEnvPush T A)).

Inductive TransformSealing T A {TS: Sealable T} {AS: Sealable A} (x: var): Transform TrfContextTy T A :=
  trf_seal G e (a: A) Ta:
    TransformSealing x (〈G⁏e ⊢ a ∶ Ta〉) (〈seal x G⁏e ⊢ seal x a ∶ seal x Ta〉).

Inductive TransformObjSealing T A {TS: Sealable T} {AS: Sealable A} (x: var): Transform TrfContextObjTy T A :=
  trf_obj_seal G Go e (a: A) Ta:
    TransformObjSealing x (〈G§§Go⁏e ⊢ a ∶ Ta〉) (〈seal x G §§ seal x Go⁏e ⊢ seal x a ∶ seal x Ta〉).

Notation TransformSealingCompat T A trf := (forall x, (@TransformCondCompat  TrfContextTy T A (@TransformCondTypeIdentical TrfContextTy T A ) trf (@TransformSealing T A _ _ x))).

Notation TransformObjSealingCompat T A trf := (forall x, (@TransformCondCompat  TrfContextObjTy T A (@TransformCondTypeIdentical TrfContextObjTy T A ) trf (@TransformObjSealing T A _ _ x))).

Inductive TransformUnhiding T A: Transform TrfContextTy T A :=
  trf_unhide G1 G2 e (a: A) Ta:
    TransformUnhiding (〈((ctx_hide G1) §& G2)⁏e ⊢ a ∶ Ta〉) (〈(G1 §& G2)⁏e ⊢  a ∶ Ta〉).

Inductive TransformObjUnhiding T A: Transform TrfContextObjTy T A :=
  trf_obj_unhide G1 G2 Go e (a: A) Ta:
    TransformObjUnhiding (〈((ctx_hide G1) §& G2)§§Go⁏e ⊢ a ∶ Ta〉) (〈(G1 §& G2)§§ Go⁏e ⊢ a ∶ Ta〉).

Notation TransformUnhidingCompat T A trf := (@TransformCondCompat  TrfContextTy T A (@TransformCondTypeIdentical TrfContextTy T A ) trf (@TransformUnhiding T A )).

Notation TransformObjUnhidingCompat T A trf := (@TransformCondCompat  TrfContextObjTy T A (@TransformCondTypeIdentical TrfContextObjTy T A ) trf (@TransformObjUnhiding T A )).

Section WithTypingMode.

Context (typing_mode: Mode).

Inductive TransformNarrowing T A: Transform TrfContextTy T A :=
  trf_narrow Ga1 x vk (Txa Txb: typ) Ga2 (e: renv) (a: A) Ta:
    ctx_ok (Ga1 § x / vk ~ Txa §& Ga2) ->
    ok e ->
    Ga1⁏e ⊢ Txb <: Txa ->
    TransformNarrowing (〈Ga1 § x / vk ~ Txa §& Ga2⁏e ⊢ a ∶ Ta〉) (〈Ga1 § x / vk ~ Txb §& Ga2 ⁏e ⊢ a ∶ Ta〉).

Inductive TransformObjNarrowing T A: Transform TrfContextObjTy T A :=
  trf_obj_narrow Ga1 x vk Txa Txb Ga2 Go (e: renv) (a: A) Ta:
    ctx_ok (Ga1 § x / vk ~ Txa §& Ga2 §§& Go) ->
    ok e ->
    Ga1⁏e ⊢ Txb <: Txa ->
    TransformObjNarrowing (〈Ga1 § x / vk ~ Txa §& Ga2 §§ Go⁏e ⊢ a ∶ Ta〉) (〈Ga1 § x / vk ~ Txb §& Ga2 §§ Go ⁏e ⊢ a ∶ Ta〉).

Inductive TransformNarrowingSubctx T A: Transform TrfContextTy T A :=
  trf_narrow_subctx G1 G2 (e: renv) (a: A) Ta:
    ok e ->
    e ⊢ G2 ⪯ G1 ->
    TransformNarrowingSubctx (〈G1 ⁏e ⊢ a ∶ Ta〉) (〈G2 ⁏e ⊢ a ∶ Ta〉).

Inductive TransformObjNarrowingSubctx T A: Transform TrfContextObjTy T A :=
  trf_obj_narrow_subctx G1 G2 Go (e: renv) (a: A) Ta:
    ok e ->
    e ⊢ G2 ⪯ G1 ->
    TransformObjNarrowingSubctx (〈G1 §§ Go⁏e ⊢ a ∶ Ta〉) (〈G2 §§ Go ⁏e ⊢ a ∶ Ta〉).

End WithTypingMode.

Notation TransformNarrowingCompat typing_mode T A trf := (@TransformCondCompat  TrfContextTy T A (@TransformCondTypeIdentical TrfContextTy T A ) trf (@TransformNarrowing typing_mode T A)).

Notation TransformObjNarrowingCompat typing_mode T A trf := (@TransformCondCompat  TrfContextObjTy T A (@TransformCondTypeIdentical TrfContextObjTy T A ) trf (@TransformObjNarrowing typing_mode T A)).

Notation TransformNarrowingSubctxCompat typing_mode T A trf := (@TransformCondCompat  TrfContextTy T A (@TransformCondTypeIdentical TrfContextTy T A ) trf (@TransformNarrowingSubctx typing_mode T A)).

Notation TransformObjNarrowingSubctxCompat typing_mode T A trf := (@TransformCondCompat  TrfContextObjTy T A (@TransformCondTypeIdentical TrfContextObjTy T A ) trf (@TransformObjNarrowingSubctx typing_mode T A)).

Section WithTypingMode.

Context (typing_mode: Mode).

Context (T A: Set) {AS: SubstVar A} {TS: SubstVar T}.

Inductive TransformSubst  (y: var) (S: typ): Transform TrfContextTy T A :=
  trf_subst G1 x vk G2 e (a: A) (Ta: T):
    ctx_ok (G1 § x / vk ~ S §& G2) ->
    x \notin ctx_fv G1 ->
    renv_notin x e ->
    G1 §& G2 /[§ x -> y] ⁏e ⊢ y ∶ S /[x -> y] ->
    (mode_has_visibility typing_mode ->
      ctx_vis (G1 § x / vk ~ S §& G2) x ->
      ctx_vis (G1 §& G2 /[§ x -> y]) y
    ) ->
    TransformSubst y S (〈(G1 § x / vk ~ S §& G2)⁏ (e & x ~ y)  ⊢ a ∶ Ta〉) (〈(G1 §& G2 /[§x->y])⁏e ⊢ a/[x->y] ∶ Ta/[x->y]〉).

Inductive TransformObjSubst (y: var) (S: typ): Transform TrfContextObjTy T A :=
  trf_obj_subst G1 x vk G2 Go e (a: A) (Ta: T):
    ctx_ok (G1 § x / vk ~ S §& G2 §§& Go) ->
    x \notin ctx_fv G1 ->
    renv_notin x e ->
    G1 §& G2 /[§ x -> y] ⁏e ⊢ y ∶ S /[x -> y] ->
    (mode_has_visibility typing_mode ->
      ctx_vis (G1 § x / vk ~ S §& G2 §§& Go) x ->
      ctx_vis (G1 §& G2 /[§ x -> y] §§& Go /[§§x->y]) y
    ) ->
    TransformObjSubst y S (〈(G1 § x / vk ~ S §& G2) §§ Go⁏ (e & x ~ y)  ⊢ a ∶ Ta〉) (〈(G1 §& G2 /[§x->y]) §§ Go /[§§x->y]⁏e ⊢ a/[x->y] ∶ Ta/[x->y]〉).

End WithTypingMode.

Notation TransformSubstCompat typing_mode T A trf := (forall (y: var) (S: typ), (@TransformCondCompat  TrfContextTy T A (@TransformCondTypeIdentical TrfContextTy T A ) trf (@TransformSubst typing_mode T A _ _ y S))).

Notation TransformObjSubstCompat typing_mode T A trf := (forall (y: var) (S: typ), (@TransformCondCompat  TrfContextObjTy T A (@TransformCondTypeIdentical TrfContextObjTy T A ) trf (@TransformObjSubst typing_mode T A _ _ y S))).
