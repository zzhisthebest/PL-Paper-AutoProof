From oadt Require Import lang_oadt.base.

From oadt Require Import lang_oadt.syntax.

Import syntax.notations.

Implicit Types (b : bool).

Inductive wval : expr -> Prop :=
| WUnitV : wval <{ () }>
| WLit b : wval <{ lit b }>
| WPair v1 v2 : wval v1 -> wval v2 -> wval <{ (v1, v2) }>
| WAbs l τ e : wval <{ \:{l}τ => e }>
| WInj b τ v : wval v -> wval <{ inj@b<τ> v }>
| WFold X v : wval v -> wval <{ fold<X> v }>
| WBoxedLit b : wval <{ [b] }>
| WBoxedInj b ω v : otval ω -> oval v -> wval <{ [inj@b<ω> v] }>
| WIf b v1 v2 :
    wval v1 -> wval v2 ->
    wval <{ ~if [b] then v1 else v2 }>
.

Inductive woval : expr -> Prop :=
| OWUnitV : woval <{ () }>
| OWBoxedLit b : woval <{ [b] }>
| OWPair v1 v2 : woval v1 -> woval v2 -> woval <{ (v1, v2) }>
| OWBoxedInj b ω v : otval ω -> oval v -> woval <{ [inj@b<ω> v] }>
| OWIf b v1 v2 :
    woval v1 -> woval v2 ->
    woval <{ ~if [b] then v1 else v2 }>
.

Inductive ovalty : expr -> expr -> Prop :=
| OTUnit : ovalty <{ () }> <{ 𝟙 }>
| OTOBool b : ovalty <{ [b] }> <{ ~𝔹 }>
| OTProd v1 v2 ω1 ω2 :
    ovalty v1 ω1 -> ovalty v2 ω2 ->
    ovalty <{ (v1, v2) }> <{ ω1 * ω2 }>
| OTOSum b v ω1 ω2 :
    ovalty v <{ ite b ω1 ω2 }> ->

    otval <{ ite b ω2 ω1 }> ->
    ovalty <{ [inj@b<ω1 ~+ ω2> v] }> <{ ω1 ~+ ω2 }>
.

Variant ectx : (expr -> expr) -> Prop :=
| CtxProd1 τ2 : ectx (fun τ1 => <{ τ1 * τ2 }>)
| CtxProd2 ω1 : otval ω1 -> ectx (fun τ2 => <{ ω1 * τ2 }>)
| CtxOSum1 τ2 : ectx (fun τ1 => <{ τ1 ~+ τ2 }>)
| CtxOSum2 ω1 : otval ω1 -> ectx (fun τ2 => <{ ω1 ~+ τ2 }>)
| CtxApp1 v2 : wval v2 -> ectx (fun e1 => <{ e1 v2 }>)
| CtxApp2 e1 : ectx (fun e2 => <{ e1 e2 }>)
| CtxLet e2 : ectx (fun e1 => <{ let e1 in e2 }>)
| CtxSec : ectx (fun e => <{ s𝔹 e }>)
| CtxIf e1 e2 : ectx (fun e0 => <{ if e0 then e1 else e2 }>)
| CtxOIf1 e1 e2 : ectx (fun e0 => <{ ~if e0 then e1 else e2 }>)
| CtxOIf2 v0 e2 : wval v0 -> ectx (fun e1 => <{ ~if v0 then e1 else e2 }>)
| CtxOIf3 v0 v1 : wval v0 -> wval v1 -> ectx (fun e2 => <{ ~if v0 then v1 else e2 }>)
| CtxPair1 e2 : ectx (fun e1 => <{ (e1, e2) }>)
| CtxPair2 v1 : wval v1 -> ectx (fun e2 => <{ (v1, e2) }>)
| CtxProj b : ectx (fun e => <{ π@b e }>)
| CtxInj b τ : ectx (fun e => <{ inj@b<τ> e }>)
| CtxOInj1 b e : ectx (fun τ => <{ ~inj@b<τ> e }>)
| CtxOInj2 b ω : otval ω -> ectx (fun e => <{ ~inj@b<ω> e }>)
| CtxCase e1 e2: ectx (fun e0 => <{ case e0 of e1 | e2 }>)
| CtxOCase e1 e2: ectx (fun e0 => <{ ~case e0 of e1 | e2 }>)
| CtxFold X : ectx (fun e => <{ fold<X> e }>)
| CtxUnfold X : ectx (fun e => <{ unfold<X> e }>)
| CtxTape : ectx (fun e => <{ tape e }>)
| CtxMux1 e1 e2 : ectx (fun e0 => <{ mux e0 e1 e2 }>)
| CtxMux2 v0 e2 : wval v0 -> ectx (fun e1 => <{ mux v0 e1 e2 }>)
| CtxMux3 v0 v1 : wval v0 -> wval v1 -> ectx (fun e2 => <{ mux v0 v1 e2 }>)
.

Variant lectx : (expr -> expr) -> Prop :=
| LCtxApp v2 : wval v2 -> lectx (fun e1 => <{ e1 v2 }>)
| LCtxSec : lectx (fun e => <{ s𝔹 e }>)
| LCtxIf e1 e2 : lectx (fun e0 => <{ if e0 then e1 else e2 }>)
| LCtxProj b : lectx (fun e => <{ π@b e }>)
| LCtxCase e1 e2: lectx (fun e0 => <{ case e0 of e1 | e2 }>)
| LCtxUnfold X : lectx (fun e => <{ unfold<X> e }>)
.

Section step.

Context (Σ : gctx).

Reserved Notation "e '-->!' e'" (at level 40).

Inductive step : expr -> expr -> Prop :=
| SApp l τ e v :
    wval v ->
    <{ (\:{l}τ => e) v }> -->! <{ e^v }>
| SLet v e :
    wval v ->
    <{ let v in e }> -->! <{ e^v }>
| SIf b e1 e2 :
    <{ if b then e1 else e2 }> -->! <{ ite b e1 e2 }>
| SCase b τ v e1 e2 :
    wval v ->
    <{ case inj@b<τ> v of e1 | e2 }> -->! <{ ite b (e1^v) (e2^v) }>
| SProj b v1 v2 :
    wval v1 -> wval v2 ->
    <{ π@b (v1, v2) }> -->! <{ ite b v1 v2 }>
| SUnfold X X' v :
    wval v ->
    <{ unfold<X> (fold <X'> v) }> -->! v
| SFun x T e :
    Σ !! x = Some (DFun T e) ->
    <{ gvar x }> -->! <{ e }>
| SOADT X τ' τ v :
    wval v ->
    Σ !! X = Some (DOADT τ' τ) ->
    <{ (gvar X) v }> -->! <{ τ^v }>
| SSec b :
    <{ s𝔹 b }> -->! <{ [b] }>
| SOInj b ω v :
    otval ω -> oval v ->
    <{ ~inj@b<ω> v }> -->! <{ [inj@b<ω> v] }>
| SMux b v1 v2 :
    wval v1 -> wval v2 ->
    <{ mux [b] v1 v2 }> -->! <{ ite b v1 v2 }>

| SOCase b ω1 ω2 v e1 e2 v1 v2 :
    oval v ->
    ovalty v1 ω1 -> ovalty v2 ω2 ->
    <{ ~case [inj@b<ω1 ~+ ω2> v] of e1 | e2 }> -->!
      <{ ~if [b] then (ite b (e1^v) (e1^v1)) else (ite b (e2^v2) (e2^v)) }>
| STapeOIf b v1 v2 :
    woval v1 -> woval v2 ->
    <{ tape (~if [b] then v1 else v2) }> -->! <{ mux [b] (tape v1) (tape v2) }>
| STapePair v1 v2 :
    woval v1 -> woval v2 ->
    <{ tape (v1, v2) }> -->! <{ (tape v1, tape v2) }>

| STapeUnitV :
    <{ tape () }> -->! <{ () }>
| STapeBoxedLit b :
    <{ tape [b] }> -->! <{ [b] }>
| STapeBoxedInj b ω v :
    otval ω -> oval v ->
    <{ tape [inj@b<ω> v] }> -->! <{ [inj@b<ω> v] }>
| SOIf b v1 v2 ℇ :
    lectx ℇ ->
    wval v1 -> wval v2 ->
    ℇ <{ ~if [b] then v1 else v2 }> -->! <{ ~if [b] then ,(ℇ v1) else ,(ℇ v2) }>

| SCtx ℇ e e' :
    ectx ℇ ->
    e -->! e' ->
    ℇ e -->! ℇ e'

where "e '-->!' e'" := (step e e').

End step.

Module notations.

Notation "Σ '⊨' e '-->!' e'" := (step Σ e e') (at level 40,
                                                e custom oadt at level 0,
                                                e' custom oadt at level 0).

Notation "Σ '⊨' e '-->*' e'" := (rtc (step Σ) e e')
                                  (at level 40,
                                   e custom oadt at level 0,
                                   e' custom oadt at level 0).

Notation "Σ '⊨' e '-->{' n '}' e'" := (nsteps (step Σ) n e e')
                                        (at level 40,
                                         e custom oadt at level 0,
                                         n constr at level 0,
                                         e' custom oadt at level 0,
                                         format "Σ  '⊨'  e  '-->{' n '}'  e'").

End notations.
