Set Implicit Arguments.

Require Import LibExtra.

Require Import AbstractSyntax PreTyping Typing GeneralTyping.

Class DecTySubstMiddle {A : Set} `{SubstVar A} `(DecTyping A) :=
  dec_ty_subst_middle : forall y S G1 G2 x d D,
    x # G2 ->
    G1 & x ~ S & G2 ⊢ d ∶d D ->
    x \notin fv_env G1 ->
    G1 & (subst_env x y G2) ⊢ trm_var (avar_f y) ∶ subst_var x y S ->
    G1 & (subst_env x y G2) ⊢ subst_var x y d ∶d subst_var x y D.

Class TySubstMiddle {A : Set} `{SubstVar A} `(Typing A) :=
  ty_subst_middle : forall y S G1 G2 x t T,
    x # G2 ->
    G1 & x ~ S & G2 ⊢ t ∶ T ->
    x \notin fv_env G1 ->
    G1 & (subst_env x y G2) ⊢ trm_var (avar_f y) ∶ subst_var x y S ->
    G1 & (subst_env x y G2) ⊢ subst_var x y t ∶ subst_var x y T.

Class TysSubstMiddle {A : Set} `{SubstVar A} `(Typings A) :=
  tys_subst_middle : forall y S G1 G2 x ts Ts,
    x # G2 ->
    G1 & x ~ S & G2 ⊢ ts :: Ts ->
    x \notin fv_env G1 ->
    G1 & (subst_env x y G2) ⊢ trm_var (avar_f y) ∶ subst_var x y S ->
    G1 & (subst_env x y G2) ⊢ subst_var x y ts :: subst_var x y Ts.

Section TySubstMiddleLemmas.

Context {A : Set} {SA: SubstVar A}.

Section DecTy.

Context {DT: DecTyping A} {H : @DecTySubstMiddle A SA DT}.

End DecTy.

Section Ty.

Context {Ty: Typing A} {H : @TySubstMiddle A SA Ty}.

Context {OA: Openable A} {FA: FreeVar A}.

Context {AS: AbstractSyntax OA FA SA}.

Context {SI: SubstIntro AS}.

Context {TW: PreTypingWeakenMiddle (TyPreTyping Ty)}.

End Ty.

Section Tys.

Context {Tys: Typings A} {H : @TysSubstMiddle A SA Tys}.

End Tys.

End TySubstMiddleLemmas.

Section DefsTySubstMiddle.

Context {A : Set} {SA: SubstVar A} {L: LabelOf A}.

Context {SL: SubstLabel SA L}.

Context {DT: DecTyping A} {DTS: @DecTySubstMiddle A SA DT}.

End DefsTySubstMiddle.
