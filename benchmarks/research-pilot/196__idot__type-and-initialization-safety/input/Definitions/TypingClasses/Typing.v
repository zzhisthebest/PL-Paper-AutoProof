Set Implicit Arguments.

Require Import LibExtra AbstractSyntax PreTyping.

Class DecTyping (A : Set) := dec_typing : ctx -> A -> dec -> Prop.

Notation "Gamma ⊢ d '∶d' D" := (dec_typing Gamma d D) (at level 40, d at level 59).

Class Typing (A : Set) := typing : ctx -> A -> typ -> Prop.

Notation "Gamma ⊢ t '∶' T" := (typing Gamma t T) (at level 40, t at level 59).

Class Typings (A : Set) := typings : ctx -> A -> typs -> Prop.

Notation "Gamma ⊢ t '::' Ts" := (typings Gamma t Ts) (at level 40, t at level 59).

Class Subtyping := subtyping : ctx -> typ -> typ -> Prop.

Notation "Gamma ⊢ T '<:' U" := (subtyping Gamma T U) (at level 40, T at level 59).

Section DecTypingLabels.

Context {A : Set} `{LabelOf A}.

Class DecTypingLabels `(DecTyping A) :=
    ty_def_label_eq :
      forall Gamma d D,
        Gamma ⊢ d ∶d D ->
        label_of D = label_of d.

End DecTypingLabels.

Section DecPreTyping.

Context {A : Set} (TyA : DecTyping A).

Instance DecPreTyping : PreTyping dec_typing := {}.

End DecPreTyping.

Existing Instance DecPreTyping.

Section TyPreTyping.

Context {A : Set} (TyA : Typing A).

Instance TyPreTyping : PreTyping typing := {}.

End TyPreTyping.

Existing Instance TyPreTyping.

Section TysPreTyping.

Context {A : Set} (TysA : Typings A).

Instance TysPreTyping : PreTyping typings := {}.

End TysPreTyping.

Section SubPreTyping.

Context {A : Set} {TysA : Subtyping}.

Instance SubPreTyping : PreTyping subtyping := {}.

End SubPreTyping.

Existing Instance SubPreTyping.

Inductive ty_defs {A : Set} `{LabelOf A} `{DecTyping A} : Typing (list A) :=

| ty_defs_one : forall Gamma d D,
    Gamma ⊢ d ∶d D ->
    Gamma ⊢ cons d nil ∶ typ_rcd D

| ty_defs_cons : forall Gamma ds d T D,
    Gamma ⊢ ds ∶ T ->
    Gamma ⊢ d ∶d D ->
    labels_hasnt ds (label_of d) ->
    Gamma ⊢ cons d ds ∶ typ_and T (typ_rcd D).

Existing Instance ty_defs | 1.

Section DefsWeaken.

Context {A : Set} {TyA: DecTyping A}
          (TyWM: PreTypingWeakenMiddle (DecPreTyping TyA)).

Context `{LabelOf A}.

End DefsWeaken.

Section DefsBndIntro.

Context {A : Set} `{TyA : DecTyping A}
          (TyBIM: PreTypingBndIntroMiddle (DecPreTyping TyA)).

Context `{LabelOf A}.

End DefsBndIntro.
