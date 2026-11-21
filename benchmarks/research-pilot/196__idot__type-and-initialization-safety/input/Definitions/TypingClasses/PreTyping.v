Set Implicit Arguments.

Require Import LibExtra AbstractSyntax.

Class PreTyping {B : Set} {A : Set} (ty_rel : ctx -> A -> B -> Prop).

Class PreTypingWeakenMiddle {A : Set} {B : Set}
      {ty_rel : ctx -> A -> B -> Prop} (PTy : PreTyping ty_rel) :=
  weaken_middle : forall Gamma1 x T' Gamma2 t T,
      ty_rel (Gamma1 & Gamma2) t T ->
      x # Gamma1 ->
      ty_rel (Gamma1 & x ~ T' & Gamma2) t T.

Class PreTypingBndIntroMiddle {A : Set} {B : Set}
      {ty_rel : ctx -> A -> B -> Prop} (PTy : PreTyping ty_rel) :=
  bnd_intro_middle : forall Gamma1 Gamma2 y T1 t T,
    ty_rel (Gamma1 & y ~ open y T1 & Gamma2) t T ->
    ty_rel (Gamma1 & y ~ typ_bnd T1 & Gamma2) t T.

Section Weakening.

Context {B : Set} {A : Set} {ty_rel : ctx -> A -> B -> Prop}.

Context {PTy : PreTyping ty_rel} {PTyWM : PreTypingWeakenMiddle PTy}.

End Weakening.

Section BndIntro.

Context {B : Set} {A : Set} {ty_rel : ctx -> A -> B -> Prop}.

Context {PTy : PreTyping ty_rel} {PTyWM : PreTypingBndIntroMiddle PTy}.

End BndIntro.
