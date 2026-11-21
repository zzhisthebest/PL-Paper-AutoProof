Set Implicit Arguments.

Require Import LibExtra AbstractSyntax.

Require Import PreTyping Typing GeneralTyping Weakening.

Require Import Initialization InitTyping.

Implicit Types (i : init_typ) (t : trm) (l : lit) (avs : avars).

Class InitTypingWeakenMiddle {A : Set} `(InitTyping A) :=
  init_weaken_middle : forall Gamma1 x T' Gamma3 Delta1 i' Delta3 vs vs' (t : A) i,
    Gamma1 & Gamma3 ⸴ Delta1 & Delta3 ⸴ vs ⊢i t ∶ i ->
    x # Gamma1 ->
    x # Delta1 ->
    Gamma1 & x ~ T' & Gamma3 ⸴ Delta1 & x ~ i' & Delta3 ⸴ vs \u vs' ⊢i t ∶ i.

Class InitTypingWeakenOkMiddle {A : Set} `(InitTyping A) :=
  init_weaken_ok_middle : forall Gamma1 Gamma2 Gamma3 Delta1 Delta2 Delta3 vs vs' (t : A) i,
    Gamma1 & Gamma3 ⸴ Delta1 & Delta3 ⸴ vs ⊢i t ∶ i ->
    ok (Gamma1 & Gamma2) ->
    ok (Delta1 & Delta2) ->
    Gamma1 & Gamma2 & Gamma3 ⸴ Delta1 & Delta2 & Delta3 ⸴ vs \u vs' ⊢i t ∶ i.

Section InitWeaken.

Context {A : Set} `{ITyA : InitTyping A}.

Section Weaken.

Context {ITyWM : InitTypingWeakenMiddle ITyA}.

End Weaken.

Section WeakenOk.

Context {ITyWM : InitTypingWeakenOkMiddle ITyA}.

End WeakenOk.

End InitWeaken.

Class CommitTypingWeakenMiddleG {A : Set} `(CommitTyping A) :=
  commit_weaken_middle_G : forall Gamma1 x T' Gamma3 Delta (t : A),
    Gamma1 & Gamma3 ⸴ Delta ⊢c t ->
    x # Gamma1 ->
    Gamma1 & x ~ T' & Gamma3 ⸴ Delta ⊢c t.

Class CommitTypingWeakenMiddleD {A : Set} `(CommitTyping A) :=
  commit_weaken_middle_D : forall Gamma Delta1 x i' Delta3 (t : A),
    Gamma ⸴ Delta1 & Delta3 ⊢c t ->
    x # Delta1 ->
    Gamma ⸴ Delta1 & x ~ i' & Delta3 ⊢c t.

Section CommitWeaken.

Context {A : Set} `{ITyA : CommitTyping A}.

Section Weaken.

Context {ITyWMG : CommitTypingWeakenMiddleG ITyA}.

Context {ITyWMD : CommitTypingWeakenMiddleD ITyA}.

End Weaken.

End CommitWeaken.
