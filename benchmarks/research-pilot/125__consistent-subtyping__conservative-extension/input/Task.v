From TLC Require Import LibLN.

Require Import DeclDef DeclInfra DeclProp.

Require Import Translation.

Require Import PBCDef PBCInfra.

Require Import DeclTyping DeclSub.

Require Import OLDef.

Theorem conservative_extension: forall E e T,
    denv_static E ->
    dterm_static e ->
    dtyp_static T ->
    otyping E e T ->
    exists A, dtyping E e A /\ dsub E A T.
