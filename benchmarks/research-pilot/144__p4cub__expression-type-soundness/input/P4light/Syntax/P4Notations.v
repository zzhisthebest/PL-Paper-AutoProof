Require Import Coq.Lists.List.

Require Import Coq.Strings.String.

Require Import Poulet4.P4light.Syntax.P4String.

Require Import VST.zlist.Zlist.

Notation "! s" := (P4String.Build_t _ _ s%string) (only printing, format "! s", at level 1, no associativity).

Notation "!! s" := (P4String.Build_t _ _ s%string) (only parsing, at level 1, no associativity).

Notation "! s" := (P4String.Build_t _ default s%string) (only parsing, at level 1, no associativity).

Notation "![ x ; .. ; y ]" := (cons (P4String.Build_t _ _ x%string) .. (cons (P4String.Build_t _ _ y%string) nil) .. )
    (only printing, format "![ x ;  .. ;  y ]", at level 1, no associativity).

Notation "!![ x ; .. ; y ]" := (cons (P4String.Build_t _ _ x%string) .. (cons (P4String.Build_t _ _ y%string) nil) .. )
    (only parsing, at level 1, no associativity).

Notation "![ x ; .. ; y ]" := (cons (P4String.Build_t _ default x%string) .. (cons (P4String.Build_t _ default y%string) nil) .. )
    (only parsing, at level 1, no associativity).
