Require Import Rules.

Set Implicit Arguments.

Require Import Metalib.Metatheory.

Require Import Program.Equality.

Require Export Coq.micromega.Lia.

Notation empty_menv := (@nil (nat * nat)).

Theorem decidability : forall A B E,
{sub E A B} + {~ sub E A B}.
