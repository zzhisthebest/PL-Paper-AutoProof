Require Import Metalib.Metatheory.

Require Import syntaxb_ott rulesb_inf.

Require Import List.

Import ListNotations.

Require Import Strings.String.

Notation "Γ ⊢ E A" := (Btyping Γ E A) (at level 45).

Notation "[ z ~> u ]' t" := (subst_term u z t) (at level 0).

Notation "t ^^' u"       := (open_term_wrt_term t u) (at level 67).

Notation "t ->* r" := (bsteps t r) (at level 68).
