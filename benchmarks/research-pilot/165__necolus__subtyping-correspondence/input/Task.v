Require Import Metalib.Metatheory.

Require Import syntax_ott.

Require Import List.

Import ListNotations.

Definition applyfs (fs : ls) (A : styp) :=
  fold_right (fun el acc =>
                match el with
                | st_ty A => styp_arrow A acc
                | st_la l => styp_rcd l acc
                end) A fs.

Theorem ASub2sub : forall fs A B c,
    ASub fs A B c -> sub A (applyfs fs B) c.

Theorem sub2ASub : forall A B c,
    sub A B c -> exists c', ASub nil A B c'.
