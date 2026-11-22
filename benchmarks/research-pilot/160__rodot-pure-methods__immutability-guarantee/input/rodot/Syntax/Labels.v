Set Implicit Arguments.

Require Import Coq.Strings.String.

Definition typ_normal_label: Set := string.

Definition fld_label: Set := string.

Definition met_label: Set := string.

Inductive typ_refcap_label: Set :=

| typ_refcap_mutability
.

Inductive typ_label: Set :=
| typ_label_normal: typ_normal_label -> typ_label
| typ_label_refcap: typ_refcap_label -> typ_label
.

Notation typ_label_mutability := (typ_label_refcap typ_refcap_mutability) (only parsing).

Inductive label: Set :=
| label_typ: typ_label -> label
| label_fld: fld_label -> label
| label_met: met_label -> label
.

Class LabelOf (A : Set) := label_of : A -> label.

Arguments label_of _ _ !_ /.
