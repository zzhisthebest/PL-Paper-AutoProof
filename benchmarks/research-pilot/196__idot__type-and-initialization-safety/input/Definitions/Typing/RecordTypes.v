Set Implicit Arguments.

Require Import LibExtra.

Require Import Coq.Program.Equality.

Require Import AbstractSyntax Typing.

Implicit Types (ds : defs) (hds : heap_defs).

Inductive record_dec : dec -> Prop :=
| rd_typ : forall A T, record_dec (dec_typ A T T)
| rd_trm : forall a T, record_dec (dec_trm a T T).

Inductive record_typ : typ -> fset label -> Prop :=
| rt_one : forall D l,
  record_dec D ->
  l = label_of D ->
  record_typ (typ_rcd D) \{l}
| rt_cons: forall T ls D l,
  record_typ T ls ->
  record_dec D ->
  l = label_of D ->
  l \notin ls ->
  record_typ (typ_and T (typ_rcd D)) (union ls \{l}).

Definition record_type T := exists ls, record_typ T ls.

Inductive record_has: typ -> dec -> Prop :=
| rh_one : forall D,
    record_has (typ_rcd D) D
| rh_andl : forall T U D,
    record_has T D ->
    record_has (typ_and T U) D
| rh_andr : forall T U D,
    record_has U D ->
    record_has (typ_and T U) D.

Section HasntNotIn.

Context {A : Set} `{LA : LabelOf A} `{DTA : DecTyping A}.

Context {DTL : DecTypingLabels DTA}.

End HasntNotIn.

Section RecordHasTyDefs.

Context {A : Set} `{LA : LabelOf A} `{DTA : DecTyping A}.

End RecordHasTyDefs.
