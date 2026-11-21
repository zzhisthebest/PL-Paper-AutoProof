Set Implicit Arguments.

Require Import LibExtra.

Require Import Coq.Program.Equality.

Require Import AbstractSyntax TypingMode GeneralTyping Indep Equivalence.

Inductive record_dec : dec -> Prop :=
| rd_typ : forall A T, record_dec (dec_typ (typ_label_normal A) T T)
| rd_typb : forall A T, record_dec (dec_typ (typ_label_normal A) typ_bot T)
| rd_fld : forall a T, record_dec (dec_fld a T T)
| rd_met : forall m TC TZ TR, record_dec (dec_met m TC TZ TR)
.

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

Inductive refcap_dec: dec -> Prop :=
  | refcap_dec_typb lt TU:
    refcap_dec (dec_typ (typ_label_refcap lt) typ_bot TU).

Inductive refcap_typ: typ -> fset label -> Prop :=
  | refcap_typ_top:
      refcap_typ typ_top \{}
  | refcap_typ_one D l:
      refcap_dec D ->
      l = label_of D ->
      refcap_typ (typ_rcd D) \{l}
  | refcap_typ_cons T ls D l:
      refcap_typ T ls ->
      refcap_dec D ->
      l = label_of D ->
      l \notin ls ->
      refcap_typ (typ_and T (typ_rcd D)) (union ls \{l}).

Definition refcap_type T := exists ls, refcap_typ T ls.

Inductive record_has: typ -> dec -> Prop :=
| rh_one : forall D,
    record_has (typ_rcd D) D
| rh_andl : forall T U D,
    record_has T D ->
    record_has (typ_and T U) D
| rh_andr : forall T U D,
    record_has U D ->
    record_has (typ_and T U) D.

Section WithTypingMode.

Context (typing_mode: Mode).

End WithTypingMode.
