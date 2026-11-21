Set Implicit Arguments.

Require Import LibExtra.

Require Import Coq.Program.Equality.

Require Import AbstractSyntax RecordTypes InertTypes Typing GeneralTyping.

Implicit Types (ds : defs) (hds : heap_defs).

Section DecTypingRecord.

Context {A : Set}.

Class DecTypingRecord `(DecTyping A) :=
    ty_def_record_dec : forall Gamma d D,
      Gamma ⊢ d ∶d D ->
      record_dec D.

End DecTypingRecord.

Section TyDefsRecordType.

Context {A : Set} `{LA : LabelOf A} `{DTA : DecTyping A}.

Context {DTL : DecTypingLabels DTA}.

Context {DTR : DecTypingRecord DTA}.

End TyDefsRecordType.
