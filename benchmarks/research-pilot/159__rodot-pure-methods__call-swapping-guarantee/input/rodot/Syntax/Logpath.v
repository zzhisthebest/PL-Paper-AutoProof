Set Implicit Arguments.

Require Import LibExtra DotTactics.

Require Import Coq.Program.Equality.

Require Import Types.

Require Import Logctx.

Inductive logpath: Set :=
| logpath_nil: logpath
| logpath_orl (oc: logpath): logpath
| logpath_orr (oc: logpath): logpath
| logpath_andl (oc: logpath): logpath
| logpath_andr (oc: logpath): logpath
.

Inductive logpath_typ: typ -> logpath -> typ -> Prop :=
| logpath_typ_nil T:
  logpath_typ T logpath_nil T
| logpath_typ_orl oc T S U:
  logpath_typ T oc U ->
  logpath_typ (typ_or T S) (logpath_orl oc) U
| logpath_typ_orr oc T S U:
  logpath_typ T oc U ->
  logpath_typ (typ_or S T) (logpath_orr oc) U
| logpath_typ_andl oc T S U:
  logpath_typ T oc U ->
  logpath_typ (typ_and T S) (logpath_andl oc) U
| logpath_typ_andr oc T S U:
  logpath_typ T oc U ->
  logpath_typ (typ_and S T) (logpath_andr oc) U
.

Inductive logpath_ctx: typ -> logpath -> logctx -> Prop :=
| logpath_ctx_nil T:
  logpath_ctx T logpath_nil logctx_nil
| logpath_ctx_orl oc T S oc1:
  logpath_ctx T oc oc1 ->
  logpath_ctx (typ_or T S) (logpath_orl oc) (logctx_orl oc1 S)
| logpath_ctx_orr oc T S  oc1:
  logpath_ctx T oc  oc1 ->
  logpath_ctx (typ_or S T) (logpath_orr oc) (logctx_orr S oc1)
| logpath_ctx_andl oc T S  oc1:
  logpath_ctx T oc  oc1 ->
  logpath_ctx (typ_and T S) (logpath_andl oc) (logctx_andl oc1 S)
| logpath_ctx_andr oc T S oc1:
  logpath_ctx T oc  oc1 ->
  logpath_ctx (typ_and S T) (logpath_andr oc) (logctx_andr S oc1)
.

Fixpoint logctx_path(oc: logctx): logpath :=
  match oc with
  | logctx_nil => logpath_nil
  | logctx_orl ocl Tr => logpath_orl (logctx_path ocl)
  | logctx_orr Tl ocr => logpath_orr (logctx_path ocr)
  | logctx_andl ocl Tr => logpath_andl (logctx_path ocl)
  | logctx_andr Tl ocr => logpath_andr (logctx_path ocr)
  end.

Fixpoint logpath_extend (oc oci: logpath): logpath :=
  match oc with
  | logpath_nil => oci
  | logpath_orl ocl => logpath_orl (logpath_extend ocl oci)
  | logpath_orr ocr => logpath_orr (logpath_extend ocr oci)
  | logpath_andl ocl => logpath_andl (logpath_extend ocl oci)
  | logpath_andr ocr => logpath_andr  (logpath_extend ocr oci)
  end.

Inductive logpath_separate: logpath->logpath->Prop :=
| logpath_separate_orl_e oc1 oc2:
  logpath_separate oc1 oc2 ->
  logpath_separate (logpath_orl oc1) (logpath_orl oc2)
| logpath_separate_orr_e oc1 oc2:
  logpath_separate oc1 oc2 ->
  logpath_separate (logpath_orr oc1) (logpath_orr oc2)
| logpath_separate_andl_e oc1 oc2:
  logpath_separate oc1 oc2 ->
  logpath_separate (logpath_andl oc1) (logpath_andl oc2)
| logpath_separate_andr_e oc1 oc2:
  logpath_separate oc1 oc2 ->
  logpath_separate (logpath_andr oc1) (logpath_andr oc2)
| logpath_separate_orl_n oc1 oc2:
  (forall oc3, oc2 <> (logpath_orl oc3) /\ oc2 <> logpath_nil) ->
  logpath_separate (logpath_orl oc1) oc2
| logpath_separate_orr_n oc1 oc2:
  (forall oc3, oc2 <> (logpath_orr oc3) /\ oc2 <> logpath_nil) ->
  logpath_separate (logpath_orr oc1) oc2
| logpath_separate_andl_n oc1 oc2:
  (forall oc3, oc2 <> (logpath_andl oc3) /\ oc2 <> logpath_nil) ->
  logpath_separate (logpath_andl oc1) oc2
| logpath_separate_andr_n oc1 oc2:
  (forall oc3, oc2 <> (logpath_andr oc3) /\ oc2 <> logpath_nil) ->
  logpath_separate (logpath_andr oc1) oc2
.

Inductive logpath_andor := logpath_and | logpath_or.

Definition logpath_andor_l TB op :=
  match TB with
    | logpath_and => logpath_andl op
    | logpath_or => logpath_orl op
  end.

Definition logpath_andor_r TB op :=
  match TB with
    | logpath_and => logpath_andr op
    | logpath_or => logpath_orr op
  end.

Definition logpath_andor_typ TB :=
  match TB with
    | logpath_and => typ_and
    | logpath_or => typ_or
  end.

Definition logpath_andor_ctx_r TB Tl op :=
  match TB with
    | logpath_and => logctx_andr Tl op
    | logpath_or => logctx_orr Tl op
  end.

Definition logpath_andor_ctx_l TB op Tr :=
  match TB with
    | logpath_and => logctx_andl op Tr
    | logpath_or => logctx_orl op Tr
  end.
