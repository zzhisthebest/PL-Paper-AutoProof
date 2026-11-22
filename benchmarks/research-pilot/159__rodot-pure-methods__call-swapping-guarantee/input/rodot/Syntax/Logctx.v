Set Implicit Arguments.

Require Import LibExtra DotTactics.

Require Import Coq.Program.Equality.

Require Import Types.

Require Import TypeInduction.

Inductive logctx: Set :=
| logctx_nil: logctx
| logctx_orl (oc: logctx) (T:typ): logctx
| logctx_orr (T:typ) (oc: logctx): logctx
| logctx_andl (oc: logctx) (T:typ): logctx
| logctx_andr (T:typ) (oc: logctx): logctx
.

Fixpoint logctx_typ (oc: logctx) (T:typ): typ :=
  match oc with
  | logctx_nil => T
  | logctx_orl ocl Tr => (typ_or (logctx_typ ocl T) Tr)
  | logctx_orr Tl ocr => (typ_or Tl (logctx_typ ocr T))
  | logctx_andl ocl Tr => (typ_and (logctx_typ ocl T) Tr)
  | logctx_andr Tl ocr => (typ_and Tl (logctx_typ ocr T))
  end.

Fixpoint logctx_extend (oc oci: logctx): logctx :=
  match oc with
  | logctx_nil => oci
  | logctx_orl ocl Tr => logctx_orl (logctx_extend ocl oci) Tr
  | logctx_orr Tl ocr => logctx_orr Tl (logctx_extend ocr oci)
  | logctx_andl ocl Tr => logctx_andl (logctx_extend ocl oci) Tr
  | logctx_andr Tl ocr => logctx_andr Tl (logctx_extend ocr oci)
  end.

Fixpoint logctx_height (oc: logctx): nat :=
  match oc with
  | logctx_nil => 0
  | logctx_orl ocl Tr => S (logctx_height ocl)
  | logctx_orr Tl ocr => S (logctx_height ocr)
  | logctx_andl ocl Tr => S (logctx_height ocl)
  | logctx_andr Tl ocr => S (logctx_height ocr)
  end.

Definition logctx_typ_separate T1 T2 := ((forall oc2, T1 <> logctx_typ oc2 T2) /\ (forall oc1, T2 <> logctx_typ oc1 T1)).

Inductive logctx_follow: logctx->logctx->Prop :=
| logctx_follow_nil :
  logctx_follow logctx_nil logctx_nil
| logctx_follow_orl oc1 oc2 Tr1 Tr2:
  logctx_follow oc1 oc2 ->
  logctx_follow (logctx_orl oc1 Tr1) (logctx_orl oc2 Tr2)
| logctx_follow_orr oc1 oc2 Tl1 Tl2:
  logctx_follow oc1 oc2 ->
  logctx_follow (logctx_orr Tl1 oc1) (logctx_orr Tl2 oc2)
| logctx_follow_andl oc1 oc2 Tr1 Tr2:
  logctx_follow oc1 oc2 ->
  logctx_follow (logctx_andl oc1 Tr1) (logctx_andl oc2 Tr2)
| logctx_follow_andr oc1 oc2 Tl1 Tl2:
  logctx_follow oc1 oc2 ->
  logctx_follow (logctx_andr Tl1 oc1) (logctx_andr Tl2 oc2)
.

Inductive logctx_separate: logctx->logctx->Prop :=
| logctx_separate_orl_e oc1 oc2 Tr:
  logctx_separate oc1 oc2 ->
  logctx_separate (logctx_orl oc1 Tr) (logctx_orl oc2 Tr)
| logctx_separate_orr_e oc1 oc2 Tl:
  logctx_separate oc1 oc2 ->
  logctx_separate (logctx_orr Tl oc1) (logctx_orr Tl oc2)
| logctx_separate_andl_e oc1 oc2 Tr:
  logctx_separate oc1 oc2 ->
  logctx_separate (logctx_andl oc1 Tr) (logctx_andl oc2 Tr)
| logctx_separate_andr_e oc1 oc2 Tl:
  logctx_separate oc1 oc2 ->
  logctx_separate (logctx_andr Tl oc1) (logctx_andr Tl oc2)
| logctx_separate_orl_n oc1 oc2 Tr:
  (forall oc3 Tr3, oc2 <> (logctx_orl oc3 Tr3) /\ oc2 <> logctx_nil) ->
  logctx_separate (logctx_orl oc1 Tr) oc2
| logctx_separate_orr_n oc1 oc2 Tl:
  (forall oc3 Tl3, oc2 <> (logctx_orr Tl3 oc3) /\ oc2 <> logctx_nil) ->
  logctx_separate (logctx_orr Tl oc1) oc2
| logctx_separate_andl_n oc1 oc2 Tr:
  (forall oc3 Tr3, oc2 <> (logctx_andl oc3 Tr3) /\ oc2 <> logctx_nil) ->
  logctx_separate (logctx_andl oc1 Tr) oc2
| logctx_separate_andr_n oc1 oc2 Tl:
  (forall oc3 Tl3, oc2 <> (logctx_andr Tl3 oc3) /\ oc2 <> logctx_nil) ->
  logctx_separate (logctx_andr Tl oc1) oc2
.

Inductive typ_log: typ -> Prop :=
| typ_log_notlog T:
  typ_notlog T ->
  typ_log T
| typ_log_log T1 T2 TB:
  typ_log T1 ->
  typ_log T2 ->
  typ_andor TB ->
  typ_log (TB T1 T2).
