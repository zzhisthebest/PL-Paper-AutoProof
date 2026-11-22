Set Implicit Arguments.

Require Import LibExtra DotTactics.

Require Import Coq.Program.Equality.

Require Import Types.

Require Import Logctx OrctxLogctx Logpath.

Inductive logpath_le: logpath -> logpath -> Prop :=
| logpath_le_nil_l op:
    logpath_le logpath_nil op
| logpath_le_and opl opr:
    logpath_le (logpath_andl opl) (logpath_andr opr)
| logpath_le_or opl opr:
    logpath_le (logpath_orl opl) (logpath_orr opr)
| logpath_le_andl opl opr:
    logpath_le opl opr ->
    logpath_le (logpath_andl opl) (logpath_andl opr)
| logpath_le_andr opl opr:
    logpath_le opl opr ->
    logpath_le (logpath_andr opl) (logpath_andr opr)
| logpath_le_orl opl opr:
    logpath_le opl opr ->
    logpath_le (logpath_orl opl) (logpath_orl opr)
| logpath_le_orr opl opr:
    logpath_le opl opr ->
    logpath_le (logpath_orr opl) (logpath_orr opr)
.

Inductive logpath_re: logpath -> logpath -> Prop :=
| logpath_re_nil_l op:
    logpath_re logpath_nil op
| logpath_re_and opl opr:
    logpath_re (logpath_andr opl) (logpath_andl opr)
| logpath_re_or opl opr:
    logpath_re (logpath_orr opl) (logpath_orl opr)
| logpath_re_andl opl opr:
    logpath_re opl opr ->
    logpath_re (logpath_andl opl) (logpath_andl opr)
| logpath_re_andr opl opr:
    logpath_re opl opr ->
    logpath_re (logpath_andr opl) (logpath_andr opr)
| logpath_re_orl opl opr:
    logpath_re opl opr ->
    logpath_re (logpath_orl opl) (logpath_orl opr)
| logpath_re_orr opl opr:
    logpath_re opl opr ->
    logpath_re (logpath_orr opl) (logpath_orr opr)
.

Definition logctx_le (ocl ocr: logctx) := logpath_le (logctx_path ocl) (logctx_path ocr).

Definition logctx_re (ocl ocr: logctx) := logpath_re (logctx_path ocl) (logctx_path ocr).

Fixpoint logctx_leb (ocl ocr: logctx): logctx :=
match ocl, ocr with
| logctx_nil, _ => logctx_nil
| logctx_orl oc T, logctx_nil => logctx_nil
| logctx_orl oc T, logctx_orl ocp U => logctx_orl (logctx_leb oc ocp) T
| logctx_orl oc T, _ => logctx_orl oc T
| logctx_andl oc T, logctx_nil => logctx_nil
| logctx_andl oc T, logctx_orl ocp U => logctx_orl ocp U
| logctx_andl oc T, logctx_andl ocp U => logctx_andl (logctx_leb oc ocp) T
| logctx_andl oc T, _ => logctx_andl oc T
| logctx_orr T oc, logctx_nil => logctx_nil
| logctx_orr T oc, logctx_orl ocp U => logctx_orl ocp U
| logctx_orr T oc, logctx_andl ocp U => logctx_andl ocp U
| logctx_orr T oc, logctx_orr U ocp => logctx_orr T (logctx_leb oc ocp)
| logctx_orr T oc, _ => logctx_orr T oc
| logctx_andr T oc, logctx_nil => logctx_nil
| logctx_andr T oc, logctx_orl ocp U => logctx_orl ocp U
| logctx_andr T oc, logctx_andl ocp U => logctx_andl ocp U
| logctx_andr T oc, logctx_orr U ocp => logctx_orr U ocp
| logctx_andr T oc, logctx_andr U ocp => logctx_andr T (logctx_leb oc ocp)
end.

Require Import Orctx.

Definition orctx_path oc := (logctx_path (orctx_logctx oc)).

Definition orctx_le (ocl ocr: orctx) := logpath_le (orctx_path ocl) (orctx_path ocr).

Definition orctx_re (ocl ocr: orctx) := logpath_re (orctx_path ocl) (orctx_path ocr).

Fixpoint orctx_leb (ocl ocr: orctx): orctx :=
match ocl, ocr with
| orctx_nil, oc => orctx_nil
| orctx_l oc T, orctx_nil => orctx_nil
| orctx_l oc T, orctx_r U ocp => orctx_l oc T
| orctx_l oc T, orctx_l ocp U => orctx_l (orctx_leb oc ocp) T
| orctx_r T oc, orctx_nil => orctx_nil
| orctx_r T oc, orctx_l ocp U => orctx_l ocp U
| orctx_r T oc, orctx_r U ocp => orctx_r T (orctx_leb oc ocp)
end.
