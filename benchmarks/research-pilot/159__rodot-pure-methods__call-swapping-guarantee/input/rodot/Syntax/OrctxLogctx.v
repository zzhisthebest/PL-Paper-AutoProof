Set Implicit Arguments.

Require Import LibExtra DotTactics.

Require Import Coq.Program.Equality.

Require Import Types.

Require Import TypeInduction.

Require Import Orctx Logctx Andctx.

Fixpoint orctx_logctx (oc: orctx): logctx :=
  match oc with
  | orctx_nil => logctx_nil
  | orctx_l ocl Tr => logctx_orl (orctx_logctx ocl) Tr
  | orctx_r Tl ocr => logctx_orr Tl (orctx_logctx ocr)
  end.

Definition logctx_isor oc := (exists oco, oc = orctx_logctx oco).

Definition logctx_andor oc := exists oc1 oc2, oc = (logctx_extend (andctx_logctx oc1) (orctx_logctx oc2)).
