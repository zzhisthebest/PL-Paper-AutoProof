Set Implicit Arguments.

Require Import LibExtra DotTactics.

Require Import Coq.Program.Equality.

Require Import Types TypeInduction.

Require Import Logctx.

Inductive andctx: Set :=
| andctx_nil: andctx
| andctx_l (oc: andctx) (T:typ): andctx
| andctx_r (T:typ) (oc: andctx): andctx
.

Fixpoint andctx_typ (oc: andctx) (T:typ): typ :=
  match oc with
  | andctx_nil => T
  | andctx_l ocl Tr => (typ_and (andctx_typ ocl T) Tr)
  | andctx_r Tl ocr => (typ_and Tl (andctx_typ ocr T))
  end.

Fixpoint andctx_logctx (oc: andctx): logctx :=
  match oc with
  | andctx_nil => logctx_nil
  | andctx_l ocl Tr => logctx_andl (andctx_logctx ocl) Tr
  | andctx_r Tl ocr => logctx_andr Tl (andctx_logctx ocr)
  end.

Definition logctx_isand oc := (exists oco, oc = andctx_logctx oco).
