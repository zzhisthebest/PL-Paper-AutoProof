Set Implicit Arguments.

Require Import LibExtra DotTactics.

Require Import Coq.Program.Equality.

Require Import Types.

Require Import TypeInduction.

Inductive orctx: Set :=
| orctx_nil: orctx
| orctx_l (oc: orctx) (T:typ): orctx
| orctx_r (T:typ) (oc: orctx): orctx
.

Fixpoint orctx_typ (oc: orctx) (T:typ): typ :=
  match oc with
  | orctx_nil => T
  | orctx_l ocl Tr => (typ_or (orctx_typ ocl T) Tr)
  | orctx_r Tl ocr => (typ_or Tl (orctx_typ ocr T))
  end.

Fixpoint orctx_extend (oc oci: orctx): orctx :=
  match oc with
  | orctx_nil => oci
  | orctx_l ocl Tr => orctx_l (orctx_extend ocl oci) Tr
  | orctx_r Tl ocr => orctx_r Tl (orctx_extend ocr oci)
  end.

Fixpoint orctx_height (oc: orctx): nat :=
  match oc with
  | orctx_nil => 0
  | orctx_l ocl Tr => S (orctx_height ocl)
  | orctx_r Tl ocr => S (orctx_height ocr)
  end.

Inductive orctx_separate: orctx->orctx->Prop :=
| orctx_separate_l oc1 oc2 Tr:
  orctx_separate oc1 oc2 ->
  orctx_separate (orctx_l oc1 Tr) (orctx_l oc2 Tr)
| orctx_separate_r oc1 oc2 Tl:
  orctx_separate oc1 oc2 ->
  orctx_separate (orctx_r Tl oc1) (orctx_r Tl oc2)
| orctx_separate_lr oc1 oc2 Tl Tr:
  orctx_separate (orctx_l oc1 Tr) (orctx_r Tl oc2)
| orctx_separate_rl oc1 oc2 Tl Tr:
  orctx_separate (orctx_r Tl oc1) (orctx_l oc2 Tr).

Inductive orctx_follow: orctx->orctx->Prop :=
| orctx_follow_nil :
  orctx_follow orctx_nil orctx_nil
| orctx_follow_l oc1 oc2 Tr1 Tr2:
  orctx_follow oc1 oc2 ->
  orctx_follow (orctx_l oc1 Tr1) (orctx_l oc2 Tr2)
| orctx_follow_r oc1 oc2 Tl1 Tl2:
  orctx_follow oc1 oc2 ->
  orctx_follow (orctx_r Tl1 oc1) (orctx_r Tl2 oc2)
.

Fixpoint orctx_common_prefix (oc1 oc2: orctx): orctx :=
  match oc1 with
  | orctx_nil => orctx_nil
  | orctx_l ocl1 Tr1 =>
    match oc2 with
    | orctx_nil => orctx_nil
    | orctx_l ocl2 Tr2 => If Tr1 = Tr2 then (orctx_l (orctx_common_prefix ocl1 ocl2) Tr1) else orctx_nil
    | orctx_r Tl2 ocr2 => orctx_nil
    end
  | orctx_r Tl1 ocr1 =>
    match oc2 with
    | orctx_nil => orctx_nil
    | orctx_l ocl2 Tr2 => orctx_nil
    | orctx_r Tl2 ocr2 => If Tl1 = Tl2 then (orctx_r Tl1 (orctx_common_prefix ocr1 ocr2)) else orctx_nil
    end
  end.
