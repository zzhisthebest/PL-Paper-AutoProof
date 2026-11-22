Set Implicit Arguments.

Require Import Coq.Program.Equality.

Require Import LibExtra DotTactics.

Require Import AbstractSyntax TypingMode.

Require Import Equivalence GeneralTyping Indep.

Require Import PreciseTyping RecordTypes InertContext EnvCorrespondence.

Require Import TightTyping InertTightSubtyping TightTypingHelpers.

Require Import Orctx Logctx Logpath.

Require Import LayeredCommon LayeredSubtypingAtomic LayeredCapabilityApprox.

Section WithTypingMode.

Context {typing_mode: Mode}.

Inductive ty_has_M G e: typ -> Prop :=




| ty_has_typ_mut TL TU:
  (mode_has_top_nm_complement typing_mode -> forall x : var, G⁏e ⊢# TL /[-> x] <: typ_bot) ->
  ty_has_M G e (typ_rcd (dec_typ (typ_label_refcap typ_refcap_mutability) TL TU))
.

Inductive ty_has_N_atomic (G: ctx) (e: renv): typ -> Prop :=




| ty_has_nocap:
    ty_has_N_atomic G e typ_nocap




| ty_has_fld a TL TU:
    ty_has_N_atomic G e (typ_rcd (dec_fld a TL TU))




| ty_has_met a TC TZ TR:
    ty_has_N_atomic G e (typ_rcd (dec_met a TC TZ TR))




| ty_has_typ_normal A TL TU:
    ty_has_N_atomic G e (typ_rcd (dec_typ (typ_label_normal A) TL TU))

| ty_has_fun T U:
    mode_has_fun typing_mode ->
    ty_has_N_atomic G e (typ_fun T U)
.

Inductive ty_has_top_atomic (G: ctx) (e: renv): typ -> Prop :=
| ty_has_top_atomic_mut TL1 TU1:

  mode_has_mut_top typing_mode ->
  (forall x : var, G⁏e ⊢# TL1/[-> x] <: typ_bot) ->
  (forall x : var, G⁏e ⊢# typ_top <: TU1/[-> x]) ->
  ty_has_top_atomic G e (typ_rcd (dec_typ (typ_label_refcap typ_refcap_mutability) TL1 TU1))
.

Inductive ty_has_N (G: ctx) (e: renv): typ -> Prop :=
| ty_has_N_has_atomic T:
  ty_has_N_atomic G e T ->
  ty_has_N G e T
| ty_has_N_has_top T:
  ty_has_top_atomic G e T ->
  ty_has_N G e T
.

End WithTypingMode.

Section WithTypingMode.

Context {typing_mode: Mode}.

End WithTypingMode.
