Set Implicit Arguments.

Require Import LibExtra DotTactics.

Require Import Coq.Program.Equality.

Require Import AbstractSyntax TypingMode Equivalence GeneralTyping.

Require Import PreciseTyping RecordTypes InertContext TightTyping Subenvironments Narrowing InertTightSubtyping EnvCorrespondence Indep Weakening Orctx Logctx Logpath.

Require Import LayeredCommon.

Section WithTypingMode.

Context {typing_mode: Mode}.

Inductive subtyp_atomic: ctx -> renv -> typ -> typ -> Prop :=

| subtyp_atomic_fun : forall L G e S T S' T',
  mode_has_fun typing_mode ->
  G⁏e ⊢# S' <: S ->
  (forall y, y \notin L ->
   G § y / v_par ~ S' ⁏e ⊢ open y T <: open y T') ->
  subtyp_atomic G e ( typ_fun S T ) ( typ_fun S' T')





| subtyp_atomic_fld : forall G e a TL1 TL2 TU1 TU2,
  G⁏e ⊢# TL2 <: TL1 ->
  G⁏e ⊢# TU1 <: TU2 ->
  subtyp_atomic G e (typ_rcd (dec_fld a TL1 TU1)) (typ_rcd (dec_fld a TL2 TU2))






| subtyp_atomic_typ : forall G e A TL1 TL2 TU1 TU2 ,
  (forall y, G⁏e ⊢# open y TL2 <: open y TL1) ->
  (forall y, G⁏e ⊢# open y TU1 <: open y TU2) ->
  subtyp_atomic G e  (typ_rcd (dec_typ A TL1 TU1)) (typ_rcd (dec_typ A TL2 TU2))








| subtyp_atomic_met : forall L G e  m TC1 TZ1 TR1 TC2 TZ2 TR2,
  G⁏e ⊢# TZ2 <: TZ1 ->
  (forall y, y \notin L ->
   G § y / v_par ~ TZ2 ⁏e ⊢ open y TC2 <: open y TC1) ->

  (mode_has_sef typing_mode -> typ_indep_b 0 TC2 -> typ_indep_b 0 TC1) ->
  (forall y, y \notin L ->
   forall z, z <> y -> z \notin L ->
   G § y / v_par ~ TZ2 § z / v_recv ~ (open y TC2) ⁏e ⊢ open y (open_rec 1 z TR1) <: open y (open_rec 1 z TR2) ) ->
  subtyp_atomic G e (typ_rcd (dec_met m TC1 TZ1 TR1)) (typ_rcd (dec_met m TC2 TZ2 TR2))
.

End WithTypingMode.
