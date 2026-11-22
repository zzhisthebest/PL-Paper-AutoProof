Set Implicit Arguments.

Require Import LibExtra AbstractSyntax GeneralTyping.
Require Import Transformation TransformationTerm TransformationLifting.
Require Import TransformationConfig TransformationSwapCalls TransformationIterateSim.
Require Import ConfigTyping OperationalSemantics TypedOperationalSemantics.

Section WithTypingMode.

Context (typing_mode: Mode).

Context (Hms : mode_has_sef typing_mode).

Context (Hmm : mode_has_mutability typing_mode).

Theorem swap_calls_transformation_guarantee ta tb Ta Tb:
  〈ctx_empty⁏empty ⊢ ta ∶ Ta〉 ∼(trf_local_idtyp_trm typing_mode (trf_swap_calls_local typing_mode))∼> 〈ctx_empty⁏empty ⊢ tb ∶ Tb〉 ->
  closed ta ->
  closed tb ->
  closed Ta ->
  closed Tb ->

  exists Ca Cb,
    config_initial ta Ca /\
    config_initial tb Cb /\
    (
      ( exists  na nb Ga2 Gb2 Ca2 Cb2,

        nb <= na /\

        ctx_empty ⊢ Ca ∶ Ta ⊣na↦* Ga2 ⊢ Ca2 /\
        ctx_empty ⊢ Cb ∶ Tb ⊣nb↦* Gb2 ⊢ Cb2 /\
        answer Ca2 /\
        answer Cb2 /\

        〈Ga2 ⊢ Ca2 ∶ Ta〉 ∼(trf_lift_sim_conf typing_mode (trf_swap_calls_local typing_mode))∼> 〈Gb2 ⊢ Cb2 ∶ Tb〉
      ) \/ (
         forall (n : nat),
         exists (Ca2 Cb2 : config),
           Ca ⊣n↦* Ca2 /\
           Cb ⊣n↦* Cb2
      )
    ).

End WithTypingMode.
