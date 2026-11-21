Require Import Syntax Notations Helpers Typing Subtyping Bigstep ViewpointAdaptation.

From Stdlib Require Import List.

From Stdlib Require String.

Import ListNotations.

Theorem preservation_pico :
  forall CT sΓ mt rΓ h stmt rΓ' h' sΓ'
    (Hwf     : wf_r_config CT sΓ rΓ h)
    (Htyping : stmt_typing CT sΓ mt stmt sΓ')
    (Heval   : eval_stmt CT rΓ h stmt OK rΓ' h'),
    wf_r_config CT sΓ' rΓ' h'.

Theorem well_typed_no_mutation_exp :
  forall CT sΓ mt rΓ h stmt rΓ' h' sΓ'
    (Hwf : wf_r_config CT sΓ rΓ h)
    (Htyping : stmt_typing CT sΓ mt stmt sΓ')
    (Heval : eval_stmt CT rΓ h stmt MUTATIONEXP rΓ' h'),
    False.
