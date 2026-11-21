From Stdlib Require Import List.

From Stdlib Require String.

Import ListNotations.

Require Import Syntax Notations Helpers Typing Subtyping Bigstep ViewpointAdaptation Reachability ConcreteState.

Theorem abstract_state_preservation :
  forall CT sΓ mt rΓ h stmt rΓ' h' sΓ' root C0 vals0 l C qr vals f
    (Himm_root : runtime_getObj h root = Some (mkObj (mkruntime_type Imm_r C0) vals0))
    (Hreach : reachable_abs CT h root l)
    (Hwf : wf_r_config CT sΓ rΓ h)
    (Htyping : stmt_typing CT sΓ mt stmt sΓ')
    (Heval : eval_stmt CT rΓ h stmt OK rΓ' h')
    (Hobj : runtime_getObj h l = Some (mkObj (mkruntime_type qr C) vals))
    (Hprotected : sf_assignability_rel CT C f Final \/
                  sf_assignability_rel CT C f RDA),
    exists vals',
      runtime_getObj h' l = Some (mkObj (mkruntime_type qr C) vals') /\
      nth_error vals f = nth_error vals' f.
