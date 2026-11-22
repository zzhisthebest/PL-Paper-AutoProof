From Fsub.CaptureTrack Require Import Fsub_LetSum_Definitions.

Theorem capture_prediction : forall E u Q U,
  value u ->
  typing E u (qtyp_qtyp Q U) ->
  subqual E (fv_exp_for_qua u) Q.
