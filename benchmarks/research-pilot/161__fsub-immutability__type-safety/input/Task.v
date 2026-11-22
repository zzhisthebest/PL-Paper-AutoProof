From Fsub Require Import Fm_Definitions.

Theorem preservation : forall E R e s e' s' T,
  typing E R e T ->
  typing_store E R s ->
  red e s e' s' ->
  exists R', wf_sig E (R' ++ R) /\
    typing E (R' ++ R) e' T /\
    typing_store E (R' ++ R) s'
with preservation_record : forall E R r s r' s' T,
  typing_record_comp E R r T ->
  typing_store E R s ->
  red_record_comp r s r' s' ->
  exists R', wf_sig E (R' ++ R) /\
    typing_record_comp E (R' ++ R) r' T /\
    typing_store E (R' ++ R) s'.

Theorem progress : forall e s R T,
  typing empty R e T ->
  typing_store empty R s ->
  value e \/ exists e' s', red e s e' s'
with progress_record_comp : forall r s R T,
  typing_record_comp empty R r T ->
  typing_store empty R s ->
  value_record_comp r \/ exists r' s', red_record_comp r s r' s'.
