From Fsub Require Import Fm_Definitions.

Theorem safety_value_multistep : forall e s e' s' f ns R T,
  sealcomp_store s ns ->
  sealcomp e f ->
  redm e s e' s' ->
  value e' ->
  typing_store empty R ns ->
  typing empty R f T ->
  exists f' ns', sealcomp e' f' /\ sealcomp_store s' ns' /\ value f' /\ redm f ns f' ns'.

Theorem safety_value_multistep' : forall e s f ns f' ns',
  expr f ->
  expr e ->
  well_formed_store s ->
  sealcomp_store s ns ->
  sealcomp e f ->
  redm f ns f' ns' ->
  value f' ->
  (exists e' s', redm e s e' s' /\ sealcomp_store s' ns' /\ sealcomp e' f' /\ value e').
