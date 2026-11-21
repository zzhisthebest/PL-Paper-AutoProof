Require Export Metalib.Metatheory.

Require Import Definitions.

Require Import Infrastructure.

Require Import Lia.

Theorem preservation : forall P mu mu' e e' dir T,
  P |== mu ->
  typing nil P e dir T ->
  step (e,mu) ((r_e e'), mu') ->
  exists P',
  extends P' P /\
  typing nil P' e' dir T /\
  P' |== mu'.

Theorem progress : forall P mu e dir T,
  P |== mu ->
  typing nil P e dir T ->
  value e \/ exists r mu', step (e, mu) (r, mu').
