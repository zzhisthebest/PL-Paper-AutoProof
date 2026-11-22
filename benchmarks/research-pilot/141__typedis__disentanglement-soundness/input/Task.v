From stdpp Require Import relations gmap.
From dislog.lang Require Import syntax semantics reducible disentangled.
From dislog.types Require Import syntactical.

(* Pure operational definitions from src/logic/wpg_adequacy.v. *)
Definition step '(σ,α,G,T,e) '(σ',α',G',T',e') :=
  lang.semantics.step σ α G T e σ' α' G' T' e'.

Definition safe he σ α G T e :=
  (is_val e /\ is_leaf T) \/ reducible he σ α G T e.

Definition always_safe_and_disentangled (allow_oob:bool) (e:expr) :=
  forall t0 σ' α' G' T' e',
  rtc step (∅,∅,{[(t0,t0)]},(Leaf t0),e) (σ',α',G',T',e') ->
  safe allow_oob σ' α' G' T' e' /\ disentangled G' α' T' e'.

Theorem soundness δ e ρ :
  locs e = ∅ ->
  syntactical.typed δ ∅ ∅ ∅ e ρ ->
  always_safe_and_disentangled true e.
