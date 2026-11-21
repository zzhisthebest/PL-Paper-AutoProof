Require Import Coq.Lists.List.

Require Import Psatz.

Require Import Coq.Arith.Compare_dec.

Require Import Coq.Arith.Peano_dec.

Require Import Coq.Arith.PeanoNat.

Require Import Coq.Bool.Bool.

Require Import FunctionalExtensionality.

Require Import Coq.Logic.PropExtensionality.

Import ListNotations.

Require Import env.

Definition nats := nat -> bool.

Definition n_empty: nats := fun x => false.

Definition n_one (x:nat): nats := fun x' => x' =? x.

Definition n_and q1 q2 (x:nat) := (q1 x) && q2 x.

Definition n_or q1 q2 (x:nat) := (q1 x) || q2 x.

Definition n_diff q1 q2 (x: nat) := (q1 x) && (negb (q2 x)).

Definition n_dom {X} (H: list X) := fun x' =>  x' <? (length H).

Definition n_dom' {X} (H: list (option X)) := fun x' => (x' <? length H) &&
  match indexr x' H with | Some (Some _) => true | _ => false end.

Definition n_sub (q1 q2: nats): Prop := forall x:nat, q1 x = true -> q2 x = true.

Definition n_splice (n: nat) (q: nats) : nats := fun x =>
         if x =? n then false else if x <? n then q x else q (pred x).

Definition n_unsplice (n: nat) (q: nats) : nats := fun x =>
         if x <? n then q x else q (S x).

Definition Nats := nat -> Prop.

Definition N_empty: Nats := fun x => False.

Definition N_one (x:nat): Nats := fun x' => x' = x.

Definition N_and p1 p2 (x:nat) := p1 x /\ p2 x.

Definition N_or p1 p2 (x:nat) := p1 x \/ p2 x.

Definition N_diff p1 p2 (x:nat) := p1 x /\ (p2 x -> False).

Definition N_dom {X} (H: list X) := fun x' =>  x' < (length H).

Definition N_sub (p1 p2: Nats): Prop := forall x:nat, p1 x -> p2 x.

Definition N_lift (b: nats): Nats := fun x => b x = true.

Definition N_splice (n: nat) (q: Nats) : Nats := fun x =>
    (x = n -> False) /\ (x < n -> q x) /\ (x > n -> q (pred x)).

Definition N_unsplice (n: nat) (q: Nats) : Nats := fun x =>
    (x < n -> q x) /\ (~ x < n -> q (S x)).

Definition closed_nats m q := (forall x, q x = true -> x < m).

Definition closed_Nats m (p: nat -> Prop) := (forall x, p x -> x < m).
