From mathcomp Require Import ssreflect.seq all_ssreflect.

Require Import List String Coq.Arith.PeanoNat Relations ZArith Datatypes Setoid Morphisms Coq.Logic.Decidable Coq.Program.Basics Coq.Init.Datatypes.

Import ListNotations.

Open Scope list_scope.

From Paco Require Import paco.

Import ListNotations.

From SST Require Import src.header src.sim src.expr src.process src.local src.global src.balanced src.typecheck src.part src.gttreeh src.step src.merge src.projection src.session.

Theorem stuck_free : forall M G, typ_sess M G -> stuckM M -> False.
