From mathcomp Require Import ssreflect.seq all_ssreflect.

Require Import List String Coq.Arith.PeanoNat Relations ZArith Datatypes Setoid Morphisms Coq.Logic.Decidable Coq.Program.Basics Coq.Init.Datatypes.

Import ListNotations.

Open Scope list_scope.

From Paco Require Import paco.

Import ListNotations.

From SST Require Import src.header src.sim src.expr src.process src.local src.global.

Inductive gtth: Type :=
  | gtth_hol    : fin -> gtth
  | gtth_send   : part -> part -> list (option (sort * gtth)) -> gtth.

Section gtth_ind_ref.

Variable P : gtth -> Prop.

End gtth_ind_ref.

Inductive typ_gtth : list (option gtt) -> gtth -> gtt -> Prop :=
  | gt_hol : forall n ctx gc, onth n ctx = Some gc -> typ_gtth ctx (gtth_hol n) gc
  | gt_send : forall ctx p q xs ys, SList xs -> List.Forall2 (fun u v => (u = None /\ v = None) \/
                                                (exists s g g', u = Some(s, g) /\ v = Some(s, g') /\ typ_gtth ctx g g')) xs ys ->
                                                typ_gtth ctx (gtth_send p q xs) (gtt_send p q ys).

Section typ_gtth_ind_ref.

Variable P : list (option gtt) -> gtth -> gtt -> Prop.

End typ_gtth_ind_ref.
