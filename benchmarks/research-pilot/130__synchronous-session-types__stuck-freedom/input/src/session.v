From mathcomp Require Import ssreflect.seq all_ssreflect.

Require Import List String Coq.Arith.PeanoNat Relations ZArith Datatypes Setoid Morphisms Coq.Logic.Decidable Coq.Program.Basics Coq.Init.Datatypes.

Import ListNotations.

Open Scope list_scope.

From Paco Require Import paco.

Import ListNotations.

From SST Require Import src.header src.sim src.expr src.process src.local src.global src.balanced src.typecheck src.part src.gttreeh src.step src.merge src.projection.

Inductive session: Type :=
  | s_ind : part   -> process -> session
  | s_par : session -> session -> session.

Notation "p '<--' P"   :=  (s_ind p P) (at level 50, no associativity).

Notation "s1 '|||' s2" :=  (s_par s1 s2) (at level 50, no associativity).

Inductive ForallT (P : part -> process -> Prop) : session -> Prop :=
  | ForallT_mono : forall pt op, P pt op -> ForallT P (pt <-- op)
  | ForallT_par : forall (M1 M2 : session), ForallT P M1 -> ForallT P M2 -> ForallT P (M1 ||| M2).

Fixpoint flattenT (M : session) : (list part) :=
  match M with
    | p <-- _   => p :: nil
    | M1 ||| M2 => flattenT M1 ++ flattenT M2
  end.

Definition InT (pt : part) (M : session) : Prop :=
  In pt (flattenT M).

Inductive unfoldP : relation session :=
  | pc_sub   : forall p P Q M, substitutionP 0 0 0 (p_rec P) P Q -> unfoldP (p <-- (p_rec P) ||| M) (p <-- Q ||| M)
  | pc_subm  : forall p P Q, substitutionP 0 0 0 (p_rec P) P Q -> unfoldP (p <-- (p_rec P)) (p <-- Q)
  | pc_refl  : forall M, unfoldP M M
  | pc_trans : forall M M' M'', unfoldP M M' -> unfoldP M' M'' -> unfoldP M M''
  | pc_par1  : forall M M', unfoldP (M ||| M') (M' ||| M)
  | pc_par2  : forall M M' M'', unfoldP ((M ||| M') ||| M'') (M ||| (M' ||| M''))
  | pc_par1m : forall M M' M'', unfoldP ((M ||| M') ||| M'') ((M' ||| M) ||| M'')
  | pc_par2m : forall M M' M'' M''', unfoldP (((M ||| M') ||| M'') ||| M''') ((M ||| (M' ||| M'')) ||| M''').

Inductive typ_sess : session -> gtt -> Prop :=
  | t_sess : forall M G, wfgC G ->
                         (forall pt, isgPartsC pt G -> InT pt M) ->
                         NoDup (flattenT M) ->
                         ForallT (fun u P => exists T, projectionC G u T /\ typ_proc nil nil P T /\ (forall n, exists m, guardP n m P)) M ->
                         typ_sess M G.

Inductive betaP: relation session :=
  | r_comm  : forall p q xs y l e v Q M,
              onth l xs = Some y -> stepE e (e_val v) ->
              betaP ((p <-- (p_recv q xs)) ||| (q <-- (p_send p l e Q)) ||| M)
                    ((p <-- subst_expr_proc y (e_val v) 0 0) ||| (q <-- Q) ||| M)
  | rt_ite  : forall p e P Q M,
              stepE e (e_val (vbool true)) ->
              betaP ((p <-- (p_ite e P Q)) ||| M) ((p <-- P) ||| M)
  | rf_ite  : forall p e P Q M,
              stepE e (e_val (vbool false)) ->
              betaP ((p <-- (p_ite e P Q)) ||| M) ((p <-- Q) ||| M)
  | r_commu  : forall p q xs y l e v Q,
              onth l xs = Some y -> stepE e (e_val v) ->
              betaP ((p <-- (p_recv q xs)) ||| (q <-- (p_send p l e Q)))
                    ((p <-- subst_expr_proc y (e_val v) 0 0) ||| (q <-- Q))
  | rt_iteu  : forall p e P Q,
              stepE e (e_val (vbool true)) ->
              betaP ((p <-- (p_ite e P Q))) ((p <-- P))
  | rf_iteu  : forall p e P Q,
              stepE e (e_val (vbool false)) ->
              betaP ((p <-- (p_ite e P Q))) ((p <-- Q))
  | r_struct: forall M1 M1' M2 M2', unfoldP M1 M1' -> unfoldP M2' M2 -> betaP M1' M2' -> betaP M1 M2.

Definition beta_multistep := multi betaP.

Inductive multiC : relation gtt :=
  | multiC_refl : forall G, multiC G G
  | multiC_step : forall G1 G2 G3 p q n, gttstepC G1 G2 p q n -> multiC G2 G3 -> multiC G1 G3.

Definition stuck (M : session) := ((exists M', unfoldP M M' /\ ForallT (fun _ P => P = p_inact) M') -> False) /\ ((exists M', betaP M M') -> False).

Definition stuckM (M : session) := exists M', multi betaP M M' /\ stuck M'.
