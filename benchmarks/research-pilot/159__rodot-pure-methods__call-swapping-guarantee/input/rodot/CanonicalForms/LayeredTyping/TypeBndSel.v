Set Implicit Arguments.

Require Import LibExtra DotTactics.

Require Import Coq.Program.Equality.

Require Import AbstractSyntax TypingMode Equivalence GeneralTyping.

Require Import PreciseTyping RecordTypes InertContext TightTyping Subenvironments Narrowing InertTightSubtyping EnvCorrespondence Indep Weakening Orctx Logctx Logpath LogpathOrder.

Require Import TypeInduction TypLogicInduction.

Definition typ_notbndsel T :=
  (forall oc x A y, T <> logctx_typ oc (typ_sel x A y)) /\
  (forall oc U, T <> logctx_typ oc (typ_bnd U)).

Fixpoint typ_bndsel_count (T: typ): nat :=
  match T with
  | typ_and T1 T2 => (typ_bndsel_count T2) + (typ_bndsel_count T1)
  | typ_or T1 T2 => (typ_bndsel_count T2) + (typ_bndsel_count T1)
  | typ_sel x T1 y => 1
  | typ_bnd T1 => 1 + (typ_bndsel_count T1)
  | _ => 0
  end.

Inductive logctx_notbndsel_le: logctx->Prop :=
| logctx_notbndsel_le_nil:
  logctx_notbndsel_le logctx_nil
| logctx_notbndsel_le_orl oc T:
  logctx_notbndsel_le oc ->
  logctx_notbndsel_le (logctx_orl oc T)
| logctx_notbndsel_le_r oc T:
  typ_notbndsel T ->
  logctx_notbndsel_le oc ->
  logctx_notbndsel_le (logctx_orr T oc)
| logctx_notbndsel_le_andl oc T:
  logctx_notbndsel_le oc ->
  logctx_notbndsel_le (logctx_andl oc T)
| logctx_notbndsel_le_andr oc T:
  typ_notbndsel T ->
  logctx_notbndsel_le oc ->
  logctx_notbndsel_le (logctx_andr T oc).

Fixpoint typ_bndsel_index T: nat :=
  match T with
  | typ_bnd T => 1
  | typ_sel x A y => 1
  | typ_or T1 T2
  | typ_and T1 T2  =>
      let nL := (typ_bndsel_index T1) in
      match nL with

      | 0 => 1 + (typ_bndsel_index T2)

      | _ => 1 + nL + (typ_bndsel_count T2)
      end
  | _ => 0
  end.

Fixpoint typ_bndsel_leftmost_logctx T: logctx :=
  match T with
  | typ_or T1 T2 =>
      let nL := (typ_bndsel_count T1) in
      match nL with

      | 0 => logctx_orr T1 (typ_bndsel_leftmost_logctx T2)

      | _ => logctx_orl (typ_bndsel_leftmost_logctx T1) T2
      end
  | typ_and T1 T2 =>
      let nL := (typ_bndsel_count T1) in
      match nL with

      | 0 => logctx_andr T1 (typ_bndsel_leftmost_logctx T2)

      | _ => logctx_andl (typ_bndsel_leftmost_logctx T1) T2
      end
  | _ => logctx_nil
  end.

Definition typ_notbnd T :=
  (forall oc U, T <> logctx_typ oc (typ_bnd U)).

Fixpoint typ_bnd_count (T: typ): nat :=
  match T with
  | typ_and T1 T2 => (typ_bnd_count T2) + (typ_bnd_count T1)
  | typ_or T1 T2 => (typ_bnd_count T2) + (typ_bnd_count T1)
  | typ_bnd T1 => 1 + (typ_bnd_count T1)
  | _ => 0
  end.

Inductive logctx_notbnd_le: logctx->Prop :=
| logctx_notbnd_le_nil:
  logctx_notbnd_le logctx_nil
| logctx_notbnd_le_orl oc T:
  logctx_notbnd_le oc ->
  logctx_notbnd_le (logctx_orl oc T)
| logctx_notbnd_le_r oc T:
  typ_notbnd T ->
  logctx_notbnd_le oc ->
  logctx_notbnd_le (logctx_orr T oc)
| logctx_notbnd_le_andl oc T:
  logctx_notbnd_le oc ->
  logctx_notbnd_le (logctx_andl oc T)
| logctx_notbnd_le_andr oc T:
  typ_notbnd T ->
  logctx_notbnd_le oc ->
  logctx_notbnd_le (logctx_andr T oc).

Fixpoint typ_bnd_index T: nat :=
  match T with
  | typ_bnd T => 1
  | typ_or T1 T2
  | typ_and T1 T2  =>
      let nL := (typ_bnd_index T1) in
      match nL with

      | 0 => 1 + (typ_bnd_index T2)

      | _ => 1 + nL + (typ_bnd_count T2)
      end
  | _ => 0
  end.

Fixpoint typ_bnd_leftmost_logctx T: logctx :=
  match T with
  | typ_or T1 T2 =>
      let nL := (typ_bnd_count T1) in
      match nL with

      | 0 => logctx_orr T1 (typ_bnd_leftmost_logctx T2)

      | _ => logctx_orl (typ_bnd_leftmost_logctx T1) T2
      end
  | typ_and T1 T2 =>
      let nL := (typ_bnd_count T1) in
      match nL with

      | 0 => logctx_andr T1 (typ_bnd_leftmost_logctx T2)

      | _ => logctx_andl (typ_bnd_leftmost_logctx T1) T2
      end
  | _ => logctx_nil
  end.
