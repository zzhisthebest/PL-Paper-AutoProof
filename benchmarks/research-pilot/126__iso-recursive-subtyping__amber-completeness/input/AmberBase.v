Require Import Metalib.Metatheory.

Require Import Program.Equality.

Require Export Rules.

Require Export infra.

Require Export DoubleUnfolding.

Definition env_amber := list (atom * atom).

Fixpoint domA (E : env_amber) : atoms :=
  match E with
  | nil => {}
  | (X,Y)::E' => {{X}} \u {{Y}} \u domA E'
  end.

Inductive wfe_amber: env_amber -> Prop :=
| wfea_base:
    wfe_amber nil
| wfea_cons: forall X Y E,
    X \notin domA E ->
    Y \notin {{X}} \u domA E ->
    wfe_amber E ->
    wfe_amber ((X,Y)::E).

Inductive wf_amber: env_amber -> typ -> Prop :=
| wfa_nat: forall E,
    wfe_amber E ->
    wf_amber E typ_nat
| wfa_top: forall E,
    wfe_amber E ->
    wf_amber E typ_top
| wfa_fvarl: forall E X Y,
    In (X,Y) E ->
    wfe_amber E ->
    wf_amber E X
| wfa_fvarr: forall E X Y,
    In (X,Y) E ->
    wfe_amber E ->
    wf_amber E Y
| wfa_arrow: forall E A1 A2,
    wf_amber E A1 ->
    wf_amber E A2 ->
    wf_amber E (typ_arrow A1 A2)
| wfa_rec: forall E A L,
    (forall X Y,
        X \notin L -> Y \notin L \u {{X}} ->
        wf_amber (X ~ Y ++ E) (open_tt A X)) ->
    wf_amber E (typ_mu A).

Inductive sub_amber: env_amber -> typ -> typ -> Prop :=
| sam_nat: forall E,
    wfe_amber E ->
    sub_amber E typ_nat typ_nat
| sam_top: forall E A,
    wf_amber E A ->
    wfe_amber E ->
    sub_amber E A typ_top
| sam_fvar: forall E X Y,
    In (X, Y) E ->
    wfe_amber E ->
    sub_amber E (typ_fvar X) (typ_fvar Y)
| sam_arrow: forall E A1 A2 B1 B2,
    sub_amber E B1 A1 ->
    sub_amber E A2 B2 ->
    sub_amber E (typ_arrow A1 A2) (typ_arrow B1 B2)
| sam_rec: forall E A B L,
    (forall X Y,
        X \notin L -> Y \notin {{X}} \u L ->
        sub_amber ((X,Y)::E) (open_tt A X) (open_tt B Y)) ->
    sub_amber E (typ_mu A) (typ_mu B)
| sam_refl: forall E A,
    wfe_amber E ->
    wf_amber E (typ_mu A) ->
    sub_amber E (typ_mu A) (typ_mu A)
.
