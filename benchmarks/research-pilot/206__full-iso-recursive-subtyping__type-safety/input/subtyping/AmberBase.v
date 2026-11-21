Require Import Metalib.Metatheory.

Require Import Program.Equality.

Require Export Rules.

Require Export Infra.

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

Inductive posvar: Mode -> atom -> typ -> typ -> Prop :=
| pos_nat: forall X m,
    posvar m X typ_nat typ_nat
| pos_top: forall X A m,
    type A ->
    posvar m X A typ_top
| pos_top_flip: forall X A m,
    type A ->
    posvar m X typ_top A
| pos_fvar_x: forall X,
    posvar Pos X (typ_fvar X) (typ_fvar X)
| pos_fvar_y: forall X Y m,
    X <> Y ->
    posvar m X (typ_fvar Y) (typ_fvar Y)
| pos_arrow: forall X m A1 A2 B1 B2,
    posvar (flip m) X B1 A1 ->
    posvar m X A2 B2 ->
    posvar m X (typ_arrow A1 A2) (typ_arrow B1 B2)
| pos_rec: forall X m A B L,
    (forall Y, Y \notin L \u {{X}} ->
               posvar m X (open_tt A Y) (open_tt B Y)) ->
     (forall Y, Y \notin L \u {{X}} ->
               posvar Pos Y (open_tt A Y) (open_tt B Y)) ->
    posvar m X (typ_mu A) (typ_mu B)
| pos_rec_t : forall A X m L,
    X \notin fv_tt A ->
    (forall Y, Y \notin L \u {{X}} ->
               type (open_tt A Y)) ->
    posvar m X (typ_mu A) (typ_mu A).

Inductive sub_amber2: env -> typ -> typ -> Prop :=
| sam2_nat: forall E,
    wf_env E ->
    sub_amber2 E typ_nat typ_nat
| sam2_top: forall E A,
    WFA E A ->
    wf_env E ->
    sub_amber2 E A typ_top
| sam2_fvar: forall E X ,
    binds X bind_sub E ->
    wf_env E ->
    sub_amber2 E (typ_fvar X) (typ_fvar X)
| sam2_arrow: forall E A1 A2 B1 B2,
    sub_amber2 E B1 A1 ->
    sub_amber2 E A2 B2 ->
    sub_amber2 E (typ_arrow A1 A2) (typ_arrow B1 B2)
| sam2_rec: forall E A B L,
    (forall X , X \notin L ->
                sub_amber2 (X ~ bind_sub ++ E) (open_tt A X) (open_tt B X)) ->
    (forall X , X \notin L ->
                posvar Pos X (typ_mu A) (typ_mu B)) ->
    sub_amber2 E (typ_mu A) (typ_mu B)
.

Fixpoint env_trans (E : env_amber) : env :=
  match E with
  | nil => nil
  | (X,Y)::E' => X ~ bind_sub ++  env_trans E'
  end.

Fixpoint rename_env (E : env_amber) (A : typ) : typ :=
  match E with
  | nil => A
  | cons (X,Y) E' => subst_tt Y (typ_fvar X) (rename_env E' A)
  end.
