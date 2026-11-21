Require Import Metalib.Metatheory.

Require Import Program.Equality.

Require Export AmberSoundness.

Require Export DoubleUnfolding.

Inductive wk_sub: env -> typ -> typ -> Prop :=
| W_nat: forall E,
    wf_env E ->
    wk_sub E typ_nat typ_nat
| W_top: forall E A,
    WFA E A ->
    wf_env E ->
    wk_sub E A typ_top
| W_fvar: forall E X ,
    binds X bind_sub E ->
    wf_env E ->
    wk_sub E (typ_fvar X) (typ_fvar X)
| W_arrow: forall E A1 A2 B1 B2,
    wk_sub E B1 A1 ->
    wk_sub E A2 B2 ->
    wk_sub E (typ_arrow A1 A2) (typ_arrow B1 B2)
| W_rec: forall E A B L,
    (forall X , X \notin L ->
                wk_sub (X ~ bind_sub ++ E) (open_tt A X) (open_tt B X)) ->
    (forall X , X \notin L ->
                posvar Pos X (open_tt A X) (open_tt B X)) ->
    wk_sub E (typ_mu A) (typ_mu B)
| W_refl: forall E A,
    wf_env E ->
    WF E (typ_mu A) ->
    wk_sub E (typ_mu A) (typ_mu A).
