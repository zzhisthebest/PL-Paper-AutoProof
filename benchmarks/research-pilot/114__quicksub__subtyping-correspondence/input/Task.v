Require Import Metalib.Metatheory.

Require Import Program.Equality.

Require Export LinearRule.

Inductive binding : Set :=
  | bind_sub : binding
  | bind_typ : typ -> binding.

Definition env := list (atom * binding).

Notation empty := (@nil (atom * binding)).

Inductive WFS : env -> typ -> Prop :=
| WFS_top : forall E, WFS E typ_top
| WFS_nat : forall E, WFS E typ_nat
| WFS_fvar : forall X E ,
    binds X (bind_sub) E ->
    WFS E (typ_fvar X)
| WFS_arrow : forall E A B,
    WFS E A ->
    WFS E B ->
    WFS E (typ_arrow A B)
| WFS_rec : forall L E A,


      (forall  X , X \notin L ->
        WFS (X ~ bind_sub ++ E) (open_tt A X)) ->
      WFS E (typ_mu A).

Inductive wf_env : env -> Prop :=
  | wf_env_empty :
      wf_env empty
  | wf_env_sub : forall (E : env) (X : atom) ,
      wf_env E ->
      X \notin dom E ->
      wf_env (X ~ bind_sub ++ E)
  | wf_env_typ : forall (E : env) (x : atom) (T : typ),
      wf_env E ->
      WFS E T ->
      x `notin` dom E ->
      wf_env (x ~ bind_typ T ++ E).

Inductive sub_amber2: env -> typ -> typ -> Prop :=
| sam2_nat: forall E,
    wf_env E ->
    sub_amber2 E typ_nat typ_nat
| sam2_top: forall E A,
    WFS E A ->
    wf_env E ->
    sub_amber2 E A typ_top
| sam2_fvar: forall E X,
    binds X (bind_sub) E ->
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

Definition drop_im b :=
  match b with
  | Rules.bind_sub _ => bind_sub
  | Rules.bind_typ t => bind_typ t
  end.

Definition drop_im_env := map drop_im.

Theorem pos_esa_sound: forall im cm evs E A B,
  Sub im cm evs E A B ->
  sub_amber2 (map drop_im E) A B.

Theorem pos_esa_complete_final: forall A B,
    sub_amber2 nil A B ->
    exists cm evs, Sub Pos cm evs nil A B.
