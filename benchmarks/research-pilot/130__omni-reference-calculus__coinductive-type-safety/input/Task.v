Set Implicit Arguments.

Require Import STLC_Ref_Soundness_Common.

Implicit Types Y : phi.

Implicit Types P : conf->Prop.

CoInductive coomnibig : conf -> (conf->Prop) -> Prop :=
  | coomnibig_val : forall c P,
      value (fst c) ->
      P c ->
      coomnibig c P
  | coomnibig_beta : forall mu t1 t2 P,
      sto_ok mu ->
      term (trm_abs t1) ->
      value t2 ->
      coomnibig (t1 ^^ t2, mu) P ->
      coomnibig (trm_app (trm_abs t1) t2, mu) P
  | coomnibig_rand : forall mu n P,
      (forall m, 0 <= m < max n 1 -> P ((trm_int m), mu)) ->
      coomnibig (trm_rand (trm_int n), mu) P
  | coomnibig_ref : forall mu t1 P,
      sto_ok mu ->
      value t1 ->
      (forall l, l # mu ->
        P (trm_loc l, (mu & l ~ t1))) ->
      coomnibig (trm_ref t1, mu) P
  | coomnibig_get : forall mu l t P,
      sto_ok mu ->
      binds l t mu ->
      P (t, mu) ->
      coomnibig (trm_get (trm_loc l), mu) P
  | coomnibig_set : forall mu l t2 P,
      sto_ok mu ->
      value t2 ->
      P (trm_unit, mu & l ~ t2) ->
      coomnibig (trm_set (trm_loc l) t2, mu) P

  | coomnibig_app_1 : forall mu t1 t2 P1 P,
      ~ value t1 ->
      coomnibig (t1, mu) P1 ->
      (forall t1' mu', P1 (t1',mu') -> coomnibig (trm_app t1' t2, mu') P) ->
      coomnibig (trm_app t1 t2, mu) P
  | coomnibig_app_2 : forall mu t1 t2 P1 P,
      value t1 ->
      ~ value t2 ->
      coomnibig (t2, mu) P1 ->
      (forall t2' mu', P1 (t2',mu') -> coomnibig (trm_app t1 t2', mu') P) ->
      coomnibig (trm_app t1 t2, mu) P
  | coomnibig_ref_1 : forall mu t1 P1 P,
      ~ value t1 ->
      coomnibig (t1, mu) P1 ->
      (forall t1' mu', P1 (t1',mu') -> coomnibig (trm_ref t1', mu') P) ->
      coomnibig (trm_ref t1, mu) P
  | coomnibig_get_1 : forall mu t1 P1 P,
      coomnibig (t1, mu) P1 ->
      (forall t1' mu', P1 (t1',mu') -> coomnibig (trm_get t1', mu') P) ->
      coomnibig (trm_get t1, mu) P
  | coomnibig_set_1 : forall mu t1 t2 P1 P,
      ~ value t1 ->
      coomnibig (t1, mu) P1 ->
      (forall t1' mu', P1 (t1',mu') -> coomnibig (trm_set t1' t2, mu') P) ->
      coomnibig (trm_set t1 t2, mu) P
  | coomnibig_set_2 : forall mu t1 t2 P1 P,
      value t1 ->
      ~ value t2 ->
      coomnibig (t2, mu) P1 ->
      (forall t2' mu', P1 (t2',mu') -> coomnibig (trm_set t1 t2', mu') P) ->
      coomnibig (trm_set t1 t2, mu) P
  | coomnibig_rand_1 : forall mu t1 P1 P,
      ~ value t1 ->
      coomnibig (t1, mu) P1 ->
      (forall t1' mu', P1 (t1',mu') -> coomnibig (trm_rand t1', mu') P) ->
      coomnibig (trm_rand t1, mu) P.

Definition post (Y:phi) (T:typ) : conf->Prop :=
  fun '(t,mu) =>
    exists Y', extends Y Y'
             /\ Y' |== mu
             /\ value t
             /\ empty ! Y' |= t ~: T.

Definition coomnibig_soundness := forall mu t Y T,
  Y |== mu ->
  empty ! Y |= t ~: T ->
  coomnibig (t,mu) (post Y T).

Definition himpl (H1 H2:conf->Prop) : Prop :=
  forall h, H1 h -> H2 h.

Notation "H1 ==> H2" := (himpl H1 H2) (at level 55).

Theorem coomnibig_soundness_result : coomnibig_soundness.
