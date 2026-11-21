From mathcomp Require Import ssreflect.seq all_ssreflect.

Require Import List String Coq.Arith.PeanoNat Relations ZArith Datatypes Setoid Morphisms Coq.Logic.Decidable Coq.Program.Basics Coq.Init.Datatypes.

Import ListNotations.

Open Scope list_scope.

From Paco Require Import paco.

Import ListNotations.

From SST Require Import src.header src.sim.

Variant value: Type :=
  | vint : Z    -> value
  | vbool: bool -> value
  | vnat : nat -> value.

Inductive sort: Type :=
  | sbool: sort
  | sint : sort
  | snat : sort.

Inductive subsort: sort -> sort -> Prop :=
  | sni  : subsort snat sint
  | srefl: forall s, subsort s s.

Section expr.

Inductive expr  : Type :=
  | e_var : ( fin ) -> expr
  | e_val : ( value   ) -> expr
  | e_succ : ( expr   ) -> expr
  | e_neg : ( expr   ) -> expr
  | e_not : ( expr   ) -> expr
  | e_gt : ( expr   ) -> ( expr   ) -> expr
  | e_plus: ( expr   ) -> ( expr   ) -> expr
  | e_det : expr -> expr -> expr.

End expr.

Inductive stepE : relation expr :=
  | ec_succ  : forall e n, stepE e (e_val (vnat n)) -> stepE (e_succ e) (e_val (vnat (n+1)))
  | ec_neg   : forall e n, stepE e (e_val (vint n)) -> stepE (e_neg e) (e_val (vint (-n)))
  | ec_neg2  : forall e n, stepE e (e_val (vnat n)) -> stepE (e_neg e) (e_val (vint (-(Z.of_nat n))))
  | ec_t_f   : forall e,   stepE e (e_val (vbool true)) -> stepE (e_not e) (e_val (vbool false))
  | ec_f_t   : forall e,   stepE e (e_val (vbool false)) -> stepE (e_not e) (e_val (vbool true))
  | ec_gt_t0 : forall e e' m n, Z.lt (Z.of_nat n) (Z.of_nat m) ->
                           stepE e (e_val (vnat m)) -> stepE e' (e_val (vnat n)) ->
                           stepE (e_gt e e') (e_val (vbool true))
  | ec_gt_t1 : forall e e' m n, Z.lt n (Z.of_nat m) ->
                           stepE e (e_val (vnat m)) -> stepE e' (e_val (vint n)) ->
                           stepE (e_gt e e') (e_val (vbool true))
  | ec_gt_t2 : forall e e' m n, Z.lt (Z.of_nat n) m ->
                           stepE e (e_val (vint m)) -> stepE e' (e_val (vnat n)) ->
                           stepE (e_gt e e') (e_val (vbool true))
  | ec_gt_t3 : forall e e' m n, Z.lt n m ->
                           stepE e (e_val (vint m)) -> stepE e' (e_val (vint n)) ->
                           stepE (e_gt e e') (e_val (vbool true))
  | ec_gt_f0 : forall e e' m n, Z.le (Z.of_nat m) (Z.of_nat n) ->
                           stepE e (e_val (vnat m)) -> stepE e' (e_val (vnat n)) ->
                           stepE (e_gt e e') (e_val (vbool false))
  | ec_gt_f1 : forall e e' m n, Z.le (Z.of_nat m) n ->
                           stepE e (e_val (vnat m)) -> stepE e' (e_val (vint n)) ->
                           stepE (e_gt e e') (e_val (vbool false))
  | ec_gt_f2 : forall e e' m n, Z.le m (Z.of_nat n) ->
                           stepE e (e_val (vint m)) -> stepE e' (e_val (vnat n)) ->
                           stepE (e_gt e e') (e_val (vbool false))
  | ec_gt_f3 : forall e e' m n, Z.le m n ->
                           stepE e (e_val (vint m)) -> stepE e' (e_val (vint n)) ->
                           stepE (e_gt e e') (e_val (vbool false))
  | ec_plus0 : forall e e' m n, stepE e (e_val (vnat n)) -> stepE e' (e_val (vnat m)) ->
                           stepE (e_plus e e') (e_val (vint ((Z.of_nat n) + (Z.of_nat m))))
  | ec_plus1 : forall e e' m n, stepE e (e_val (vnat n)) -> stepE e' (e_val (vint m)) ->
                           stepE (e_plus e e') (e_val (vint ((Z.of_nat n) + m)))
  | ec_plus2 : forall e e' m n, stepE e (e_val (vint n)) -> stepE e' (e_val (vnat m)) ->
                           stepE (e_plus e e') (e_val (vint (n + (Z.of_nat m))))
  | ec_plus3 : forall e e' m n, stepE e (e_val (vint n)) -> stepE e' (e_val (vint m)) ->
                           stepE (e_plus e e') (e_val (vint (n + m)))
  | ec_detl  : forall m n v, stepE m v -> stepE (e_det m n) v
  | ec_detr  : forall m n v, stepE n v -> stepE (e_det m n) v
  | ec_refl  : forall e, stepE e e
  | ec_trans : forall e e' e'', stepE e e' -> stepE e' e'' -> stepE e e''.
