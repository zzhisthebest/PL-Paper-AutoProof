From Stdlib Require Import List.
Require Import Syntax.
Import ListNotations.
Open Scope list.

Inductive sred: term -> term -> Prop :=
  | sred_lam:
    forall t,
      sred
        (Lam t)
        (Value (Closure t []))

  | sred_beta:
    forall t v sigma',
      sred
        (App (Value (Closure t sigma')) (Value v))
        (t.[subst_of_env (v :: sigma')])
  | sred_app_left_conflict:
      forall t sigma,
        sred
          (App (Value (Closure t sigma)) Conflict)
          Conflict
  | sred_app_right_conflict:
    forall u,
      sred (App Conflict u) Conflict
  | sred_app_right:
    forall t u1 u2 sigma,
      sred (u1) (u2) ->
      sred
        (App (Value (Closure t sigma)) u1)
        (App (Value (Closure t sigma)) u2)
  | sred_app_left:
    forall t1 t2 u,
      sred (t1) (t2) ->
      sred
        (App t1 u)
        (App t2 u)

  | sred_binop_finish:
    forall op v v1 v2,
    Some v = get_op op v1 v2 ->
    sred
      (Binop op (Value v1) (Value v2))
      (Value v)
  | sred_binop_right_conflict:
    forall op u,
      sred (Binop op Conflict u) Conflict
  | sred_binop_left_conflict:
    forall op v,
      sred
        (Binop op (Value v) Conflict)
        Conflict
  | sred_binop_right:
    forall op v u1 u2,
      sred (u1) (u2) ->
      sred
        (Binop op (Value v) u1)
        (Binop op (Value v) u2)
  | sred_binop_left:
    forall op t1 t2 u,
      sred (t1) (t2) ->
      sred
        (Binop op t1 u)
        (Binop op t2 u)

  | sred_default_JTrue:
    forall tc,
      sred (Default [] (Value (Bool true)) tc) tc
  | sred_default_JFalse:
    forall tc,
      sred (Default [] (Value (Bool false)) tc) Empty
  | sred_default_JConflict:
    forall tc,
      sred (Default [] Conflict tc) Conflict
  | sred_default_J:
    forall tj1 tj2 tc,
      sred tj1 tj2 ->
      sred (Default [] tj1 tc) (Default [] tj2 tc)
  | sred_default_Conflict:
    forall ts vi vj tjust tcons,
      sred (Default ((Value (VPure vi))::(Value (VPure vj))::ts) tjust tcons) Conflict
  | sred_default_E_value:
    forall vi tjust tcons,
      sred (Default [Value (VPure vi)] tjust tcons) (Value (VPure vi))
  | sred_default_E_zero_conflict:
    forall ts2 tjust tcons,
      sred (Default (Conflict::ts2) tjust tcons) Conflict
  | sred_default_E_one_conflict:
    forall vi ts2 tjust tcons,
      sred (Default ((Value (VPure vi))::Conflict::ts2) tjust tcons) Conflict
  (* todo : add a comment to explain why version of the semantics and not the sred t Empty -> sred (Default (t::ts) tj tc) (Default ts tj tc). *)
  | sred_default_E_one_empty:
    forall vi ts tjust tcons,
      sred
        (Default ((Value (VPure vi))::Empty::ts) tjust tcons)
        (Default ((Value (VPure vi))::ts) tjust tcons)
  | sred_default_E_zero_empty:
    forall ts2 tj tc,
      sred (Default (Empty::ts2) tj tc) (Default ts2 tj tc)

  | sred_default_E_one:
    forall vi tj tj' ts3 tjust tcons,
      sred tj tj' ->
      sred
        (Default ((Value (VPure vi))::tj::ts3) tjust tcons)
        (Default ((Value (VPure vi))::tj'::ts3) tjust tcons)
  | sred_default_E_zero:
    forall ti ti' ts2 tj tc,
      sred ti ti' ->
      sred (Default (ti::ts2) tj tc) (Default (ti'::ts2) tj tc)




  | sred_match_None:
    forall t1 t2,
      sred (Match_ (Value (VNone)) t1 t2) t1
  | sred_match_Some:
    forall v t1 t2,
      sred (Match_ (Value (VSome v)) t1 t2) t2.[Value v/]
  | sred_match_conflict:
    forall t1 t2,
      sred
        (Match_ Conflict t1 t2)
        Conflict
  | sred_match_cond:
    forall u1 u2 t1 t2,
      sred u1 u2 ->
      sred (Match_ u1 t1 t2) (Match_ u2 t1 t2)

  | sred_None:
    sred ENone (Value VNone)

  | sred_Some_conflict:
    sred (ESome Conflict) Conflict
  | sred_Some:
    forall v,
      sred (ESome (Value v)) (Value (VSome v))
  | sred_Some_context:
    forall t1 t2,
      sred t1 t2 ->
      sred (ESome t1) (ESome t2)

  | sred_if_cond_conflict:
    forall ta tb,
      sred (If Conflict ta tb) Conflict
  | sred_if_true:
    forall ta tb,
      sred (If (Value (Bool true)) ta tb) ta
  | sred_if_false:
    forall ta tb,
      sred (If (Value (Bool false)) ta tb) tb
  | sred_if_cond:
    forall u1 u2 ta tb,
      sred u1 u2 ->
      sred (If u1 ta tb) (If u2 ta tb)

  | sred_ErrorOnEmpty:
    forall ta tb,
      sred ta tb ->
      sred (ErrorOnEmpty ta) (ErrorOnEmpty tb)
  | sred_eoe_empty:
    sred (ErrorOnEmpty Empty) (Conflict)
  | sred_eoe_value:
    forall v,
      sred (ErrorOnEmpty (Value (VPure v))) (Value v)
  | sred_eoe_conflict:
    sred (ErrorOnEmpty Conflict) (Conflict)

  | sred_DefaultPure_value:
    forall v,
      sred (DefaultPure (Value v)) (Value (VPure v))
  | sred_DefaultPure:
    forall ta tb,
      sred ta tb ->
      sred (DefaultPure ta) (DefaultPure tb)
  | sred_DefaultPure_conflit:
    sred (DefaultPure Conflict) Conflict

  | sred_Fold_rec:
    forall f h t v,
    sred
      (Fold f (h::t) (Value v))
      (Fold f (t) (App (App f h) (Value v)))
  | sred_Fold_init:
    forall f v,
    sred
      (Fold f ([]) (Value v))
      (Value v)
  | sred_Fold_step:
    forall f ts t1 t2,
    sred t1 t2 ->
    sred
      (Fold f ts t1)
      (Fold f ts t2)
  | sred_Fold_Conflict:
    forall f ts ,
    sred
      (Fold f ts Conflict)
      (Conflict)
.
