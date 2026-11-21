From Stdlib Require Import List Arith.

Import ListNotations.

Require Export Arith.EqNat.

From Stdlib Require Export PeanoNat.

Require Import Coq.Program.Equality.

From Stdlib Require Import Lia.

From Stdlib Require Import PeanoNat.

Definition id := nat.

Inductive ty : Type :=
| TTop : ty
| TFun : ty -> ty -> ty
| TAll : ty -> ty -> ty
| TVarF : id -> ty
| TVarH : id -> ty
| TVarB : id -> ty
| TCell : ty -> ty
.

Inductive tm : Type :=
| tvar : id -> tm
| tabs : ty -> tm -> tm
| tapp : tm -> tm -> tm
| ttabs : ty -> tm -> tm
| ttapp : tm -> ty -> tm
| tnew : tm -> tm
| tget : tm -> tm
| tset : tm -> tm -> tm
.

Inductive binding {X: Type} :=
| bind_tm : X -> binding
| bind_ty : X -> binding
.

Inductive vl : Type :=

| vabs : list vl   -> ty -> tm -> vl

| vtabs : list vl   -> ty -> tm -> vl

| vty : list vl   -> ty -> vl

| vloc : id -> vl
.

Definition tenv := list (@binding ty).

Definition venv := list vl.

Definition aenv := list (venv*ty).

Fixpoint indexr {X : Type} (n : id) (l : list X) : option X :=
  match l with
    | [] => None
    | a :: l' =>
      if (Nat.eqb n (length l')) then Some a else indexr n l'
  end.

Fixpoint update {X : Type} (n : id) (l : list X) (v: X) : list X :=
  match l with
    | [] => []
    | a :: l' =>
      if (Nat.eqb n (length l')) then v :: l' else a :: update n l' v
  end.

Inductive closed: nat  -> nat  -> nat  -> ty -> Prop :=
| cl_top: forall i j k,
    closed i j k TTop
| cl_fun: forall i j k T1 T2,
    closed i j k T1 ->
    closed i j k T2 ->
    closed i j k (TFun T1 T2)
| cl_all: forall i j k T1 T2,
    closed i j k T1 ->
    closed (S i) j k T2 ->
    closed i j k (TAll T1 T2)
| cl_cell: forall i j k T,
    closed i j k T ->
    closed i j k (TCell T)
| cl_sel: forall i j k x,
    k > x ->
    closed i j k (TVarF x)
| cl_selh: forall i j k x,
    j > x ->
    closed i j k (TVarH x)
| cl_selb: forall i j k x,
    i > x ->
    closed i j k (TVarB x)
.

Fixpoint open_rec (k: nat) (u: ty) (T: ty) { struct T }: ty :=
  match T with
    | TTop        => TTop
    | TFun T1 T2  => TFun (open_rec k u T1) (open_rec k u T2)
    | TAll T1 T2  => TAll (open_rec k u T1) (open_rec (S k) u T2)
    | TCell T1 => TCell (open_rec k u T1)
    | TVarF x => TVarF x
    | TVarH i => TVarH i
    | TVarB i => if Nat.eqb k i then u else TVarB i
  end.

Definition open u T := open_rec 0 u T.

Fixpoint subst (U : ty) (T : ty) {struct T} : ty :=
  match T with
    | TTop         => TTop
    | TFun T1 T2   => TFun (subst U T1) (subst U T2)
    | TAll T1 T2   => TAll (subst U T1) (subst U T2)
    | TCell T1 => TCell (subst U T1)
    | TVarB i      => TVarB i
    | TVarF i      => TVarF i
    | TVarH i      => if Nat.eqb i 0 then U else TVarH (i-1)
  end.

Inductive stp: tenv -> tenv -> ty -> ty -> Prop :=
| stp_top: forall G1 GH T1,
    closed 0 (length GH) (length G1) T1 ->
    stp G1 GH T1 TTop
| stp_fun: forall G1 GH T1 T2 T3 T4,
    stp G1 GH T3 T1 ->
    stp G1 GH T2 T4 ->
    stp G1 GH (TFun T1 T2) (TFun T3 T4)
| stp_sel1: forall G1 GH T T2 x,
    indexr x G1 = Some (bind_ty T) ->
    closed 0 0 (length G1) T ->
    stp G1 GH T T2 ->
    stp G1 GH (TVarF x) T2
| stp_selx: forall G1 GH v x,

    indexr x G1 = Some v ->
    stp G1 GH (TVarF x) (TVarF x)
| stp_sela1: forall G1 GH T T2 x,
    indexr x GH = Some (bind_ty T) ->
    closed 0 x (length G1) T ->
    stp G1 GH T T2 ->
    stp G1 GH (TVarH x) T2
| stp_selax: forall G1 GH v x,

    indexr x GH = Some v  ->
    stp G1 GH (TVarH x) (TVarH x)
| stp_all: forall G1 GH T1 T2 T3 T4 x,
    stp G1 GH T3 T1 ->
    x = length GH ->
    closed 1 (length GH) (length G1) T2 ->
    closed 1 (length GH) (length G1) T4 ->
    stp G1 ((bind_ty T3)::GH) (open (TVarH x) T2) (open (TVarH x) T4) ->
    stp G1 GH (TAll T1 T2) (TAll T3 T4)
| stp_cell: forall G1 GH T1 T2,
    stp G1 GH T1 T2 ->
    stp G1 GH T2 T1 ->
    stp G1 GH (TCell T1) (TCell T2)
.

Inductive has_type : tenv -> tm -> ty -> Prop :=
| t_var: forall x env T1,
           indexr x env = Some (bind_tm T1) ->
           stp env [] T1 T1 ->
           has_type env (tvar x) T1
| t_app: forall env f x T1 T2,
           has_type env f (TFun T1 T2) ->
           has_type env x T1 ->
           has_type env (tapp f x) T2
| t_abs: forall env y T1 T2,
           has_type (bind_tm T1::env) y T2 ->
           stp env [] (TFun T1 T2) (TFun T1 T2) ->
           has_type env (tabs T1 y) (TFun T1 T2)
| t_tapp: forall env f T11 T12 T,
           has_type env f (TAll T11 T12) ->
           T = open T11 T12 ->
           has_type env (ttapp f T11) T
| t_tabs: forall env y T1 T2,
           has_type (bind_ty T1::env) y (open (TVarF (length env)) T2) ->
           stp env [] (TAll T1 T2) (TAll T1 T2) ->
           has_type env (ttabs T1 y) (TAll T1 T2)
| t_new: forall env x T1,
           has_type env x T1 ->
           stp env [] T1 T1 ->
           has_type env (tnew x) (TCell T1)
| t_get: forall env T1 x,
           has_type env x (TCell T1) ->
           has_type env (tget x) T1
| t_set: forall env T1 x y,
           has_type env x (TCell T1) ->
           has_type env y T1 ->
           has_type env (tset x y) T1
| t_sub: forall env e T1 T2,
           has_type env e T1 ->
           stp env [] T1 T2 ->
           has_type env e T2
.

Inductive stp2: bool   ->
                venv -> ty -> venv -> ty -> aenv  ->
                nat   ->
                Prop :=
| stp2_top: forall G1 G2 GH T n,
    closed 0 (length GH) (length G1) T ->
    stp2 true G1 T G2 TTop GH (S n)
| stp2_fun: forall G1 G2 T1 T2 T3 T4 GH n1 n2,
    stp2 false G2 T3 G1 T1 GH n1 ->
    stp2 false G1 T2 G2 T4 GH n2 ->
    stp2 true G1 (TFun T1 T2) G2 (TFun T3 T4) GH (S (n1 + n2))


| stp2_sel1: forall G1 G2 GX TX x T2 GH n1,
    indexr x G1 = Some (vty GX TX) ->
    closed 0 0 (length GX) TX ->
    stp2 true GX TX G2 T2 GH n1 ->
    stp2 true G1 (TVarF x) G2 T2 GH (S n1)
| stp2_sel2: forall G1 G2 GX TX x T1 GH n1,
    indexr x G2 = Some (vty GX TX) ->
    closed 0 0 (length GX) TX ->
    stp2 false G1 T1 GX TX GH n1 ->
    stp2 true G1 T1 G2 (TVarF x) GH (S n1)
| stp2_selx: forall G1 G2 v x1 x2 GH n,
    indexr x1 G1 = Some v ->
    indexr x2 G2 = Some v ->
    stp2 true G1 (TVarF x1) G2 (TVarF x2) GH (S n)



| stp2_sela1: forall G1 G2 GX TX x T2 GH n1,
    indexr x GH = Some (GX, TX) ->
    closed 0 x (length GX) TX ->
    stp2 false GX TX G2 T2 GH n1 ->
    stp2 true G1 (TVarH x) G2 T2 GH (S n1)
| stp2_selax: forall G1 G2 v x GH n,
    indexr x GH = Some v ->
    stp2 true G1 (TVarH x) G2 (TVarH x) GH (S n)

| stp2_all: forall G1 G2 T1 T2 T3 T4 x GH n1 n2,
    stp2 false G2 T3 G1 T1 GH n1 ->
    x = length GH ->
    closed 1 (length GH) (length G1) T2 ->
    closed 1 (length GH) (length G2) T4 ->
    stp2 false G1 (open (TVarH x) T2) G2 (open (TVarH x) T4) ((G2, T3)::GH) n2 ->
    stp2 true G1 (TAll T1 T2) G2 (TAll T3 T4) GH (S (n1 + n2))

| stp2_cell: forall G1 G2 T1 T2 GH n1 n2,
    stp2 false G1 T1 G2 T2 GH n1 ->
    stp2 false G2 T2 G1 T1 GH n2 ->
    stp2 true G1 (TCell T1) G2 (TCell T2) GH (S (n1+n2))

| stp2_wrapf: forall G1 G2 T1 T2 GH n1,
    stp2 true G1 T1 G2 T2 GH n1 ->
    stp2 false G1 T1 G2 T2 GH (S n1)

| stp2_transf: forall G1 G2 G3 T1 T2 T3 GH n1 n2,
    stp2 true G1 T1 G2 T2 GH n1 ->
    stp2 false G2 T2 G3 T3 GH n2 ->
    stp2 false G1 T1 G3 T3 GH (S (n1+n2))
.

Inductive wf_env : aenv -> venv -> tenv -> Prop :=
| wfe_nil : forall sto, wf_env sto nil nil
| wfe_cons : forall sto v t vs ts,
    val_type sto (v::vs) v t ->
    wf_env sto vs ts ->
    wf_env sto (cons v vs) (cons t ts)


with val_type : aenv -> venv -> vl -> @binding ty -> Prop :=
| v_ty: forall sto env venv tenv T1 TE,
    wf_env sto venv tenv ->
    (exists n, stp2 true venv T1 env TE [] n) ->
    val_type sto env (vty venv T1) (bind_ty TE)
| v_abs: forall sto env venv tenv x y T1 T2 TE,
    wf_env sto venv tenv ->
    has_type (bind_tm T1::tenv) y T2 ->
    length venv = x ->
    (exists n, stp2 true venv (TFun T1 T2) env TE [] n) ->
    val_type sto env (vabs venv T1 y) (bind_tm TE)
| v_tabs: forall sto env venv tenv x y T1 T2 TE,
    wf_env sto venv tenv ->
    has_type (bind_ty T1::tenv) y (open (TVarF x) T2) ->
    length venv = x ->
    (exists n, stp2 true venv (TAll T1 T2) env TE [] n) ->
    val_type sto env (vtabs venv T1 y) (bind_tm TE)
| v_loc: forall sto venv venv1 b T1 TE,
    indexr b sto = Some (venv1,T1) ->
    (exists n, stp2 true venv1 (TCell T1) venv TE [] n) ->
    val_type sto venv (vloc b) (bind_tm TE)
.

Fixpoint teval(n: nat)(sto: venv)(env: venv)(t: tm){struct n}: (venv*option (option vl)) :=
  match n with
    | 0 => (sto, None)
    | S n =>
      match t with
        | tvar x     => (sto, Some (indexr x env))
        | tabs T y => (sto, Some (Some (vabs env T y)))
        | ttabs T y  => (sto, Some (Some (vtabs env T y)))
        | tnew ex =>
          match teval n sto env ex with
            | (sto1, None) => (sto1, None)
            | (sto1, Some None) => (sto1, Some None)
            | (sto1, Some (Some v)) => (v::sto1, Some (Some (vloc (length sto1))))
          end
        | tget ex =>
          match teval n sto env ex with
            | (sto1, None) => (sto1, None)
            | (sto1, Some None) => (sto1, Some None)
            | (sto1, Some (Some (vty _ _))) => (sto1, Some None)
            | (sto1, Some (Some (vabs _ _ _))) => (sto1, Some None)
            | (sto1, Some (Some (vtabs _ _ _))) => (sto1, Some None)
            | (sto1, Some (Some (vloc i))) => (sto1, Some (indexr i sto1))
          end
        | tset ex ey =>
          match teval n sto env ex with
            | (sto1, None) => (sto1, None)
            | (sto1, Some None) => (sto1, Some None)
            | (sto1, Some (Some (vty _ _))) => (sto1, Some None)
            | (sto1, Some (Some (vabs _ _ _))) => (sto1, Some None)
            | (sto1, Some (Some (vtabs _ _ _))) => (sto1, Some None)
            | (sto1, Some (Some (vloc i))) =>
              match teval n sto1 env ey with
                | (sto2, None) => (sto2, None)
                | (sto2, Some None) => (sto2, Some None)
                | (sto2, Some (Some v)) => (update i sto2 v, Some (Some v))
              end
          end
        | tapp ef ex   =>
          match teval n sto env ex with
            | (sto1, None) => (sto1, None)
            | (sto1, Some None) => (sto1, Some None)
            | (sto1, Some (Some vx)) =>
              match teval n sto1 env ef with
                | (sto2, None) => (sto2, None)
                | (sto2, Some None) => (sto2, Some None)
                | (sto2, Some (Some (vty _ _))) => (sto2, Some None)
                | (sto2, Some (Some (vtabs _ _ _))) => (sto2, Some None)
                | (sto2, Some (Some (vloc _))) => (sto2, Some None)
                | (sto2, Some (Some (vabs env2 _ ey))) =>
                  teval n sto2 (vx::env2) ey
              end
          end
        | ttapp ef ex   =>
          match teval n sto env ef with
            | (sto1, None) => (sto1, None)
            | (sto1, Some None) => (sto1, Some None)
            | (sto1, Some (Some (vty _ _))) => (sto1, Some None)
            | (sto1, Some (Some (vabs _ _ _))) => (sto1, Some None)
            | (sto1, Some (Some (vloc _))) => (sto1, Some None)
            | (sto1, Some (Some (vtabs env2 T ey))) =>
              teval n sto1 ((vty env ex)::env2) ey
          end
      end
  end.

Inductive wf_sto: aenv -> venv -> aenv -> Prop :=
| wfs_nil: forall G,
  wf_sto G nil nil
| wfs_cons: forall G venv v t vs ts,
  val_type G venv v (bind_tm t) ->
  wf_sto G vs ts ->
  wf_sto G (v::vs) ((venv,t)::ts)
.

Inductive res_type: aenv -> venv -> (venv*option (option vl)) -> ty -> Prop :=
| res_val: forall STO sto venv v T,
      val_type STO venv v (bind_tm T) ->
      wf_sto STO sto STO ->
      res_type STO venv (sto,(Some (Some v))) T
| res_timeout: forall STO sto venv T,
      wf_sto STO sto STO ->
      res_type STO venv (sto,None) T.

Theorem full_safety : forall n e senv sto tenv venv r T,
  teval n sto venv e = r ->
  has_type tenv e T ->
  wf_env senv venv tenv ->
  wf_sto senv sto senv ->
  exists senv', res_type (senv'++senv) venv r T.
