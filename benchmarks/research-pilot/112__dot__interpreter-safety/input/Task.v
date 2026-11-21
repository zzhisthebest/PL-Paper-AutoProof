From Stdlib Require Import List Arith.
Import ListNotations.
Require Export Arith.EqNat.

From Stdlib Require Export PeanoNat.

Require Import Coq.Program.Equality.

From Stdlib Require Import Lia.

From Stdlib Require Import PeanoNat.

Module DOT.

Definition id := nat.

Inductive var : Type :=
  | varF   : id -> var
  | varH   : id -> var
  | varB   : id -> var
.

Inductive ty : Type :=
  | TBool  : ty
  | TBot   : ty
  | TTop   : ty
  | TMem   : id -> ty -> ty -> ty
  | TSel   : var -> id -> ty
  | TAll   : id -> ty -> ty -> ty
  | TBind  : ty -> ty
  | TAnd   : ty -> ty -> ty
  | TOr    : ty -> ty -> ty
.

Inductive tm : Type :=
  | ttrue  : tm
  | tfalse : tm
  | tvar   : id -> tm
  | tapp   : tm -> id -> tm -> tm
  | tobj   : id -> list (id * def) -> tm
  | tlet   : id -> tm -> tm -> tm
 with def : Type :=
  | dfun   : id -> tm -> def
  | dmem   : ty -> def
.

Inductive vl : Type :=
| vbool : bool -> vl
| vobj  : list (id*vl) -> id -> list (id * def) -> vl
.

Definition tenv := list (id*ty).

Definition venv := list (id*vl).

Definition aenv := list (id*(venv*ty)).

Fixpoint fresh {X: Type} (l : list (id * X)): nat :=
  match l with
    | [] => 0
    | (n',a)::l' => 1 + n'
  end.

Fixpoint index {X : Type} (n : id) (l : list (id * X)) : option X :=
  match l with
    | [] => None
    | (n',a) :: l'  =>
      if le_lt_dec (fresh l') n' then
        if (Nat.eqb n n') then Some a else index n l'
      else None
  end.

Fixpoint indexr {X : Type} (n : id) (l : list (id * X)) : option X :=
  match l with
    | [] => None
    | (n',a) :: l'  =>
      if (Nat.eqb n (length l')) then Some a else indexr n l'
  end.

Fixpoint tailr {X : Type} (n : id) (l : list (id * X)) : list (id * X) :=
  match l with
    | [] => []
    | (n',a) :: l'  =>
      if (Nat.eqb n (length l)) then l else tailr n l'
  end.

Inductive closed_rec: nat -> nat -> ty -> Prop :=
| cl_top: forall k l,
    closed_rec k l TTop
| cl_bot: forall k l,
    closed_rec k l TBot
| cl_bool: forall k l,
    closed_rec k l TBool
| cl_mem: forall k l m T1 T2,
    closed_rec k l T1 ->
    closed_rec k l T2 ->
    closed_rec k l (TMem m T1 T2)
| cl_all: forall k l m T1 T2,
    closed_rec k l T1 ->
    closed_rec (S k) l T2 ->
    closed_rec k l (TAll m T1 T2)
| cl_bind: forall k l T2,
    closed_rec (S k) l T2 ->
    closed_rec k l (TBind T2)
| cl_sel: forall k l x m,
    closed_rec k l (TSel (varF x) m)
| cl_and: forall k l T1 T2,
    closed_rec k l T1 ->
    closed_rec k l T2 ->
    closed_rec k l (TAnd T1 T2)
| cl_or: forall k l T1 T2,
    closed_rec k l T1 ->
    closed_rec k l T2 ->
    closed_rec k l (TOr T1 T2)
| cl_selh: forall k l x m,
    l > x ->
    closed_rec k l (TSel (varH x) m)
| cl_selb: forall k l i m,
    k > i ->
    closed_rec k l (TSel (varB i) m)
.

Definition closed j l T := closed_rec j l T.

Fixpoint open_rec (k: nat) (u: var) (T: ty) { struct T }: ty :=
  match T with
    | TSel (varF x) m => TSel (varF x) m
    | TSel (varH i) m => TSel (varH i) m
    | TSel (varB i) m => TSel (if Nat.eqb k i then u else varB i) m
    | TAll m T1 T2  => TAll m (open_rec k u T1) (open_rec (S k) u T2)
    | TBind T2    => TBind (open_rec (S k) u T2)
    | TTop        => TTop
    | TBot        => TBot
    | TBool       => TBool
    | TMem m T1 T2  => TMem m (open_rec k u T1) (open_rec k u T2)
    | TAnd T1 T2  => TAnd (open_rec k u T1) (open_rec k u T2)
    | TOr  T1 T2  => TOr  (open_rec k u T1) (open_rec k u T2)
  end.

Definition open u T := open_rec 0 u T.

Fixpoint subst (U : var) (T : ty) {struct T} : ty :=
  match T with
    | TTop         => TTop
    | TBot         => TBot
    | TBool        => TBool
    | TMem m T1 T2   => TMem m (subst U T1) (subst U T2)
    | TSel (varB i) m => TSel (varB i) m
    | TSel (varF i) m => TSel (varF i) m
    | TSel (varH i) m => TSel (if Nat.eqb i 0 then U else varH (i-1)) m
    | TAll m T1 T2   => TAll m (subst U T1) (subst U T2)
    | TBind T2     => TBind (subst U T2)
    | TAnd T1 T2   => TAnd (subst U T1) (subst U T2)
    | TOr  T1 T2   => TOr  (subst U T1) (subst U T2)
  end.

Fixpoint nosubst (T : ty) {struct T} : Prop :=
  match T with
    | TTop         => True
    | TBot         => True
    | TBool        => True
    | TMem m T1 T2   => nosubst T1 /\ nosubst T2
    | TSel (varB i) m => True
    | TSel (varF i) m => True
    | TSel (varH i) m => i <> 0
    | TAll m T1 T2   => nosubst T1 /\ nosubst T2
    | TBind T2     => nosubst T2
    | TAnd T1 T2   => nosubst T1 /\ nosubst T2
    | TOr  T1 T2   => nosubst T1 /\ nosubst T2
  end.

Inductive stp: tenv -> tenv -> ty -> ty -> Prop :=
| stp_topx: forall G1 GH,
    stp G1 GH TTop TTop
| stp_botx: forall G1 GH,
    stp G1 GH TBot TBot
| stp_top: forall G1 GH T1,
    stp G1 GH T1 T1 ->
    stp G1 GH T1 TTop
| stp_bot: forall G1 GH T2,
    stp G1 GH T2 T2 ->
    stp G1 GH TBot T2
| stp_bool: forall G1 GH,
    stp G1 GH TBool TBool
| stp_mem: forall G1 GH m T1 T2 T3 T4,
    stp G1 GH T3 T1 ->
    stp G1 GH T2 T4 ->
    stp G1 GH (TMem m T1 T2) (TMem m T3 T4)
| stp_sel1: forall G1 GH TX m T2 x,
    index x G1 = Some TX ->
    closed 0 0 TX ->
    stp G1 [] TX (TMem m TBot T2) ->
    stp G1 GH T2 T2 ->
    stp G1 GH (TSel (varF x) m) T2
| stp_sel2: forall G1 GH TX m T1 x,
    index x G1 = Some TX ->
    closed 0 0 TX ->
    stp G1 [] TX (TMem m T1 TTop) ->
    stp G1 GH T1 T1 ->
    stp G1 GH T1 (TSel (varF x) m)
| stp_selb1: forall G1 GH TX m T2 x,
    index x G1 = Some TX ->
    stp G1 [] TX (TBind (TMem m TBot T2)) ->
    stp G1 GH (open (varF x) T2) (open (varF x) T2) ->
    stp G1 GH (TSel (varF x) m) (open (varF x) T2)
| stp_selb2: forall G1 GH TX m T1 x,
    index x G1 = Some TX ->
    stp G1 [] TX (TBind (TMem m T1 TTop)) ->
    stp G1 GH (open (varF x) T1) (open (varF x) T1) ->
    stp G1 GH (open (varF x) T1) (TSel (varF x) m)
| stp_selx: forall G1 GH TX x m,
    index x G1 = Some TX ->
    stp G1 GH (TSel (varF x) m) (TSel (varF x) m)
| stp_sela1: forall G1 GH GL TX m T2 x,
    tailr (S x) GH = (0,TX)::GL ->
    stp G1 ((0,TX)::GL) TX (TMem m TBot T2) ->
    stp G1 GH T2 T2 ->
    stp G1 GH (TSel (varH x) m) T2
| stp_sela2: forall G1 GH GL TX m T1 x,
    tailr (S x) GH = (0,TX)::GL ->
    stp G1 ((0,TX)::GL) TX (TMem m T1 TTop) ->
    stp G1 GH T1 T1 ->
    stp G1 GH T1 (TSel (varH x) m)
| stp_selab1: forall G1 GH GL TX m T2 T2' x,
    tailr (S x) GH = (0,TX)::GL ->
    closed 0 x (TBind (TMem m TBot T2)) ->
    stp G1 ((0,TX)::GL) TX (TBind (TMem m TBot T2)) ->
    T2' = (open (varH x) T2) ->
    stp G1 GH T2' T2' ->
    stp G1 GH (TSel (varH x) m) T2'
| stp_selab2: forall G1 GH GL TX m T1 T1' x,
    tailr (S x) GH = (0,TX)::GL ->
    closed 0 x (TBind (TMem m T1 TTop)) ->
    stp G1 ((0,TX)::GL) TX (TBind (TMem m T1 TTop)) ->
    T1' = (open (varH x) T1) ->
    stp G1 GH T1' T1' ->
    stp G1 GH T1' (TSel (varH x) m)
| stp_selax: forall G1 GH TX x m,
    indexr x GH = Some TX  ->
    stp G1 GH (TSel (varH x) m) (TSel (varH x) m)
| stp_all: forall G1 GH m T1 T2 T3 T4 x,
    stp G1 GH T3 T1 ->
    x = length GH ->
    closed 1 (length GH) T2 ->
    closed 1 (length GH) T4 ->
    stp G1 ((0,T1)::GH) (open (varH x) T2) (open (varH x) T2) ->
    stp G1 ((0,T3)::GH) (open (varH x) T2) (open (varH x) T4) ->
    stp G1 GH (TAll m T1 T2) (TAll m T3 T4)
| stp_bindx: forall G1 GH T1 T2 x,
    x = length GH ->
    closed 1 (length GH) T1 ->
    closed 1 (length GH) T2 ->
    stp G1 ((0,open (varH x) T2)::GH) (open (varH x) T2) (open (varH x) T2) ->
    stp G1 ((0,open (varH x) T1)::GH) (open (varH x) T1) (open (varH x) T2) ->
    stp G1 GH (TBind T1) (TBind T2)
| stp_bind1: forall G1 GH T1 T2 x,
    x = length GH ->
    closed 1 (length GH) T1 ->
    closed 0 (length GH) T2 ->
    stp G1 GH T2 T2 ->
    stp G1 ((0,open (varH x) T1)::GH) (open (varH x) T1) T2 ->
    stp G1 GH (TBind T1) T2
| stp_and11: forall G GH T1 T2 T,
    stp G GH T1 T ->
    stp G GH T2 T2 ->
    stp G GH (TAnd T1 T2) T
| stp_and12: forall G GH T1 T2 T,
    stp G GH T2 T ->
    stp G GH T1 T1 ->
    stp G GH (TAnd T1 T2) T
| stp_and2: forall G GH T1 T2 T,
    stp G GH T T1 ->
    stp G GH T T2 ->
    stp G GH T (TAnd T1 T2)
| stp_or21: forall G GH T1 T2 T,
    stp G GH T T1 ->
    stp G GH T2 T2 ->
    stp G GH T (TOr T1 T2)
| stp_or22: forall G GH T1 T2 T,
    stp G GH T T2 ->
    stp G GH T1 T1 ->
    stp G GH T (TOr T1 T2)
| stp_or1: forall G GH T1 T2 T,
    stp G GH T1 T ->
    stp G GH T2 T ->
    stp G GH (TOr T1 T2) T
.

Definition tand (t1: ty) (t2: ty) :=
  match t2 with
    | TTop => t1
    | _ => TAnd t1 t2
  end.

Inductive has_type : tenv -> tm -> ty -> Prop :=
| t_true: forall env,
           has_type env ttrue TBool
| t_false: forall env,
           has_type env tfalse TBool
| t_var: forall x env T1,
           index x env = Some T1 ->
           stp env [] T1 T1 ->
           has_type env (tvar x) T1
| t_var_pack: forall x env T1,
           has_type env (tvar x) (open (varF x) T1) ->
           stp env [] (TBind T1) (TBind T1) ->
           has_type env (tvar x) (TBind T1)
| t_var_unpack: forall x env T1,
           has_type env (tvar x) (TBind T1) ->
           stp env [] (open (varF x) T1) (open (varF x) T1) ->
           has_type env (tvar x) (open (varF x) T1)
| t_obj: forall env f ds T TX,
           fresh env = f ->
           open (varF f) T = TX ->
           dcs_has_type ((f, TX)::env) f ds T ->
           stp ((f, TX)::env) [] TX TX ->
           stp env [] (TBind T) (TBind T) ->
           has_type env (tobj f ds) (TBind T)
| t_app: forall env f l x T1 T2,
           has_type env f (TAll l T1 T2) ->
           has_type env x T1 ->
           stp env [] T2 T2 ->
           has_type env (tapp f l x) T2
| t_app_var: forall env f l x T1 T2 T2X,
           has_type env f (TAll l T1 T2) ->
           has_type env (tvar x) T1 ->
           open (varF x) T2 = T2X ->
           stp env [] T2X T2X ->
           has_type env (tapp f l (tvar x)) T2X
| t_let: forall env x ex e Tx T,
           has_type env ex Tx ->
           fresh env <= x ->
           has_type ((x, Tx)::env) e T ->
           stp env [] T T ->
           has_type env (tlet x ex e) T

| t_sub: forall env e T1 T2,
           has_type env e T1 ->
           stp env [] T1 T2 ->
           has_type env e T2

with dcs_has_type: tenv -> id -> list (id * def) -> ty -> Prop :=
| dt_nil: forall env f,
            dcs_has_type env f nil TTop
| dt_fun: forall env f x y m T1 T2 dcs TS T,
            has_type ((x,open (varF f) T1)::env) y (open (varF x) (open_rec 1 (varF f) T2)) ->
            dcs_has_type env f dcs TS ->
            fresh env = x ->
            m = length dcs ->
            T = tand (TAll m T1 T2) TS ->
            dcs_has_type env f ((m, dfun x y)::dcs) T
| dt_mem: forall env f m T1 dcs TS T,
            dcs_has_type env f dcs TS ->
            m = length dcs ->
            T = tand (TMem m T1 T1) TS ->
            dcs_has_type env f ((m, dmem T1)::dcs) T
.

Definition MAX := 1.

Inductive stp2: nat -> bool -> venv -> ty -> venv -> ty -> list (id*(venv*ty)) -> nat -> Prop :=
| stp2_topx: forall m G1 G2 GH n1,
    stp2 m true G1 TTop G2 TTop GH (S n1)
| stp2_botx: forall m G1 G2 GH n1,
    stp2 m true G1 TBot G2 TBot GH (S n1)
| stp2_top: forall m G1 G2 GH T n1,
    stp2 m true G1 T G1 T GH n1 ->
    stp2 m true G1 T G2 TTop GH (S n1)
| stp2_bot: forall m G1 G2 GH T n1,
    stp2 m true G2 T G2 T GH n1 ->
    stp2 m true G1 TBot G2 T GH (S n1)
| stp2_bool: forall m G1 G2 GH n1,
    stp2 m true G1 TBool G2 TBool GH (S n1)
| stp2_mem: forall G1 G2 l T1 T2 T3 T4 GH n1 n2,
    stp2 0 false G2 T3 G1 T1 GH n1 ->
    stp2 0 true G1 T2 G2 T4 GH n2 ->
    stp2 0 true G1 (TMem l T1 T2) G2 (TMem l T3 T4) GH (S (n1+n2))

| stp2_mem2: forall m G1 G2 l T1 T2 T3 T4 GH n1 n2,
    stp2 (S m) false G2 T3 G1 T1 GH n1 ->
    stp2 (S m) false G1 T2 G2 T4 GH n2 ->
    stp2 (S m) true G1 (TMem l T1 T2) G2 (TMem l T3 T4) GH (S (n1+n2))



| stp2_strong_sel1: forall G1 G2 GX l f ds TX x T2 GH GX' TX' n1 n2,
    index x G1 = Some (vobj GX f ds) ->
    val_type GX' (vobj GX f ds) TX' 1 ->
    stp2 0 false GX' TX' G2 (TMem l TBot T2) GH n2 ->
    index l ds = Some (dmem TX) ->
    closed 1 0 TX ->
    stp2 0 true ((f, vobj GX f ds)::GX) (open (varF f) TX) G2 T2 GH n1 ->
    stp2 0 true G1 (TSel (varF x) l) G2 T2 GH (S (n1+n2))

| stp2_strong_sel2: forall G1 G2 GX l f ds TX x T1 GH GX' TX' n1 n2,
    index x G2 = Some (vobj GX f ds) ->
    val_type GX' (vobj GX f ds) TX' 1 ->
    stp2 0 false GX' TX' G1 (TMem l T1 TTop) GH n2 ->
    index l ds = Some (dmem TX) ->
    closed 1 0 TX ->
    stp2 0 false G1 T1 ((f, vobj GX f ds)::GX) (open (varF f) TX) GH n1 ->
    stp2 0 true G1 T1 G2 (TSel (varF x) l) GH (S (n1+n2))

| stp2_strong_selx: forall G1 G2 l v x1 x2 GH n1,
    index x1 G1 = Some v ->
    index x2 G2 = Some v ->
    stp2 0 true G1 (TSel (varF x1) l) G2 (TSel (varF x2) l) GH n1



| stp2_sel1: forall m G1 G2 GX l TX x T2 GH n1 n2 v,
    index x G1 = Some v ->
    val_type GX v TX 1 ->
    closed 0 0 TX ->
    stp2 (S m) false GX TX G2 (TMem l TBot T2) GH n1 ->
    stp2 (S m) true G2 T2 G2 T2 GH n2 ->
    stp2 (S m) true G1 (TSel (varF x) l) G2 T2 GH (S (n1+n2))











| stp2_sel2: forall m G1 G2 GX l TX x T1 GH n1 n2 v,
    index x G2 = Some v ->
    val_type GX v TX 1 ->
    closed 0 0 TX ->
    stp2 (S m) false GX TX G1 (TMem l T1 TTop) GH n1 ->
    stp2 (S m) true G1 T1 G1 T1 GH n2 ->
    stp2 (S m) true G1 T1 G2 (TSel (varF x) l) GH (S (n1+n2))











| stp2_selx: forall m G1 G2 l v x1 x2 GH n1,
    index x1 G1 = Some v ->
    index x2 G2 = Some v ->
    stp2 (S m) true G1 (TSel (varF x1) l) G2 (TSel (varF x2) l) GH (S n1)










| stp2_sela1: forall m G1 G2 GX l TX x T2 GH GU GL n1 n2,
    indexr x GH = Some (GX, TX) ->
    closed 0 (S x) TX ->
    length GL = (S x) ->
    GH = GU ++ GL ->
    stp2 (S m) false GX TX G2 (TMem l TBot T2) GL n1 ->
    stp2 (S m) true G2 T2 G2 T2 GH n2 ->
    stp2 (S m) true G1 (TSel (varH x) l) G2 T2 GH (S (n1+n2))

| stp2_sela2: forall m G1 G2 GX l TX x T1 GH GU GL n1 n2,
    indexr x GH = Some (GX, TX) ->
    closed 0 (S x) TX ->
    length GL = (S x) ->
    GH = GU ++ GL ->
    stp2 (S m) false GX TX G1 (TMem l T1 TTop) GL n1 ->
    stp2 (S m) true G1 T1 G1 T1 GH n2 ->
    stp2 (S m) true G1 T1 G2 (TSel (varH x) l) GH (S (n1+n2))

| stp2_selab1: forall m G1 G2 GX l TX x T2 T2' GH GU GL n1 n2,
    indexr x GH = Some (GX, TX) ->
    closed 1 x T2 ->
    length GL = (S x) ->
    GH = GU ++ GL ->
    stp2 (S m) false GX TX G2 (TBind (TMem l TBot T2)) GL n1 ->
    T2' = (open (varH x) T2) ->
    stp2 (S m) true G2 T2' G2 T2' GH n2 ->
    stp2 (S m) true G1 (TSel (varH x) l) G2 T2' GH (S (n1+n2))

| stp2_selab2: forall m G1 G2 GX l TX x T1 T1' GH GU GL n1 n2,
    indexr x GH = Some (GX, TX) ->
    closed 1 x T1 ->
    length GL = (S x) ->
    GH = GU ++ GL ->
    stp2 (S m) false GX TX G1 (TBind (TMem l T1 TTop)) GL n1 ->
    T1' = (open (varH x) T1) ->
    stp2 (S m) true G1 T1' G1 T1' GH n2 ->
    stp2 (S m) true G1 T1' G2 (TSel (varH x) l) GH (S (n1+n2))



| stp2_selax: forall m G1 G2 GX l TX x GH n1,
    indexr x GH = Some (GX, TX) ->
    stp2 (S m) true G1 (TSel (varH x) l) G2 (TSel (varH x) l) GH (S n1)


| stp2_all: forall m G1 G2 l T1 T2 T3 T4 GH n1 n1' n2,
    stp2 1 false G2 T3 G1 T1 GH n1 ->
    closed 1 (length GH) T2 ->
    closed 1 (length GH) T4 ->
    stp2 1 false G1 (open (varH (length GH)) T2) G1 (open (varH (length GH)) T2) ((0,(G1, T1))::GH) n1' ->
    stp2 1 false G1 (open (varH (length GH)) T2) G2 (open (varH (length GH)) T4) ((0,(G2, T3))::GH) n2 ->
    stp2 m true G1 (TAll l T1 T2) G2 (TAll l T3 T4) GH (S (n1+n1'+n2))

| stp2_bind: forall m G1 G2 T1 T2 GH n1 n2,
    closed 1 (length GH) T1 ->
    closed 1 (length GH) T2 ->
    stp2 1 false G2 (open (varH (length GH)) T2) G2 (open (varH (length GH)) T2) ((0,(G2, open (varH (length GH)) T2))::GH) n2 ->
    stp2 1 false G1 (open (varH (length GH)) T1) G2 (open (varH (length GH)) T2) ((0,(G1, open (varH (length GH)) T1))::GH) n1 ->
    stp2 m true G1 (TBind T1) G2 (TBind T2) GH (S (n1+n2))

| stp2_bind1: forall m G1 G2 T1 T2 GH n1 n2,
    closed 1 (length GH) T1 ->
    closed 0 (length GH) T2 ->
    stp2 m false G2 T2 G2 T2 GH n2 ->
    stp2 1 false G1 (open (varH (length GH)) T1) G2 T2 ((0,(G1, open (varH (length GH)) T1))::GH) n1 ->
    stp2 m true G1 (TBind T1) G2 T2 GH (S (n1+n2))


| stp2_and11: forall m n1 n2 G1 G2 GH T1 T2 T,
    stp2 m true G1 T1 G2 T GH n1 ->
    stp2 m true G1 T2 G1 T2 GH n2 ->
    stp2 m true G1 (TAnd T1 T2) G2 T GH (S (n1+n2))
| stp2_and12: forall m n1 n2 G1 G2 GH T1 T2 T,
    stp2 m true G1 T2 G2 T GH n1 ->
    stp2 m true G1 T1 G1 T1 GH n2 ->
    stp2 m true G1 (TAnd T1 T2) G2 T GH (S (n1+n2))
| stp2_and2: forall m n1 n2 G1 G2 GH T1 T2 T,
    stp2 m false G1 T G2 T1 GH n1 ->
    stp2 m false G1 T G2 T2 GH n2 ->
    stp2 m true G1 T G2 (TAnd T1 T2) GH (S (n1+n2))

| stp2_or21: forall m n1 n2 G1 G2 GH T1 T2 T,
    stp2 m false G1 T G2 T1 GH n1 ->
    stp2 m true G2 T2 G2 T2 GH n2 ->
    stp2 m true G1 T G2 (TOr T1 T2) GH (S (n1+n2))
| stp2_or22: forall m n1 n2 G1 G2 GH T1 T2 T,
    stp2 m false G1 T G2 T2 GH n1 ->
    stp2 m true G2 T1 G2 T1 GH n2 ->
    stp2 m true G1 T G2 (TOr T1 T2) GH (S (n1+n2))
| stp2_or1: forall m n1 n2 G1 G2 GH T1 T2 T,
    stp2 m true G1 T1 G2 T GH n1 ->
    stp2 m true G1 T2 G2 T GH n2 ->
    stp2 m true G1 (TOr T1 T2) G2 T GH (S (n1+n2))

| stp2_wrapf: forall m G1 G2 T1 T2 GH n1,
    stp2 m true G1 T1 G2 T2 GH n1 ->
    stp2 m false G1 T1 G2 T2 GH (S n1)
| stp2_transf: forall m G1 G2 G3 T1 T2 T3 GH n1 n2,
    stp2 m true G1 T1 G2 T2 GH n1 ->
    stp2 m false G2 T2 G3 T3 GH n2 ->
    stp2 m false G1 T1 G3 T3 GH (S (n1+n2))



with wf_env : venv -> tenv -> Prop :=
| wfe_nil : wf_env nil nil
| wfe_cons : forall n v t vs ts nv,
    val_type ((n,v)::vs) v t nv ->
    wf_env vs ts ->
    wf_env (cons (n,v) vs) (cons (n,t) ts)

with val_type : venv -> vl -> ty -> nat -> Prop :=
| v_bool: forall venv b TE,
    (exists n, stp2 0 true [] TBool venv TE [] n) ->
    val_type venv (vbool b) TE 1
| v_obj: forall env venv tenv f ds T TX TE,
    wf_env venv tenv ->
    open (varF f) T = TX ->
    dcs_has_type ((f,TX)::tenv) f ds T ->
    fresh venv = f ->
    (exists n, stp2 0 true ((f, vobj venv f ds)::venv) TX env TE [] n)->
    val_type env (vobj venv f ds) TE 1
| v_pack: forall venv venv3 x v T T2 T3 n,
    index x venv = Some v ->
    val_type venv v T n ->
    open (varF x) T2 = T ->
    (exists n, stp2 0 true venv (TBind T2) venv3 T3 [] n) ->
    val_type venv3 v T3 (S n)
.

Inductive wf_envh : venv -> aenv -> tenv -> Prop :=
| wfeh_nil : forall vvs, wf_envh vvs nil nil
| wfeh_cons : forall n t vs vvs ts,
    wf_envh vvs vs ts ->
    wf_envh vvs (cons (n,(vvs,t)) vs) (cons (n,t) ts)
.

Inductive valh_type : venv -> aenv -> (venv*ty) -> ty -> Prop :=
| v_tya: forall aenv venv T1,
    valh_type venv aenv (venv, T1) T1
.

Definition stpd2 b G1 T1 G2 T2 GH := exists n, stp2 MAX b G1 T1 G2 T2 GH n.

Definition sstpd2 b G1 T1 G2 T2 GH := exists n, stp2 0 b G1 T1 G2 T2 GH n.

Definition valtpd G v T := exists n, val_type G v T n.

Fixpoint teval(n: nat)(env: venv)(t: tm){struct n}: option (option vl) :=
  match n with
    | 0 => None
    | S n =>
      match t with
        | ttrue      => Some (Some (vbool true))
        | tfalse     => Some (Some (vbool false))
        | tvar x     => Some (index x env)
        | tobj f ds => Some (Some (vobj env f ds))
        | tapp ef m ex   =>
          match teval n env ex with
            | None => None
            | Some None => Some None
            | Some (Some vx) =>
              match teval n env ef with
                | None => None
                | Some None => Some None
                | Some (Some (vbool _)) => Some None
                | Some (Some (vobj env2 f ds)) =>
                  match index m ds with
                    | None => Some None
                    | Some (dmem _) => Some None
                    | Some (dfun x ey) =>
                      teval n ((x,vx)::(f,vobj env2 f ds)::env2) ey
                  end
              end
          end
        | tlet x ex ey =>
          match teval n env ex with
            | None => None
            | Some None => Some None
            | Some (Some vx) => teval n ((x,vx)::env) ey
          end
      end
  end.

Inductive res_type: venv -> option vl -> ty -> Prop :=
| not_stuck: forall venv v T n,
      val_type venv v T n ->
      res_type venv (Some v) T.

Theorem full_safety : forall n e tenv venv res T,
  teval n venv e = Some res -> has_type tenv e T -> wf_env venv tenv ->
  res_type venv res T.

End DOT.
