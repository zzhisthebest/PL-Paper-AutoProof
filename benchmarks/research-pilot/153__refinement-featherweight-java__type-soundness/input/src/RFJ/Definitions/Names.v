Require Import Arith.

Require Import Lists.ListSet.

Require Import List.

Require Import Definitions.Syntax.

Definition names := set vname.

Definition empty := empty_set vname.

Definition singleton (x:vname) := @set_add vname Nat.eq_dec x empty.

Definition names_add := @set_add vname Nat.eq_dec.

Definition names_rem := @set_remove vname Nat.eq_dec.

Definition names_mem := @set_mem vname Nat.eq_dec.

Definition union := @set_union vname Nat.eq_dec.

Definition intersect := @set_inter vname Nat.eq_dec.

Definition diff := @set_diff vname Nat.eq_dec.

Definition Elem := @set_In vname.

Definition Subset (xs : names) (ys: names) : Prop :=
    forall (x : vname), Elem x xs -> Elem x ys.

Fixpoint Elem_many nml nms {struct nml}:=
  match nml with
  | nil => True
  | n::nml' => Elem n nms /\ Elem_many nml' nms
  end.

Fixpoint fv (e0:expr) : names :=
    match e0 with
    | (Bc _)          => empty
    | (Ic _)          => empty
    | (BV _)          => empty
    | (FV x)          => singleton x
    | (ExpUnOp op e)     => fv e
    | (ExpBinOp op e1 e2)=> union (fv e1) (fv e2)
    | (ExpMethodInvoc e1 m e2)=> union (fv e1) (fv e2)
    | (ExpFieldAccess e1 f) => fv e1
    | (ExpNew c es) => (fix f (es': [expr]) := match es' with | nil => empty | e::es''=> union (fv e) (f es'') end) es
    | (ExpLet   ex e)    => union (fv ex) (fv e)
    end

with free (t0:type) : names :=
    match t0 with
    | (TRefn b   rs)     => fvP rs
    end

with fvP (ps0:preds) : names :=
    match ps0 with
    | PEmpty       => empty
    | (PCons p ps) => union (fv p) (fvP ps)
    end.

Fixpoint frees ts: names :=
  match ts with
  | nil => empty
  | t:: ts' => union (free t) (frees ts')
  end.

Fixpoint fvs ts: names :=
  match ts with
  | nil => empty
  | t:: ts' => union (fv t) (fvs ts')
  end.

Inductive env : Set :=
    | Empty
    | Cons  (x : vname) (t : type) (g : env).

Fixpoint Cons_many ys ts e :=
  match ys, ts with
  | y::ys', t::ts' => Cons y t (Cons_many ys' ts' e)
  | _, _ => e
  end.

Fixpoint Cons_many_many ys ts e :=
  match ys, ts with
  | y::ys', t::ts' => Cons_many ys ts e::(Cons_many_many ys' ts' e)
  | _, _ => e::nil
  end.

Fixpoint binds (g : env) : names :=
    match g with
    | Empty         => empty
    | (Cons  x t g) => names_add x (binds g)
    end.

Definition in_env (x : vname) (g : env) : Prop := Elem x (binds g).

Fixpoint unique (g0 : env) : Prop :=
    match g0 with
    | Empty         => True
    | (Cons  x t g) => ~ in_env x g /\ unique g
    end.

Fixpoint bound_in (x : vname) (t : type) (g0 : env) : Prop :=
    match g0 with
    | Empty          => False
    | (Cons  y t' g) => (x = y /\ t = t') \/ bound_in x t g
    end.

Inductive fjenv :=
    | FEmpty
    | FCons  (x : vname) (t : fjtype) (g : fjenv).

Fixpoint bindsFJ (g : fjenv) : names :=
    match g with
    | FEmpty         => empty
    | (FCons  x t g) => names_add x (bindsFJ g)
    end.

Definition in_envFJ (x : vname) (g : fjenv) : Prop := Elem x (bindsFJ g).

Fixpoint uniqueF (g0 : fjenv) : Prop :=
    match g0 with
    | FEmpty         => True
    | (FCons  x t g) => ~ in_envFJ x g /\ uniqueF g
    end.

Fixpoint bound_inF (x : vname) (t : fjtype) (g0 : fjenv) : Prop :=
    match g0 with
    | FEmpty          => False
    | (FCons  y t' g) => (x = y /\ t = t') \/ bound_inF x t g
    end.

Fixpoint erase_env (g0 : env) : fjenv :=
    match g0 with
    | Empty         => FEmpty
    | (Cons  x t g) => FCons  x (erase t) (erase_env g)
    end.

Definition fresh (xs:names) : vname  :=  1 + List.list_max xs.

Definition fresh_varF (xs : names) (g : fjenv) : vname :=
  max (fresh xs) (fresh (bindsFJ g)).

Definition fresh_var_excludingF (xs:names) (g:fjenv) (y:vname) :=
    max (fresh_varF xs g) (1+y).

Definition fresh_varFE (xs : names) (g : fjenv) (e : expr) : vname :=
  max (fresh_varF xs g) ((fresh (fv e))).

Definition fresh_var (xs : names) (g : env) : vname :=
  max (fresh xs) (fresh (binds g)).

Definition fresh_var_excluding (xs:names) (g:env) (y:vname) :=
    max (fresh_var xs g) (1+y).

Definition fresh_varE (xs : names) (g : env) (e : expr) : vname :=
  max (fresh_var xs g) (fresh (fv e)).

Definition fresh_varT (xs : names) (g : env) (t : type) : vname :=
  max (fresh_var xs g) (fresh (free t)).

Fixpoint concatE (g g'0 : env) : env :=
    match g'0 with
    | Empty          => g
    | (Cons  x t g') => Cons  x t (concatE g g')
    end.

Fixpoint concatF (g g'0 : fjenv) : fjenv :=
  match g'0 with
  | FEmpty          => g
  | (FCons  x t g') => FCons  x t (concatF g g')
  end.

Fixpoint esubFV (x:vname) (v:expr) (g0:env) : env :=
  match g0 with
  | Empty           => Empty
  | (Cons  z t_z g) => Cons z (tsubFV x v t_z) (esubFV x v g)
  end.
