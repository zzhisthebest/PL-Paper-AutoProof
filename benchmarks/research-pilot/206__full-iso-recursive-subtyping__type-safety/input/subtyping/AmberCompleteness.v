Require Import Metalib.Metatheory.

Require Import Program.Equality.

Require Export AmberSoundness.

Require Export PositiveSubtyping.

Definition env_mode := list ( Mode).

Inductive monotone: env -> typ -> typ -> env_mode -> Prop :=
| M_base: forall A B,
    monotone nil A B nil
| M_neg: forall A B E  EM  X ,
    monotone E A B EM ->
    posvar Neg X A B ->
    monotone (X~bind_sub ++ E) A B  ( Neg::EM)
| M_pos: forall A B E  EM  X ,
    monotone E A B  EM ->
    posvar Pos X A B ->
    monotone (X~bind_sub ++ E) A B  ( Pos::EM)
.

Fixpoint domL (E : env_amber) : atoms :=
  match E with
  | nil => {}
  | (X,Y)::E' => add X (domL E')
  end.

Fixpoint domR (E : env_amber) : atoms :=
  match E with
  | nil => {}
  | (X,Y)::E' => add Y (domR E')
  end.

Fixpoint domS (E : list atom) : atoms :=
  match E with
  | nil => {}
  | Y::E' => add Y (domS E')
  end.

Inductive env_copy:  env ->  list atom -> atoms -> Prop :=
| EC_base: forall A,
    env_copy  nil  nil A
| EC_cons1: forall  X EX Y EY m Z A,
    env_copy  EX  EY A ->
    X \notin dom EX ->
    X \in domS EY ->
    Y \notin domS EY \u {{X}} \u dom EX \u A ->
    Z \notin domS EY \u {{Y}} \u {{X}} \u dom EX \u A ->
    env_copy (X~m ++ EX)  (Z :: Y :: EY) A
| EC_cons2: forall  X EX Y EY m A,
    env_copy  EX  EY A ->
    X \notin dom EX \u domS EY->
    Y \notin domS EY \u {{X}} \u dom EX \u A ->
    env_copy (X~m ++ EX)  (X :: Y :: EY) A.

Definition minus A B := forall X, X \in A -> X \notin B.

Inductive env_conv:  env -> env_amber -> Prop :=
| EV_base:
    env_conv  nil  nil
| EV_cons: forall  X EX Y EY m ,
    env_conv EX EY ->
    env_conv (X~m ++ EX) ((X,Y)::EY).

Inductive distinct:  list atom -> Prop :=
| DT_base:
    distinct nil
| DT_cons: forall  X E ,
    distinct E ->
    X \notin domS E ->
    distinct (X::E).

Fixpoint filter_env (E:env) (G:list atom) : list atom :=
  match E with
  | nil => G
  | (X,_)::E' => filter_env E' (List.remove eq_dec X G)
  end.

Fixpoint domE (E:env) : list atom :=
  match E with
  | nil => nil
  | (X,m)::E' => X::(domE E')
  end.

Definition disjoint (E:atoms) (G:atoms) :=
  forall X, (X \in E -> X \notin G) /\ (X \in G -> X \notin E).

Definition flipEx (A : option Mode) : option Mode :=
  match A with
  | Some x => Some (flip x)
  | None => None
  end.

Definition eqMode (a b: Mode)  : bool :=
  match a,b with
  | Pos, Pos => true
  | Neg, Neg => true
  | _,_ => false
  end.

Definition eqM (a: option Mode) (b: Mode) : bool :=
  match a with
  | None => false
  | Some a' => eqMode a' b
  end.

Fixpoint amber_cov (Ea : env_amber) (Em : env_mode) (T:typ) (m:Mode) : typ :=
  match Ea, Em with
  | (X,Y)::E, m'::Em' => if (eqMode m' m) then amber_cov E Em' (subst_tt X Y T) m
                         else amber_cov E Em' T m
  | _,_ => T
  end.

Fixpoint isBindsub (E:env) : Prop :=
  match E with
  | nil => True
  | (a,bind_sub)::E' => isBindsub E'
  | _ => False
  end.
