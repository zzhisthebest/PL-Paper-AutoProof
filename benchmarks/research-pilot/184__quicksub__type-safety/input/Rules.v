Require Import Metalib.Metatheory.

Require Import Program.Equality.

Inductive typ : Set :=
| typ_top   : typ
| typ_nat   : typ
| typ_bvar  : nat -> typ
| typ_fvar  : var -> typ
| typ_mu :    typ -> typ
| typ_arrow : typ -> typ -> typ
.

Coercion typ_bvar : nat >-> typ.

Coercion typ_fvar : atom >-> typ.

Fixpoint open_tt_rec (K : nat) (U : typ) (T : typ) {struct T} : typ :=
  match T with
  | typ_nat         => typ_nat
  | typ_top         => typ_top
  | typ_bvar J      => if K === J then U else (typ_bvar J)
  | typ_fvar X      => typ_fvar X
  | typ_arrow T1 T2 => typ_arrow (open_tt_rec K U T1) (open_tt_rec K U T2)
  | typ_mu T        => typ_mu (open_tt_rec (S K) U T)
  end.

Definition open_tt T U := open_tt_rec 0 U T.

Inductive type : typ -> Prop :=
  | type_top :
      type typ_top
  | type_nat :
      type typ_nat
  | type_var : forall X,
      type (typ_fvar X)
  | type_arrow : forall T1 T2,
      type T1 ->
      type T2 ->
      type (typ_arrow T1 T2)
  | type_mu : forall L T,
      (forall X, X \notin L -> type (open_tt T (typ_fvar X))) ->
      type (typ_mu T)
.

Fixpoint subst_tt (Z : atom) (U : typ) (T : typ) {struct T} : typ :=
  match T with
  | typ_top => typ_top
  | typ_nat => typ_nat
  | typ_bvar J => typ_bvar J
  | typ_fvar X => if X == Z then U else (typ_fvar X)
  | typ_arrow T1 T2 => typ_arrow (subst_tt Z U T1) (subst_tt Z U T2)
  | typ_mu T => typ_mu (subst_tt Z U T)
  end.

Fixpoint fv_tt (T : typ) {struct T} : atoms :=
  match T with
  | typ_top => {}
  | typ_nat => {}
  | typ_bvar J => {}
  | typ_fvar X => {{ X }}
  | typ_arrow T1 T2 => (fv_tt T1) `union` (fv_tt T2)
  | typ_mu T => (fv_tt T)
  end.

Inductive IsoMode := Neg | Pos.

Inductive CmpMode := Lt | Eq.

Inductive binding : Set :=
  | bind_sub : IsoMode -> binding
  | bind_typ : typ -> binding.

Definition env := list (atom * binding).

Definition emp := Metatheory.empty.

Notation empty := (@nil (atom * binding)).

Inductive WFS : env -> typ -> Prop :=
| WFS_top : forall E, WFS E typ_top
| WFS_nat : forall E, WFS E typ_nat
| WFS_fvar : forall X E im,
    binds X (bind_sub im) E ->
    WFS E (typ_fvar X)
| WFS_arrow : forall E A B,
    WFS E A ->
    WFS E B ->
    WFS E (typ_arrow A B)
| WFS_rec : forall L E A im,


      (forall  X , X \notin L ->
        WFS (X ~ bind_sub im ++ E) (open_tt A X)) ->
      WFS E (typ_mu A).

Inductive wf_env : env -> Prop :=
  | wf_env_empty :
      wf_env empty
  | wf_env_sub : forall (E : env) (X : atom) im,
      wf_env E ->
      X \notin dom E ->
      wf_env (X ~ bind_sub im ++ E)
  | wf_env_typ : forall (E : env) (x : atom) (T : typ),
      wf_env E ->
      WFS E T ->
      x `notin` dom E ->
      wf_env (x ~ bind_typ T ++ E).

Definition flip_im (im : IsoMode) : IsoMode :=
  match im with
    | Neg => Pos
    | Pos => Neg
  end.

Definition compose_cm (cm1 cm2 : CmpMode) (evs1 evs2 : atoms ) : option (CmpMode) :=
  match cm1, cm2 with
    | Lt, Lt => Some Lt
    | Eq, Lt => if AtomSetImpl.is_empty evs1 then Some Lt else None
    | Lt, Eq => if AtomSetImpl.is_empty evs2 then Some Lt else None
    | Eq, Eq => Some Eq
  end.

Inductive exp : Set :=
  | exp_bvar : nat -> exp
  | exp_fvar : atom -> exp
  | exp_abs : typ -> exp -> exp
  | exp_app : exp -> exp -> exp
  | exp_nat : exp
  | exp_unfold : typ -> exp -> exp
  | exp_fold : typ -> exp -> exp
.

Coercion exp_bvar : nat >-> exp.

Coercion exp_fvar : atom >-> exp.

Fixpoint open_ee_rec (k : nat) (f : exp) (e : exp)  {struct e} : exp :=
  match e with
  | exp_bvar i => if k == i then f else (exp_bvar i)
  | exp_fvar x => exp_fvar x
  | exp_abs t e1 => exp_abs t (open_ee_rec (S k) f e1)
  | exp_app e1 e2 => exp_app (open_ee_rec k f e1) (open_ee_rec k f e2)
  | exp_nat => exp_nat
  | exp_unfold T e => exp_unfold T (open_ee_rec k f e)
  | exp_fold T e => exp_fold T (open_ee_rec k f e)
  end.

Notation open_ee e1 e2     := (open_ee_rec 0 e2 e1).

Fixpoint subst_ee (y:atom) (u:exp) (e:exp) {struct e} : exp :=
  match e with
  | (exp_bvar n)   => exp_bvar n
  | (exp_fvar x)   => (if x == y then u else (exp_fvar x))
  | (exp_abs T e1)    => exp_abs T (subst_ee y u e1)
  | (exp_app e1 e2) => exp_app (subst_ee y u e1) (subst_ee y u e2)
  | exp_nat => exp_nat
  | exp_unfold T e => exp_unfold T (subst_ee y u e)
  | exp_fold T e => exp_fold T (subst_ee y u e)
  end.

Fixpoint fv_exp (e_5:exp) : vars :=
  match e_5 with
  | (exp_bvar nat)   => {}
  | (exp_fvar x)   => {{x}}
  | (exp_abs T e)     => fv_exp e
  | (exp_app e1 e2) => fv_exp e1 \u fv_exp e2
  | exp_nat => {}
  | exp_unfold T e => fv_exp e
  | exp_fold T e => fv_exp e
  end.

Inductive expr : exp -> Prop :=
 | lc_fvar : forall (x:var),
     expr (exp_fvar x)
 | lc_abs : forall (e:exp) L T,
     (forall x, x \notin L -> expr (open_ee e (exp_fvar x)))  ->
     type T ->
     expr (exp_abs T e)
 | lc_app : forall (e1 e2:exp),
     expr e1 ->
     expr e2 ->
     expr (exp_app e1 e2)
 | lc_nat :
     expr exp_nat
 | lc_unfold: forall T e,
     type T ->
     expr e ->
     expr (exp_unfold T e)
 | lc_fold: forall T e,
     type T ->
     expr e ->
     expr (exp_fold T e).

Inductive Sub : IsoMode -> CmpMode -> atoms -> env -> typ -> typ -> Prop :=





| Sa_nat: forall E im,
    wf_env E ->
    Sub im Eq emp E typ_nat typ_nat





| Sa_top_eq: forall E im,
    wf_env E ->
    Sub im Eq emp E typ_top typ_top






| Sa_top_lt: forall E im A,
    wf_env E -> WFS E A -> A <> typ_top ->
    Sub im Lt emp E A typ_top
| Sa_fvar_pos: forall E X im,
    wf_env E -> binds X (bind_sub im) E ->
    Sub im Eq emp E (typ_fvar X) (typ_fvar X)
| Sa_fvar_neg: forall E X im,
    wf_env E -> binds X (bind_sub (flip_im im)) E ->
    Sub im Eq (singleton X) E (typ_fvar X) (typ_fvar X)
| Sa_arrow: forall E A1 A2 B1 B2 cm1 cm2 evs1 evs2 cm im,
    Sub (flip_im im) cm1 evs1 E B1 A1 ->
    Sub im cm2 evs2 E A2 B2 ->
    compose_cm cm1 cm2 evs1 evs2 = Some cm ->
    Sub im cm (evs1 `union` evs2) E (typ_arrow A1 A2) (typ_arrow B1 B2)
| Sa_rec_lt: forall L A1 A2 evs E im,
    (forall X,  X \notin L ->
        Sub im Lt evs (X ~ bind_sub im ++ E) (open_tt A1 X) (open_tt A2 X)) ->

    Sub im Lt evs E (typ_mu A1) (typ_mu A2)
| Sa_rec_eq_notin: forall L A1 A2 evs E im,
    (forall X,  X \notin L ->
        Sub im Eq evs (X ~ bind_sub im ++ E) (open_tt A1 X) (open_tt A2 X)) ->
    Sub im Eq evs E (typ_mu A1) (typ_mu A2)





| Sa_rec_eq_in: forall L A1 A2 evs E im,
    (forall X,  X \notin L ->
        Sub im Eq (add X evs) (X ~ bind_sub im ++ E) (open_tt A1 X) (open_tt A2 X)) ->
    Sub im Eq (evs `union` fv_tt A1) E (typ_mu A1) (typ_mu A2)
| Sa_evs_proper: forall im cm evs evs' E A1 A2,
    Sub im cm evs E A1 A2 ->
    evs [=] evs' ->
    Sub im cm evs' E A1 A2
.

Inductive typing : env -> exp -> typ -> Prop :=
| typing_nat: forall G,
    wf_env G ->
    typing G (exp_nat) (typ_nat)
| typing_var : forall (G:env) (x:var) (T:typ),
     wf_env G ->
     binds x (bind_typ T) G  ->
     typing G (exp_fvar x) T
 | typing_abs : forall (L:vars) (G:env) (T1:typ) (e:exp) (T2:typ),
     (forall x , x \notin L -> typing ((x ~ bind_typ T1) ++ G) (open_ee e x) T2)  ->
     typing G (exp_abs T1 e) (typ_arrow T1 T2)
 | typing_app : forall (G:env) (e1 e2:exp) (T2 T1:typ),
     typing G e1 (typ_arrow T1 T2) ->
     typing G e2 T1 ->
     typing G (exp_app e1 e2) T2
 | typing_fold : forall G A e ,
     typing G e  (open_tt A  (typ_mu A))    ->
     WFS G (typ_mu A) ->
     typing G (exp_fold (typ_mu A) e) (typ_mu A)
 | typing_unfold : forall G T e,
     typing G e (typ_mu T) ->
     typing G (exp_unfold (typ_mu T) e)  (open_tt T  (typ_mu T))
 | typing_sub: forall G T e S evs cm,
     typing G e S ->
     Sub Pos cm evs G S T ->

     typing G e T.

Inductive value : exp -> Prop :=
  | value_abs : forall t1 T,
      expr (exp_abs T t1) ->
      value (exp_abs T t1)
  | value_nat:
      value exp_nat
  | value_fold: forall T e,
      type T ->
      value e ->
      value (exp_fold T e).

Inductive step : exp -> exp -> Prop :=
 | step_beta : forall (e1 e2:exp) T,
     expr (exp_abs T e1) ->
     value e2 ->
     step (exp_app  (exp_abs T e1) e2)  (open_ee e1 e2)
 | step_app1 : forall (e1 e2 e1':exp),
     expr e2 ->
     step e1 e1' ->
     step (exp_app e1 e2) (exp_app e1' e2)
 | step_app2 : forall v1 e2 e2',
     value v1 ->
     step e2 e2' ->
     step (exp_app v1 e2) (exp_app v1 e2')
 | step_fld: forall S T v,
     value v ->
     type T ->
     type S ->
     step (exp_unfold S (exp_fold T v)) v
 | step_fold: forall e e' T,
     step e e' ->
     type T ->
     step (exp_fold T e) (exp_fold T e')
 | step_unfold: forall e e' T,
     step e e' ->
     type T ->
     step (exp_unfold T e) (exp_unfold T e').
