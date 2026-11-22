Require Export Fsub.EffectExclusion.LabelMap.

Require Export Fsub.EffectExclusion.Label.

Require Export Fsub.FbMeta.Metatheory.

Require Export String.

Require Export Coq.ZArith.ZArith.

Require Export Fsub.EffectExclusion.Lattice.

Parameter B : Set.
Parameter O : Order B.
Parameter L : Lattice B.
Parameter LSet : @LOSet B O L.
Parameter D : @DistributiveLattice B L.
Parameter BA : @BooleanAlgebra B L D.
#[export] Existing Instances O L LSet D BA.

Inductive qua : Set :=
  | qua_base : B -> qua
  | qua_bvar : nat -> qua
  | qua_fvar : atom -> qua
  | qua_meet : qua -> qua -> qua
  | qua_join : qua -> qua -> qua
  | qua_negate : qua -> qua
.

Notation "`impure" := (qua_base top).

Notation "`pure" := (qua_base bot).

Inductive typ : Set :=
  | typ_top : typ
  | typ_int : typ
  | typ_bvar : nat -> typ
  | typ_fvar : atom -> typ
  | typ_arrow : qtyp -> qtyp -> typ
  | typ_all : typ -> qtyp -> typ
  | typ_qall : qua -> qtyp -> typ
  | typ_sum : qtyp -> qtyp -> typ
  | typ_pair : qtyp -> qtyp -> typ
  | typ_ref : qtyp -> typ
with qtyp : Set :=
  | qtyp_qtyp : qua -> typ -> qtyp
.

Inductive exp : Set :=
  | exp_int : qua -> Z -> exp
  | exp_bvar : nat -> exp
  | exp_fvar : atom -> exp
  | exp_abs : qua -> qtyp -> exp -> exp
  | exp_app : exp -> exp -> exp
  | exp_tabs : qua -> typ -> exp -> exp
  | exp_tapp : exp -> typ -> exp
  | exp_qabs : qua -> qua -> exp -> exp
  | exp_qapp : exp -> qua -> exp
  | exp_let : exp -> exp -> exp
  | exp_inl : qua -> exp -> exp
  | exp_inr : qua -> exp -> exp
  | exp_case : exp -> exp -> exp -> exp
  | exp_pair : qua -> exp -> exp -> exp
  | exp_first : exp -> exp
  | exp_second : exp -> exp
  | exp_ref : qua -> exp -> exp
  | exp_ref_label : qua -> label -> exp
  | exp_deref : exp -> exp
  | exp_set_ref : exp -> exp -> exp
  | exp_upqual : qua -> exp -> exp
  | exp_check : qua -> exp -> exp
  | exp_without : qua -> exp -> exp
  | exp_do : B -> exp
  | exp_if0 : exp -> exp -> exp -> exp
.

Coercion typ_bvar : nat >-> typ.

Coercion typ_fvar : atom >-> typ.

Coercion exp_bvar : nat >-> exp.

Coercion exp_fvar : atom >-> exp.

Coercion qua_bvar : nat >-> qua.

Coercion qua_fvar : atom >-> qua.

Definition concrete_qua : Set := B.

Fixpoint concretize (q : qua) : (option concrete_qua) :=
  match q with
  | qua_base b => Some b
  | qua_fvar X => None
  | qua_bvar n => None
  | qua_join Q1 Q2 =>
    match (concretize Q1, concretize Q2) with
    | (Some b1, Some b2) => Some (b1 ⊔ b2)
    | _ => None
    end
  | qua_meet Q1 Q2 =>
    match (concretize Q1, concretize Q2) with
    | (Some b1, Some b2) => Some (b1 ⊓ b2)
    | _ => None
    end
  | qua_negate Q1 =>
    match (concretize Q1) with
    | Some b1 => Some (negate b1)
    | None => None
    end
  end.

Definition abstractize (s : concrete_qua) :=
  qua_base s.

Fixpoint open_qq_rec (K : nat) (R : qua) (Q : qua)  {struct Q} : qua :=
  match Q with
  | qua_base b => qua_base b
  | qua_bvar J => if (K == J) then R else (qua_bvar J)
  | qua_fvar X => qua_fvar X
  | qua_meet Q1 Q2 => qua_meet (open_qq_rec K R Q1) (open_qq_rec K R Q2)
  | qua_join Q1 Q2 => qua_join (open_qq_rec K R Q1) (open_qq_rec K R Q2)
  | qua_negate Q1 => qua_negate (open_qq_rec K R Q1)
  end.

Fixpoint open_tt_rec (K : nat) (U : typ) (T : typ)  {struct T} : typ :=
  match T with
  | typ_top => typ_top
  | typ_int => typ_int
  | typ_bvar J => if K == J then U else (typ_bvar J)
  | typ_fvar X => typ_fvar X
  | typ_arrow T1 T2 => typ_arrow (open_tqt_rec K U T1) (open_tqt_rec (S K) U T2)
  | typ_all T1 T2 => typ_all (open_tt_rec K U T1) (open_tqt_rec (S K) U T2)
  | typ_qall Q T => typ_qall Q (open_tqt_rec (S K) U T)
  | typ_sum T1 T2 => typ_sum (open_tqt_rec K U T1) (open_tqt_rec K U T2)
  | typ_pair T1 T2 => typ_pair (open_tqt_rec K U T1) (open_tqt_rec K U T2)
  | typ_ref T1 => typ_ref (open_tqt_rec K U T1)
  end
with open_tqt_rec (K : nat) (U : typ) (T : qtyp)  {struct T} : qtyp :=
  match T with
  | qtyp_qtyp Q T => qtyp_qtyp Q (open_tt_rec K U T)
  end.

Fixpoint open_qt_rec (K : nat) (R : qua) (T : typ)  {struct T} : typ :=
  match T with
  | typ_top => typ_top
  | typ_int => typ_int
  | typ_bvar J => typ_bvar J
  | typ_fvar X => typ_fvar X
  | typ_arrow T1 T2 => typ_arrow (open_qqt_rec K R T1) (open_qqt_rec (S K) R T2)
  | typ_all T1 T2 => typ_all (open_qt_rec K R T1) (open_qqt_rec (S K) R T2)
  | typ_qall Q T => typ_qall (open_qq_rec K R Q) (open_qqt_rec (S K) R T)
  | typ_sum T1 T2 => typ_sum (open_qqt_rec K R T1) (open_qqt_rec K R T2)
  | typ_pair T1 T2 => typ_pair (open_qqt_rec K R T1) (open_qqt_rec K R T2)
  | typ_ref T1 => typ_ref (open_qqt_rec K R T1)
  end
with open_qqt_rec (K : nat) (R : qua) (T : qtyp)  {struct T} : qtyp :=
  match T with
  | qtyp_qtyp Q T => qtyp_qtyp (open_qq_rec K R Q) (open_qt_rec K R T)
  end.

Fixpoint open_te_rec (K : nat) (U : typ) (e : exp) {struct e} : exp :=
  match e with
  | exp_int Q i => exp_int Q i
  | exp_bvar i => exp_bvar i
  | exp_fvar x => exp_fvar x
  | exp_abs P V e1 => exp_abs P (open_tqt_rec K U V)  (open_te_rec (S K) U e1)
  | exp_app e1 e2 => exp_app  (open_te_rec K U e1) (open_te_rec K U e2)
  | exp_tabs P V e1 => exp_tabs P (open_tt_rec K U V)  (open_te_rec (S K) U e1)
  | exp_tapp e1 V => exp_tapp (open_te_rec K U e1) (open_tt_rec K U V)
  | exp_qabs P Q e1 => exp_qabs P Q (open_te_rec (S K) U e1)
  | exp_qapp e1 Q => exp_qapp (open_te_rec K U e1) Q
  | exp_let e1 e2 => exp_let (open_te_rec K U e1) (open_te_rec (S K) U e2)
  | exp_inl P e1 => exp_inl P (open_te_rec K U e1)
  | exp_inr P e2 => exp_inr P (open_te_rec K U e2)
  | exp_case e1 e2 e3 =>
      exp_case (open_te_rec K U e1) (open_te_rec (S K) U e2) (open_te_rec (S K) U e3)
  | exp_pair R e1 e2 => exp_pair R (open_te_rec K U e1) (open_te_rec K U e2)
  | exp_first e1 => exp_first (open_te_rec K U e1)
  | exp_second e2 => exp_second (open_te_rec K U e2)
  | exp_ref P e1 => exp_ref P (open_te_rec K U e1)
  | exp_ref_label P l => exp_ref_label P l
  | exp_deref e1 => exp_deref (open_te_rec K U e1)
  | exp_set_ref e1 e2 => exp_set_ref (open_te_rec K U e1) (open_te_rec K U e2)
  | exp_check P e1 => exp_check P (open_te_rec K U e1)
  | exp_upqual P e1 => exp_upqual P (open_te_rec K U e1)
  | exp_without P e1 => exp_without P (open_te_rec K U e1)
  | exp_do b => exp_do b
  | exp_if0 e1 e2 e3 =>
      exp_if0 (open_te_rec K U e1) (open_te_rec K U e2) (open_te_rec K U e3)
  end.

Fixpoint open_qe_rec (K : nat) (R : qua) (e : exp) {struct e} : exp :=
  match e with
  | exp_int P i => exp_int (open_qq_rec K R P) i
  | exp_bvar i => exp_bvar i
  | exp_fvar x => exp_fvar x
  | exp_abs P V e1 => exp_abs (open_qq_rec K R P) (open_qqt_rec K R V)  (open_qe_rec (S K) R e1)
  | exp_app e1 e2 => exp_app  (open_qe_rec K R e1) (open_qe_rec K R e2)
  | exp_tabs P V e1 => exp_tabs (open_qq_rec K R P) (open_qt_rec K R V)  (open_qe_rec (S K) R e1)
  | exp_tapp e1 V => exp_tapp (open_qe_rec K R e1) (open_qt_rec K R V)
  | exp_qabs P Q e1 => exp_qabs (open_qq_rec K R P) (open_qq_rec K R Q)  (open_qe_rec (S K) R e1)
  | exp_qapp e1 Q => exp_qapp (open_qe_rec K R e1) (open_qq_rec K R Q)
  | exp_let e1 e2 => exp_let (open_qe_rec K R e1) (open_qe_rec (S K) R e2)
  | exp_inl P e1 => exp_inl (open_qq_rec K R P) (open_qe_rec K R e1)
  | exp_inr P e2 => exp_inr (open_qq_rec K R P) (open_qe_rec K R e2)
  | exp_case e1 e2 e3 =>
      exp_case (open_qe_rec K R e1) (open_qe_rec (S K) R e2) (open_qe_rec (S K) R e3)
  | exp_pair P e1 e2 => exp_pair (open_qq_rec K R P) (open_qe_rec K R e1) (open_qe_rec K R e2)
  | exp_first e1 => exp_first (open_qe_rec K R e1)
  | exp_second e2 => exp_second (open_qe_rec K R e2)
  | exp_ref P e1 => exp_ref (open_qq_rec K R P) (open_qe_rec K R e1)
  | exp_ref_label P l => exp_ref_label (open_qq_rec K R P) l
  | exp_deref e1 => exp_deref (open_qe_rec K R e1)
  | exp_set_ref e1 e2 => exp_set_ref (open_qe_rec K R e1) (open_qe_rec K R e2)
  | exp_check P e1 => exp_check (open_qq_rec K R P) (open_qe_rec K R e1)
  | exp_upqual P e1 => exp_upqual (open_qq_rec K R P) (open_qe_rec K R e1)
  | exp_without P e1 => exp_without (open_qq_rec K R P) (open_qe_rec K R e1)
  | exp_do b => exp_do b
  | exp_if0 e1 e2 e3 =>
      exp_if0 (open_qe_rec K R e1) (open_qe_rec K R e2) (open_qe_rec K R e3)
  end.

Fixpoint open_ee_rec (k : nat) (f : exp) (e : exp)  {struct e} : exp :=
  match e with
  | exp_int P i => exp_int P i
  | exp_bvar i => if k == i then f else (exp_bvar i)
  | exp_fvar x => exp_fvar x
  | exp_abs P V e1 => exp_abs P V (open_ee_rec (S k) f e1)
  | exp_app e1 e2 => exp_app (open_ee_rec k f e1) (open_ee_rec k f e2)
  | exp_tabs P V e1 => exp_tabs P V (open_ee_rec (S k) f e1)
  | exp_tapp e1 V => exp_tapp (open_ee_rec k f e1) V
  | exp_qabs P Q e1 => exp_qabs P Q (open_ee_rec (S k) f e1)
  | exp_qapp e1 Q => exp_qapp (open_ee_rec k f e1) Q
  | exp_let e1 e2 => exp_let (open_ee_rec k f e1) (open_ee_rec (S k) f e2)
  | exp_inl P e1 => exp_inl P (open_ee_rec k f e1)
  | exp_inr P e2 => exp_inr P (open_ee_rec k f e2)
  | exp_case e1 e2 e3 =>
      exp_case (open_ee_rec k f e1)
               (open_ee_rec (S k) f e2)
               (open_ee_rec (S k) f e3)
  | exp_pair P e1 e2 => exp_pair P (open_ee_rec k f e1) (open_ee_rec k f e2)
  | exp_first e1 => exp_first (open_ee_rec k f e1)
  | exp_second e2 => exp_second (open_ee_rec k f e2)
  | exp_ref P e1 => exp_ref P (open_ee_rec k f e1)
  | exp_ref_label P l => exp_ref_label P l
  | exp_deref e1 => exp_deref (open_ee_rec k f e1)
  | exp_set_ref e1 e2 => exp_set_ref (open_ee_rec k f e1) (open_ee_rec k f e2)
  | exp_check P e1 => exp_check P (open_ee_rec k f e1)
  | exp_upqual P e1 => exp_upqual P (open_ee_rec k f e1)
  | exp_without P e1 => exp_without P (open_ee_rec k f e1)
  | exp_do b => exp_do b
  | exp_if0 e1 e2 e3 =>
      exp_if0 (open_ee_rec k f e1)
              (open_ee_rec k f e2)
              (open_ee_rec k f e3)
  end.

Definition open_tt T U := open_tt_rec 0 U T.

Definition open_te e U := open_te_rec 0 U e.

Definition open_ee e1 e2 := open_ee_rec 0 e2 e1.

Definition open_qq Q R := open_qq_rec 0 R Q.

Definition open_qe e R := open_qe_rec 0 R e.

Definition open_qt T R := open_qt_rec 0 R T.

Definition open_qqt T R := open_qqt_rec 0 R T.

Definition open_tqt T R := open_tqt_rec 0 R T.

Inductive qual : qua -> Prop :=
  | qual_base : forall b,
      qual (qua_base b)
  | qual_fvar : forall (X : atom),
      qual (qua_fvar X)
  | qual_meet : forall Q1 Q2,
      qual Q1 ->
      qual Q2 ->
      qual (qua_meet Q1 Q2)
  | qual_join : forall Q1 Q2,
      qual Q1 ->
      qual Q2 ->
      qual (qua_join Q1 Q2)
  | qual_negate : forall Q1,
      qual Q1 ->
      qual (qua_negate Q1)
.

Inductive type : typ -> Prop :=
  | type_top :
      type typ_top
  | type_int :
      type typ_int
  | type_var : forall X,
      type (typ_fvar X)
  | type_arrow : forall T1 T2,
      qtype T1 ->
      qtype T2 ->
      type (typ_arrow T1 T2)
  | type_all : forall L T1 T2,
      type T1 ->
      (forall X : atom, X `notin` L -> qtype (open_tqt T2 X)) ->
      type (typ_all T1 T2)
  | type_qall : forall L Q T,
      qual Q ->
      (forall X : atom, X `notin` L -> qtype (open_qqt T X)) ->
      type (typ_qall Q T)
  | type_sum : forall T1 T2,
      qtype T1 ->
      qtype T2 ->
      type (typ_sum T1 T2)
  | type_pair : forall T1 T2,
      qtype T1 ->
      qtype T2 ->
      type (typ_pair T1 T2)
with qtype : qtyp -> Prop :=
  | qtype_qtyp : forall Q T,
      qual Q ->
      type T ->
      qtype (qtyp_qtyp Q T)
.

Inductive expr : exp -> Prop :=
  | expr_int : forall P i,
      qual P ->
      expr (exp_int P i)
  | expr_var : forall x,
      expr (exp_fvar x)
  | expr_abs : forall L P T e1,
      qual P ->
      qtype T ->
      qual P ->
      (forall x : atom, x `notin` L -> expr (open_ee e1 x)) ->
      expr (exp_abs P T e1)
  | expr_app : forall e1 e2,
      expr e1 ->
      expr e2 ->
      expr (exp_app e1 e2)
  | expr_tabs : forall L P T e1,
      qual P ->
      type T ->
      (forall X : atom, X `notin` L -> expr (open_te e1 X)) ->
      expr (exp_tabs P T e1)
  | expr_tapp : forall e1 V,
      expr e1 ->
      type V ->
      expr (exp_tapp e1 V)
  | expr_qabs : forall L P Q e1,
      qual P ->
      qual Q ->
      (forall X : atom, X `notin` L -> expr (open_qe e1 X)) ->
      expr (exp_qabs P Q e1)
  | expr_qapp : forall e1 Q,
      expr e1 ->
      qual Q ->
      expr (exp_qapp e1 Q)
  | expr_let : forall L e1 e2,
      expr e1 ->
      (forall x : atom, x `notin` L -> expr (open_ee e2 x)) ->
      expr (exp_let e1 e2)
  | expr_inl : forall P e1,
      qual P ->
      expr e1 ->
      expr (exp_inl P e1)
  | expr_inr : forall P e1,
      qual P ->
      expr e1 ->
      expr (exp_inr P e1)
  | expr_case : forall L e1 e2 e3,
      expr e1 ->
      (forall x : atom, x `notin` L -> expr (open_ee e2 x)) ->
      (forall x : atom, x `notin` L -> expr (open_ee e3 x)) ->
      expr (exp_case e1 e2 e3)
  | expr_pair : forall P e1 e2,
      qual P ->
      expr e1 ->
      expr e2 ->
      expr (exp_pair P e1 e2)
  | expr_first : forall e1,
      expr e1 ->
      expr (exp_first e1)
  | expr_second : forall e1,
      expr e1 ->
      expr (exp_second e1)
  | expr_upqual : forall P e1,
      qual P ->
      expr e1 ->
      expr (exp_upqual P e1)
  | expr_check : forall P e1,
      qual P ->
      expr e1 ->
      expr (exp_check P e1)
  | expr_without : forall P e1,
        qual P ->
        expr e1 ->
        expr (exp_without P e1)
  | expr_do : forall b,
        expr (exp_do b)
  | expr_if0 : forall e1 e2 e3,
      expr e1 ->
      expr e2 ->
      expr e3 ->
      expr (exp_if0 e1 e2 e3)
.

Definition body_e (e : exp) :=
  exists L, forall x : atom, x `notin` L -> expr (open_ee e x).

Inductive binding : Set :=
  | bind_sub : typ -> binding
  | bind_typ : qtyp -> binding
  | bind_qua : qua -> binding.

Notation env := (list (atom * binding)).

Notation empty := (@nil (atom * binding)).

Inductive wf_qua : env -> qua -> Prop :=
  | wf_qua_base : forall E b,
      wf_qua E (qua_base b)
  | wf_qua_fvar : forall R E (X : atom),
      binds X (bind_qua R) E ->
      wf_qua E (qua_fvar X)
  | wf_qua_meet : forall E Q1 Q2,
      wf_qua E Q1 ->
      wf_qua E Q2 ->
      wf_qua E (qua_meet Q1 Q2)
  | wf_qua_join : forall E Q1 Q2,
      wf_qua E Q1 ->
      wf_qua E Q2 ->
      wf_qua E (qua_join Q1 Q2)
  | wf_qua_negate : forall E Q1,
      wf_qua E Q1 ->
      wf_qua E (qua_negate Q1)
.

Notation "E |-q Q wf" := (wf_qua E Q) (at level 70).

Inductive wf_typ : env -> typ -> Prop :=
  | wf_typ_top : forall E,
      wf_typ E typ_top
  | wf_typ_int : forall E,
      wf_typ E typ_int
  | wf_typ_var : forall U E (X : atom),
      binds X (bind_sub U) E ->
      wf_typ E (typ_fvar X)
  | wf_typ_arrow : forall E T1 T2,
      wf_qtyp E T1 ->
      wf_qtyp E T2 ->
      wf_typ E (typ_arrow T1 T2)
  | wf_typ_all : forall L E T1 T2,
      wf_typ E T1 ->
      (forall X : atom, X `notin` L ->
        wf_qtyp (X ~ bind_sub T1 ++ E) (open_tqt T2 X)) ->
      wf_typ E (typ_all T1 T2)
  | wf_typ_qall : forall L E T1 T2,
      wf_qua E T1 ->
      (forall X : atom, X `notin` L ->
        wf_qtyp (X ~ bind_qua T1 ++ E) (open_qqt T2 X)) ->
      wf_typ E (typ_qall T1 T2)
  | wf_typ_sum : forall E T1 T2,
      wf_qtyp E T1 ->
      wf_qtyp E T2 ->
      wf_typ E (typ_sum T1 T2)
  | wf_typ_pair : forall E T1 T2,
      wf_qtyp E T1 ->
      wf_qtyp E T2 ->
      wf_typ E (typ_pair T1 T2)
with wf_qtyp : env -> qtyp -> Prop :=
  | wf_qtyp_qtyp : forall E Q T,
      wf_qua E Q ->
      wf_typ E T ->
      wf_qtyp E (qtyp_qtyp Q T)
.

Notation "E |-t T wf" := (wf_typ E T) (at level 70).

Notation "E |-qt T wf" := (wf_qtyp E T) (at level 70).

Inductive wf_env : env -> Prop :=
  | wf_env_empty :
      wf_env empty
  | wf_env_sub : forall (E : env) (X : atom) (T : typ),
      wf_env E ->
      wf_typ E T ->
      X `notin` dom E ->
      wf_env (X ~ bind_sub T ++ E)
  | wf_env_typ : forall (E : env) (x : atom) (T : qtyp),
      wf_env E ->
      wf_qtyp E T ->
      x `notin` dom E ->
      wf_env (x ~ bind_typ T ++ E)
  | wf_env_qua : forall (E : env) (X : atom) (Q : qua),
      wf_env E ->
      wf_qua E Q ->
      X `notin` dom E ->
      wf_env (X ~ bind_qua Q ++ E)
.

Notation "|- E wf" := (wf_env E) (at level 70).

Inductive subqual : env -> qua -> qua -> Prop :=
  | subqual_top : forall E Q,
      wf_env E ->
      wf_qua E Q ->
      subqual E Q (qua_base top)
  | subqual_bot : forall E Q,
      wf_env E ->
      wf_qua E Q ->
      subqual E (qua_base bot) Q
  | subqual_eval_elim : forall E Q' Q R b,
      subqual E Q Q' ->
      concretize Q' = Some b ->
      subqual E (qua_base b) R ->
      subqual E Q R
  | subqual_eval_intro : forall E Q' Q R b,
      subqual E Q' R ->
      concretize Q' = Some b ->
      subqual E Q (qua_base b) ->
      subqual E Q R
  | subqual_lift_elem : forall E b1 b2,
      wf_env E ->
      ord b1 b2 ->
      subqual E (qua_base b1) (qua_base b2)
  | subqual_refl_qvar : forall E X,
      wf_env E ->
      wf_qua E (qua_fvar X) ->
      subqual E (qua_fvar X) (qua_fvar X)
  | subqual_trans_qvar : forall R E Q X,
      binds X (bind_qua R) E ->
      subqual E R Q ->
      subqual E (qua_fvar X) Q
  | subqual_join_inl : forall E R1 R2 Q,
      subqual E Q R1 ->
      wf_qua E R2 ->
      subqual E Q (qua_join R1 R2)
  | subqual_join_inr : forall E R1 R2 Q,
      wf_qua E R1 ->
      subqual E Q R2 ->
      subqual E Q (qua_join R1 R2)
  | subqual_join_elim : forall E R1 R2 Q,
      subqual E R1 Q ->
      subqual E R2 Q ->
      subqual E (qua_join R1 R2) Q
  | subqual_meet_eliml : forall E R1 R2 Q,
      subqual E R1 Q ->
      wf_qua E R2 ->
      subqual E (qua_meet R1 R2) Q
  | subqual_meet_elimr : forall E R1 R2 Q,
      wf_qua E R1 ->
      subqual E R2 Q ->
      subqual E (qua_meet R1 R2) Q
  | subqual_meet_intro : forall E R1 R2 Q,
      subqual E Q R1 ->
      subqual E Q R2 ->
      subqual E Q (qua_meet R1 R2)
  | subqual_dist : forall E Q R S,
      wf_env E ->
      wf_qua E Q ->
      wf_qua E R ->
      wf_qua E S ->
      subqual E (qua_meet Q (qua_join R S))
                (qua_join (qua_meet Q R) (qua_meet Q S))
  | subqual_trans : forall E Q R S,
      subqual E Q R ->
      subqual E R S ->
      subqual E Q S
  | subqual_negate_intro : forall E Q,
      wf_env E ->
      wf_qua E Q ->
      subqual E (qua_base top) (qua_join Q (qua_negate Q))
  | subqual_negate_elim : forall E Q,
      wf_env E ->
      wf_qua E Q ->
      subqual E (qua_meet Q (qua_negate Q)) (qua_base bot)
  | subqual_refl_negate : forall E Q,
      wf_env E ->
      wf_qua E Q ->
      subqual E (qua_negate Q) (qua_negate Q)
.

Notation "E |-sq Q1 <: Q2" := (subqual E Q1 Q2) (at level 70).

Inductive sub : env -> typ -> typ -> Prop :=
  | sub_top : forall E S,
      wf_env E ->
      wf_typ E S ->
      sub E S typ_top
  | sub_refl_int : forall E,
      wf_env E ->
      sub E typ_int typ_int
  | sub_refl_tvar : forall E X,
      wf_env E ->
      wf_typ E (typ_fvar X) ->
      sub E (typ_fvar X) (typ_fvar X)
  | sub_trans_tvar : forall U E T X,
      binds X (bind_sub U) E ->
      sub E U T ->
      sub E (typ_fvar X) T
  | sub_arrow : forall E S1 S2 T1 T2,
      subqtype E T1 S1 ->
      subqtype E S2 T2 ->
      sub E (typ_arrow S1 S2) (typ_arrow T1 T2)
  | sub_all : forall L E S1 S2 T1 T2,
      sub E T1 S1 ->
      (forall X : atom, X `notin` L ->
          subqtype (X ~ bind_sub T1 ++ E) (open_tqt S2 X) (open_tqt T2 X)) ->
      sub E (typ_all S1 S2) (typ_all T1 T2)
  | sub_qall : forall L E S1 S2 T1 T2,
      subqual E T1 S1 ->
      (forall X : atom, X `notin` L ->
          subqtype (X ~ bind_qua T1 ++ E) (open_qqt S2 X) (open_qqt T2 X)) ->
      sub E (typ_qall S1 S2) (typ_qall T1 T2)
  | sub_sum : forall E S1 S2 T1 T2,
      subqtype E S1 T1 ->
      subqtype E S2 T2 ->
      sub E (typ_sum S1 S2) (typ_sum T1 T2)
  | sub_pair : forall E S1 S2 T1 T2,
      subqtype E S1 T1 ->
      subqtype E S2 T2 ->
      sub E (typ_pair S1 S2) (typ_pair T1 T2)
with subqtype : env -> qtyp -> qtyp -> Prop :=
  | sub_qtyp_qtyp : forall E Q1 T1 Q2 T2,
      subqual E Q1 Q2 ->
      sub E T1 T2 ->
      subqtype E (qtyp_qtyp Q1 T1) (qtyp_qtyp Q2 T2)
.

Notation "E |-t S <: T" := (sub E S T) (at level 70).

Notation "E |-sqt S <: T" := (subqtype E S T) (at level 70).

Inductive typing : env -> qua -> exp -> qtyp -> Prop :=
  | typing_int : forall E P i,
      wf_env E ->
      wf_qua E P ->
      typing E (qua_base bot) (exp_int P i) (qtyp_qtyp P typ_int)
  | typing_var : forall E x T,
      wf_env E ->
      binds x (bind_typ T) E ->
      typing E (qua_base bot) (exp_fvar x) T

  | typing_abs : forall L E P V e1 T1,
      (forall x : atom, x `notin` L ->
        typing (x ~ bind_typ V ++ E) P (open_ee e1 x) T1) ->
      typing E (qua_base bot) (exp_abs P V e1) (qtyp_qtyp P (typ_arrow V T1))

  | typing_app : forall Q T1 E e1 e2 T2,
      typing E Q e1 (qtyp_qtyp Q (typ_arrow T1 T2)) ->
      typing E Q e2 T1 ->
      typing E Q (exp_app e1 e2) T2

  | typing_tabs : forall L E P V e1 T1,
      (forall X : atom, X `notin` L ->
        typing (X ~ bind_sub V ++ E) P (open_te e1 X) (open_tqt T1 X)) ->
      typing E (qua_base bot) (exp_tabs P V e1) (qtyp_qtyp P (typ_all V T1))

  | typing_tapp : forall Q T1 E e1 T T2,
      typing E Q e1 (qtyp_qtyp Q (typ_all T1 T2)) ->
      sub E T T1 ->
      typing E Q (exp_tapp e1 T) (open_tqt T2 T)

  | typing_qabs : forall L E P Q e1 T1,
      wf_qua E P ->
      (forall X : atom, X `notin` L ->
        typing (X ~ bind_qua Q ++ E) P (open_qe e1 X) (open_qqt T1 X)) ->
      typing E (qua_base bot) (exp_qabs P Q e1) (qtyp_qtyp P (typ_qall Q T1))

  | typing_qapp : forall Q E e1 Q1 T,
      typing E Q e1 (qtyp_qtyp Q (typ_qall Q1 T)) ->
      subqual E Q Q1 ->
      typing E Q (exp_qapp e1 Q) (open_qqt T Q)

  | typing_sub : forall S E Q e T,
      typing E Q e S ->
      subqtype E S T ->
      typing E Q e T

  | typing_subqual : forall E Q R e T,
      typing E Q e T ->
      subqual E Q R ->
      typing E R e T

  | typing_let : forall L T1 T2 e1 e2 E Q,
      typing E Q e1 T1 ->
      (forall x : atom, x `notin` L ->
        typing (x ~ bind_typ T1 ++ E) Q (open_ee e2 x) T2) ->
      typing E Q (exp_let e1 e2) T2


  | typing_inl : forall T1 T2 P e1 E Q,
      wf_qua E P ->
      typing E Q e1 T1 ->
      wf_qtyp E T2 ->
      typing E Q (exp_inl P e1) (qtyp_qtyp P (typ_sum T1 T2))
  | typing_inr : forall T1 T2 P e1 E Q,
      wf_qua E P ->
      typing E Q e1 T2 ->
      wf_qtyp E T1 ->
      typing E Q (exp_inr P e1) (qtyp_qtyp P (typ_sum T1 T2))
  | typing_case : forall L T1 T2 P T e1 e2 e3 E Q,
      typing E Q e1 (qtyp_qtyp P (typ_sum T1 T2)) ->
      (forall x : atom, x `notin` L ->
        typing (x ~ bind_typ T1 ++ E) Q (open_ee e2 x) T) ->
      (forall x : atom, x `notin` L ->
        typing (x ~ bind_typ T2 ++ E) Q (open_ee e3 x) T) ->
      typing E Q (exp_case e1 e2 e3) T
  | typing_pair : forall T1 T2 P e1 e2 E Q,
      wf_qua E P ->
      typing E Q e1 T1 ->
      typing E Q e2 T2 ->
      typing E Q (exp_pair P e1 e2) (qtyp_qtyp P (typ_pair T1 T2))
  | typing_first : forall Q T1 T2 P e E,
      typing E Q e (qtyp_qtyp P (typ_pair T1 T2)) ->
      typing E Q (exp_first e) T1
  | typing_second : forall Q T1 T2 P e E,
      typing E Q e (qtyp_qtyp P (typ_pair T1 T2)) ->
      typing E Q (exp_second e) T2
  | typing_upqual : forall E R Q T P e,
      typing E R e (qtyp_qtyp Q T) ->
      subqual E Q P ->
      typing E R (exp_upqual P e) (qtyp_qtyp P T)
  | typing_check : forall E R Q T P e,
      typing E R e (qtyp_qtyp Q T) ->
      subqual E Q P ->
      typing E R (exp_check P e) (qtyp_qtyp Q T)
  | typing_without : forall E R Q T P e,
      typing E R e (qtyp_qtyp Q T) ->
      subqual E R (qua_negate P) ->
      typing E R (exp_without P e) (qtyp_qtyp Q T)
  | typing_do : forall E b,
      wf_env E ->
      typing E (qua_base b) (exp_do b) (qtyp_qtyp (qua_base bot) typ_int)
  | typing_if0 : forall E R Q e1 e2 e3 T,
      typing E R e1 (qtyp_qtyp Q typ_int) ->
      typing E R e2 T ->
      typing E R e3 T ->
      typing E R (exp_if0 e1 e2 e3) T
.

Notation "E @ Q |-t e : T" := (typing E Q e T) (at level 70).

Inductive value : exp -> Prop :=
  | value_int : forall P x,
      qual P ->
      value (exp_int P x)
  | value_abs : forall P T e1,
      expr (exp_abs P T e1) ->
      value (exp_abs P T e1)
  | value_tabs : forall P T e1,
      expr (exp_tabs P T e1) ->
      value (exp_tabs P T e1)
 | value_qabs : forall P Q e1,
      expr (exp_qabs P Q e1) ->
      value (exp_qabs P Q e1)
  | value_inl : forall P e1,
      qual P ->
      value e1 ->
      value (exp_inl P e1)
  | value_inr : forall P e1,
      qual P ->
      value e1 ->
      value (exp_inr P e1)
  | value_pair : forall P e1 e2,
      qual P ->
      value e1 ->
      value e2 ->
      value (exp_pair P e1 e2)
.

Inductive frame : Set :=

  | frame_abs (e : exp) : frame

  | frame_app (f : exp) : frame

  | frame_tabs (T : typ) : frame

  | frame_qabs (R : qua) : frame

  | frame_let (e : exp) : frame

  | frame_inl (P : qua) : frame

  | frame_inr (P : qua) : frame

  | frame_case (e1 : exp) (e2 : exp) : frame

  | frame_pair_1 (P : qua) (e1 : exp) : frame

  | frame_pair_2 (P : qua) (e2 : exp) : frame

  | frame_first : frame

  | frame_second : frame

  | frame_upqual (P : qua) : frame

  | frame_check (P : qua) : frame

  | frame_without : concrete_qua -> frame

  | frame_barrier : concrete_qua -> frame

  | frame_if0 (e1 : exp) (e2: exp) : frame.

Notation ctx := (list frame).

Notation done := (@nil frame).

Inductive typing_ctx : env -> qua -> ctx -> qtyp -> qtyp -> Prop :=

  | typing_ctx_done : forall E Q T,
      wf_env E ->
      wf_qua E Q ->
      wf_qtyp E T ->
      typing_ctx E Q done T T

  | typing_ctx_abs : forall E Q c e1 T1 T2 U,
      typing_ctx E Q c T2 U ->
      typing E Q e1 T1 ->
      typing_ctx E Q (frame_abs e1 :: c) (qtyp_qtyp Q (typ_arrow T1 T2)) U

  | typing_ctx_app : forall E Q c e1 T1 T2 U,
      typing_ctx E Q c T2 U ->
      value e1 ->
      typing E Q e1 (qtyp_qtyp Q (typ_arrow T1 T2)) ->
      typing_ctx E Q (frame_app e1 :: c) T1 U

  | typing_ctx_tabs : forall L E Q c T1 T1' T2 U,
      typing_ctx E Q c (open_tqt T2 T1') U ->
      sub E T1' T1 ->
      (forall X : atom, X `notin` L ->
          wf_qtyp (X ~ bind_sub T1 ++ E) (open_tqt T2 X)) ->
      typing_ctx E Q (frame_tabs T1' :: c) (qtyp_qtyp Q (typ_all T1 T2)) U
  | typing_ctx_qabs : forall L E Q c R R' T2 U,
      typing_ctx E Q c (open_qqt T2 R') U ->
      subqual E R' R ->
      (forall X : atom, X `notin` L ->
          wf_qtyp (X ~ bind_qua R ++ E) (open_qqt T2 X)) ->
      typing_ctx E Q (frame_qabs R' :: c) (qtyp_qtyp Q (typ_qall R T2)) U

  | typing_ctx_let : forall L E Q c e1 T1 T2 U,
      typing_ctx E Q c T2 U->
      (forall x, x `notin` L -> typing (x ~ bind_typ T1 ++ E) Q (open_ee e1 x) T2) ->
      typing_ctx E Q (frame_let e1 :: c) T1 U

  | typing_ctx_inl : forall E P Q c T1 T2 U,
      typing_ctx E Q c (qtyp_qtyp P (typ_sum T1 T2)) U ->
      typing_ctx E Q (frame_inl P :: c) T1 U
  | typing_ctx_inr : forall E P Q c T1 T2 U,
      typing_ctx E Q c (qtyp_qtyp P (typ_sum T1 T2)) U ->
      typing_ctx E Q (frame_inr P :: c) T2 U

  | typing_ctx_case : forall L E P Q c T T1 T2 e2 e3 U,
      wf_qua E P ->
      typing_ctx E Q c T U ->
      (forall x : atom, x `notin` L ->
        typing (x ~ bind_typ T1 ++ E) Q (open_ee e2 x) T) ->
      (forall x : atom, x `notin` L ->
        typing (x ~ bind_typ T2 ++ E) Q (open_ee e3 x) T) ->
      typing_ctx E Q (frame_case e2 e3 :: c) (qtyp_qtyp P (typ_sum T1 T2)) U

  | typing_ctx_pair_1 : forall E P Q c e T1 T2 U,
      wf_qua E P ->
      typing_ctx E Q c (qtyp_qtyp P (typ_pair T1 T2)) U ->
      typing E Q e T2 ->
      typing_ctx E Q (frame_pair_1 P e :: c) T1 U
  | typing_ctx_pair_2 : forall E P Q c v T1 T2 U,
      wf_qua E P ->
      typing_ctx E Q c (qtyp_qtyp P (typ_pair T1 T2)) U ->
      value v ->
      typing E Q v T1 ->
      typing_ctx E Q (frame_pair_2 P v :: c) T2 U

  | typing_ctx_first : forall E P Q c T1 T2 U,
      wf_qua E P ->
      typing_ctx E Q c T1 U ->
      wf_qtyp E T2 ->
      typing_ctx E Q (frame_first :: c) (qtyp_qtyp P (typ_pair T1 T2)) U
  | typing_ctx_second : forall E P Q c T1 T2 U,
      wf_qua E P ->
      typing_ctx E Q c T2 U ->
      wf_qtyp E T1 ->
      typing_ctx E Q (frame_second :: c) (qtyp_qtyp P (typ_pair T1 T2)) U

  | typing_ctx_barrier : forall E Q c s t T U,
      typing_ctx E Q c T U ->
      (concretize Q) = Some s ->
      t ≤ s ->
      typing_ctx E (abstractize t) (frame_barrier t :: c) T U

  | typing_ctx_upqual : forall E Q c P T U,
      typing_ctx E Q c (qtyp_qtyp P T) U ->
      typing_ctx E Q (frame_upqual P :: c) (qtyp_qtyp P T) U
  | typing_ctx_check :  forall E Q c R P T U,
      wf_qua E R ->
      typing_ctx E Q c (qtyp_qtyp P T) U ->
      typing_ctx E Q (frame_check R :: c) (qtyp_qtyp (qua_meet P R) T) U

  | typing_ctx_sub : forall E Q c S T U,
      typing_ctx E Q c T U ->
      subqtype E S T ->
      typing_ctx E Q c S U
  | typing_ctx_subqual : forall E Q R c T U,
      typing_ctx E Q c T U ->
      subqual E R Q ->
      typing_ctx E R c T U



  | typing_ctx_without : forall E Q c t T U,
      typing_ctx E Q c T U ->
      typing_ctx E (qua_meet (abstractize (negate t)) Q) (frame_without t :: c) T U

  | typing_ctx_if0 : forall E R c e2 e3 T Q U,
      wf_qua E Q ->
      typing_ctx E R c T U ->
      typing E R e2 T ->
      typing E R e3 T ->
      typing_ctx E R (frame_if0 e2 e3 :: c) (qtyp_qtyp Q typ_int) U
.

Notation "E @ Q |-c c : T ~~> U" := (typing_ctx E Q c T U) (at level 70).

Inductive state : Type :=
  | state_step (e : exp) (c : ctx) : state.

Notation "〈 e | c 〉" := (state_step e c).

Inductive typing_state : env -> state -> qtyp -> Prop :=
  | typing_step : forall E Q e c T U,
    typing E Q e T ->
    typing_ctx E Q c T U ->
    typing_state E 〈 e | c 〉U
.

Notation "E |-s 〈 e | c 〉 : U" := (typing_state E 〈 e | c 〉 U) (at level 70).

Inductive barrier_compatible : ctx -> concrete_qua -> Prop :=
  | barrier_compatible_done : forall s, barrier_compatible done s
  | barrier_compatible_frame : forall c s t,
      barrier_compatible c s ->
      s ≤ t ->
      barrier_compatible (frame_barrier t :: c) s
  | barrier_compatible_without : forall c s t,
      barrier_compatible c s ->
      s ≤ (negate t) ->
      barrier_compatible (frame_without t :: c) s
  | barrier_compatible_other : forall c s f,
      barrier_compatible c s ->
      (forall t, f <> frame_barrier t) ->
      (forall t, f <> frame_without t) ->
      barrier_compatible (f :: c) s
.

Inductive step : state -> state -> Prop :=

  | step_barrier : forall e s k,
      value e ->
      step〈 e | frame_barrier s :: k 〉〈 e | k 〉

  | step_app_1 : forall e1 e2 k,
      step〈 (exp_app e1 e2) | k 〉
        〈 e1 | frame_abs e2 :: k 〉
  | step_app_2 : forall v e2 k,
      value v ->
      step〈 v | frame_abs e2 :: k 〉
        〈 e2 | frame_app v :: k 〉
  | step_tapp : forall e1 T k,
      step〈 (exp_tapp e1 T) | k 〉
        〈 e1 | frame_tabs T :: k 〉
  | step_qapp : forall e1 Q k,
      step〈 (exp_qapp e1 Q) | k 〉
        〈 e1 | frame_qabs Q :: k 〉
  | step_let : forall e1 e2 k,
      step〈 (exp_let e1 e2) | k 〉
        〈 e1 | frame_let e2 :: k 〉
  | step_inl : forall e1 P k,
      step〈 (exp_inl P e1) | k 〉
        〈 e1 | frame_inl P :: k 〉
  | step_inr : forall e1 k P,
      step〈 (exp_inr P e1) | k 〉
        〈 e1 | frame_inr P :: k 〉
  | step_case : forall e1 e2 e3 k,
      step〈 (exp_case e1 e2 e3) | k 〉
        〈 e1 | frame_case e2 e3 :: k 〉
  | step_pair_1 : forall P e1 e2 k,
      step〈 (exp_pair P e1 e2) | k 〉
        〈 e1 | frame_pair_1 P e2 :: k 〉
  | step_pair_2 : forall P v e2 k,
      value v ->
      step〈 v | frame_pair_1 P e2 :: k 〉
        〈 e2 | frame_pair_2 P v :: k 〉
  | step_first : forall e1 k,
      step〈 (exp_first e1) | k 〉
        〈 e1 | frame_first :: k 〉
  | step_second : forall e1 k,
      step〈 (exp_second e1) | k 〉
        〈 e1 | frame_second :: k 〉


  | step_app_abs : forall Q V e1 e2 t k,
      value e2 ->
      concretize Q = Some t ->
      barrier_compatible k t ->
      step〈 e2 | frame_app (exp_abs Q V e1) :: k 〉
        〈 (open_ee e1 e2) | frame_barrier t :: k 〉
  | step_app_tabs : forall P T e1 V t k,
      type V ->
      concretize P = Some t ->
      barrier_compatible k t ->
      step〈 (exp_tabs P T e1) | frame_tabs V :: k 〉
        〈 (open_te e1 V) | frame_barrier t :: k 〉
  | step_app_qabs : forall P Q e1 R t k,
      qual R ->
      concretize P = Some t ->
      barrier_compatible k t ->
      step〈 (exp_qabs P Q e1) | frame_qabs R :: k 〉
        〈 (open_qe e1 R) | frame_barrier t :: k 〉
  | step_let_value : forall v1 e2 k,
      value v1 ->
      step〈 v1 | frame_let e2 :: k 〉
        〈 (open_ee e2 v1) | k 〉
  | step_case_inl : forall P v1 e2 e3 k,
      value v1 ->
      step〈 (exp_inl P v1) | frame_case e2 e3 :: k 〉
        〈 (open_ee e2 v1) | k 〉
  | step_case_inr : forall P v1 e2 e3 k,
      value v1 ->
      step〈 (exp_inr P v1) | frame_case e2 e3 :: k 〉
        〈 (open_ee e3 v1) | k 〉
  | step_first_pair : forall P v1 v2 k,
      value v1 ->
      value v2 ->
      step〈 (exp_pair P v1 v2) | frame_first :: k 〉
        〈 v1 | k 〉
  | step_second_pair : forall P v1 v2 k,
      value v1 ->
      value v2 ->
      step〈 (exp_pair P v1 v2) | frame_second :: k 〉
        〈 v2 | k 〉
  | step_make_inl : forall P v1 k,
      value v1 ->
        step〈 v1 | frame_inl P :: k 〉
            〈 (exp_inl P v1) | k 〉
  | step_make_inr : forall P v1 k,
      value v1 ->
        step〈 v1 | frame_inr P :: k 〉
            〈 (exp_inr P v1) | k 〉
  | step_make_pair : forall P v1 v2 k,
      value v2 ->
      value v1 ->
            step〈 v2 | frame_pair_2 P v1 :: k 〉
                〈 (exp_pair P v1 v2) | k 〉

  | step_upqual_1 : forall P e1 k,
      step 〈 (exp_upqual P e1) | k 〉
      〈 e1 | (frame_upqual P :: k) 〉
  | step_upqual_int : forall P Q cP cQ z k,
      concretize P = Some cP ->
      concretize Q = Some cQ ->
      cQ ≤ cP ->
      step 〈 (exp_int Q z) | frame_upqual P :: k 〉
      〈 (exp_int P z) | k 〉
  | step_upqual_abs : forall P Q cP cQ V e1 k,
      concretize P = Some cP ->
      concretize Q = Some cQ ->
      cQ ≤ cP ->
      step 〈 (exp_abs Q V e1) | frame_upqual P :: k 〉
      〈 (exp_abs P V e1) | k 〉
  | step_upqual_tabs : forall P Q cP cQ V e1 k,
      concretize P = Some cP ->
      concretize Q = Some cQ ->
      cQ ≤ cP ->
      step 〈 (exp_tabs Q V e1) | frame_upqual P :: k 〉
      〈 (exp_tabs P V e1) | k 〉
  | step_upqual_qabs : forall P Q cP cQ V e1 k,
      concretize P = Some cP ->
      concretize Q = Some cQ ->
      cQ ≤ cP ->
      step 〈 (exp_qabs Q V e1) | frame_upqual P :: k 〉
      〈 (exp_qabs P V e1) | k 〉
  | step_upqual_inl : forall P Q cP cQ v1 k,
      value v1 ->
      concretize P = Some cP ->
      concretize Q = Some cQ ->
      cQ ≤ cP ->
      step 〈 (exp_inl Q v1) | frame_upqual P :: k 〉
      〈 (exp_inl P v1) | k 〉
  | step_upqual_inr : forall P Q cP cQ v1 k,
      value v1 ->
      concretize P = Some cP ->
      concretize Q = Some cQ ->
      cQ ≤ cP ->
      step 〈 (exp_inr Q v1) | frame_upqual P :: k 〉
      〈 (exp_inr P v1) | k 〉
  | step_upqual_pair : forall P Q cP cQ v1 v2 k,
      value v1 ->
      value v2 ->
      cQ ≤ cP ->
      concretize P = Some cP ->
      concretize Q = Some cQ ->
      step 〈 (exp_pair Q v1 v2) | frame_upqual P :: k 〉
      〈 (exp_pair P v1 v2) | k 〉
  | step_check_1 : forall P e1 k,
      step 〈 (exp_check P e1) | k 〉
      〈 e1 | (frame_check P :: k) 〉
  | step_check_int : forall P Q cP cQ z k,
      concretize P = Some cP ->
      concretize Q = Some cQ ->
      cQ ≤ cP ->
      step 〈 (exp_int Q z) | frame_check P :: k 〉
      〈 (exp_int Q z) | k 〉
  | step_check_abs : forall P Q cP cQ V e1 k,
      concretize P = Some cP ->
      concretize Q = Some cQ ->
      cQ ≤ cP ->
      step 〈 (exp_abs Q V e1) | frame_check P :: k 〉
      〈 (exp_abs Q V e1) | k 〉
  | step_check_tabs : forall P Q cP cQ V e1 k,
      concretize P = Some cP ->
      concretize Q = Some cQ ->
      cQ ≤ cP ->
      step 〈 (exp_tabs Q V e1) | frame_check P :: k 〉
      〈 (exp_tabs Q V e1) | k 〉
  | step_check_qabs : forall P Q cP cQ V e1 k,
      concretize P = Some cP ->
      concretize Q = Some cQ ->
      cQ ≤ cP ->
      step 〈 (exp_qabs Q V e1) | frame_check P :: k 〉
      〈 (exp_qabs Q V e1) | k 〉
  | step_check_inl : forall P Q cP cQ v1 k,
      value v1 ->
      concretize P = Some cP ->
      concretize Q = Some cQ ->
      cQ ≤ cP ->
      step 〈 (exp_inl Q v1) | frame_check P :: k 〉
      〈 (exp_inl Q v1) | k 〉
  | step_check_inr : forall P Q cP cQ v1 k,
      value v1 ->
      concretize P = Some cP ->
      concretize Q = Some cQ ->
      cQ ≤ cP ->
      step 〈 (exp_inr Q v1) | frame_check P :: k 〉
      〈 (exp_inr Q v1) | k 〉
  | step_check_pair : forall P Q cP cQ v1 v2 k,
      value v1 ->
      value v2 ->
      concretize P = Some cP ->
      concretize Q = Some cQ ->
      step 〈 (exp_pair Q v1 v2) | frame_check P :: k 〉
      〈 (exp_pair Q v1 v2) | k  〉



  | step_without : forall Q e1 t k,
      concretize Q = Some t ->
      step〈 exp_without Q e1 | k 〉
        〈 e1 | frame_without t :: k 〉

  | step_elim_without : forall e s k,
      value e ->
      step〈 e | frame_without s :: k 〉〈 e | k 〉
  | step_do : forall b k,
      barrier_compatible k b ->
      step 〈 exp_do b | k 〉〈 (exp_int (qua_base bot) 42) | k 〉
  | step_if0 : forall e1 e2 e3 k,
      step 〈 (exp_if0 e1 e2 e3) | k 〉
        〈 e1 | frame_if0 e2 e3 :: k 〉
  | step_if0_zero : forall Q e2 e3 k,
      step 〈 (exp_int Q 0) | frame_if0 e2 e3 :: k 〉
        〈 e2 | k 〉
  | step_if0_nonzero : forall Q e2 e3 n k,
      (not (Z.eq n 0)) ->
      step 〈 (exp_int Q n)| frame_if0 e2 e3 :: k 〉
        〈 e3 | k 〉
.

Notation "s1 --> s2" := (step s1 s2).

Inductive done_state : state -> Prop :=
  | done_value : forall v, value v -> done_state (state_step v done).
