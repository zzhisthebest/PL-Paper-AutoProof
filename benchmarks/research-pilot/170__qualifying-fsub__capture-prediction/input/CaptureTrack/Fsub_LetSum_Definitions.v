(* Based on the System F-sub development by Brian Aydemir and Arthur
   Charguéraud, with Aaron Bohannon, Jeffrey Vaughan, and Dimitrios Vytiniotis. *)

Require Export Fsub.CaptureTrack.LabelMap.

Require Export Fsub.CaptureTrack.Label.

Require Export Fsub.FqMeta.Metatheory.

Require Export String.

Inductive qua : Set :=
  | qua_top : qua
  | qua_bvar : nat -> qua
  | qua_fvar : atom -> qua
  | qua_meet : qua -> qua -> qua
  | qua_join : qua -> qua -> qua
  | qua_bot : qua
.

Inductive typ : Set :=
  | typ_top : typ
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
  | exp_bvar : nat -> exp
  | exp_fvar : atom -> exp
  | exp_abs : qua -> qtyp -> exp -> exp
  | exp_app : exp -> exp -> qua -> exp
  | exp_tabs : qua -> typ -> exp -> exp
  | exp_tapp : exp -> typ -> exp
  | exp_qabs : qua -> qua -> exp -> exp
  | exp_qapp : exp -> qua -> exp
  | exp_let : qua -> exp -> exp -> exp
  | exp_inl : qua -> exp -> exp
  | exp_inr : qua -> exp -> exp
  | exp_case : exp -> qua -> exp -> qua -> exp -> exp
  | exp_pair : qua -> exp -> exp -> exp
  | exp_first : exp -> exp
  | exp_second : exp -> exp
  | exp_ref : qua -> exp -> exp
  | exp_ref_label : qua -> label -> exp
  | exp_deref : exp -> exp
  | exp_set_ref : exp -> exp -> exp
  | exp_upqual : qua -> exp -> exp
  | exp_check : qua -> exp -> exp
.

Coercion typ_bvar : nat >-> typ.

Coercion typ_fvar : atom >-> typ.

Coercion exp_bvar : nat >-> exp.

Coercion exp_fvar : atom >-> exp.

Coercion qua_bvar : nat >-> qua.

Coercion qua_fvar : atom >-> qua.

Inductive concrete_qua : Set := cqua_top | cqua_bot.

Fixpoint concretize (q : qua) : (option concrete_qua) :=
  match q with
  | qua_top => Some cqua_top
  | qua_fvar X => None
  | qua_bvar n => None
  | qua_join Q1 Q2 =>
    match (concretize Q1) with
    | Some cqua_top => Some cqua_top
    | Some cqua_bot => (concretize Q2)
    | None => None
    end
  | qua_meet Q1 Q2 =>
    match (concretize Q1) with
    | Some cqua_top => (concretize Q2)
    | Some cqua_bot => Some cqua_bot
    | None => None
    end
  | qua_bot => Some cqua_bot
  end.

Definition abstractize (s : concrete_qua) :=
  match s with
  | cqua_top => qua_top
  | cqua_bot => qua_bot
  end.

Inductive cqua_compatible : concrete_qua -> concrete_qua -> Prop :=
  | cqua_compatible_same : forall s, cqua_compatible s s
  | cqua_compatible_up : cqua_compatible cqua_bot cqua_top.

Notation "s ≤ t" := (cqua_compatible s t) (at level 70).

Fixpoint open_qq_rec (K : nat) (R : qua) (Q : qua)  {struct Q} : qua :=
  match Q with
  | qua_top => qua_top
  | qua_bvar J => if (K == J) then R else (qua_bvar J)
  | qua_fvar X => qua_fvar X
  | qua_meet Q1 Q2 => qua_meet (open_qq_rec K R Q1) (open_qq_rec K R Q2)
  | qua_join Q1 Q2 => qua_join (open_qq_rec K R Q1) (open_qq_rec K R Q2)
  | qua_bot => qua_bot
  end.

Fixpoint open_tt_rec (K : nat) (U : typ) (T : typ)  {struct T} : typ :=
  match T with
  | typ_top => typ_top
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
  | exp_bvar i => exp_bvar i
  | exp_fvar x => exp_fvar x
  | exp_abs P V e1 => exp_abs P (open_tqt_rec K U V)  (open_te_rec (S K) U e1)
  | exp_app e1 e2 Q => exp_app  (open_te_rec K U e1) (open_te_rec K U e2) Q
  | exp_tabs P V e1 => exp_tabs P(open_tt_rec K U V)  (open_te_rec (S K) U e1)
  | exp_tapp e1 V => exp_tapp (open_te_rec K U e1) (open_tt_rec K U V)
  | exp_qabs P Q e1 => exp_qabs P Q (open_te_rec (S K) U e1)
  | exp_qapp e1 Q => exp_qapp (open_te_rec K U e1) Q
  | exp_let Q e1 e2 => exp_let Q (open_te_rec K U e1) (open_te_rec (S K) U e2)
  | exp_inl P e1 => exp_inl P (open_te_rec K U e1)
  | exp_inr P e2 => exp_inr P (open_te_rec K U e2)
  | exp_case e1 Q1 e2 Q2 e3 =>
      exp_case (open_te_rec K U e1) Q1 (open_te_rec (S K) U e2) Q2 (open_te_rec (S K) U e3)
  | exp_pair P e1 e2 => exp_pair P (open_te_rec K U e1) (open_te_rec K U e2)
  | exp_first e1 => exp_first (open_te_rec K U e1)
  | exp_second e2 => exp_second (open_te_rec K U e2)
  | exp_ref P e1 => exp_ref P (open_te_rec K U e1)
  | exp_ref_label P l => exp_ref_label P l
  | exp_deref e1 => exp_deref (open_te_rec K U e1)
  | exp_set_ref e1 e2 => exp_set_ref (open_te_rec K U e1) (open_te_rec K U e2)
  | exp_check P e1 => exp_check P (open_te_rec K U e1)
  | exp_upqual P e1 => exp_upqual P (open_te_rec K U e1)
  end.

Fixpoint open_qe_rec (K : nat) (R : qua) (e : exp) {struct e} : exp :=
  match e with
  | exp_bvar i => exp_bvar i
  | exp_fvar x => exp_fvar x
  | exp_abs P V e1 => exp_abs (open_qq_rec K R P) (open_qqt_rec K R V)  (open_qe_rec (S K) R e1)
  | exp_app e1 e2 Q => exp_app  (open_qe_rec K R e1) (open_qe_rec K R e2) (open_qq_rec K R Q)
  | exp_tabs P V e1 => exp_tabs (open_qq_rec K R P) (open_qt_rec K R V)  (open_qe_rec (S K) R e1)
  | exp_tapp e1 V => exp_tapp (open_qe_rec K R e1) (open_qt_rec K R V)
  | exp_qabs P Q e1 => exp_qabs (open_qq_rec K R P) (open_qq_rec K R Q)  (open_qe_rec (S K) R e1)
  | exp_qapp e1 Q => exp_qapp (open_qe_rec K R e1) (open_qq_rec K R Q)
  | exp_let Q e1 e2 => exp_let (open_qq_rec K R Q) (open_qe_rec K R e1) (open_qe_rec (S K) R e2)
  | exp_inl P e1 => exp_inl (open_qq_rec K R P) (open_qe_rec K R e1)
  | exp_inr P e2 => exp_inr (open_qq_rec K R P) (open_qe_rec K R e2)
  | exp_case e1 Q1 e2 Q2 e3 =>
      exp_case (open_qe_rec K R e1) (open_qq_rec K R Q1) (open_qe_rec (S K) R e2) (open_qq_rec K R Q2) (open_qe_rec (S K) R e3)
  | exp_pair P e1 e2 => exp_pair  (open_qq_rec K R P) (open_qe_rec K R e1) (open_qe_rec K R e2)
  | exp_first e1 => exp_first (open_qe_rec K R e1)
  | exp_second e2 => exp_second (open_qe_rec K R e2)
  | exp_ref P e1 => exp_ref (open_qq_rec K R P) (open_qe_rec K R e1)
  | exp_ref_label P l => exp_ref_label (open_qq_rec K R P) l
  | exp_deref e1 => exp_deref (open_qe_rec K R e1)
  | exp_set_ref e1 e2 => exp_set_ref (open_qe_rec K R e1) (open_qe_rec K R e2)
  | exp_check P e1 => exp_check (open_qq_rec K R P) (open_qe_rec K R e1)
  | exp_upqual P e1 => exp_upqual (open_qq_rec K R P) (open_qe_rec K R e1)
  end.

Fixpoint open_ee_rec (k : nat) (f : exp) (R : qua) (e : exp)  {struct e} : exp :=
  match e with
  | exp_bvar i => if k == i then f else (exp_bvar i)
  | exp_fvar x => exp_fvar x
  | exp_abs P V e1 => exp_abs (open_qq_rec k R P) (open_qqt_rec k R V) (open_ee_rec (S k) f R e1)
  | exp_app e1 e2 Q => exp_app (open_ee_rec k f R e1) (open_ee_rec k f R e2) (open_qq_rec k R Q)
  | exp_tabs P V e1 => exp_tabs (open_qq_rec k R P) (open_qt_rec k R V) (open_ee_rec (S k) f R e1)
  | exp_tapp e1 V => exp_tapp (open_ee_rec k f R e1) (open_qt_rec k R V)
  | exp_qabs P Q e1 => exp_qabs (open_qq_rec k R P) (open_qq_rec k R Q) (open_ee_rec (S k) f R e1)
  | exp_qapp e1 Q => exp_qapp (open_ee_rec k f R e1) (open_qq_rec k R Q)
  | exp_let Q e1 e2 => exp_let (open_qq_rec k R Q) (open_ee_rec k f R e1) (open_ee_rec (S k) f R e2)
  | exp_inl P e1 => exp_inl (open_qq_rec k R P) (open_ee_rec k f R e1)
  | exp_inr P e2 => exp_inr (open_qq_rec k R P)(open_ee_rec k f R e2)
  | exp_case e1 Q1 e2 Q2 e3 =>
      exp_case (open_ee_rec k f R e1)
               (open_qq_rec k R Q1)
               (open_ee_rec (S k) f R e2)
               (open_qq_rec k R Q2)
               (open_ee_rec (S k) f R e3)
  | exp_pair P e1 e2 => exp_pair (open_qq_rec k R P) (open_ee_rec k f R e1) (open_ee_rec k f R e2)
  | exp_first e1 => exp_first (open_ee_rec k f R e1)
  | exp_second e2 => exp_second (open_ee_rec k f R e2)
  | exp_ref P e1 => exp_ref (open_qq_rec k R P) (open_ee_rec k f R e1)
  | exp_ref_label P l => exp_ref_label (open_qq_rec k R P) l
  | exp_deref e1 => exp_deref (open_ee_rec k f R e1)
  | exp_set_ref e1 e2 => exp_set_ref (open_ee_rec k f R e1) (open_ee_rec k f R e2)
  | exp_check P e1 => exp_check (open_qq_rec k R P) (open_ee_rec k f R e1)
  | exp_upqual P e1 => exp_upqual (open_qq_rec k R P) (open_ee_rec k f R e1)
  end.

Definition open_tt T U := open_tt_rec 0 U T.

Definition open_te e U := open_te_rec 0 U e.

Definition open_ee e1 e2 R:= open_ee_rec 0 e2 R e1.

Definition open_qq Q R := open_qq_rec 0 R Q.

Definition open_qe e R := open_qe_rec 0 R e.

Definition open_qt T R := open_qt_rec 0 R T.

Definition open_qqt T R := open_qqt_rec 0 R T.

Definition open_tqt T R := open_tqt_rec 0 R T.

Inductive qual : qua -> Prop :=
  | qual_top :
      qual qua_top
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
  | qual_bot :
      qual qua_bot
.

Inductive type : typ -> Prop :=
  | type_top :
      type typ_top
  | type_var : forall X,
      type (typ_fvar X)
  | type_arrow : forall L T1 T2,
      qtype T1 ->
      (forall X: atom, X `notin` L -> qtype (open_qqt T2 X)) ->
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
  | expr_var : forall x,
      expr (exp_fvar x)
  | expr_abs : forall L P T e1,
      qual P ->
      qtype T ->
      (forall x : atom, x `notin` L -> expr (open_ee e1 x x)) ->
      expr (exp_abs P T e1)
  | expr_app : forall e1 e2 Q,
      expr e1 ->
      expr e2 ->
      qual Q ->
      expr (exp_app e1 e2 Q)
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
  | expr_let : forall L Q e1 e2,
      qual Q ->
      expr e1 ->
      (forall x : atom, x `notin` L -> expr (open_ee e2 x x)) ->
      expr (exp_let Q e1 e2)
  | expr_inl : forall P e1,
      qual P ->
      expr e1 ->
      expr (exp_inl P e1)
  | expr_inr : forall P e1,
      qual P ->
      expr e1 ->
      expr (exp_inr P e1)
  | expr_case : forall L e1 Q1 e2 Q2 e3,
      expr e1 ->
      qual Q1 ->
      qual Q2 ->
      (forall x : atom, x `notin` L -> expr (open_ee e2 x x)) ->
      (forall x : atom, x `notin` L -> expr (open_ee e3 x x)) ->
      expr (exp_case e1 Q1 e2 Q2 e3)
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
.

Definition body_e (e : exp) :=
  exists L, forall x : atom, x `notin` L -> expr (open_ee e x x).

Inductive binding : Set :=
  | bind_sub : typ -> binding
  | bind_typ : qtyp -> binding
  | bind_qua : qua -> binding.

Notation env := (list (atom * binding)).

Notation empty := (@nil (atom * binding)).

Inductive wf_qua : env -> qua -> Prop :=
  | wf_qua_top : forall E,
      wf_qua E qua_top
  | wf_qua_fvar : forall R E (X : atom),
      binds X (bind_qua R) E ->
      wf_qua E (qua_fvar X)
  | wf_qua_term_fvar : forall T E (x : atom),
      binds x (bind_typ T) E ->
      wf_qua E (qua_fvar x)
  | wf_qua_meet : forall E Q1 Q2,
      wf_qua E Q1 ->
      wf_qua E Q2 ->
      wf_qua E (qua_meet Q1 Q2)
  | wf_qua_join : forall E Q1 Q2,
      wf_qua E Q1 ->
      wf_qua E Q2 ->
      wf_qua E (qua_join Q1 Q2)
  | wf_qua_bot : forall E,
      wf_qua E qua_bot
.

Inductive wf_typ : env -> typ -> Prop :=
  | wf_typ_top : forall E,
      wf_typ E typ_top
  | wf_typ_var : forall U E (X : atom),
      binds X (bind_sub U) E ->
      wf_typ E (typ_fvar X)
  | wf_typ_arrow : forall L E T1 T2,
      wf_qtyp E T1 ->
      (forall X : atom, X `notin` L ->
        wf_qtyp (X ~ bind_typ T1 ++ E) (open_qqt T2 X)) ->
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

Inductive subqual : env -> qua -> qua -> Prop :=
  | subqual_top : forall E Q,
      wf_env E ->
      wf_qua E Q ->
      subqual E Q qua_top
  | subqual_bot : forall E Q,
      wf_env E ->
      wf_qua E Q ->
      subqual E qua_bot Q
  | subqual_refl_qvar : forall E X,
      wf_env E ->
      wf_qua E (qua_fvar X) ->
      subqual E (qua_fvar X) (qua_fvar X)
  | subqual_trans_qvar : forall R E Q X,
      binds X (bind_qua R) E ->
      subqual E R Q ->
      subqual E (qua_fvar X) Q
  | subqual_trans_term_qvar : forall R E T Q X,
      binds X (bind_typ (qtyp_qtyp R T)) E ->
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
.

Inductive sub : env -> typ -> typ -> Prop :=
  | sub_top : forall E S,
      wf_env E ->
      wf_typ E S ->
      sub E S typ_top
  | sub_refl_tvar : forall E X,
      wf_env E ->
      wf_typ E (typ_fvar X) ->
      sub E (typ_fvar X) (typ_fvar X)
  | sub_trans_tvar : forall U E T X,
      binds X (bind_sub U) E ->
      sub E U T ->
      sub E (typ_fvar X) T
  | sub_arrow : forall L E S1 S2 T1 T2,
      subqtype E T1 S1 ->
      (forall X : atom, X `notin` L ->
        subqtype (X ~ bind_typ T1 ++ E) (open_qqt S2 X) (open_qqt T2 X)) ->
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

Fixpoint fv_exp_for_qua (e : exp)  {struct e} : qua :=
  match e with
  | exp_bvar i => qua_bot
  | exp_fvar x => qua_fvar x
  | exp_abs P V e1 => (fv_exp_for_qua e1)
  | exp_app e1 e2 q => (qua_join (fv_exp_for_qua e1) (fv_exp_for_qua e2))
  | exp_tabs P V e1 => (fv_exp_for_qua e1)
  | exp_tapp e1 V => (fv_exp_for_qua e1)
  | exp_qabs P Q e1 => (fv_exp_for_qua e1)
  | exp_qapp e1 Q => (fv_exp_for_qua e1)
  | exp_let q e1 e2 => (qua_join (fv_exp_for_qua e1) (fv_exp_for_qua e2))
  | exp_inl P e1 => (fv_exp_for_qua e1)
  | exp_inr P e2 => (fv_exp_for_qua e2)
  | exp_case e1 q1 e2 q2 e3 => (qua_join (fv_exp_for_qua e1) (qua_join
      (fv_exp_for_qua e2) (fv_exp_for_qua e3)))
  | exp_pair P e1 e2 => (qua_join (fv_exp_for_qua e1) (fv_exp_for_qua e2))
  | exp_first e1 => (fv_exp_for_qua e1)
  | exp_second e2 => (fv_exp_for_qua e2)
  | exp_ref P e1 => (fv_exp_for_qua e1)
  | exp_ref_label P l => qua_bot
  | exp_deref e1 => (fv_exp_for_qua e1)
  | exp_set_ref e1 e2 => (qua_join (fv_exp_for_qua e1) (fv_exp_for_qua e2))
  | exp_upqual P e1 => (fv_exp_for_qua e1)
  | exp_check P e1 => (fv_exp_for_qua e1)
  end.

Inductive typing : env -> exp -> qtyp -> Prop :=
  | typing_var : forall E x Q S,
      wf_env E ->
      binds x (bind_typ (qtyp_qtyp Q S)) E ->
      typing E (exp_fvar x) (qtyp_qtyp (qua_fvar x) S)
  | typing_abs : forall L P E V e1 T1,
      subqual E (fv_exp_for_qua e1) P ->
      (forall x : atom, x `notin` L ->
        typing (x ~ bind_typ V ++ E) (open_ee e1 x x) (open_qqt T1 x)) ->
      typing E (exp_abs P V e1) (qtyp_qtyp P (typ_arrow V T1))
  | typing_app : forall Q R T1 E e1 e2 T2,
      typing E e1 (qtyp_qtyp Q (typ_arrow (qtyp_qtyp R T1) T2)) ->
      typing E e2 (qtyp_qtyp R T1) ->
      typing E (exp_app e1 e2 R) (open_qqt T2 R)
  | typing_tabs : forall L P E V e1 T1,
      subqual E (fv_exp_for_qua e1) P ->
      (forall X : atom, X `notin` L ->
        typing (X ~ bind_sub V ++ E) (open_te e1 X) (open_tqt T1 X)) ->
      typing E (exp_tabs P V e1) (qtyp_qtyp P (typ_all V T1))
  | typing_tapp : forall Q T1 E e1 T T2,
      typing E e1 (qtyp_qtyp Q (typ_all T1 T2)) ->
      sub E T T1 ->
      typing E (exp_tapp e1 T) (open_tqt T2 T)
  | typing_qabs : forall L E P Q e1 T1,
      subqual E (fv_exp_for_qua e1) P ->
      (forall X : atom, X `notin` L ->
        typing (X ~ bind_qua Q ++ E) (open_qe e1 X) (open_qqt T1 X)) ->
      typing E (exp_qabs P Q e1) (qtyp_qtyp P (typ_qall Q T1))
  | typing_qapp : forall R Q E e1 Q1 T,
      typing E e1 (qtyp_qtyp R (typ_qall Q1 T)) ->
      subqual E Q Q1 ->
      typing E (exp_qapp e1 Q) (open_qqt T Q)
  | typing_sub : forall S E e T,
      typing E e S ->
      subqtype E S T ->
      typing E e T
  | typing_let : forall L Q S T2 e1 e2 E,
      typing E e1 (qtyp_qtyp Q S) ->
      wf_qtyp E T2 ->
      (forall x : atom, x `notin` L ->
        typing (x ~ bind_typ (qtyp_qtyp Q S) ++ E) (open_ee e2 x x) T2) ->
      typing E (exp_let Q e1 e2) T2
  | typing_inl : forall P Q1 S1 T2 e1 E,
      subqual E Q1 P ->
      typing E e1 (qtyp_qtyp Q1 S1) ->
      wf_qtyp E T2 ->
      typing E (exp_inl P e1) (qtyp_qtyp P (typ_sum (qtyp_qtyp Q1 S1) T2))
  | typing_inr : forall P T1 Q2 S2 e1 E,
      subqual E Q2 P ->
      typing E e1 (qtyp_qtyp Q2 S2) ->
      wf_qtyp E T1 ->
      typing E (exp_inr P e1) (qtyp_qtyp P (typ_sum T1 (qtyp_qtyp Q2 S2)))
  | typing_case : forall L R Q1 S1 Q2 S2 T e1 e2 e3 E,
      typing E e1 (qtyp_qtyp R (typ_sum (qtyp_qtyp Q1 S1) (qtyp_qtyp Q2 S2))) ->
      wf_qtyp E T ->
      (forall x : atom, x `notin` L ->
        typing (x ~ bind_typ (qtyp_qtyp Q1 S1) ++ E) (open_ee e2 x x) T) ->
      (forall x : atom, x `notin` L ->
        typing (x ~ bind_typ (qtyp_qtyp Q2 S2) ++ E) (open_ee e3 x x) T) ->
      typing E (exp_case e1 Q1 e2 Q2 e3) T
  | typing_pair : forall P Q1 S1 Q2 S2 e1 e2 E,
      subqual E (qua_join Q1 Q2) P ->
      typing E e1 (qtyp_qtyp Q1 S1) ->
      typing E e2 (qtyp_qtyp Q2 S2) ->
      typing E (exp_pair P e1 e2) (qtyp_qtyp P (typ_pair (qtyp_qtyp Q1 S1) (qtyp_qtyp Q2 S2)))
  | typing_first : forall Q T1 T2 e E,
      typing E e (qtyp_qtyp Q (typ_pair T1 T2)) ->
      typing E (exp_first e) T1
  | typing_second : forall Q T1 T2 e E,
      typing E e (qtyp_qtyp Q (typ_pair T1 T2)) ->
      typing E (exp_second e) T2
  | typing_upqual : forall E Q T P e,
      typing E e (qtyp_qtyp Q T) ->
      subqual E Q P ->
      typing E (exp_upqual P e) (qtyp_qtyp P T)
  | typing_check : forall E Q T P e,
      typing E e (qtyp_qtyp Q T) ->
      subqual E Q P ->
      typing E (exp_check P e) (qtyp_qtyp Q T)
.

Inductive value : exp -> Prop :=
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

Inductive red : exp -> exp -> Prop :=
  | red_app_1 : forall e1 e1' e2 Q,
      expr e2 ->
      qual Q ->
      red e1 e1' ->
      red (exp_app e1 e2 Q) (exp_app e1' e2 Q)
  | red_app_2 : forall e1 e2 e2' Q,
      value e1 ->
      qual Q ->
      red e2 e2' ->
      red (exp_app e1 e2 Q) (exp_app e1 e2' Q)
  | red_tapp : forall e1 e1' V,
      type V ->
      red e1 e1' ->
      red (exp_tapp e1 V) (exp_tapp e1' V)
  | red_qapp : forall e1 e1' R,
      qual R ->
      red e1 e1' ->
      red (exp_qapp e1 R) (exp_qapp e1' R)
  | red_abs : forall P T e1 v2 Q,
      expr (exp_abs P T e1) ->
      value v2 ->
      qual Q ->
      red (exp_app (exp_abs P T e1) v2 Q) (open_ee e1 v2 Q)
  | red_tabs : forall P T1 e1 T2,
      expr (exp_tabs P T1 e1) ->
      type T2 ->
      red (exp_tapp (exp_tabs P T1 e1) T2) (open_te e1 T2)
  | red_qabs : forall P Q1 e1 Q2,
      expr (exp_qabs P Q1 e1) ->
      qual Q2 ->
      red (exp_qapp (exp_qabs P Q1 e1) Q2) (open_qe e1 Q2)
  | red_let_1 : forall Q e1 e1' e2,
      qual Q ->
      red e1 e1' ->
      body_e e2 ->
      red (exp_let Q e1 e2) (exp_let Q e1' e2)
  | red_let : forall Q v1 e2,
      qual Q ->
      value v1 ->
      body_e e2 ->
      red (exp_let Q v1 e2) (open_ee e2 v1 Q)
  | red_inl_1 : forall P e1 e1',
      qual P ->
      red e1 e1' ->
      red (exp_inl P e1) (exp_inl P e1')
  | red_inr_1 : forall P e1 e1',
      qual P ->
      red e1 e1' ->
      red (exp_inr P e1) (exp_inr P e1')
  | red_case_1 : forall e1 e1' Q1 Q2 e2 e3,
      qual Q1 ->
      qual Q2 ->
      red e1 e1' ->
      body_e e2 ->
      body_e e3 ->
      red (exp_case e1 Q1 e2 Q2 e3) (exp_case e1' Q1 e2 Q2 e3)
  | red_case_inl : forall P v1 Q1 Q2 e2 e3,
      qual P ->
      qual Q1 ->
      qual Q2 ->
      value v1 ->
      body_e e2 ->
      body_e e3 ->
      red (exp_case (exp_inl P v1) Q1 e2 Q2 e3) (open_ee e2 v1 Q1)
  | red_case_inr : forall P v1 Q1 Q2 e2 e3,
      qual P ->
      qual Q1 ->
      qual Q2 ->
      value v1 ->
      body_e e2 ->
      body_e e3 ->
      red (exp_case (exp_inr P v1) Q1 e2 Q2 e3) (open_ee e3 v1 Q2)
  | red_pair_1 : forall P e1 e1' e2,
      qual P ->
      red e1 e1' ->
      expr e2 ->
      red (exp_pair P e1 e2) (exp_pair P e1' e2)
  | red_pair_2 : forall P v1 e2 e2',
      qual P ->
      value v1 ->
      red e2 e2' ->
      red (exp_pair P v1 e2) (exp_pair P v1 e2')
  | red_pair_first_1 : forall e1 e1',
      red e1 e1' ->
      red (exp_first e1) (exp_first e1')
  | red_pair_second_1 : forall e1 e1',
      red e1 e1' ->
      red (exp_second e1) (exp_second e1')
  | red_pair_first_2 : forall P v1 v2,
      qual P ->
      value v1 ->
      value v2 ->
      red (exp_first (exp_pair P v1 v2)) v1
  | red_pair_second_2 : forall P v1 v2,
      qual P ->
      value v1 ->
      value v2 ->
      red (exp_second (exp_pair P v1 v2)) v2



  | red_upqual_1 : forall P e1 e1',
      qual P ->
      red e1 e1' ->
      red (exp_upqual P e1) (exp_upqual P e1')
  | red_upqual_abs : forall P Q cP cQ V e1,
      qual P ->
      qual Q ->
      expr (exp_abs Q V e1) ->
      concretize P = Some cP ->
      concretize Q = Some cQ ->
      cqua_compatible cQ cP ->
      red (exp_upqual P (exp_abs Q V e1)) (exp_abs P V e1)
  | red_upqual_tabs : forall P Q cP cQ V e1,
      qual P ->
      qual Q ->
      expr (exp_tabs Q V e1) ->
      concretize P = Some cP ->
      concretize Q = Some cQ ->
      cqua_compatible cQ cP ->
      red (exp_upqual P (exp_tabs Q V e1)) (exp_tabs P V e1)
  | red_upqual_qabs : forall P Q cP cQ V e1,
      qual P ->
      qual Q ->
      expr (exp_qabs Q V e1) ->
      concretize P = Some cP ->
      concretize Q = Some cQ ->
      cqua_compatible cQ cP ->
      red (exp_upqual P (exp_qabs Q V e1)) (exp_qabs P V e1)
   | red_upqual_inl : forall P Q cP cQ e1,
      qual P ->
      qual Q ->
      expr (exp_inl Q e1) ->
      concretize P = Some cP ->
      concretize Q = Some cQ ->
      cqua_compatible cQ cP ->
      red (exp_upqual P (exp_inl Q e1)) (exp_inl P e1)
   | red_upqual_inr : forall P Q cP cQ e1,
      qual P ->
      qual Q ->
      expr (exp_inr Q e1) ->
      concretize P = Some cP ->
      concretize Q = Some cQ ->
      cqua_compatible cQ cP ->
      red (exp_upqual P (exp_inr Q e1)) (exp_inr P e1)
   | red_upqual_pair : forall P Q cP cQ e1 e2,
      qual P ->
      qual Q ->
      expr (exp_pair Q e1 e2) ->
      concretize P = Some cP ->
      concretize Q = Some cQ ->
      cqua_compatible cQ cP ->
      red (exp_upqual P (exp_pair Q e1 e2)) (exp_pair P e1 e2)
  | red_check_1 : forall P e1 e1',
      qual P ->
      red e1 e1' ->
      red (exp_check P e1) (exp_check P e1')
  | red_check_abs : forall P Q cP cQ V e1,
      qual P ->
      qual Q ->
      expr (exp_abs Q V e1) ->
      concretize P = Some cP ->
      concretize Q = Some cQ ->
      cqua_compatible cQ cP ->
      red (exp_check P (exp_abs Q V e1)) (exp_abs Q V e1)
  | red_check_tabs : forall P Q cP cQ V e1,
      qual P ->
      qual Q ->
      expr (exp_tabs Q V e1) ->
      concretize P = Some cP ->
      concretize Q = Some cQ ->
      cqua_compatible cQ cP ->
      red (exp_check P (exp_tabs Q V e1)) (exp_tabs Q V e1)
  | red_check_qabs : forall P Q cP cQ V e1,
      qual P ->
      qual Q ->
      expr (exp_qabs Q V e1) ->
      concretize P = Some cP ->
      concretize Q = Some cQ ->
      cqua_compatible cQ cP ->
      red (exp_check P (exp_qabs Q V e1)) (exp_qabs Q V e1)
   | red_check_inl : forall P Q cP cQ e1,
      qual P ->
      qual Q ->
      expr (exp_inl Q e1) ->
      concretize P = Some cP ->
      concretize Q = Some cQ ->
      cqua_compatible cQ cP ->
      red (exp_check P (exp_inl Q e1)) (exp_inl Q e1)
   | red_check_inr : forall P Q cP cQ e1,
      qual P ->
      qual Q ->
      expr (exp_inr Q e1) ->
      concretize P = Some cP ->
      concretize Q = Some cQ ->
      cqua_compatible cQ cP ->
      red (exp_check P (exp_inr Q e1)) (exp_inr Q e1)
   | red_check_pair : forall P Q cP cQ e1 e2,
      qual P ->
      qual Q ->
      expr (exp_pair Q e1 e2) ->
      concretize P = Some cP ->
      concretize Q = Some cQ ->
      cqua_compatible cQ cP ->
      red (exp_check P (exp_pair Q e1 e2)) (exp_pair Q e1 e2)
.
