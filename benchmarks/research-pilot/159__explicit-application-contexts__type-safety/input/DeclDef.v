Set Implicit Arguments.

From TLC Require Import LibList.

From TLC Require Import LibLN.

Implicit Types x : var.

Inductive typ : Set :=
  | typ_nat   : typ
  | typ_bvar  : nat -> typ
  | typ_fvar  : var -> typ
  | typ_arrow : typ -> typ -> typ
  | typ_all   : typ -> typ.

Inductive trm : Set :=
  | trm_bvar   : nat -> trm
  | trm_fvar   : var -> trm
  | trm_nat    : nat -> trm
  | trm_abs    : trm -> trm
  | trm_absann : typ -> trm -> trm
  | trm_app    : trm -> trm -> trm
  | trm_tabs   : trm -> trm
  | trm_tapp   : trm -> typ -> trm
.

Fixpoint open_tt_rec (K : nat) (U : typ) (T : typ) {struct T} : typ :=
  match T with
  | typ_nat         => typ_nat
  | typ_bvar J      => If K = J then U else (typ_bvar J)
  | typ_fvar X      => typ_fvar X
  | typ_arrow T1 T2 => typ_arrow (open_tt_rec K U T1) (open_tt_rec K U T2)
  | typ_all T       => typ_all (open_tt_rec (S K) U T)
  end.

Definition open_tt T U := open_tt_rec 0 U T.

Fixpoint open_te_rec (k : nat) (f : typ) (e : trm) {struct e} : trm :=
  match e with
  | trm_bvar i       => trm_bvar i
  | trm_fvar x       => trm_fvar x
  | trm_nat i        => trm_nat i
  | trm_abs e1       => trm_abs (open_te_rec k f e1)
  | trm_absann V e1  => trm_absann (open_tt_rec k f V)
                                    (open_te_rec k f e1)
  | trm_app e1 e2    => trm_app (open_te_rec k f e1)
                                 (open_te_rec k f e2)
  | trm_tabs e1      => trm_tabs (open_te_rec (S k) f e1)
  | trm_tapp e1 e2   => trm_tapp (open_te_rec k f e1)
                                  (open_tt_rec k f e2)
  end.

Definition open_te t u := open_te_rec 0 u t.

Fixpoint open_ee_rec (k : nat) (f : trm) (e : trm) {struct e} : trm :=
  match e with
  | trm_bvar i       => If k = i then f else (trm_bvar i)
  | trm_fvar x       => trm_fvar x
  | trm_nat i        => trm_nat i
  | trm_abs e1       => trm_abs (open_ee_rec (S k) f e1)
  | trm_absann V e1  => trm_absann V (open_ee_rec (S k) f e1)
  | trm_app e1 e2    => trm_app (open_ee_rec k f e1) (open_ee_rec k f e2)
  | trm_tabs e       => trm_tabs (open_ee_rec k f e)
  | trm_tapp e T     => trm_tapp (open_ee_rec k f e) T
  end.

Definition open_ee t u := open_ee_rec 0 u t.

Notation "T 'open_tt_var' X" := (open_tt T (typ_fvar X)) (at level 67).

Notation "t 'open_te_var' X" := (open_te t (typ_fvar X)) (at level 67).

Notation "t 'open_ee_var' x" := (open_ee t (trm_fvar x)) (at level 67).

Inductive type : typ -> Prop :=
  | type_nat :
      type typ_nat
  | type_fvar : forall X,
      type (typ_fvar X)
  | type_arrow : forall T1 T2,
      type T1 ->
      type T2 ->
      type (typ_arrow T1 T2)
  | type_all : forall L T,
      (forall X, X \notin L -> type (T open_tt_var X)) ->
      type (typ_all T).

Inductive term : trm -> Prop :=
  | term_var : forall x,
      term (trm_fvar x)
  | term_nat : forall i,
      term (trm_nat i)
  | term_abs : forall L e1,
      (forall x, x \notin L -> term (e1 open_ee_var x)) ->
      term (trm_abs e1)
  | term_absann : forall L V e1,
      type V ->
      (forall x, x \notin L -> term (e1 open_ee_var x)) ->
      term (trm_absann V e1)
  | term_app : forall e1 e2,
      term e1 ->
      term e2 ->
      term (trm_app e1 e2)
  | term_tabs : forall L e1,
      (forall X, X \notin L -> term (e1 open_te_var X)) ->
      term (trm_tabs e1)
  | term_tapp : forall e1 V,
      term e1 ->
      type V ->
      term (trm_tapp e1 V).

Inductive bind : Set :=
  | bind_tvar : bind
  | bind_def  : typ -> bind
  | bind_typ  : typ -> bind
.

Notation "X ~tvar" := (X ~ bind_tvar)
  (at level 23, left associativity) : env_scope.

Notation "X ~= T" := (X ~ bind_def T)
  (at level 23, left associativity) : env_scope.

Notation "x ~: T" := (x ~ bind_typ T)
  (at level 23, left associativity) : env_scope.

Definition env := LibEnv.env bind.

Fixpoint subst_tt (Z : var) (U : typ) (T : typ) {struct T} : typ :=
  match T with
  | typ_nat         => typ_nat
  | typ_bvar J      => typ_bvar J
  | typ_fvar X      => If X = Z then U else (typ_fvar X)
  | typ_arrow T1 T2 => typ_arrow (subst_tt Z U T1) (subst_tt Z U T2)
  | typ_all T       => typ_all (subst_tt Z U T)
  end.

Fixpoint apply_env (E : env) (e : typ) : typ :=
  match E with
  | nil => e
  | cons (x, bind_typ T) E'   => apply_env E' e
  | cons (x, bind_tvar)  E'   => apply_env E' e
  | cons (x, bind_def T) E'   => apply_env E' (subst_tt x T e)
  end
.

Inductive wft : env -> typ -> Prop :=
  | wft_nat : forall E,
      wft E typ_nat
  | wft_tvar : forall E X,
      binds X bind_tvar E ->
      wft E (typ_fvar X)
  | wft_arrow : forall E T1 T2,
      wft E T1 ->
      wft E T2 ->
      wft E (typ_arrow T1 T2)
  | wft_all : forall L E T,
      (forall X, X \notin L ->
        wft (E & X ~tvar ) (T open_tt_var X)) ->
      wft E (typ_all T).

Inductive okt : env -> Prop :=
  | okt_empty :
      okt empty
  | okt_tvar : forall E X,
      okt E -> X # E -> okt (E & X ~tvar)
  | okt_def : forall E X T,
      okt E -> wft E T -> X # E -> okt (E & X ~= T)
  | okt_typ : forall E x T,
      okt E -> wft E T -> x # E -> okt (E & x ~: T).

Inductive item : Set :=
  | item_def  : typ -> item
  | item_typ  : typ -> item
.

Definition aenv := list item.

Inductive wfa : env -> aenv -> Prop :=
  | wfa_empty : forall E,
      wfa E nil
  | wfa_def : forall E S A,
      wfa E S ->
      wft E A ->
      wfa E (item_def A :: S)
  | wfa_typ : forall E S A,
      wfa E S ->
      wft E A ->
      wfa E (item_typ A :: S)
.

Inductive sub : aenv -> typ -> typ -> Prop :=
  | sub_empty : forall A,
      sub nil A A
  | sub_tapp : forall S A B C,
      sub S (open_tt B A) C ->
      sub (item_def A :: S) (typ_all B) C
  | sub_app : forall S A B C,
      sub S B C ->
      sub (item_typ A :: S) (typ_arrow A B) C
.

Inductive typing : env -> aenv -> trm -> typ -> Prop :=
  | typing_var : forall E S x A B,
      okt E ->
      wfa E S ->
      binds x (bind_typ A) E ->
      sub S A B ->
      typing E S (trm_fvar x) B
  | typing_nat : forall E i,
      okt E ->
      typing E nil (trm_nat i) typ_nat
  | typing_abs : forall L E S V e1 T1,
      (forall x, x \notin L ->
        typing (E & x ~: V) S (e1 open_ee_var x) T1) ->
      typing E (item_typ V :: S)(trm_abs e1) T1
  | typing_absann_a : forall L E V e1 T1,
      (forall x, x \notin L ->
        typing (E & x ~: apply_env E V) nil (e1 open_ee_var x) T1) ->
      typing E nil (trm_absann V e1) (typ_arrow (apply_env E V) T1)
  | typing_absann_b : forall L E S V e1 T1,
      (forall x, x \notin L ->
        typing (E & x ~: apply_env E V) S (e1 open_ee_var x) T1) ->
      typing E (item_typ (apply_env E V) :: S) (trm_absann V e1) T1
  | typing_app : forall T1 E S e1 e2 T2,
      typing E nil e2 T1 ->
      typing E (item_typ T1 :: S) e1 T2 ->
      typing E S (trm_app e1 e2) T2
  | typing_tabs_a : forall L E e1 T1,
      (forall x, x \notin L ->
        typing (E & x ~tvar) nil (e1 open_te_var x) (T1 open_tt_var x)) ->
      typing E nil (trm_tabs e1) (typ_all T1)
  | typing_tabs_b : forall L E S e1 T1 A,
      (forall x, x \notin L ->
        typing (E & x ~= A) S (e1 open_te_var x) T1) ->
      typing E (item_def A :: S) (trm_tabs e1) T1
  | typing_tapp : forall E S e1 T2 A,
      typing E (item_def (apply_env E A) :: S) e1 T2 ->
      typing E S (trm_tapp e1 A) T2
.

Inductive value : trm -> Prop :=
  | value_abs     : forall e1,   term (trm_abs e1) ->
                            value (trm_abs e1)
  | value_absann  : forall V e1, term (trm_absann V e1) ->
                            value (trm_absann V e1)
  | value_tabs    : forall e1,   term (trm_tabs e1) ->
                            value (trm_tabs e1)
  | value_nat    : forall i,    value (trm_nat i).

Inductive red : trm -> trm -> Prop :=
  | red_app : forall e1 e1' e2,
      term e2 ->
      red e1 e1' ->
      red (trm_app e1 e2) (trm_app e1' e2)
  | red_tapp : forall e1 e1' V,
      type V ->
      red e1 e1' ->
      red (trm_tapp e1 V) (trm_tapp e1' V)
  | red_abs : forall e1 v2,
      term (trm_abs e1) ->
      term v2 ->
      red (trm_app (trm_abs e1) v2) (open_ee e1 v2)
  | red_absann : forall V e1 v2,
      term (trm_absann V e1) ->
      term v2 ->
      red (trm_app (trm_absann V e1) v2) (open_ee e1 v2)
  | red_tabs : forall e1 V2,
      term (trm_tabs e1) ->
      type V2 ->
      red (trm_tapp (trm_tabs e1) V2) (open_te e1 V2).
