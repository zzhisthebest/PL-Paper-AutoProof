Set Implicit Arguments.

From TLC Require Import LibList.

From TLC Require Import LibLN.

Implicit Types x : var.

Inductive dtyp : Set :=
  | dtyp_nat : dtyp
  | dtyp_bvar  : nat -> dtyp
  | dtyp_fvar  : var -> dtyp
  | dtyp_arrow : dtyp -> dtyp -> dtyp
  | dtyp_all   : dtyp -> dtyp
  | dtyp_pair  : dtyp -> dtyp -> dtyp
.

Inductive dtrm : Set :=
  | dtrm_bvar   : nat -> dtrm
  | dtrm_fvar   : var -> dtrm
  | dtrm_nat    : nat -> dtrm
  | dtrm_abs    : dtrm -> dtrm
  | dtrm_absann : dtyp -> dtrm -> dtrm
  | dtrm_app    : dtrm -> dtrm -> dtrm
  | dtrm_pair   : dtrm -> dtrm -> dtrm
  | dtrm_fst    : dtrm
  | dtrm_snd    : dtrm
.

Fixpoint dopen_tt_rec (K : nat) (U : dtyp) (T : dtyp) {struct T} : dtyp :=
  match T with
  | dtyp_nat         => dtyp_nat
  | dtyp_bvar J      => If K = J then U else (dtyp_bvar J)
  | dtyp_fvar X      => dtyp_fvar X
  | dtyp_arrow T1 T2 => dtyp_arrow (dopen_tt_rec K U T1) (dopen_tt_rec K U T2)
  | dtyp_all T       => dtyp_all (dopen_tt_rec (S K) U T)
  | dtyp_pair T1 T2  => dtyp_pair (dopen_tt_rec K U T1) (dopen_tt_rec K U T2)
  end.

Definition dopen_tt T U := dopen_tt_rec 0 U T.

Fixpoint dopen_ee_rec (k : nat) (f : dtrm) (e : dtrm) {struct e} : dtrm :=
  match e with
  | dtrm_bvar i       => If k = i then f else (dtrm_bvar i)
  | dtrm_fvar x       => dtrm_fvar x
  | dtrm_nat i        => dtrm_nat i
  | dtrm_abs e1       => dtrm_abs (dopen_ee_rec (S k) f e1)
  | dtrm_absann V e1  => dtrm_absann V (dopen_ee_rec (S k) f e1)
  | dtrm_app e1 e2    => dtrm_app (dopen_ee_rec k f e1) (dopen_ee_rec k f e2)
  | dtrm_pair e1 e2   => dtrm_pair (dopen_ee_rec k f e1) (dopen_ee_rec k f e2)
  | dtrm_fst          => dtrm_fst
  | dtrm_snd          => dtrm_snd
  end.

Definition dopen_ee t u := dopen_ee_rec 0 u t.

Notation "T 'dopen_tt_var' X" := (dopen_tt T (dtyp_fvar X)) (at level 67).

Notation "t 'dopen_ee_var' x" := (dopen_ee t (dtrm_fvar x)) (at level 67).

Inductive dtype : dtyp -> Prop :=
  | dtype_nat :
      dtype dtyp_nat
  | dtype_var : forall X,
      dtype (dtyp_fvar X)
  | dtype_arrow : forall T1 T2,
      dtype T1 ->
      dtype T2 ->
      dtype (dtyp_arrow T1 T2)
  | dtype_all : forall L T2,
      (forall X, X \notin L -> dtype (T2 dopen_tt_var X)) ->
      dtype (dtyp_all T2)
  | dtype_pair : forall T1 T2,
      dtype T1 ->
      dtype T2 ->
      dtype (dtyp_pair T1 T2)
.

Inductive dmono : dtyp -> Prop :=
  | dmono_nat :
      dmono dtyp_nat
  | dmono_var: forall X,
      dmono (dtyp_fvar X)
  | dmono_arrow : forall T1 T2,
      dmono T1 ->
      dmono T2 ->
      dmono (dtyp_arrow T1 T2)
  | dmono_pair : forall T1 T2,
      dmono T1 ->
      dmono T2 ->
      dmono (dtyp_pair T1 T2).

Inductive dwft : vars -> dtyp -> Prop :=
  | dwft_nat : forall E,
      dwft E dtyp_nat
  | dwft_var : forall X E,
      X \in E ->
      dwft E (dtyp_fvar X)
  | dwft_arrow : forall T1 T2 E,
      dwft E T1 ->
      dwft E T2 ->
      dwft E (dtyp_arrow T1 T2)
  | dwft_all : forall L T2 E,
      (forall X, X \notin L -> dwft (E \u \{X}) (T2 dopen_tt_var X)) ->
      dwft E (dtyp_all T2)
  | dwft_pair : forall T1 T2 E,
      dwft E T1 ->
      dwft E T2 ->
      dwft E (dtyp_pair T1 T2)
.

Inductive dterm : dtrm -> Prop :=
  | dterm_var : forall x,
      dterm (dtrm_fvar x)
  | dterm_abs : forall L e1,
      (forall x, x \notin L -> dterm (e1 dopen_ee_var x)) ->
      dterm (dtrm_abs e1)
  | dterm_nat : forall i,
      dterm (dtrm_nat i)
  | dterm_absann : forall L V e1,
      dtype V ->
      (forall x, x \notin L -> dterm (e1 dopen_ee_var x)) ->
      dterm (dtrm_absann V e1)
  | dterm_app : forall e1 e2,
      dterm e1 ->
      dterm e2 ->
      dterm (dtrm_app e1 e2)
  | dterm_pair : forall e1 e2,
      dterm e1 ->
      dterm e2 ->
      dterm (dtrm_pair e1 e2)
  | dterm_fst :
      dterm dtrm_fst
  | dterm_snd :
      dterm dtrm_snd
.

Inductive dwterm : dtrm -> Prop :=
  | dwterm_var : forall x,
      dwterm (dtrm_fvar x)
  | dwterm_abs : forall L e1,
      (forall x, x \notin L -> dwterm (e1 dopen_ee_var x)) ->
      dwterm (dtrm_abs e1)
  | dwterm_nat : forall i,
      dwterm (dtrm_nat i)
  | dwterm_absann : forall L V e1,
      dwft \{} V ->
      (forall x, x \notin L -> dwterm (e1 dopen_ee_var x)) ->
      dwterm (dtrm_absann V e1)
  | dwterm_app : forall e1 e2,
      dwterm e1 ->
      dwterm e2 ->
      dwterm (dtrm_app e1 e2)
  | dwterm_pair : forall e1 e2,
      dwterm e1 ->
      dwterm e2 ->
      dwterm (dtrm_pair e1 e2)
  | dwterm_fst :
      dwterm dtrm_fst
  | dwterm_snd :
      dwterm dtrm_snd
.

Definition denv := LibEnv.env dtyp.

Inductive dokt : denv -> Prop :=
  | dokt_empty :
      dokt empty
  | dokt_typ : forall E x T,
      dokt E -> dtype T -> x # E -> dokt (E & x ~ T).

Definition dstack := list dtyp.

Inductive aenv := plain | stack : dstack -> aenv.

Inductive dsub : aenv -> dtyp -> dtyp -> Prop :=
  |dsub_nat :
     dsub plain dtyp_nat dtyp_nat
  |dsub_tvar : forall X,
     dsub plain (dtyp_fvar X) (dtyp_fvar X)
  |dsub_arrow : forall S1 S2 T1 T2,
     dsub plain T1 S1 ->
     dsub plain S2 T2 ->
     dsub plain (dtyp_arrow S1 S2) (dtyp_arrow T1 T2)
  |dsub_alll1 : forall S2 T2 U,
     dtype U ->
     dmono U ->
     dsub plain (dopen_tt S2 U) T2 ->
     dsub plain (dtyp_all S2) T2
  |dsub_allr : forall L S2 T2,
     (forall X, X \notin L ->
           dsub plain S2 (T2 dopen_tt_var X)) ->
     dsub plain S2 (dtyp_all T2)

  |dsub_empty : forall A,
      dtype A ->
      dsub (stack nil) A A
  |dsub_alll2 : forall S2 T2 U c cs,
     dtype U ->
     dmono U ->
     dsub (stack (cons c cs)) (dopen_tt S2 U) T2 ->
     dsub (stack (cons c cs)) (dtyp_all S2) T2
  |dsub_arrow_stack : forall S1 S2 T2 c cs,
     dsub plain c S1 ->
     dsub (stack cs) S2 T2 ->
     dsub (stack (cons c cs)) (dtyp_arrow S1 S2) (dtyp_arrow c T2)
  |dsub_pair : forall T1 T2 T3 T4,
      dsub plain T1 T3 ->
      dsub plain T2 T4 ->
      dsub plain (dtyp_pair T1 T2) (dtyp_pair T3 T4).

Fixpoint dfv_tt (T : dtyp) {struct T} : vars :=
  match T with
  | dtyp_nat         => \{}
  | dtyp_bvar J      => \{}
  | dtyp_fvar X      => \{X}
  | dtyp_arrow T1 T2 => (dfv_tt T1) \u (dfv_tt T2)
  | dtyp_all T1      => (dfv_tt T1)
  | dtyp_pair T1 T2  => (dfv_tt T1) \u (dfv_tt T2)
  end.

Fixpoint dfv_tt_env (E : denv) {struct E} : vars :=
  match E with
  | nil            => \{}
  | cons (x, t) E' => dfv_tt t \u dfv_tt_env E'
  end.

Inductive dgen : denv -> dtyp -> dtyp -> Prop :=
  | dgen_empty : forall E t,
      dokt E ->
      dtype t ->
      (dfv_tt t) \- (dfv_tt_env E) = \{} ->
      dgen E t t
  | dgen_step : forall x E t t2,
      x \in (dfv_tt (t dopen_tt_var x) \- dfv_tt_env E) ->
      x \notin dfv_tt t ->
      dgen E (dtyp_all t) t2 ->
      dgen E (t dopen_tt_var x) t2.

Definition fst_typ := dtyp_all (dtyp_all (dtyp_arrow
                                            (dtyp_pair (dtyp_bvar 1) (dtyp_bvar 0))
                                            (dtyp_bvar 1)))
.

Definition snd_typ := dtyp_all (dtyp_all (dtyp_arrow
                                            (dtyp_pair (dtyp_bvar 1) (dtyp_bvar 0))
                                            (dtyp_bvar 0)))
.

Inductive dtyping : denv -> dstack -> dtrm -> dtyp -> Prop :=
  | dtyping_var : forall E x T T2 cs,
      dokt E ->
      binds x T E ->
      dsub (stack cs) T T2 ->
      dtyping E cs (dtrm_fvar x) T2
  | dtyping_nat : forall E i,
      dokt E ->
      dtyping E nil (dtrm_nat i) (dtyp_nat)
  | dtyping_absann : forall L E V e1 T1,
      dwft \{} V ->
      (forall x, x \notin L ->
            dtyping (E & x ~ V) nil (e1 dopen_ee_var x) T1) ->
      dtyping E nil (dtrm_absann V e1) (dtyp_arrow V T1)
  | dtyping_abs : forall L E t e1 T1,
      dtype t ->
      dmono t ->
      (forall x, x \notin L ->
            dtyping (E & x ~ t) nil (e1 dopen_ee_var x) T1) ->
      dtyping E nil (dtrm_abs e1) (dtyp_arrow t T1)

  | dtyping_absann_stack : forall L E V e1 T1 c cs,
      dwft \{} V ->
      dsub plain c V ->
      (forall x, x \notin L ->
            dtyping (E & x ~ V) cs (e1 dopen_ee_var x) T1) ->
      dtyping E (cons c cs) (dtrm_absann V e1) (dtyp_arrow c T1)
  | dtyping_abs_stack : forall L E e1 T1 c cs,
      (forall x, x \notin L ->
            dtyping (E & x ~ c) cs (e1 dopen_ee_var x) T1) ->
      dtyping E (cons c cs) (dtrm_abs e1) (dtyp_arrow c T1)
  | dtyping_app : forall T1 E e1 e2 T2 cs T3,
      dtyping E nil e2 T1 ->
      dgen E T1 T3 ->
      dtyping E (cons T3 cs) e1 (dtyp_arrow T3 T2) ->
      dtyping E cs (dtrm_app e1 e2) T2
  | dtyping_pair : forall E e1 e2 T1 T2,
      dtyping E nil e1 T1 ->
      dtyping E nil e2 T2 ->
      dtyping E nil (dtrm_pair e1 e2) (dtyp_pair T1 T2)
  | dtyping_fst : forall E T cs,
      dokt E ->
      dsub (stack cs) fst_typ T ->
      dtyping E cs dtrm_fst T
  | dtyping_snd : forall E T cs,
      dokt E ->
      dsub (stack cs) snd_typ T ->
      dtyping E cs dtrm_snd T
.
