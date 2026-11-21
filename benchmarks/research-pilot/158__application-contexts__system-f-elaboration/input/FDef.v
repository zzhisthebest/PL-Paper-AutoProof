Set Implicit Arguments.

From TLC Require Import LibList.

From TLC Require Import LibLN.

Require Import DeclDef.

Implicit Types x : var.

Definition ftyp := dtyp.

Definition ftyp_nat := dtyp_nat.

Definition ftyp_bvar := dtyp_bvar.

Definition ftyp_fvar := dtyp_fvar.

Definition ftyp_arrow := dtyp_arrow.

Definition ftyp_all := dtyp_all.

Definition ftyp_pair := dtyp_pair.

Inductive ftrm : Set :=
  | ftrm_bvar   : nat -> ftrm
  | ftrm_fvar   : var -> ftrm
  | ftrm_nat    : nat -> ftrm
  | ftrm_absann : ftyp -> ftrm -> ftrm
  | ftrm_app    : ftrm -> ftrm -> ftrm
  | ftrm_tabs   : ftrm -> ftrm
  | ftrm_tapp   : ftrm -> ftyp -> ftrm
  | ftrm_pair   : ftrm -> ftrm -> ftrm
  | ftrm_fst    : ftrm -> ftrm
  | ftrm_snd    : ftrm -> ftrm
.

Definition fopen_tt_rec := dopen_tt_rec.

Definition fopen_tt T U := fopen_tt_rec 0 U T.

Fixpoint fopen_te_rec (K : nat) (U : ftyp) (e : ftrm) {struct e} : ftrm :=
  match e with
  | ftrm_bvar i       => ftrm_bvar i
  | ftrm_fvar x       => ftrm_fvar x
  | ftrm_nat i        => ftrm_nat i
  | ftrm_absann V e1  => ftrm_absann (fopen_tt_rec K U V)  (fopen_te_rec K U e1)
  | ftrm_app e1 e2    => ftrm_app    (fopen_te_rec K U e1) (fopen_te_rec K U e2)
  | ftrm_tabs e1      => ftrm_tabs   (fopen_te_rec (S K) U e1)
  | ftrm_tapp e1 e2   => ftrm_tapp   (fopen_te_rec K U e1) (fopen_tt_rec K U e2)
  | ftrm_pair e1 e2   => ftrm_pair    (fopen_te_rec K U e1) (fopen_te_rec K U e2)
  | ftrm_fst e1       => ftrm_fst    (fopen_te_rec K U e1)
  | ftrm_snd e1       => ftrm_snd    (fopen_te_rec K U e1)
  end.

Definition fopen_te t U := fopen_te_rec 0 U t.

Fixpoint fopen_ee_rec (k : nat) (f : ftrm) (e : ftrm) {struct e} : ftrm :=
  match e with
  | ftrm_bvar i       => If k = i then f else (ftrm_bvar i)
  | ftrm_fvar x       => ftrm_fvar x
  | ftrm_nat i        => ftrm_nat i
  | ftrm_absann V e1  => ftrm_absann V (fopen_ee_rec (S k) f e1)
  | ftrm_app e1 e2    => ftrm_app (fopen_ee_rec k f e1) (fopen_ee_rec k f e2)
  | ftrm_tabs e1      => ftrm_tabs (fopen_ee_rec k f e1)
  | ftrm_tapp e1 e2   => ftrm_tapp (fopen_ee_rec k f e1) e2
  | ftrm_pair e1 e2   => ftrm_pair (fopen_ee_rec k f e1) (fopen_ee_rec k f e2)
  | ftrm_fst e1       => ftrm_fst (fopen_ee_rec k f e1)
  | ftrm_snd e1       => ftrm_snd (fopen_ee_rec k f e1)
  end.

Definition fopen_ee t u := fopen_ee_rec 0 u t.

Notation "T 'fopen_tt_var' X" := (fopen_tt T (ftyp_fvar X)) (at level 67).

Notation "t 'fopen_te_var' X" := (fopen_te t (ftyp_fvar X)) (at level 67).

Notation "t 'fopen_ee_var' x" := (fopen_ee t (ftrm_fvar x)) (at level 67).

Definition ftype := dtype.

Definition ftype_nat := dtype_nat.

Definition ftype_var := dtype_var.

Definition ftype_arrow := dtype_arrow.

Definition ftype_all := dtype_all.

Definition ftype_pair := dtype_pair.

Inductive fterm : ftrm -> Prop :=
  | fterm_var : forall x,
      fterm (ftrm_fvar x)
  | fterm_nat : forall i,
      fterm (ftrm_nat i)
  | fterm_absann : forall L V e1,
      dtype V ->
      (forall x, x \notin L -> fterm (e1 fopen_ee_var x)) ->
      fterm (ftrm_absann V e1)
  | fterm_app : forall e1 e2,
      fterm e1 ->
      fterm e2 ->
      fterm (ftrm_app e1 e2)
  | fterm_tabs : forall L e1,
      (forall X, X \notin L -> fterm (e1 fopen_te_var X)) ->
      fterm (ftrm_tabs e1)
  | fterm_tapp : forall e1 V,
      fterm e1 ->
      ftype V ->
      fterm (ftrm_tapp e1 V)
  | fterm_pair : forall e1 e2,
      fterm e1 ->
      fterm e2 ->
      fterm (ftrm_pair e1 e2)
  | fterm_fst : forall e1,
      fterm e1 ->
      fterm (ftrm_fst e1)
  | fterm_snd : forall e1,
      fterm e1 ->
      fterm (ftrm_snd e1)
.

Inductive fbind := dbind.

Definition fenv := denv.

Definition fokt := dokt.

Definition fokt_empty := dokt_empty.

Definition fokt_typ := dokt_typ.

Inductive ftyping : denv -> ftrm -> dtyp -> Prop :=
  | ftyping_var : forall E x T,
      fokt E ->
      binds x T E ->
      ftyping E (ftrm_fvar x) T
  | ftyping_nat : forall E i,
      fokt E ->
      ftyping E (ftrm_nat i) (ftyp_nat)
  | ftyping_absann : forall L E V e1 T1,
      (forall x, x \notin L ->
            ftyping (E & x ~ V) (e1 fopen_ee_var x) T1) ->
      ftyping E (ftrm_absann V e1) (ftyp_arrow V T1)
  | ftyping_tabs : forall L E e1 T1,
      (forall X, X \notin L ->
        ftyping E (e1 fopen_te_var X) (T1 fopen_tt_var X)) ->
      ftyping E (ftrm_tabs e1) (ftyp_all T1)
  | ftyping_app : forall T1 E e1 e2 T2,
      ftyping E e2 T1 ->
      ftyping E e1 (ftyp_arrow T1 T2) ->
      ftyping E (ftrm_app e1 e2) T2
  | ftyping_tapp : forall T1 E e1 T2,
      ftyping E e1 (ftyp_all T1) ->
      dtype T2 ->
      ftyping E (ftrm_tapp e1 T2) (fopen_tt T1 T2)
  | ftyping_pair : forall T1 E e1 e2 T2,
      ftyping E e1 T1 ->
      ftyping E e2 T2 ->
      ftyping E (ftrm_pair e1 e2) (ftyp_pair T1 T2)
  | ftyping_fst : forall T1 E e1 T2,
      ftyping E e1 (ftyp_pair T1 T2) ->
      ftyping E (ftrm_fst e1) T1
  | ftyping_snd : forall T1 E e1 T2,
      ftyping E e1 (ftyp_pair T1 T2) ->
      ftyping E (ftrm_snd e1) T2
.
