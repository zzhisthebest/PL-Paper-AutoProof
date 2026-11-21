Set Implicit Arguments.

Require Export StdSetup.

Require Export VarDef.

Inductive typ : Set :=
| typ_top : typ
| typ_bot : typ
| typ_sel : avar -> typ
| typ_all : typ -> typ -> typ
| typ_bnd :  typ -> typ -> typ.

Inductive lc_avar_at : nat -> avar -> Prop :=
  | lc_ab : forall {n m}, n < m -> lc_avar_at m (avar_b n)
  | lc_af : forall {n x}, lc_avar_at n (avar_f x).

Global Instance LcAvar : LC avar := { lc_at := lc_avar_at }.

Inductive lc_typ_at : nat -> typ -> Prop :=
  | lc_typ_top : forall {n}, lc_typ_at n typ_top
  | lc_typ_bot : forall {n}, lc_typ_at n typ_bot
  | lc_typ_sel : forall {n v}, lc_at n v -> lc_typ_at n (typ_sel v)
  | lc_typ_all : forall {n T U}, lc_typ_at n T -> lc_typ_at (S n) U ->
                            lc_typ_at n (typ_all T U)
  | lc_typ_bnd : forall {n S U}, lc_typ_at n S -> lc_typ_at n U ->
                            lc_typ_at n (typ_bnd S U).

Global Instance LcTyp : LC typ := { lc_at := lc_typ_at }.

Definition open_rec_avar (k : nat) (u : var) (a : avar) : avar :=
    match a with
    | avar_b i => if k == i then avar_f u else avar_b i
    | avar_f x => avar_f x
    end.

Fixpoint open_rec_typ (k : nat) (u : var) (T : typ) : typ :=
    match T with
    | typ_top => typ_top
    | typ_bot => typ_bot
    | typ_sel x => typ_sel $ open_rec_avar k u x
    | typ_all T U => typ_all (open_rec_typ k u T) $ open_rec_typ (S k) u U
    | typ_bnd T U => typ_bnd (open_rec_typ k u T) $ open_rec_typ k u U
    end.

Global Instance OpenAvar : CanOpen avar := { open_rec := open_rec_avar }.

Global Instance OpenTyp : CanOpen typ := { open_rec := open_rec_typ }.

Notation env := (list (var * typ)).

Definition fv_avar (v : avar) : vars :=
    match v with
    | avar_b _ => {}
    | avar_f x => {{ x }}
    end.

Fixpoint fv_typ (T : typ) : vars :=
    match T with
    | typ_top | typ_bot => {}
    | typ_sel x => fv_avar x
    | typ_all T1 T2 | typ_bnd T1 T2 => fv_typ T1 \u fv_typ T2
    end.

Global Instance FvAvar : HasFv avar := { fv := fv_avar }.

Global Instance FvTyp : HasFv typ := { fv := fv_typ }.

Global Instance FvEnv : HasFv env := { fv := fun e => dom e `union` fv_values fv e }.
