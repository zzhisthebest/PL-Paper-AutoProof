Require Import AmberBase.

Require Import Metalib.Metatheory.

Require Import Program.Equality.

Definition env_mode := list ( Mode).

Definition eqMode (a b: Mode)  : bool :=
  match a,b with
  | Pos, Pos => true
  | Neg, Neg => true
  | _,_ => false
  end.

Fixpoint amber_cov (Ea : env_amber) (Em : env_mode) (T:typ) (m:Mode) : typ :=
  match Ea, Em with
  | (X,Y)::E, m'::Em' => if (eqMode m' m) then amber_cov E Em' (subst_tt X Y T) m
                         else amber_cov E Em' T m
  | _,_ => T
  end.

Theorem amber_complete: forall  A B,
    sub nil A B ->
    sub_amber nil (amber_cov nil nil A Neg) (amber_cov nil nil B Pos) .
