Set Implicit Arguments.

Require Export Metalib.Metatheory.

Require Export Fii_inf.

Fixpoint fv_stctx (GG : stctx) {struct GG} : vars :=
  match GG with
  | nil            => {}
  | cons (x, A) P' => fv_sty_in_sty A \u fv_stctx P'
  end.

Inductive same_stctx {a b} : list (atom * a) -> list (atom * b) -> Prop :=
| same_empty : same_stctx nil nil
| same_cons : forall X A B s1 s2,
    same_stctx s1 s2 ->  same_stctx ([(X , A)] ++ s1) ([(X , B)] ++ s2).
