Require Import Language.

Fixpoint ctx_nom (G : context) := match G with
  | nil => nil
  | (x, Tm _) :: G' => (x, Nom) :: ctx_nom G'
  | (x, Co _) :: G' => ctx_nom G'
  end.

Definition Good (G : context) (D : available_props):=
  forall c1 A B1 T1 R,
    binds c1 (Co (Eq A B1 T1 R)) G
    -> c1 `in` D
    -> exists C, Par (ctx_nom G) A C R /\ Par (ctx_nom G) B1 C R.

Definition irrelevant G D (a : tm) :=
  (forall x A, binds x (Tm A) G -> x `notin` fv_tm_tm_tm a) /\ Good G D.

Theorem confluence : forall W a a1 R,
  Par W a a1 R ->
  forall a2, Par W a a2 R -> exists b, Par W a1 b R /\ Par W a2 b R.

Theorem reduction_preservation : forall a a' R, reduction_in_one a a' R -> forall G A D,
      Typing G a A -> Typing G a' A /\ DefEq G D a a' A R.

Theorem progress : forall G a A R, Typing G a A ->
                          irrelevant G (dom G) a ->
                          Value R a \/ exists a', reduction_in_one a a' R.
