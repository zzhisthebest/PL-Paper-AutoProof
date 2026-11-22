Set Implicit Arguments.

Require Import LibExtra.

Require Import SyntaxClassDefs.

Generalizable Variables A B.

Class OpenTwice `(AS: Openable A) :=
  open_twice_comp : forall n x y,
    (open_rec n y) ∘ (open_rec n x) = (open_rec n x).

Class OpenCommut `(AS: Openable A) :=
    open_commut_comp : forall m n x y,
        m <> n ->
        (open_rec m x) ∘ (open_rec n y) = (open_rec n y) ∘ (open_rec m x).

Class SubstFresh `(AS : AbstractSyntax A) :=
  subst_fresh : forall x y X,
    x \notin fv X -> subst_var x y X = X.

Class SubstOpenCommut `(AS : AbstractSyntax A) :=
  subst_open_commut : forall x y z X n,
    subst_var x y (open_rec n z X)
    = open_rec n (z \[x -> y]) (subst_var x y X).

Class SubstCommut `(AS : AbstractSyntax A) :=
  subst_commut_comp x y w z:
    x <> w ->
    (y <> w \/ x = z ) ->
    (subst_var x y) ∘ (subst_var w z) = (subst_var w (z \[x -> y])) ∘ (subst_var x y).

Class SubstId `(AS : AbstractSyntax A) :=
  subst_id_comp x:
    (subst_var x x) = id.

Class FvOpenCases `(AS : AbstractSyntax A) :=
  fv_open_cases : forall x a n,
    fv (open_rec n x a) = fv a \/
    fv (open_rec n x a) = \{ x} \u fv a.

Definition FvOpenCasesInd `(AS : AbstractSyntax A) x :=
  (forall (T: A) n,
    fv (open_rec n x T) = fv T \/
    fv (open_rec n x T) = \{ x} \u fv T).

Class OpenClose `(Cl: Closing A) :=
  open_close_comp : forall n x,
    (open_rec n x) ∘ (close_rec n x) = open_rec n x.

Class CloseOpen `(Cl: Closing A) :=
  close_open_comp : forall n x,
    (close_rec n x) ∘ (open_rec n x) = close_rec n x.

Class SubstOpenClose `(Cl: Closing A) :=
  subst_open_close_comp : forall n x y,
    (subst_var x y) ∘ (open_rec n x) = (open_rec n y) ∘ (close_rec n x).

Class CloseSubst `(Cl: Closing A) :=
  close_subst_comp : forall n x y,
    (close_rec n y) ∘ (subst_var x y) = (close_rec n y) ∘ (close_rec n x).

Class SubstCloseCommut `(Cl: Closing A) :=
  subst_close_commut_comp : forall n x y z,
    z <> x -> z <> y ->
    (subst_var x y) ∘ (close_rec n z) = (close_rec n z) ∘ (subst_var x y).

Class CloseCommut `(Cl: Closing A) :=
  close_commut_comp : forall m n x y,
    x <> y ->
    (close_rec m x) ∘ (close_rec n y) = (close_rec n y) ∘ (close_rec m x).

Class OpenCloseCommut `(Cl: Closing A) :=
  open_close_commut_comp : forall m n x y,
    x <> y -> m <> n ->
    (close_rec m x) ∘ (open_rec n y) = (open_rec n y) ∘ (close_rec m x).

Class CloseUnbound `(Cl: Closing) :=
  close_unbound : forall x a n,
    x \notin fv a ->
    close_rec n x a = a.

Class OpenInjective `(AS : AbstractSyntax) :=
  open_fresh_injective : forall (X Y : A) k z,
    z \notin fv X ->
    z \notin fv Y ->
    open_rec k z X = open_rec k z Y ->
    X = Y.

Class SubstIntro `(AS : AbstractSyntax) :=
  subst_intro : forall x y n X,
    x \notin (fv X) ->
    open_rec n y X = subst_var x y (open_rec n x X).

Class SealOpen {A:Set} `(AS : AbstractSyntax A) `(SA : Sealable A) := {

  open_seal_fold_comp n x:
    (open_rec n x) ∘ (seal_rec (S n) x) = (seal_rec n x);

  open_seal_commut_comp n m x y:
    n < m ->
    (open_rec n x) ∘ (seal_rec m y) = (seal_rec m y) ∘ (open_rec n x)
}.

Class SealClose {A:Set} `(AS : AbstractSyntax A) `(SA : Sealable A)  `(CA : Closing A) := {

  close_seal_commut_comp n m x y:
    n < m -> x <> y ->
    (close_rec n x) ∘ (seal_rec m y) = (seal_rec m y) ∘ (close_rec n x)
}.

Notation SealClosedOf n y X := (
    (forall m x, n <= m -> open_rec m x X = X) ->
    seal_rec n y X = X
)(only parsing).

Class SealClosed(A:Set) `(AS : AbstractSyntax A) `(SA : Sealable A) :=

  closed_sealed_rec n y X: SealClosedOf n y X.

Notation OpenSealInvOf n y m x X := (
    n < m ->
    open_rec n y (seal_rec m x X) = open_rec n y X ->
    (seal_rec m x X) = X
) (only parsing).

Class OpenSealInv(A:Set) `(AS : AbstractSyntax A) `(SA : Sealable A) :=

  open_seal_inv n y m x X:  OpenSealInvOf n y m x X.

Notation FvSealCasesOf x a n := (
    fv (seal_rec n x a) = fv a \/
    fv (seal_rec n x a) = \{ x} \u fv a
) (only parsing).

Class FvSealCases `(AS : AbstractSyntax A) `(SA : Sealable A) :=
  fv_seal_cases x a n: FvSealCasesOf x a n.

Notation OpenTwiceInvOf m n y1 y2 x := (
    m%nat <> n%nat ->
    open_rec m y1 (open_rec n y2 x) = open_rec m y1 x ->
    open_rec n y2 x = x
) (only parsing).

Class OpenTwiceInv (A:Set)  `(AS : AbstractSyntax A) :=
  open_twice_inv m n y1 y2 (x: A):
    m <> n ->
    open_rec m y1 (open_rec n y2 x) = open_rec m y1 x ->
    open_rec n y2 x = x.

Notation FvSubstCasesOf x y a := (

    (fv (subst_var x y a) = fv a /\ (x = y \/ x \notin fv a) ) \/

    (x <> y /\ x \in (fv a) /\ fv (subst_var x y a) = (fv a \- \{ x}) \u \{y})
  ) (only parsing).

Class FvSubstCases `(AS : AbstractSyntax A) :=
  fv_subst_cases x y a: FvSubstCasesOf x y a.

Notation FvCloseOf n x a := (
    (fv (close_rec n x a) = fv a \- \{x})
  ) (only parsing).

Class FvClose `(AS : AbstractSyntax A) (C: Closing AS) :=
  fv_close n x a: FvCloseOf n x a.

Notation SubstVarsEqInvOf xs ys1 ys2 a := (
    fresh (from_list ys1 \u from_list ys2) (length xs) xs%list ->
    length ys1 = length xs ->
    length ys2 = length xs ->
    (from_list xs) \c fv a ->
    (subst_vars xs ys1 a = subst_vars xs ys2 a) ->
    (ys1%list = ys2%list)
  ) (only parsing).

Class SubstVarsEqInv `(AS : AbstractSyntax A) :=
  subst_vars_eq_inv xs ys1 ys2 a: SubstVarsEqInvOf xs ys1 ys2 a.

Class ClosingInner
      `{AS: AbstractSyntax A}
      {DFv: DecideFv AS} (DFvS: ReflectFv DFv)
      (C: Closing AS) :=
  close_inner : forall n x,
    close_depth_rec n x
    = (dec_apply (dec_notin_fv x) (ignore_second id) (close_depth_rec n x)).

Class SubstitutionInner
      `{AS: AbstractSyntax A}
      {DFv: DecideFv AS} (DFvS: ReflectFv DFv) :=
  subst_inner : forall {B : Type} x y,
    (ignore_second (B:=B) (subst_var x y))
    = (dec_apply (dec_notin_fv x) (ignore_second id) (ignore_second (subst_var x y))).
