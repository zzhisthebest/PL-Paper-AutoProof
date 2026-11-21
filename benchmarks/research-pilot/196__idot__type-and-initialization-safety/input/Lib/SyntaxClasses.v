Set Implicit Arguments.

Require Import Coq.Bool.Bool.

Require Import Stdlib.Init.Sumbool.

Require Import LibExtra.

Generalizable Variables A B.

Declare Scope syntax_scope.

Delimit Scope syntax_scope with S.

Open Scope syntax_scope.

Class Openable (A : Type) := open_rec : nat -> var -> A -> A.

Class FreeVar (A : Type) := fv : A -> vars.

Class SubstVar (A : Type) := subst_var : var -> var -> A -> A.

Bind Scope syntax_scope with Openable FreeVar SubstVar.

Arguments open_rec _ _ _ _ !_ /.

Arguments fv _ _ !_ /.

Arguments subst_var _ _ _ _ !_ /.

Class AbstractSyntax (A : Type) `(Openable A) `(FreeVar A) `(SubstVar A).

Notation "z '/[' x '->' y ']'"
  := (subst_var x y z) (x at level 69, at level 70) : syntax_scope.

Notation subst_vars := (vars_zip_map subst_var).

Notation "z '/[' xs '-->' ys ']'"
  := (subst_vars xs ys z) (xs at level 69, at level 70) : syntax_scope.

Notation open := (open_rec 0).

Definition open_depth_rec `{AS : Openable A} n x a d
  := open_rec (n + d) x a.

Notation open_depth := (open_depth_rec 0).

Arguments open_depth_rec _ _ _ _ !_ _ /.

Definition closed `{AS: Openable A} a
  := forall n x, open_rec n x a = a.

Fixpoint open_rec_vars `{AS : Openable A} (k: nat) (ys: list var) (X: A): A :=
  match ys with
  | nil => X
  | cons y ys => open_rec_vars (S k) ys (open_rec k y X)
  end.

Notation open_vars := (open_rec_vars 0).

Arguments open_rec_vars _ _ _ !_ _ /.

Class DecideFv `(AS: AbstractSyntax A) := dec_fv : var -> A -> bool.

Arguments dec_fv _ _ _ _ _ _ _ !_ /.

Definition dec_notin_fv `{DFv: DecideFv A} x a := negb (dec_fv x a).

Arguments dec_notin_fv _ _ _ _ _ _ _ !_ /.

Class ReflectFv `(DFv: DecideFv A) :=
  reflect_fv : forall x a,
    (x \in fv a) <-> (dec_fv x a) = true.

Class Closing `(AS: AbstractSyntax A) :=
  close_rec : nat -> var -> A -> A.

Bind Scope syntax_scope with Closing.

Notation close := (close_rec 0).

Arguments close_rec _ _ _ _ _ _ _ _ !_ /.

Definition close_depth_rec `{Cl : Closing A} n x a d
  := close_rec (n + d) x a.

Notation close_depth := (close_depth_rec 0).

Arguments close_depth_rec _ _ _ _ _ _ _ _ !_ /.

Parameter typ_label: Set.

Parameter trm_label: Set.

Inductive label: Set :=
| label_typ: typ_label -> label
| label_trm: trm_label -> label.

Class LabelOf (A : Type) := label_of : A -> label.

Arguments label_of _ _ !_ /.

Class GetLabeled (B A : Type) `(LabelOf B) :=
  get_labeld : label -> A -> option B.

Arguments get_labeld _ _ _ _ _ !_ /.

Definition labels_has `{GetLabeled B A} (ds: A) (d: B) :=
  get_labeld (label_of d) ds = Some d.

Definition labels_hasnt `{GetLabeled B A} (ds: A) (l: label) :=
  get_labeld l ds = None.

Class SubstLabel `(SubstVar A) `(LabelOf A) :=
  subst_label: forall x y d,
    label_of (subst_var x y d) = label_of d.

Class OpenTwice `(AS: Openable A) :=
  open_twice : forall n x y,
    (open_rec n y) ∘ (open_rec n x) = (open_rec n x).

Class OpenCommut `(AS: Openable A) :=
    open_commut : forall m n x y,
        m <> n ->
        (open_rec m x) ∘ (open_rec n y) = (open_rec n y) ∘ (open_rec m x).

Class SubstFresh `(AS : AbstractSyntax A) :=
  subst_fresh : forall x y X,
    x \notin fv X -> subst_var x y X = X.

Class SubstOpenCommut `(AS : AbstractSyntax A) :=
  subst_open_commut : forall x y z X n,
    subst_var x y (open_rec n z X)
    = open_rec n (z \[x -> y]) (subst_var x y X).

Class FvOpenCases `(AS : AbstractSyntax A) :=
  fv_open_cases : forall x a n,
    fv (open_rec n x a) = fv a \/
    fv (open_rec n x a) = \{ x} \u fv a.

Class OpenClose `(Cl: Closing A) :=
  open_close : forall n x,
    (open_rec n x) ∘ (close_rec n x) = open_rec n x.

Class CloseOpen `(Cl: Closing A) :=
  close_open : forall n x,
    (close_rec n x) ∘ (open_rec n x) = close_rec n x.

Class SubstOpenClose `(Cl: Closing A) :=
  subst_open_close : forall n x y,
    (subst_var x y) ∘ (open_rec n x) = (open_rec n y) ∘ (close_rec n x).

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

Class ToList (B A : Type) :=
  to_list : A -> list B.

Arguments to_list _ _ _ !_ /.

Class OfList (B A : Type) :=
  of_list : list B -> A.

Arguments of_list _ _ _ !_ /.

Class ListLike {B A : Type} `(ToList B A) `(OfList B A) :=
  { to_list_of_list : forall x, (of_list (to_list x)) = x;
    of_list_to_list : forall l, (to_list (of_list l)) = l;
  }.

Bind Scope syntax_scope with ToList OfList.

Notation fv_env := (fv_in_values fv).

Notation subst_env x y := (map (subst_var x y)).

Notation subst_env_vars xs ys := (map (subst_vars xs ys)).

Instance VarsSubstVar : SubstVar vars :=
  fun (x: var) (y: var) (vs: vars) =>
    If x \in vs then (vs \- \{x}) \u \{y} else vs.

Section Open_depth.

Context `{AS: AbstractSyntax A}.

End Open_depth.

Section Subst_depth.

Context `{AS: AbstractSyntax A}.

End Subst_depth.

Section Close_depth.

Context `{AS: AbstractSyntax A} {Cl: Closing AS}.

End Close_depth.

Section Fv_env.

Context `{AS: AbstractSyntax A}.

End Fv_env.

Section Subst_env.

Context `{AS: AbstractSyntax A}.

End Subst_env.

Section About_OpenTwice.

Context `{OpenTwice}.

End About_OpenTwice.

Section About_OpenCommut.

Context `{OpenCommut}.

End About_OpenCommut.

Section About_SubstFresh.

Context `{SubstFresh A}.

End About_SubstFresh.

Section About_SubstOpenCommut.

Context `{SubstOpenCommut}.

End About_SubstOpenCommut.

Section About_FvOpenCases.

Context `{FvOpenCases}.

End About_FvOpenCases.

Section About_ClosingSanity.

Section OpenClose.

Context `{OpenClose}.

End OpenClose.

Section CloseOpen.

Context `{CloseOpen}.

End CloseOpen.

Section SubstOpenClose.

Context `{SubstOpenClose}.

End SubstOpenClose.

End About_ClosingSanity.

Section About_ListLike.

Context `{ListLike B A}.

Definition app_s xs ys := of_list ((to_list xs) ++ (to_list ys)).

Infix "++" := app_s (right associativity, at level 60).

Definition map_f f x := of_list (List.map f (to_list x)).

Definition length_s xs := length (to_list xs).

End About_ListLike.

Infix "++" := app_s (right associativity, at level 60) : syntax_scope.

Arguments app_s _ _ _ _ _ !_ /.

Arguments length_s _ _ _ !_ /.

Arguments map_f _ _ _ _ _ !_ /.

Section About_CloseUnbound.

Context `{AS: AbstractSyntax A}.

Context {C: Closing AS}.

Context {CU: CloseUnbound C}.

Context {CO: CloseOpen C}.

Context {SOC: SubstOpenClose C}.

End About_CloseUnbound.

Section ListOfSyntax.

Context {A: Type}.

Section GetLabeled.

Context {L: LabelOf A}.

Fixpoint get_labeld_list (l: label) (ds: list A): option A :=
      match ds with
      | nil => None
      | cons d ds =>
        If label_of d = l then Some d else get_labeld_list l ds
    end.

Instance ListGetLabeled : GetLabeled (list A) L :=
      get_labeld_list.

End GetLabeled.

Context {O: Openable A}.

Context {F: FreeVar A}.

Context {S: SubstVar A}.

Context {AS: AbstractSyntax O F S}.

Definition open_rec_list : Openable (list A) :=
    (fun n x => List.map (open_rec n x)).

Definition fv_list : FreeVar (list A) :=
    (List.fold_right (fun a acc => union (fv a) acc) \{}).

Definition subst_var_list : SubstVar (list A) :=
    (fun x y => List.map (subst_var x y)).

Arguments open_rec_list /.

Arguments fv_list /.

Arguments subst_var_list /.

Instance ListOpenable : Openable (list A) := open_rec_list.

Instance ListFreeVar : FreeVar (list A) := fv_list.

Instance ListSubstVar : SubstVar (list A) := subst_var_list.

Instance ListAbstractSyntax : AbstractSyntax ListOpenable ListFreeVar ListSubstVar := {}.

Section LabelHasnt.

Context {L: LabelOf A}.

Context {SL: SubstLabel S L}.

Existing Instance ListGetLabeled.

End LabelHasnt.

Section OpenCompose.

Context {OT: OpenTwice O}.

Context {OC: OpenCommut O}.

End OpenCompose.

Section SubstFresh.

Context {SF: SubstFresh AS}.

End SubstFresh.

Section SubstOpenCommut.

Context {SF: SubstOpenCommut AS}.

End SubstOpenCommut.

Section FvOpenCases.

Context {FOC: FvOpenCases AS}.

End FvOpenCases.

Section Closing.

Context {C: Closing AS}.

Instance ListClosing : Closing ListAbstractSyntax :=
      (fun n x => List.map (close_rec n x)).

Context {OC: OpenClose C}.

Context {CO: CloseOpen C}.

Context {SOC: SubstOpenClose C}.

Context {CU: CloseUnbound C}.

End Closing.

End ListOfSyntax.

Arguments ListOpenable _ _ _ /.

Arguments ListFreeVar _ _ _ /.

Arguments ListSubstVar _ _ _ /.

Existing Instance ListGetLabeled | 1.

Existing Instance ListOpenable | 1.

Existing Instance ListFreeVar | 1.

Existing Instance ListSubstVar | 1.

Existing Instance ListAbstractSyntax | 1.

Existing Instance ListClosing | 1.
