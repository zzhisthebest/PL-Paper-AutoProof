Set Implicit Arguments.

Require Import LibExtra.

Require Import SyntaxClassDefs SyntaxClassProperties.

Generalizable Variables A B.

Class ToList (B A : Set) :=
  to_list : A -> list B.

Arguments to_list _ _ _ !_ /.

Class OfList (B A : Set) :=
  of_list : list B -> A.

Arguments of_list _ _ _ !_ /.

Class ListLike {B A : Set} `(ToList B A) `(OfList B A) :=
  { to_list_of_list : forall x, (of_list (to_list x)) = x;
    of_list_to_list : forall l, (to_list (of_list l)) = l;
  }.

Bind Scope syntax_scope with ToList OfList.

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

Section ListOfSyntax.

Context {A: Set}.

Context {O: Openable A}.

Context {F: FreeVar A}.

Context {S: SubstVar A}.

Context {AS: AbstractSyntax O F S}.

Instance ListOpenable : Openable (list A) :=
    (fun n x => List.map (open_rec n x)).

Instance ListFreeVar : FreeVar (list A) :=
    (List.fold_right (fun a acc => union (fv a) acc) \{}).

Instance ListSubstVar : SubstVar (list A) :=
    (fun x y => List.map (subst_var x y)).

Instance ListSealable {FX: Sealable A} : Sealable (list A) :=
    (fun n x => List.map (seal_rec n x)).

Instance ListAbstractSyntax : AbstractSyntax ListOpenable ListFreeVar ListSubstVar := {}.

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

Definition ListClosing : Closing ListAbstractSyntax :=
      (fun n x => List.map (close_rec n x)).

Context {OC: OpenClose C}.

Context {CO: CloseOpen C}.

Context {SOC: SubstOpenClose C}.

Context {CS: CloseSubst C}.

Context {SCCo: SubstCloseCommut C}.

Context {CCo: CloseCommut C}.

Context {OCCo: OpenCloseCommut C}.

Context {CU: CloseUnbound C}.

End Closing.

End ListOfSyntax.
