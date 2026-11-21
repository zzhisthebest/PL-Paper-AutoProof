Set Implicit Arguments.

Require Import LibExtra AbstractSyntax.

Notation effect := (var * trm_label)%type.

Notation effects := (list effect).

Notation eff_ctx := (env effects).

Fixpoint def_eff (x : var) (ds : defs) : (list effect) :=
  match ds with
  | nil => nil
  | (def_typ _ _) :: ds => def_eff x ds
  | (def_trm l) :: ds => (x,l) :: (def_eff x ds)
  end%list.

Reserved Notation "'⊢e' t '∶' eff"
         (at level 40, t at level 59).

Inductive eff_trm :
  trm -> effects -> Prop :=

| eff_ignore : forall t,
    ⊢e t ∶ nil

| eff_fld_asn : forall x a y,
    ⊢e trm_asn (avar_f x) a (avar_f y) ∶ ((x,a) :: nil)

| eff_let : forall L T t u eff1 eff2,
    ⊢e t ∶ eff1 ->
    (forall x, x \notin L -> ⊢e open x u ∶ eff2) ->
    ⊢e trm_let T t u ∶ (eff1 ++ eff2)

| eff_llit : forall L T l u eff,
    (forall x, x \notin L -> ⊢e open x u ∶ eff) ->
    ⊢e trm_lit T l u ∶ eff

where "'⊢e' t '∶' eff" := (eff_trm t eff).

Definition has_effs t effs := exists effs',
    ⊢e t ∶ effs' /\ from_list effs = from_list effs'.
