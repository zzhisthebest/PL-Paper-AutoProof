Set Implicit Arguments.

Require Import LibExtra SyntaxClasses.

Require Import AbstractSyntax Defs GeneralTyping Equivalence Indep.

Fixpoint deref_base A (su: SubstVar A) (e: renv) (X: A): A :=
  match e with
  | nil => X
  | cons (w,y) ys => (deref_base su ys (subst_var w y X))
  end.

Class Deref A :=
  deref (e: renv) (a: A): A.

Instance deref_var: Deref var := deref_base VarSubstVar.

Instance deref_avar: Deref avar := deref_base AvarSubstVar.

Instance deref_def: Deref def :=
fun e d => match d with
| def_fld l x => def_fld l (deref e x)
| def_met l t => def_met l t
| def_typ l T => def_typ l T
end.

Fixpoint deref_defs_fix(e: renv)(ds: defs) :=
match ds with
| defs_nil => defs_nil
| defs_cons ds d => defs_cons (deref_defs_fix e ds) (deref_def e d)
end.

Instance deref_defs: Deref defs := deref_defs_fix.

Class DerefInFv (A: Set) (AD: Deref A) (AF: FreeVar A):=
  deref_in_fv x e (d: A):
    x \in fv (deref e d) ->
    x \in fv d \/ x \in fv_env e.
