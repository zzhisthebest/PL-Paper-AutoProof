Require Export fintype.

Inductive valtype  : Type :=
  | zero : valtype
  | one : valtype
  | U : comptype  -> valtype
  | Sigma : valtype  -> valtype  -> valtype
  | cross : valtype  -> valtype  -> valtype
 with comptype  : Type :=
  | cone : comptype
  | F : valtype  -> comptype
  | Pi : comptype  -> comptype  -> comptype
  | arrow : valtype  -> comptype  -> comptype .

Inductive value (nvalue : nat) : Type :=
  | var_value : fin (nvalue) -> value (nvalue)
  | u : value (nvalue)
  | pair : value (nvalue) -> value (nvalue) -> value (nvalue)
  | inj : bool  -> value (nvalue) -> value (nvalue)
  | thunk : comp (nvalue) -> value (nvalue)
 with comp (nvalue : nat) : Type :=
  | cu : comp (nvalue)
  | force : value (nvalue) -> comp (nvalue)
  | lambda : comp (S nvalue) -> comp (nvalue)
  | app : comp (nvalue) -> value (nvalue) -> comp (nvalue)
  | tuple : comp (nvalue) -> comp (nvalue) -> comp (nvalue)
  | ret : value (nvalue) -> comp (nvalue)
  | letin : comp (nvalue) -> comp (S nvalue) -> comp (nvalue)
  | proj : bool  -> comp (nvalue) -> comp (nvalue)
  | caseZ : value (nvalue) -> comp (nvalue)
  | caseS : value (nvalue) -> comp (S nvalue) -> comp (S nvalue) -> comp (nvalue)
  | caseP : value (nvalue) -> comp (S (S nvalue)) -> comp (nvalue).

Definition upRen_value_value { m : nat } { n : nat } (xi : fin (m) -> fin (n)) : _ :=
  up_ren xi.

Fixpoint ren_value { mvalue : nat } { nvalue : nat } (xivalue : fin (mvalue) -> fin (nvalue)) (s : value (mvalue)) : _ :=
    match s with
    | var_value (_) s => (var_value (nvalue)) (xivalue s)
    | u (_)  => u (nvalue)
    | pair (_) s0 s1 => pair (nvalue) (ren_value xivalue s0) (ren_value xivalue s1)
    | inj (_) s0 s1 => inj (nvalue) s0 (ren_value xivalue s1)
    | thunk (_) s0 => thunk (nvalue) (ren_comp xivalue s0)
    end
 with ren_comp { mvalue : nat } { nvalue : nat } (xivalue : fin (mvalue) -> fin (nvalue)) (s : comp (mvalue)) : _ :=
    match s with
    | cu (_)  => cu (nvalue)
    | force (_) s0 => force (nvalue) (ren_value xivalue s0)
    | lambda (_) s0 => lambda (nvalue) (ren_comp (upRen_value_value xivalue) s0)
    | app (_) s0 s1 => app (nvalue) (ren_comp xivalue s0) (ren_value xivalue s1)
    | tuple (_) s0 s1 => tuple (nvalue) (ren_comp xivalue s0) (ren_comp xivalue s1)
    | ret (_) s0 => ret (nvalue) (ren_value xivalue s0)
    | letin (_) s0 s1 => letin (nvalue) (ren_comp xivalue s0) (ren_comp (upRen_value_value xivalue) s1)
    | proj (_) s0 s1 => proj (nvalue) s0 (ren_comp xivalue s1)
    | caseZ (_) s0 => caseZ (nvalue) (ren_value xivalue s0)
    | caseS (_) s0 s1 s2 => caseS (nvalue) (ren_value xivalue s0) (ren_comp (upRen_value_value xivalue) s1) (ren_comp (upRen_value_value xivalue) s2)
    | caseP (_) s0 s1 => caseP (nvalue) (ren_value xivalue s0) (ren_comp (upRen_value_value (upRen_value_value xivalue)) s1)
    end.

Definition up_value_value { m : nat } { nvalue : nat } (sigma : fin (m) -> value (nvalue)) : _ :=
  scons ((var_value (S nvalue)) var_zero) (funcomp (ren_value shift) sigma).

Fixpoint subst_value { mvalue : nat } { nvalue : nat } (sigmavalue : fin (mvalue) -> value (nvalue)) (s : value (mvalue)) : _ :=
    match s with
    | var_value (_) s => sigmavalue s
    | u (_)  => u (nvalue)
    | pair (_) s0 s1 => pair (nvalue) (subst_value sigmavalue s0) (subst_value sigmavalue s1)
    | inj (_) s0 s1 => inj (nvalue) s0 (subst_value sigmavalue s1)
    | thunk (_) s0 => thunk (nvalue) (subst_comp sigmavalue s0)
    end
 with subst_comp { mvalue : nat } { nvalue : nat } (sigmavalue : fin (mvalue) -> value (nvalue)) (s : comp (mvalue)) : _ :=
    match s with
    | cu (_)  => cu (nvalue)
    | force (_) s0 => force (nvalue) (subst_value sigmavalue s0)
    | lambda (_) s0 => lambda (nvalue) (subst_comp (up_value_value sigmavalue) s0)
    | app (_) s0 s1 => app (nvalue) (subst_comp sigmavalue s0) (subst_value sigmavalue s1)
    | tuple (_) s0 s1 => tuple (nvalue) (subst_comp sigmavalue s0) (subst_comp sigmavalue s1)
    | ret (_) s0 => ret (nvalue) (subst_value sigmavalue s0)
    | letin (_) s0 s1 => letin (nvalue) (subst_comp sigmavalue s0) (subst_comp (up_value_value sigmavalue) s1)
    | proj (_) s0 s1 => proj (nvalue) s0 (subst_comp sigmavalue s1)
    | caseZ (_) s0 => caseZ (nvalue) (subst_value sigmavalue s0)
    | caseS (_) s0 s1 s2 => caseS (nvalue) (subst_value sigmavalue s0) (subst_comp (up_value_value sigmavalue) s1) (subst_comp (up_value_value sigmavalue) s2)
    | caseP (_) s0 s1 => caseP (nvalue) (subst_value sigmavalue s0) (subst_comp (up_value_value (up_value_value sigmavalue)) s1)
    end.

Arguments var_value {nvalue}.

Arguments u {nvalue}.

Arguments pair {nvalue}.

Arguments inj {nvalue}.

Arguments thunk {nvalue}.

Arguments cu {nvalue}.

Arguments force {nvalue}.

Arguments lambda {nvalue}.

Arguments app {nvalue}.

Arguments tuple {nvalue}.

Arguments ret {nvalue}.

Arguments letin {nvalue}.

Arguments proj {nvalue}.

Arguments caseZ {nvalue}.

Arguments caseS {nvalue}.

Arguments caseP {nvalue}.

Instance Subst_value : Subst1 value value := @subst_value .

Instance Subst_comp : Subst1 value comp := @subst_comp .

Instance Ren_value : Ren1 value := @ren_value .

Instance Ren_comp : Ren1 comp := @ren_comp .

Instance VarInstance_value : Var value := @var_value .

Notation "x '__value'" := (@ids value VarInstance_value (_) x) (at level 30, format "x __value") : subst_scope.

Notation "⇑__value" := (@up_value_value (_)) (only printing) : subst_scope.
