From Stdlib Require Import List.

From Autosubst Require Export Autosubst.

Set Implicit Arguments.

Inductive level := Prp | Typ.

Inductive termL : Type :=
| VarL (x : var)
| ProdL (a : termL) (b : {bind termL})
| AppL (a b : termL)
| LamL (a : termL) (b : {bind termL})
| SortL (u : level).

#[export] Instance Ids_termL : Ids termL := VarL.

Fixpoint rename_termL (xi : var -> var) (t : termL) : termL :=
  match t with
  | VarL x => VarL (xi x)
  | ProdL a b => ProdL (rename_termL xi a) (rename_termL (upren xi) b)
  | AppL a b => AppL (rename_termL xi a) (rename_termL xi b)
  | LamL a b => LamL (rename_termL xi a) (rename_termL (upren xi) b)
  | SortL s => SortL s
  end.

#[export] Instance Rename_termL : Rename termL := rename_termL.

Fixpoint subst_termL (sigma : var -> termL) (t : termL) : termL :=
  match t with
  | VarL x => sigma x
  | ProdL a b => ProdL (subst_termL sigma a) (subst_termL (up sigma) b)
  | AppL a b => AppL (subst_termL sigma a) (subst_termL sigma b)
  | LamL a b => LamL (subst_termL sigma a) (subst_termL (up sigma) b)
  | SortL s => SortL s
  end.

#[export] Instance Subst_termL : Subst termL := subst_termL.

Inductive atnd : list termL -> var -> termL -> Prop :=
  | Atnd0 Delta A A' :
      A' = A.[ren(+1)] -> atnd (A :: Delta) 0 A'
  | AtndS Delta x A B B' :
      atnd Delta x B -> B' = B.[ren(+1)] -> atnd (A :: Delta) (S x) B'.

Inductive typingL (Gamma : list termL) : termL -> termL -> Prop :=
| typingL_ax :
    typingL Gamma (SortL Prp) (SortL Typ)
| typingL_var x a u :
    atnd Gamma x a -> typingL Gamma a (SortL u) ->
    typingL Gamma (VarL x) a
| typingL_prod a b u :
    typingL Gamma a (SortL u) -> typingL (a :: Gamma) b (SortL Prp) ->
    typingL Gamma (ProdL a b) (SortL Prp)
| typingL_app a b c d d' :
    typingL Gamma a (ProdL c d) -> typingL Gamma b c -> d' = d.[b/] ->
    typingL Gamma (AppL a b) d'
| typingL_lam a b c u :
    typingL Gamma a (SortL u) ->
    typingL (a :: Gamma) c (SortL Prp) ->
    typingL (a :: Gamma) b c ->
    typingL Gamma (LamL a b) (ProdL a c).

Inductive typeF : Type :=
| TyVarF (x : var)
| ImpF (A B : typeF)
| AllF (A : {bind typeF}).

Inductive termF : Type :=
| TmVarF (x : var)
| AppF (s t : termF)
| LamF (A : typeF) (s : {bind termF})
| TySpecF (s : termF) (A : typeF)
| TyAbsF (s : {bind typeF in termF}).

#[export] Instance Ids_typeF : Ids typeF := TyVarF.

Fixpoint rename_typeF (xi : var -> var) (T : typeF) : typeF :=
  match T with
  | TyVarF x => TyVarF (xi x)
  | ImpF A B => ImpF (rename_typeF xi A) (rename_typeF xi B)
  | AllF A => AllF (rename_typeF (upren xi) A)
  end.

#[export] Instance Rename_typeF : Rename typeF := rename_typeF.

Fixpoint subst_typeF (replacement : var -> typeF) (T : typeF) : typeF :=
  match T with
  | TyVarF x => replacement x
  | ImpF A B => ImpF (subst_typeF replacement A) (subst_typeF replacement B)
  | AllF A => AllF (subst_typeF (up replacement) A)
  end.

#[export] Instance Subst_typeF : Subst typeF := subst_typeF.

Inductive atn : list typeF -> var -> typeF -> Prop :=
| Atn0 Delta A : atn (A :: Delta) 0 A
| AtnS Delta x A B :
    atn Delta x B -> atn (A :: Delta) (S x) B.

Inductive istyF (N : nat) : typeF -> Prop :=
| istyF_var x : x < N -> istyF N (TyVarF x)
| istyF_imp A B : istyF N A -> istyF N B -> istyF N (ImpF A B)
| istyF_all A : istyF (1 + N) A -> istyF N (AllF A).

Inductive typingF (N : nat) (Gamma : list typeF) : termF -> typeF -> Prop :=
| typingF_var x A :
    atn Gamma x A -> istyF N A ->
    typingF N Gamma (TmVarF x) A
| typingF_app s t A B :
    typingF N Gamma s (ImpF A B) -> typingF N Gamma t A ->
    typingF N Gamma (AppF s t) B
| typingF_lam s A B :
    istyF N A -> typingF N (A :: Gamma) s B ->
    typingF N Gamma (LamF A s) (ImpF A B)
| typingF_tyspec s A A' B :
    istyF N B -> typingF N Gamma s (AllF A) -> A' = A.[B/] ->
    typingF N Gamma (TySpecF s B) A'
| typingF_tyabs s A :
    typingF (1 + N) Gamma..[ren (+1)] s A ->
    typingF N Gamma (TyAbsF s) (AllF A).

Definition vrel := list (var * var).

Definition vr (R : vrel) (x y : var) : Prop := In (x, y) R.

Definition vrm (R : vrel) (xi zeta : var -> var) : vrel :=
  map (fun p => (xi (fst p), zeta (snd p))) R.

Inductive tyrel (R : vrel) : typeF -> termL -> Prop :=
| tyrel_var x y : vr R x y -> tyrel R (TyVarF x) (VarL y)
| tyrel_imp A B a b :
    tyrel R A a -> tyrel (vrm R id (+1)) B b -> tyrel R (ImpF A B) (ProdL a b)
| tyrel_all A a :
    tyrel ((0, 0) :: vrm R (+1) (+1)) A a -> tyrel R (AllF A) (ProdL (SortL Prp) a).

Inductive tmrel (Rty Rtm : vrel) : termF -> termL -> Prop :=
| tmrel_var x y : vr Rtm x y -> tmrel Rty Rtm (TmVarF x) (VarL y)
| tmrel_app s t a b :
    tmrel Rty Rtm s a -> tmrel Rty Rtm t b -> tmrel Rty Rtm (AppF s t) (AppL a b)
| tmrel_lam A s a b :
    tyrel Rty A a ->
    tmrel (vrm Rty id (+1)) ((0, 0) :: vrm Rtm (+1) (+1)) s b ->
    tmrel Rty Rtm (LamF A s) (LamL a b)
| tmrel_tyspec s A a b :
    tmrel Rty Rtm s a -> tyrel Rty A b ->
    tmrel Rty Rtm (TySpecF s A) (AppL a b)
| tmrel_tyabs s a :
    tmrel ((0, 0) :: vrm Rty (+1) (+1)) (vrm Rtm id (+1)) s a ->
    tmrel Rty Rtm (TyAbsF s) (LamL (SortL Prp) a).

Theorem system_f_type_to_lambda2 : forall A,
  istyF 0 A <->
  exists! a, tyrel nil A a /\ typingL nil a (SortL Prp).

Theorem system_f_term_to_lambda2 : forall s A,
  typingF 0 nil s A <->
  exists! ab : termL * termL,
    tmrel nil nil s (fst ab) /\ tyrel nil A (snd ab) /\
    typingL nil (fst ab) (snd ab) /\ typingL nil (snd ab) (SortL Prp).

Theorem lambda2_type_to_system_f : forall a,
  typingL nil a (SortL Prp) <->
  exists! A, tyrel nil A a /\ istyF 0 A.

Theorem lambda2_term_to_system_f : forall a b,
  (typingL nil a b /\ typingL nil b (SortL Prp)) <->
  exists! sA : termF * typeF,
    tmrel nil nil (fst sA) a /\ tyrel nil (snd sA) b /\
    typingF 0 nil (fst sA) (snd sA).
