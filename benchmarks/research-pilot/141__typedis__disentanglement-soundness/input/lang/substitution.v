From Coq Require Import Wellfounded ssreflect.

From stdpp Require Import strings binders gmap gmultiset ssreflect.

From dislog.lang Require Import syntax.

Definition binder_set (x:binder) : gset string :=
  match x with
  | BAnon => ∅
  | BNamed x => {[x]}
  end.

Fixpoint subst (x:string) (v:val) (e:expr) : expr :=
  match e with
  | Val _ => e
  | Clo c => Clo (subst_clo x v c)
  | Var y =>
       if (decide (x=y)) then v else e
  | Call e ts =>
      Call (subst x v e) (subst x v <$> ts)
  | CallPrim p e1 e2 =>
      CallPrim p (subst x v e1) (subst x v e2)
  | If e1 e2 e3 =>
      If (subst x v e1) (subst x v e2) (subst x v e3)
  | Let y e1 e2 =>
      Let y (subst x v e1)
        (if (decide (y = BNamed x)) then e2 else subst x v e2)
  | Alloc e1 e2 =>
      Alloc (subst x v e1) (subst x v e2)
  | Load e1 e2 =>
      Load (subst x v e1) (subst x v e2)
  | Store e1 e2 e3 =>
      Store (subst x v e1) (subst x v e2) (subst x v e3)
  | Length e1 =>
      Length (subst x v e1)
  | Prod e1 e2 =>
      Prod (subst x v e1) (subst x v e2)
  | Fst e1 => Fst (subst x v e1)
  | Snd e1 => Snd (subst x v e1)
  | InL e1 => InL (subst x v e1)
  | InR e1 => InR (subst x v e1)
  | Case e1 x2 e2 x3 e3 =>
      Case (subst x v e1)
        x2 (if (decide ((BNamed x) = x2)) then e2 else subst x v e2)
        x3 (if (decide ((BNamed x) = x3)) then e3 else subst x v e3)
  | Par e1 e2 =>
      Par (subst x v e1) (subst x v e2)
  | RunPar e1 e2 =>
      RunPar (subst x v e1) (subst x v e2)
  | CAS e1 e2 e3 e4 =>
      CAS (subst x v e1) (subst x v e2) (subst x v e3) (subst x v e4)
  | Fold e1 => Fold (subst x v e1)
  | Unfold e1 => Unfold (subst x v e1)
  end
with subst_clo x v (c:function) :=
  match c with
  | Lam f ys e =>
      if (decide (x ∈ binder_set f ∪ ⋃ (binder_set <$> ys))) then c else Lam f ys (subst x v e) end.

Definition subst' (x:binder) (v:val) (e:expr) :=
  match x with
  | BAnon => e
  | BNamed x => subst x v e end.

Definition substs (xlvs : list (string * val)) (i : expr) : expr :=
  foldr (fun '(x, lv) => subst x lv) i xlvs.

Definition substs' (xlvs : list (binder * val)) (i : expr) : expr :=
  foldr (fun '(x, lv) => subst' x lv) i xlvs.

Fixpoint fv (e:expr) : gset string :=
  match e with
  | Val x => ∅
  | Clo x => fv_func x
  | Var x => {[x]}
  | Call x x1 => fv x ∪ ⋃ (fv <$> x1)
  | CallPrim x x0 x1 => fv x0 ∪ fv x1
  | If x x0 x1 => fv x ∪ fv x0 ∪ fv x1
  | Let x x0 x1 => fv x0 ∪ (fv x1 ∖ binder_set x)
  | Fst x | Snd x | InL x | InR x | Length x | Fold x | Unfold x => fv x
  | Case x x0 x1 x2 x3 => fv x ∪ (fv x1 ∖ binder_set x0) ∪ (fv x3 ∖ binder_set x2)
  | Prod x x0 | Alloc x x0 | Load x x0 | Par x x0 | RunPar x x0 => fv x ∪ fv x0
  | Store x x0 x1 => fv x ∪ fv x0 ∪ fv x1
  | CAS x x0 x1 x2 => fv x ∪ fv x0 ∪ fv x1 ∪ fv x2
  end
with fv_func (f:function) : gset string :=
  match f with
  | Lam x x3 x4 => fv x4 ∖ (binder_set x ∪ ⋃ (binder_set <$> x3))
  end.
