Require Import List.

Require Import Nat.

Require Import Util.

From Corelib Require Import Init.Wf.

Require Import Wellfounded.Inverse_Image.

Require Import Section3_Requirements.

Import Relation_Operators.

Import List.

Import ListNotations.

Section Integrator.

Variable Lit : Type.

Notation T := (UIType Lit).

Variable DRule : Lit -> Lit -> Type.

Variable DPremise : forall (l r : Lit), DRule l r -> T -> T -> Prop.

Definition Intersect : list Lit -> T
  := fold_right (fun l => TIsect (TLit l)) TTop.

Fixpoint Integrate (intersect : list Lit -> T) (t : T) : T :=
    match t with
    | TBot => TBot
    | TTop => intersect []
    | TUni tl tr => TUni (Integrate intersect tl) (Integrate intersect tr)
    | TIsect tl tr => Integrate (fun l => Integrate (fun l' => intersect (l ++ l')) tr) tl
    | TLit l => intersect [l]
    end.

Fixpoint Integrated_int (intersected : list Lit -> Prop) (t : T) : Prop :=
    match t with
    | TBot => False
    | TTop => intersected []
    | TUni tl tr => False
    | TIsect tl tr => Integrated_int (fun l => Integrated_int (fun l' => intersected (l ++ l')) tr) tl
    | TLit l => intersected [l]
    end.

Fixpoint Integrated (intersected : list Lit -> Prop) (t : T) : Prop :=
    match t with
    | TBot => True
    | TTop => intersected []
    | TUni tl tr => (Integrated intersected tl) /\ (Integrated intersected tr)
    | TIsect tl tr => Integrated_int intersected (TIsect tl tr)
    | TLit l => intersected [l]
    end.

Fixpoint Exists_Intersection (P : list Lit -> Prop) (t : T) : Prop :=
    match t with
    | TBot => False
    | TTop => P []
    | TUni tl tr => (Exists_Intersection P tl) \/ (Exists_Intersection P tr)
    | TIsect tl tr => Integrated_int P (TIsect tl tr)
    | TLit l => P [l]
    end.

Inductive sig2T {A B : Type} {C : A -> B -> Type} : Type :=
    exist2T (a : A) (b : B) (c : C a b).

Arguments sig2T { A B }.

Definition proj2T1 {A B : Type} {C : A -> B -> Type} (s : sig2T C) : A :=
    match s with exist2T a _ _ => a end.

Definition proj2T2 {A B : Type} {C : A -> B -> Type} (s : sig2T C) : B :=
    match s with exist2T _ b _ => b end.

Definition proj2V {A B : Type} {C : A -> B -> Type} (v : sig2T C) : C (proj2T1 v) (proj2T2 v) :=
    match v as v0 return C (proj2T1 v0) (proj2T2 v0) with
    | exist2T _ _ c => c
    end.

Inductive dsubda {Assumed : T -> T -> Prop} : T -> T -> Prop :=
  | dsubda_refl : forall t : T, dsubda t t
  | dsubda_trans : forall tl tm tr : T, dsubda tl tm -> dsubda tm tr -> dsubda tl tr
  | dsubda_assume : forall tl tr : T, Assumed tl tr -> dsubda tl tr
  | dsubda_lit : forall {ll lr : Lit} (r : DRule ll lr), (forall ptl ptr : T, DPremise ll lr r ptl ptr -> dsubda ptl ptr) -> dsubda (TLit ll) (TLit lr)
  | dsubda_top : forall t : T, dsubda t TTop
  | dsubda_bot : forall t : T, dsubda TBot t
  | dsubda_uni_l : forall tl tr t : T, dsubda tl t -> dsubda tr t -> dsubda (TUni tl tr) t
  | dsubda_uni_rl : forall tl tr : T, dsubda tl (TUni tl tr)
  | dsubda_uni_rr : forall tl tr : T, dsubda tr (TUni tl tr)
  | dsubda_int_r : forall t tl tr : T, dsubda t tl -> dsubda t tr -> dsubda t (TIsect tl tr)
  | dsubda_int_ll : forall tl tr : T, dsubda (TIsect tl tr) tl
  | dsubda_int_lr : forall tl tr : T, dsubda (TIsect tl tr) tr
  | dsubda_dist : forall tl trl trr : T, dsubda (TIsect tl (TUni trl trr)) (TUni (TIsect tl trl) (TIsect tl trr))
  .

Arguments dsubda : clear implicits.

End Integrator.

Arguments Intersect {Lit}.

Arguments Integrate {Lit}.

Arguments Integrated_int {Lit}.

Arguments Integrated {Lit}.

Arguments Exists_Intersection {Lit}.

Arguments sig2T {A B}.

Arguments dsubda {Lit DRule}.

Arguments dsubda_refl {Lit DRule DPremise}.

Arguments dsubda_trans {Lit DRule DPremise}.

Arguments dsubda_assume {Lit DRule DPremise}.

Arguments dsubda_lit {Lit DRule DPremise}.

Arguments dsubda_top {Lit DRule DPremise}.

Arguments dsubda_bot {Lit DRule DPremise}.

Arguments dsubda_uni_l {Lit DRule DPremise}.

Arguments dsubda_uni_rl {Lit DRule DPremise}.

Arguments dsubda_uni_rr {Lit DRule DPremise}.

Arguments dsubda_int_r {Lit DRule DPremise}.

Arguments dsubda_int_ll {Lit DRule DPremise}.

Arguments dsubda_int_lr {Lit DRule DPremise}.

Arguments dsubda_dist {Lit DRule DPremise}.

Module Type Intersector (M_traditional : Traditional).

Import M_traditional.

Parameter extension : T -> T -> Prop.

Notation esub := (dsubda (@DPremise) extension).

Parameter intersect : list Lit -> T.

Parameter IntersectorCompleteness : forall tl tr : T, extension tl tr -> dsub (Integrate intersect tl) tr.

Parameter IntersectorSoundness : forall ls : list Lit, esub (Intersect ls) (intersect ls).

Parameter MeasurePreservation : forall tl tr : T, clos_refl_trans M mlt (m (Integrate intersect tl) tr) (m tl tr).

Parameter LiteralDereliction : forall ls : list Lit, rsub (intersect ls) (Intersect ls).

Parameter intersected : list Lit -> Prop.

Parameter IntersectorIntegrated : forall ls : list Lit, Integrated intersected (intersect ls).

Parameter LiteralPromotion : forall (ls ls' : list Lit) (rs : list (sig2T RRule)), Forall (fun l' : Lit => Exists (fun r : (sig2T RRule) => proj2T2 r = l') rs) ls' -> incl (map proj2T1 rs) ls -> intersected ls -> exists rs' : list (sig2T RRule), Exists_Intersection (fun ls'' => ls'' = map proj2T2 rs' /\ incl (map proj2T1 rs') ls /\ Forall (fun r' : sig2T RRule => forall tl tr :T, RPremise (proj2V r') tl tr -> rsubam (@RPremise) (fun tl' tr' => Exists (fun r => RPremise (proj2V r) tl' tr') rs) tl tr) rs') (intersect ls').

End Intersector.
