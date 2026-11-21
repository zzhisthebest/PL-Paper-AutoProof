Require Import List.

Require Import Nat.

Require Import Util.

From Corelib Require Import Init.Wf.

From Stdlib Require Import PeanoNat.

Require Import Wellfounded.Transitive_Closure.

Require Import Wellfounded.Inverse_Image.

Require Import Relation_Definitions.

Import Relation_Operators.

Import List.

Import ListNotations.

Inductive UIType {Lit : Type} : Type :=
| TTop : UIType
| TBot : UIType
| TUni (l r : UIType) : UIType
| TIsect (l r : UIType) : UIType
| TLit (l : Lit) : UIType
.

Arguments UIType : clear implicits.

Section DSub.

Variable Lit : Type.

Notation T := (UIType Lit).

Variable DRule : Lit -> Lit -> Type.

Variable DPremise : forall (l r : Lit), DRule l r -> T -> T -> Prop.

Inductive dsuba {Assumed : T -> T -> Prop} : T -> T -> Prop :=
| dsuba_refl : forall t : T, dsuba t t
| dsuba_trans : forall tl tm tr : T, dsuba tl tm -> dsuba tm tr -> dsuba tl tr
| dsuba_assume : forall tl tr : T, Assumed tl tr -> dsuba tl tr
| dsuba_lit : forall {ll lr : Lit} (r : DRule ll lr), (forall ptl ptr : T, DPremise ll lr r ptl ptr -> dsuba ptl ptr) -> dsuba (TLit ll) (TLit lr)
| dsuba_top : forall t : T, dsuba t TTop
| dsuba_bot : forall t : T, dsuba TBot t
| dsuba_uni_l : forall tl tr t : T, dsuba tl t -> dsuba tr t -> dsuba (TUni tl tr) t
| dsuba_uni_rl : forall tl tr : T, dsuba tl (TUni tl tr)
| dsuba_uni_rr : forall tl tr : T, dsuba tr (TUni tl tr)
| dsuba_int_r : forall t tl tr : T, dsuba t tl -> dsuba t tr -> dsuba t (TIsect tl tr)
| dsuba_int_ll : forall tl tr : T, dsuba (TIsect tl tr) tl
| dsuba_int_lr : forall tl tr : T, dsuba (TIsect tl tr) tr
.

Arguments dsuba : clear implicits.

Definition dsubf : T -> T -> Prop :=
  dsuba (fun _ _ => False).

End DSub.

Arguments dsuba {Lit DRule}.

Arguments dsuba_refl {Lit DRule DPremise}.

Arguments dsuba_trans {Lit DRule DPremise}.

Arguments dsuba_assume {Lit DRule DPremise}.

Arguments dsuba_lit {Lit DRule DPremise}.

Arguments dsuba_top {Lit DRule DPremise}.

Arguments dsuba_bot {Lit DRule DPremise}.

Arguments dsuba_uni_l {Lit DRule DPremise}.

Arguments dsuba_uni_rl {Lit DRule DPremise}.

Arguments dsuba_uni_rr {Lit DRule DPremise}.

Arguments dsuba_int_r {Lit DRule DPremise}.

Arguments dsuba_int_ll {Lit DRule DPremise}.

Arguments dsuba_int_lr {Lit DRule DPremise}.

Arguments dsubf {Lit DRule}.

Section RSub.

Variable Lit : Type.

Notation T := (UIType Lit).

Variable RRule : Lit -> Lit -> Type.

Variable RPremise : forall (l r : Lit), RRule l r -> T -> T -> Prop.

Inductive uisub {R : Lit -> Lit -> Prop} : T -> T -> Prop :=
| ui_lit (ll lr : Lit) : R ll lr -> uisub (TLit ll) (TLit lr)
| ui_top (tl : T) : uisub tl TTop
| ui_int_ll (il ir tr : T) : uisub il tr -> uisub (TIsect il ir) tr
| ui_int_lr (il ir tr : T) : uisub ir tr -> uisub (TIsect il ir) tr
| ui_int_r (tl il ir : T) : uisub tl il -> uisub tl ir -> uisub tl (TIsect il ir)
| ui_bot (tr : T) : uisub TBot tr
| ui_uni_rl (tl ul ur : T) : uisub tl ul -> uisub tl (TUni ul ur)
| ui_uni_rr (tl ul ur : T) : uisub tl ur -> uisub tl (TUni ul ur)
| ui_uni_l (ul ur tr : T) : uisub ul tr -> uisub ur tr -> uisub (TUni ul ur) tr
.

Arguments uisub : clear implicits.

Inductive lsub (R : T -> T -> Prop) (ll lr : Lit) : Prop :=
| Lsub (r : RRule ll lr) : (forall tl tr : T, RPremise ll lr r tl tr -> R tl tr) -> lsub R ll lr
.

Inductive rsubf : T -> T -> Prop :=
| Rsubf (tl tr : T) : uisub (lsub (rsubf)) tl tr -> rsubf tl tr
.

Inductive rsubam {Assumed : T -> T -> Prop} : T -> T -> Prop :=
| ram_assumption (tl tr : T) : Assumed tl tr -> rsubam tl tr
| ram_mono (tl tl' tr' tr : T) : rsubf tl tl' -> rsubam tl' tr' -> rsubf tr' tr -> rsubam tl tr
| ram_lit (ll lr : Lit) (r : RRule ll lr) : (forall pl pr : T, RPremise ll lr r pl pr -> rsubam pl pr) -> rsubam (TLit ll) (TLit lr)
| ram_top (tl : T) : rsubam tl TTop
| ram_int_ll (il ir tr : T) : rsubam il tr -> rsubam (TIsect il ir) tr
| ram_int_lr (il ir tr : T) : rsubam ir tr -> rsubam (TIsect il ir) tr
| ram_int_r (tl il ir : T) : rsubam tl il -> rsubam tl ir -> rsubam tl (TIsect il ir)
| ram_bot (tr : T) : rsubam TBot tr
| ram_uni_rl (tl ul ur : T) : rsubam tl ul -> rsubam tl (TUni ul ur)
| ram_uni_rr (tl ul ur : T) : rsubam tl ur -> rsubam tl (TUni ul ur)
| ram_uni_l (ul ur tr : T) : rsubam ul tr -> rsubam ur tr -> rsubam (TUni ul ur) tr
.

Arguments rsubam : clear implicits.

End RSub.

Arguments uisub { Lit }.

Arguments ui_lit {Lit R}.

Arguments ui_top {Lit R}.

Arguments ui_int_ll {Lit R}.

Arguments ui_int_lr {Lit R}.

Arguments ui_int_r {Lit R}.

Arguments ui_bot {Lit R}.

Arguments ui_uni_l {Lit R}.

Arguments ui_uni_rl {Lit R}.

Arguments ui_uni_rr {Lit R}.

Arguments lsub {Lit RRule}.

Arguments Lsub {Lit RRule}.

Arguments rsubf {Lit RRule}.

Arguments rsubam {Lit RRule}.

Arguments ram_assumption {Lit RRule RPremise Assumed}.

Arguments ram_mono {Lit RRule RPremise Assumed}.

Arguments ram_lit {Lit RRule RPremise Assumed}.

Arguments ram_top {Lit RRule RPremise Assumed}.

Arguments ram_int_ll {Lit RRule RPremise Assumed}.

Arguments ram_int_lr {Lit RRule RPremise Assumed}.

Arguments ram_int_r {Lit RRule RPremise Assumed}.

Arguments ram_bot {Lit RRule RPremise Assumed}.

Arguments ram_uni_l {Lit RRule RPremise Assumed}.

Arguments ram_uni_rl {Lit RRule RPremise Assumed}.

Arguments ram_uni_rr {Lit RRule RPremise Assumed}.

Inductive subui {Lit : Type} : UIType Lit -> UIType Lit -> Prop :=
| sub_uni_l : forall (t tr : UIType Lit) , subui t (TUni t tr)
| sub_uni_r : forall (t tl : UIType Lit) , subui t (TUni tl t)
| sub_isect_l : forall (t tr : UIType Lit) , subui t (TIsect t tr)
| sub_isect_r : forall (t tl : UIType Lit) , subui t (TIsect tl t)
.

Module Type Traditional.

Parameter Lit : Type.

Notation T := (UIType Lit).

Parameter DRule : Lit -> Lit -> Type.

Parameter DPremise : forall {l r : Lit}, DRule l r -> T -> T -> Prop.

Notation dsub := (dsubf (@DPremise)).

Parameter RRule : Lit -> Lit -> Type.

Parameter RPremise : forall {l r : Lit}, RRule l r -> T -> T -> Prop.

Notation rsub := (rsubf (@RPremise)).

Parameter SyntaxDirectedness_Rules : forall ll lr : Lit, { rrules : list (RRule ll lr) | forall r : RRule ll lr, In r rrules }.

Parameter SyntaxDirectedness_Premises : forall {ll lr : Lit} (r : RRule ll lr), { rpremises : list (prod T T) | forall pl pr : T, RPremise r pl pr <-> In (pair pl pr) rpremises }.

Parameter M : Type.

Parameter mlt : M -> M -> Prop.

Parameter mltwf : well_founded mlt.

Parameter m : T -> T -> M.

Parameter m_ui_l : forall (tl tl' tr : T), subui tl tl' -> (clos_refl_trans M mlt) (m tl tr) (m tl' tr).

Parameter m_ui_r : forall (tl tr tr' : T), subui tr tr' -> (clos_refl_trans M mlt) (m tl tr) (m tl tr').

Parameter m_lit : forall {ll lr : Lit} (r : RRule ll lr), forall pl pr : T, RPremise r pl pr -> mlt (m pl pr) (m (TLit ll) (TLit lr)).

Parameter LiteralReflexivity : forall l : Lit, exists r : RRule l l, forall pl pr : T, RPremise r pl pr -> pl = pr.

Parameter RRuleToDProof : forall {ll lr : Lit} (r : RRule ll lr), dsuba (@DPremise) (RPremise r) (TLit ll) (TLit lr).

Parameter DRuleToRProof : forall {ll lr : Lit} (r : DRule ll lr), rsubam (@RPremise) (DPremise r) (TLit ll) (TLit lr).

Parameter LiteralTransitivity : forall {ll lm lr : Lit} (rl : RRule ll lm) (rr : RRule lm lr),
     exists r : RRule ll lr,
       forall pl pr : T, RPremise r pl pr ->
          exists pm : T, (rsubam (@RPremise) (RPremise rl) pl pm /\ rsubam (@RPremise) (RPremise rr) pm pr) \/ (rsubam (@RPremise) (RPremise rr) pl pm /\ rsubam (@RPremise) (RPremise rl) pm pr).

End Traditional.
