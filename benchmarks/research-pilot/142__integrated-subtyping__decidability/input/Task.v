Require Import Section3_Requirements.

Require Import Section4_Requirements.

Module Integrated (M_traditional : Traditional) (M_intersector : Intersector M_traditional).

Import M_traditional.

Import M_intersector.

Inductive IPremise {ll lr : Lit} (r : RRule ll lr) : T -> T -> Prop :=
    ipremise (tl tr : T) : RPremise r tl tr -> IPremise r (Integrate intersect tl) tr.

Definition isub' : T -> T -> Prop :=
    rsubf (@IPremise).

Definition isub (tl : T) : T -> Prop :=
    isub' (Integrate intersect tl).

Theorem IntegratedSoundness : forall tl tr : T, isub tl tr -> esub tl tr.

Theorem IntegratedDecidability : forall tl tr : T, {isub tl tr} + {~ isub tl tr}.

Theorem IntegratedCompleteness : forall tl tr : T, esub tl tr -> isub tl tr.

Theorem DecidabilityOfExtendedSubtyping : forall tl tr : T, {esub tl tr} + {~ esub tl tr}.

End Integrated.
