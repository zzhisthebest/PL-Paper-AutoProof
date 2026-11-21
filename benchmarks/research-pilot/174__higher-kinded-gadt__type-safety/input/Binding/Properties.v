Require Import Utf8.

Require Import Binding.Core.

Require Vector.

Require Import Morphisms.

Section Properties.

Context {Obj : Type}.

Context {Arr : Obj → Obj → Type} {EqArr : EqIndCore Arr} {AC : ArrowCore Arr}.

Context {ArrEq : EqInd Arr} {AA : Arrow Arr}.

Context {Sub : Obj → Obj → Type} {EqSub : EqIndCore Sub} {SC : ArrowCore Sub}.

Context {ASC : SubstCore Arr Sub} {SubEq : EqInd Sub} {AS : Arrow Sub} {SS : Subst Arr Sub}.

Context {F G : Obj → Type}.

Context {Inc : Obj → Obj}.

Context {Sh  : ShiftableCore Arr Inc}.

Context {ALC : LiftableCore Arr Inc}.

Context {SLC : LiftableCore Sub Inc}.

Context {Sb : SubstitutableCore Sub F Inc}.

Context {LAS : LiftAShift Arr Inc}.

Context {LSS : LiftSShift Arr Sub Inc}.

Context {MapF : FunctorCore (Arr := Arr) F}.

Context {MapG : FunctorCore (Arr := Arr) G}
          {MG : Functor G}.

Context {BindF : BindCore (Sub := Sub) F}.

Context {BindG : BindCore (Sub := Sub) G}
          {BMPG : BindMapPure G} {BMCG : BindMapComm G} {BG : Bind G}.

Context {SbShF  : SubstShift Arr Sub F Inc}.

Context {SbMapF : SubstFMap  Arr Sub F Inc}.

Context {SbBndF : SubstBind  Sub F Inc}.

Context {AL     : Liftable Arr Inc}.

Context {SL     : Liftable Sub Inc}.

Context {ASLI   : ASLiftInj Arr Sub Inc} {ASLC : ASLiftComm Arr Sub Inc}.

Local Open Scope bind_scope.

End Properties.
