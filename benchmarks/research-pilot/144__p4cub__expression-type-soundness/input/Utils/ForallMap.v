From Coq Require Export Lists.List micromega.Lia Arith.Compare_dec.

Require Export Poulet4.Utils.Util.ListUtil.

Export ListNotations.

Section MapCombine.

Variables U V : Type.

End MapCombine.

Section Forall.

Variables (A B : Type) (R : A -> B -> Prop).

Variable Q : A -> B -> Prop.

End Forall.

Section ForallMap.

Variables (A B C : Type) (R : A -> B -> Prop).

End ForallMap.

Section MapMap.

Variables (U V W X : Type)
            (f : U -> W) (g : V -> X).

End MapMap.

Section Forall2Impl.

Variables (T U V : Type).

Variables (R : T -> V -> Prop) (S : U -> V -> Prop).

End Forall2Impl.

Section Forall3.

Context {T U V : Type}.

Variable R : T -> U -> V -> Prop.

Inductive Forall3 : list T -> list U -> list V -> Prop :=
  | Forall3_nil :
      Forall3 [] [] []
  | Forall3_cons t u v ts us vs :
      R t u v ->
      Forall3 ts us vs ->
      Forall3 (t :: ts) (u :: us) (v :: vs).

End Forall3.

Section Forall_Map_Forall2.

Variables U V : Type.

Variable R : U -> V -> Prop.

Variable f : U -> V.

End Forall_Map_Forall2.

Section Forall2_Repeat_Forall_l.

Variables U V : Type.

Variable R : U -> V -> Prop.

End Forall2_Repeat_Forall_l.

Section Forall2_Repeat_Forall_r.

Variables U V : Type.

Variable R : U -> V -> Prop.

End Forall2_Repeat_Forall_r.

Section Nth_Update.

Variable U : Type.

End Nth_Update.

Section Forall_nth_update.

Variable U : Type.

Variable F : U -> Prop.

Variable u : U.

Variable n : nat.

End Forall_nth_update.

Section Forall2_nth_update_r.

Variable U V : Type.

Variable R : U -> V -> Prop.

Variable u : U.

Variable v : V.

Variable n : nat.

End Forall2_nth_update_r.

Section Forall2_nth_update_l.

Variable U V : Type.

Variable R : U -> V -> Prop.

Variable u : U.

Variable v : V.

Variable n : nat.

End Forall2_nth_update_l.

Section Forall2Pat.

Variables T U V : Type.

Variable R : T -> U -> V -> Prop.

End Forall2Pat.

Section Forall4.

Context {T U V W : Type}.

Variable R : T -> U -> V -> W -> Prop.

Inductive Forall4 :
    list T -> list U -> list V -> list W -> Prop :=
  | Forall4_nil : Forall4 [] [] [] []
  | Forall4_cons t u v w ts us vs ws :
    R t u v w ->
    Forall4 ts us vs ws ->
    Forall4 (t :: ts) (u :: us) (v :: vs) (w :: ws).

End Forall4.
