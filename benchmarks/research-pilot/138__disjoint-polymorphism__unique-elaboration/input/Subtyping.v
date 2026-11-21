Require Import String.

Require Import Coq.Structures.Equalities.

Require Import Coq.MSets.MSetInterface.

Require Import Arith.

Require Import Setoid.

Require Import Coq.Program.Equality.

Require Import SystemF.

Require Import Infrastructure.

Module MSubtyping
       (Import VarTyp : UsualDecidableTypeFull)
       (Import set : MSetInterface.S).

Module MInfrastructure := MInfrastructure(VarTyp)(set).

Export MInfrastructure.

Definition join_sum {A : Type} (s : A + A) : A :=
  match s with inl a => a | inr a => a end.

Inductive Atomic : PTyp -> Prop :=
  | AInt : Atomic PInt
  | AFun : forall t1 t2, Atomic (Fun t1 t2)
  | AVar : forall v, Atomic (PFVarT v)
  | AForAll : forall d t, Atomic (ForAll d t)
  | ARec : forall l t, Atomic (Rec l t).

Inductive usub : PTyp -> PTyp -> Prop :=
  | USInt : usub PInt PInt
  | USFun : forall o1 o2 o3 o4, usub o3 o1 -> usub o2 o4 -> usub (Fun o1 o2) (Fun  o3 o4)
  | USAnd1 : forall t t1 t2, usub t t1 -> usub t t2 -> usub t (And  t1 t2)
  | USAnd2 : forall t t1 t2 , usub t1 t -> PType t2 -> usub (And t1 t2) t
  | USAnd3 : forall t t1 t2, usub t2 t -> PType t1 -> usub (And t1 t2) t
  | USVar   : forall v, usub (PFVarT v) (PFVarT v)
  | USForAll : forall L d1 d2 t1 t2,
                 (forall x, not (In x L) -> usub (open_typ_source t1 (PFVarT x))
                                           (open_typ_source t2 (PFVarT x))) ->
                 usub d2 d1 ->
                 usub (ForAll d1 t1) (ForAll d2 t2)
  | USTop : forall t, PType t -> usub t Top
  | USRec : forall l t1 t2, usub t1 t2 -> usub (Rec l t1) (Rec l t2).

Inductive and_coercion (e : SExp var) : PTyp -> sum (SExp var) (SExp var) -> Prop :=
  | ACInt : and_coercion e PInt (inr e)
  | ACFunL : forall A B e1, and_coercion e B (inl e1) ->
                       and_coercion e (Fun A B) (inl (STLam _ e1))
  | ACFunR : forall A B, and_coercion e B (inr e) ->
                    and_coercion e (Fun A B) (inr e)
  | ACAndL : forall A B e1 e2, and_coercion e A (inl e1) ->
                          and_coercion e B (inl e2) ->
                          and_coercion e (And A B) (inl (STPair _ e1 e2))
  | ACAndR1 : forall A B, and_coercion e A (inr e) ->
                     and_coercion e (And A B) (inr e)
  | ACAndR2 : forall A B, and_coercion e B (inr e) ->
                     and_coercion e (And A B) (inr e)
  | ACVar : forall x, and_coercion e (PFVarT x) (inr e)
  | ACForAllL : forall L A d e1,
                  (forall x, not (In x L) ->
                        and_coercion e (open_typ_source A (PFVarT x)) (inl e1)) ->
                  and_coercion e (ForAll d A) (inl (STTLam _ e1))
  | ACForAllR : forall L A d,
                  (forall x, not (In x L) ->
                        and_coercion e (open_typ_source A (PFVarT x)) (inr e)) ->
                  and_coercion e (ForAll d A) (inr e)
  | ACTop : and_coercion e Top (inl (STUnit _))
  | ACRec : forall l t r, and_coercion e t r ->
                     and_coercion e (Rec l t) r.

Inductive sub : PTyp -> PTyp -> (SExp var) -> Prop :=
  | SInt : sub PInt PInt (STLam _ (STBVar _ 0))
  | SFun : forall o1 o2 o3 o4 c1 c2,
             sub o3 o1 c1 ->
             sub o2 o4 c2 ->
             sub (Fun o1 o2) (Fun o3 o4) (STLam _ (STLam _ (STApp _ c2 (STApp _ (STBVar _ 1) (STApp _ c1 (STBVar _ 0))))))
  | SAnd1 : forall t t1 t2 c1 c2,
              sub t t1 c1 ->
              sub t t2 c2 ->
              sub t (And t1 t2) (STLam _ (STPair _ (STApp _ c1 (STBVar _ 0)) (STApp _ c2 (STBVar _ 0))))
  | SAnd2 : forall t t1 t2 c ac,
              sub t1 t c ->
              Atomic t ->
              PType t2 ->
              and_coercion ((STApp _ c (STProj1 _ (STBVar _ 0)))) t ac ->
              sub (And t1 t2) t (STLam _ (join_sum ac))


  | SAnd3 : forall t t1 t2 c ac,
              sub t2 t c ->
              Atomic t ->
              PType t1 ->

              and_coercion ((STApp _ c (STProj2 _ (STBVar _ 0)))) t ac ->
              sub (And t1 t2) t (STLam _ (join_sum ac))
  | SVar : forall v, sub (PFVarT v) (PFVarT v) (STLam _ (STBVar _ 0))
  | SForAll : forall L d1 d2 t1 t2 c c',
                (forall x, not (In x L) -> sub (open_typ_source t1 (PFVarT x))
                                         (open_typ_source t2 (PFVarT x))
                                         (open_typ_term c (STFVarT x))) ->
                sub d2 d1 c' ->
                sub (ForAll d1 t1) (ForAll d2 t2)
                    (STLam _ (STTLam _ (STApp _ c (STTApp _ (STBVar _ 0) (STBVarT 0)))))
  | STop : forall t, PType t -> sub t Top (STLam _ (STUnit _))
  | SRec : forall l t1 t2 c, sub t1 t2 c -> sub (Rec l t1) (Rec l t2) c.

Definition Sub (t1 t2 : PTyp) : Prop := exists (e:SExp var), sub t1 t2 e.

Fixpoint subst_typ_term (z : var) (u : STyp) (t : SExp var) {struct t} : SExp var :=
  match t with
  | STBVar _ i     => STBVar _ i
  | STFVar _ x     => STFVar _ x
  | STUnit _       => STUnit _
  | STLit _ n      => STLit _ n
  | STLam _ t      => STLam _ (subst_typ_term z u t)
  | STApp _ t1 t2  => STApp _ (subst_typ_term z u t1) (subst_typ_term z u t2)
  | STPair _ t1 t2 => STPair _ (subst_typ_term z u t1) (subst_typ_term z u t2)
  | STProj1 _ t    => STProj1 _ (subst_typ_term z u t)
  | STProj2 _ t    => STProj2 _ (subst_typ_term z u t)
  | STTLam _ t     => STTLam _ (subst_typ_term z u t)
  | STTApp _ t ty  => STTApp _ (subst_typ_term z u t) (subst_typ z u ty)
  end.

End MSubtyping.
