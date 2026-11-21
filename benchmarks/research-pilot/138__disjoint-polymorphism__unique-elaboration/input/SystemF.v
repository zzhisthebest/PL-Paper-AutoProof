Require Import Coq.Arith.EqNat.

Require Import Coq.Structures.Equalities.

Require Import Coq.Lists.List.

Require Import Coq.MSets.MSetInterface.

Require Import Coq.MSets.MSetWeakList.

Require Import Coq.Program.Equality.

Require Import Coq.Arith.PeanoNat.

Require Import MSetProperties.

Require Import Coq.Init.Specif.

Module SysF
       (Import VarTyp : UsualDecidableTypeFull)
       (Import set : MSetInterface.S).

Module EqFacts := BoolEqualityFacts(VarTyp).

Module M := MSetWeakList.Make(VarTyp).

Export M.

Module MSetProperties := WPropertiesOn(VarTyp)(M).

Definition var : Type := VarTyp.t.

Inductive STyp :=
  | STUnitT : STyp
  | STInt : STyp
  | STFun : STyp -> STyp -> STyp
  | STTuple : STyp -> STyp -> STyp
  | STFVarT : var -> STyp
  | STBVarT : nat -> STyp
  | STForAll : STyp -> STyp.

Inductive SExp (A : Type) :=
  | STFVar  : A -> SExp A
  | STBVar  : nat -> SExp A
  | STUnit  : SExp A
  | STLit   : nat -> SExp A
  | STLam   : SExp A -> SExp A
  | STApp   : SExp A -> SExp A -> SExp A
  | STPair  : SExp A -> SExp A -> SExp A
  | STProj1 : SExp A -> SExp A
  | STProj2 : SExp A -> SExp A
  | STTLam  : SExp A -> SExp A
  | STTApp  : SExp A -> STyp -> SExp A.

Definition Exp := forall A, SExp A.

Definition vars := M.t.

Definition context (A : Type) := list (var * A).

Definition extend {A} (x : var) (a : A) (c : context A) : context A :=
  ((x,a) :: nil) ++ c.

Definition dom {A} (c : context A) : vars :=
  fold_right (fun el r => add (fst el) r) empty c.

Definition mapctx {A B} (f : A -> B) (c : context A) : context B :=
  map (fun p => (fst p, (f (snd p)))) c.

Inductive ok {A} : context A -> Prop :=
  | Ok_nil : ok nil
  | Ok_push : forall (E : context A) (v : var) (ty : A),
                ok E -> not (In v (dom E)) -> ok (extend v ty E).

Fixpoint fv_typ (sTyp : STyp) : vars :=
  match sTyp with
  | STUnitT       => empty
  | STInt         => empty
  | STFun t1 t2   => union (fv_typ t1) (fv_typ t2)
  | STTuple t1 t2 => union (fv_typ t1) (fv_typ t2)
  | STFVarT v     => singleton v
  | STBVarT n     => empty
  | STForAll t    => fv_typ t
  end.

Fixpoint fv (sExp : SExp var) : vars :=
  match sExp with
    | STFVar _ v => singleton v
    | STBVar _ _ => empty
    | STUnit _ => empty
    | STLit _ _ => empty
    | STLam _ t => fv t
    | STApp _ t1 t2 => union (fv t1) (fv t2)
    | STPair _ t1 t2 => union (fv t1) (fv t2)
    | STProj1 _ t => fv t
    | STProj2 _ t => fv t
    | STTLam _ t => fv t
    | STTApp _ t ty => union (fv t) (fv_typ ty)
  end.

Fixpoint open_rec_typ (k : nat) (u : STyp) (t : STyp) {struct t} : STyp :=
  match t with
  | STUnitT       => STUnitT
  | STInt         => STInt
  | STFun t1 t2   => STFun (open_rec_typ k u t1) (open_rec_typ k u t2)
  | STTuple t1 t2 => STTuple (open_rec_typ k u t1) (open_rec_typ k u t2)
  | STFVarT x     => STFVarT x
  | STBVarT i     => if Nat.eqb k i then u else (STBVarT i)
  | STForAll t    => STForAll (open_rec_typ (S k) u t)
  end.

Fixpoint open_rec_typ_term (k : nat) (u : STyp) (t : SExp var) {struct t} :
  SExp var :=
  match t with
  | STBVar _ i => STBVar _ i
  | STFVar _ x => STFVar _ x
  | STUnit _ => STUnit _
  | STLit _ x => STLit _ x
  | STLam _ t1 => STLam _ (open_rec_typ_term k u t1)
  | STApp _ t1 t2 => STApp _ (open_rec_typ_term k u t1) (open_rec_typ_term k u t2)
  | STPair _ t1 t2 => STPair _ (open_rec_typ_term k u t1) (open_rec_typ_term k u t2)
  | STProj1 _ t => STProj1 _ (open_rec_typ_term k u t)
  | STProj2 _ t => STProj2 _ (open_rec_typ_term k u t)
  | STTLam _ t => STTLam _ (open_rec_typ_term (S k) u t)
  | STTApp _ t ty => STTApp _ (open_rec_typ_term k u t) (open_rec_typ k u ty)
  end.

Fixpoint open_rec (k : nat) (u : SExp var) (t : SExp var) {struct t} : SExp var :=
  match t with
  | STBVar _ i => if Nat.eqb k i then u else (STBVar _ i)
  | STFVar _ x => STFVar _ x
  | STUnit _ => STUnit _
  | STLit _ x => STLit _ x
  | STLam _ t1 => STLam _ (open_rec (S k) u t1)
  | STApp _ t1 t2 => STApp _ (open_rec k u t1) (open_rec k u t2)
  | STPair _ t1 t2 => STPair _ (open_rec k u t1) (open_rec k u t2)
  | STProj1 _ t => STProj1 _ (open_rec k u t)
  | STProj2 _ t => STProj2 _ (open_rec k u t)
  | STTLam _ t => STTLam _ (open_rec k u t)
  | STTApp _ t ty => STTApp _ (open_rec k u t) ty
  end.

Definition open (t : SExp var) u := open_rec 0 u t.

Definition open_typ (t : STyp) u := open_rec_typ 0 u t.

Definition open_typ_term (t : SExp var) u := open_rec_typ_term 0 u t.

Fixpoint subst (z : var) (u : SExp var) (t : SExp var) {struct t} : SExp var :=
  match t with
  | STBVar _ i     => STBVar _ i
  | STFVar _ x     => if VarTyp.eqb x z then u else (STFVar _ x)
  | STUnit _       => STUnit _
  | STLit _ n      => STLit _ n
  | STLam _ t      => STLam _ (subst z u t)
  | STApp _ t1 t2  => STApp _ (subst z u t1) (subst z u t2)
  | STPair _ t1 t2 => STPair _ (subst z u t1) (subst z u t2)
  | STProj1 _ t    => STProj1 _ (subst z u t)
  | STProj2 _ t    => STProj2 _ (subst z u t)
  | STTLam _ t     => STTLam _ (subst z u t)
  | STTApp _ t ty  => STTApp _ (subst z u t) ty
  end.

Fixpoint subst_typ (z : var) (u : STyp) (t : STyp) {struct t} : STyp :=
  match t with
  | STUnitT       => STUnitT
  | STInt         => STInt
  | STFun t1 t2   => STFun (subst_typ z u t1) (subst_typ z u t2)
  | STTuple t1 t2 => STTuple (subst_typ z u t1) (subst_typ z u t2)
  | STFVarT x     => if VarTyp.eqb x z then u else (STFVarT x)
  | STBVarT i     => STBVarT i
  | STForAll t    => STForAll (subst_typ z u t)
  end.

Notation "[ z ~> u ] t" := (subst z u t) (at level 68).

Notation "{ k ~> u } t" := (open_rec k u t) (at level 67).

Notation "t ^ x" := (open t (STFVar var x)).

Notation "t ^^ u" := (open t u) (at level 67).

Inductive STType : STyp -> Prop :=
  | STType_Var : forall x, STType (STFVarT x)
  | STType_Unit : STType STUnitT
  | STType_Int : STType STInt
  | STType_Fun : forall t1 t2, STType t1 -> STType t2 -> STType (STFun t1 t2)
  | STType_Tuple : forall t1 t2, STType t1 -> STType t2 -> STType (STTuple t1 t2)
  | STType_ForAll : forall L t,
      (forall x, not (In x L) -> STType (open_typ t (STFVarT x))) ->
      STType (STForAll t).

Inductive TyEnv (t : Type) : Type :=
  | TyVar : TyEnv t
  | TermVar : t -> TyEnv t.

Inductive WFType : context (TyEnv STyp) -> STyp -> Prop :=
  | WFType_Var : forall x Gamma, ok Gamma -> List.In (x,TyVar _) Gamma -> WFType Gamma (STFVarT x)
  | WFType_Unit : forall Gamma, ok Gamma -> WFType Gamma STUnitT
  | WFType_Int : forall Gamma, ok Gamma -> WFType Gamma STInt
  | WFType_Fun : forall Gamma t1 t2, WFType Gamma t1 -> WFType Gamma t2 -> WFType Gamma (STFun t1 t2)
  | WFType_Tuple : forall Gamma t1 t2, WFType Gamma t1 -> WFType Gamma t2 -> WFType Gamma (STTuple t1 t2)
  | WFType_ForAll : forall L Gamma t,
      (forall x, not (In x L) -> WFType (extend x (TyVar _) Gamma) (open_typ t (STFVarT x))) ->
      WFType Gamma (STForAll t).

Inductive STTerm : SExp var -> Prop :=
  | STTerm_Var : forall x,
      STTerm (STFVar _ x)
  | STTerm_Unit : STTerm (STUnit _)
  | STTerm_Lit : forall n,
      STTerm (STLit _ n)
  | STTerm_Lam : forall L t1,
      (forall x, not (In x L) -> STTerm (open t1 (STFVar _ x))) ->
      STTerm (STLam _ t1)
  | STTerm_App : forall t1 t2,
      STTerm t1 ->
      STTerm t2 ->
      STTerm (STApp _ t1 t2)
  | STTerm_Pair : forall t1 t2,
      STTerm t1 ->
      STTerm t2 ->
      STTerm (STPair _ t1 t2)
  | STTerm_Proj1 : forall t,
      STTerm t ->
      STTerm (STProj1 _ t)
  | STTerm_Proj2 : forall t,
      STTerm t ->
      STTerm (STProj2 _ t)
  | STTerm_TLam : forall L t,
      (forall x, not (In x L) -> STTerm (open_typ_term t (STFVarT x))) ->
      STTerm (STTLam _ t)
  | STTerm_TApp : forall t ty,
      STTerm t ->
      STType ty ->
      STTerm (STTApp _ t ty).

Fixpoint fresh (L : vars) (n : nat) (xs : list var) : Prop :=
  match xs with
  | nil => match n with
           | 0 => True
           | S _ => False
           end
  | (x :: xs')%list =>
      match n with
      | 0 => False
      | S n' => (not (In x L)) /\ fresh (union L (singleton x)) n' xs'
      end
  end.

Definition body_typ_term t :=
  exists L, forall x, ~ In x L -> STTerm (open_typ_term t (STFVarT x)).

Inductive has_type_st : (context (TyEnv STyp)) -> (SExp var) -> STyp -> Prop :=
  | STTyVar : forall Gamma x ty, WFType Gamma ty ->
                ok Gamma -> List.In (x,TermVar _ ty) Gamma -> has_type_st Gamma (STFVar _ x) ty
  | STTyUnit : forall Gamma, ok Gamma -> has_type_st Gamma (STUnit _) STUnitT
  | STTyLit : forall Gamma x, ok Gamma -> has_type_st Gamma (STLit _ x) STInt
  | STTyLam : forall L Gamma t A B,
                (forall x, not (In x L) ->
                      has_type_st (extend x (TermVar _ A) Gamma) (open t (STFVar _ x)) B) ->
                WFType Gamma A ->
                has_type_st Gamma (STLam _ t) (STFun A B)
  | STTyApp : forall Gamma A B t1 t2, has_type_st Gamma t1 (STFun A B) ->
                             has_type_st Gamma t2 A -> has_type_st Gamma (STApp _ t1 t2) B
  | STTyPair : forall Gamma A B t1 t2, has_type_st Gamma t1 A ->
                              has_type_st Gamma t2 B ->
                              has_type_st Gamma (STPair _ t1 t2) (STTuple A B)
  | STTyProj1 : forall Gamma t A B, has_type_st Gamma t (STTuple A B) ->
                           has_type_st Gamma (STProj1 _ t) A
  | STTyProj2 : forall Gamma t A B, has_type_st Gamma t (STTuple A B) ->
                           has_type_st Gamma (STProj2 _ t) B
  | STTyTLam : forall L Gamma t A,
                 (forall x, not (In x L) ->
                       has_type_st (extend x (TyVar _) Gamma)
                                   (open_typ_term t (STFVarT x))
                                   (open_typ A (STFVarT x))) ->
                 has_type_st Gamma (STTLam _ t) (STForAll A)
  | STTyTApp : forall Gamma t A ty, WFType Gamma A ->
                           has_type_st Gamma t (STForAll ty) ->
                           has_type_st Gamma (STTApp _ t A) (open_typ ty A).

Definition body_type t :=
  exists L, forall x, not (In x L) -> STType (open_typ t (STFVarT x)).

Definition body_wf_type t Gamma :=
  exists L, forall x, not (In x L) -> ok (extend x (TyVar _) Gamma) ->
            WFType (extend x (TyVar _) Gamma) (open_typ t (STFVarT x)).

End SysF.
