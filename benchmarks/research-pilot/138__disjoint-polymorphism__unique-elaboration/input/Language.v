Require Import String.

Require Import Coq.Structures.Equalities.

Require Import Coq.MSets.MSetInterface.

Require Import Arith.

Require Import Setoid.

Require Import SystemF.

Require Import Coq.Program.Equality.

Module MLanguage
       (Import VarTyp : UsualDecidableTypeFull)
       (Import set : MSetInterface.S).

Module SF := SysF(VarTyp)(set).

Export SF.

Inductive PTyp : Type :=
  | PInt : PTyp
  | Fun : PTyp -> PTyp -> PTyp
  | And : PTyp -> PTyp -> PTyp
  | PBVarT : nat -> PTyp
  | PFVarT : var -> PTyp
  | ForAll : PTyp -> PTyp -> PTyp
  | Top : PTyp
  | Rec : var -> PTyp -> PTyp  .

Fixpoint ptyp2styp (t : PTyp) : STyp :=
  match t with
    | PInt => STInt
    | Fun t1 t2 => STFun (ptyp2styp t1) (ptyp2styp t2)
    | And t1 t2 => STTuple (ptyp2styp t1) (ptyp2styp t2)
    | PBVarT n => STBVarT n
    | PFVarT v => STFVarT v
    | ForAll _ t => STForAll (ptyp2styp t)
    | Top => STUnitT
    | Rec l t => ptyp2styp t
  end.

Notation "'|' t '|'" := (ptyp2styp t) (at level 60).

Fixpoint open_rec_typ_source (k : nat) (u : PTyp) (t : PTyp) {struct t} : PTyp :=
  match t with
  | PInt        => PInt
  | Fun t1 t2   => Fun (open_rec_typ_source k u t1) (open_rec_typ_source k u t2)
  | And t1 t2   => And (open_rec_typ_source k u t1) (open_rec_typ_source k u t2)
  | PFVarT x    => PFVarT x
  | PBVarT i    => if Nat.eqb k i then u else (PBVarT i)
  | ForAll d t => ForAll (open_rec_typ_source k u d)
                        (open_rec_typ_source (S k) u t)
  | Top         => Top
  | Rec l t     => Rec l (open_rec_typ_source k u t)
  end.

Definition open_typ_source (t : PTyp) u := open_rec_typ_source 0 u t.

Fixpoint subst_typ_source (z : var) (u : PTyp) (t : PTyp) {struct t} : PTyp :=
  match t with
  | PInt        => PInt
  | Fun t1 t2   => Fun (subst_typ_source z u t1) (subst_typ_source z u t2)
  | And t1 t2   => And (subst_typ_source z u t1) (subst_typ_source z u t2)
  | PFVarT x    => if VarTyp.eqb x z then u else (PFVarT x)
  | PBVarT i    => PBVarT i
  | ForAll d t  => ForAll (subst_typ_source z u d) (subst_typ_source z u t)
  | Top         => Top
  | Rec l t     => Rec l (subst_typ_source z u t)
  end.

Fixpoint fv_ptyp (pTyp : PTyp) : vars :=
  match pTyp with
    | PInt        => empty
    | Fun t1 t2   => union (fv_ptyp t1) (fv_ptyp t2)
    | And t1 t2   => union (fv_ptyp t1) (fv_ptyp t2)
    | PBVarT n    => empty
    | PFVarT v    => singleton v
    | ForAll d t  => union (fv_ptyp d) (fv_ptyp t)
    | Top         => empty
    | Rec l t     => union (singleton l) (fv_ptyp t)
  end.

Inductive PType : PTyp -> Prop :=
  | PType_Var : forall x, PType (PFVarT x)
  | PType_Int : PType PInt
  | PType_Fun : forall t1 t2, PType t1 -> PType t2 -> PType (Fun t1 t2)
  | PType_And : forall t1 t2, PType t1 -> PType t2 -> PType (And t1 t2)
  | PType_ForAll : forall L d t,
                     PType d ->
                     (forall x, not (In x L) -> PType (open_typ_source t (PFVarT x))) ->
                     PType (ForAll d t)
  | PType_Top : PType Top
  | PType_Rec : forall l t, PType t -> PType (Rec l t).

Inductive PExp :=
  | PUnit  : PExp
  | PFVar  : var -> PExp
  | PBVar  : nat -> PExp
  | PLit   : nat -> PExp
  | PLam   : PExp -> PExp
  | PApp   : PExp -> PExp -> PExp
  | PMerge : PExp -> PExp -> PExp
  | PAnn   : PExp -> PTyp -> PExp
  | PTLam  : PTyp -> PExp -> PExp
  | PTApp  : PExp -> PTyp -> PExp
  | PRec   : var -> PExp -> PExp
  | PProjR : PExp -> var -> PExp.

Fixpoint fv_source (pExp : PExp) : vars :=
  match pExp with
    | PUnit => empty
    | PFVar v => singleton v
    | PBVar _ => empty
    | PLit _ => empty
    | PLam t => fv_source t
    | PApp t1 t2 => union (fv_source t1) (fv_source t2)
    | PMerge t1 t2 => union (fv_source t1) (fv_source t2)
    | PAnn t1 A => fv_source t1
    | PTLam tydis t => union (fv_ptyp tydis) (fv_source t)
    | PTApp t ty => union (fv_source t) (fv_ptyp ty)
    | PRec l t => union (singleton l) (fv_source t)
    | PProjR t l => union (fv_source t) (singleton l)
  end.

Inductive TyEnvSource : Type :=
  | TyDis : PTyp -> TyEnvSource
  | TermV : PTyp -> TyEnvSource.

Inductive WFEnv : context TyEnvSource -> Prop :=
  | WFNil : WFEnv nil
  | WFPushV : forall Gamma v ty,
                WFEnv Gamma -> not (In v (fv_ptyp ty)) -> ~ In v (dom Gamma) ->
                WFEnv (extend v (TyDis ty) Gamma)
  | WFPushT : forall Gamma v ty,
                WFEnv Gamma -> ~ In v (dom Gamma) -> WFEnv (extend v (TermV ty) Gamma).

Fixpoint subst_env (Gamma : context TyEnvSource) (z : var) (u : PTyp) :=
  match Gamma with
    | nil => nil
    | (x,TyDis d) :: tl => (x, TyDis (subst_typ_source z u d)) ::
                           (subst_env tl z u)
    | (x, TermV ty) :: tl => (x, TermV ty) :: (subst_env tl z u)
  end.

Definition MapsTo (Gamma : context TyEnvSource) (z : var) (d : PTyp) :=
  find (fun x => eqb (fst x) z) Gamma = Some (z, TyDis d).

Definition TyEnvMatch {A} (f : PTyp -> A) (tyenv : TyEnvSource) : A :=
  match tyenv with
    | TyDis d => f d
    | TermV ty => f ty
  end.

Definition codom (c : context TyEnvSource) : vars :=
  fold_right (fun el r => union (TyEnvMatch fv_ptyp (snd el)) r) empty c.

Fixpoint open_rec_source (k : nat) (u : PExp) (t : PExp) {struct t} : PExp  :=
  match t with
  | PUnit        => PUnit
  | PBVar i      => if Nat.eqb k i then u else (PBVar i)
  | PFVar x      => PFVar x
  | PLit x       => PLit x
  | PLam t1      => PLam (open_rec_source (S k) u t1)
  | PApp t1 t2   => PApp (open_rec_source k u t1) (open_rec_source k u t2)
  | PMerge t1 t2 => PMerge (open_rec_source k u t1) (open_rec_source k u t2)
  | PAnn e t     => PAnn (open_rec_source k u e) t
  | PTLam ty t   => PTLam ty (open_rec_source k u t)
  | PTApp t ty   => PTApp (open_rec_source k u t) ty
  | PRec l t     => PRec l (open_rec_source k u t)
  | PProjR t l   => PProjR (open_rec_source k u t) l
  end.

Fixpoint open_rec_typ_term_source (k : nat) (u : PTyp) (t : PExp) {struct t} : PExp :=
  match t with
  | PUnit        => PUnit
  | PBVar i      => PBVar i
  | PFVar x      => PFVar x
  | PLit x       => PLit x
  | PLam t1      => PLam (open_rec_typ_term_source k u t1)
  | PApp t1 t2   => PApp (open_rec_typ_term_source k u t1)
                        (open_rec_typ_term_source k u t2)
  | PMerge t1 t2 => PMerge (open_rec_typ_term_source k u t1)
                          (open_rec_typ_term_source k u t2)
  | PAnn e t     => PAnn (open_rec_typ_term_source k u e) t
  | PTLam ty t   => PTLam ty (open_rec_typ_term_source (S k) u t)
  | PTApp t ty   => PTApp (open_rec_typ_term_source k u t)
                         (open_rec_typ_source k u ty)
  | PRec l t     => PRec l (open_rec_typ_term_source k u t)
  | PProjR t l   => PProjR (open_rec_typ_term_source k u t) l
  end.

Definition open_source t u := open_rec_source 0 u t.

Definition open_typ_term_source t u := open_rec_typ_term_source 0 u t.

Definition ptyp2styp_tyenv (t : TyEnvSource) : TyEnv STyp :=
  match t with
    | TyDis _ => TyVar _
    | TermV t => TermVar _ (ptyp2styp t)
  end.

Definition conv_context (env : context TyEnvSource) : context (TyEnv STyp) :=
  mapctx ptyp2styp_tyenv env.

Notation "'∥' t '∥'" := (conv_context t) (at level 60).

Inductive PTerm : PExp -> Prop :=
  | PTerm_Unit :
      PTerm PUnit
  | PTerm_Var : forall x,
      PTerm (PFVar x)
  | PTerm_Lit : forall n,
      PTerm (PLit n)
  | PTerm_Lam : forall L t1,
      (forall x, not (In x L) -> PTerm (open_source t1 (PFVar x))) ->
      PTerm (PLam t1)
  | PTerm_App : forall t1 t2,
      PTerm t1 ->
      PTerm t2 ->
      PTerm (PApp t1 t2)
  | PTerm_Merge : forall t1 t2,
      PTerm t1 ->
      PTerm t2 ->
      PTerm (PMerge t1 t2)
  | PTerm_Ann : forall e t,
      PTerm e ->
      PTerm (PAnn e t)
  | PTerm_TLam : forall L t ty,
      (forall x, not (In x L) -> PTerm (open_typ_term_source t (PFVarT x))) ->
      PTerm (PTLam ty t)
  | PTerm_TApp : forall t ty,
      PTerm t ->
      PType ty ->
      PTerm (PTApp t ty)
  | PTerm_Rec : forall l t,
      PTerm t ->
      PTerm (PRec l t)
  | PTerm_ProjR : forall l t,
      PTerm t ->
      PTerm (PProjR t l).

End MLanguage.
