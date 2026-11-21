Require Import String.

Require Import Coq.Structures.Equalities.

Require Import Coq.MSets.MSetInterface.

Require Import Arith.

Require Import Setoid.

Require Import SystemF.

Require Import Coq.Program.Equality.

Require Import Disjointness.

Module MTyping
       (Import VarTyp : UsualDecidableTypeFull)
       (Import set : MSetInterface.S).

Module MDisjointness := MDisjointness(VarTyp)(set).

Export MDisjointness.

Inductive WFTyp : context TyEnvSource -> PTyp -> Prop :=
  | WFInt : forall Gamma, WFEnv Gamma -> WFTyp Gamma PInt
  | WFFun : forall Gamma t1 t2, WFTyp Gamma t1 -> WFTyp Gamma t2 -> WFTyp Gamma (Fun t1 t2)
  | WFAnd : forall Gamma t1 t2, WFTyp Gamma t1 -> WFTyp Gamma t2 -> Ortho Gamma t1 t2 -> WFTyp Gamma (And t1 t2)
  | WFVar : forall Gamma x ty, List.In (x,TyDis ty) Gamma -> WFEnv Gamma -> WFTyp Gamma (PFVarT x)
  | WFForAll : forall L Gamma d t,
                 (forall x, not (In x L) -> WFTyp (extend x (TyDis d) Gamma) (open_typ_source t (PFVarT x))) ->
                 WFTyp Gamma d ->
                 WFTyp Gamma (ForAll d t)
  | WFTop : forall Gamma, WFEnv Gamma -> WFTyp Gamma Top
  | WFRec : forall Gamma l t, WFTyp Gamma t -> WFTyp Gamma (Rec l t).

Inductive Dir := Inf | Chk.

Inductive has_type_source_alg : context TyEnvSource -> PExp -> Dir -> PTyp -> (SExp var) -> Prop :=

  | ATyTop : forall Gamma, WFEnv Gamma -> has_type_source_alg Gamma PUnit Inf Top (STUnit _)
  | ATyVar : forall Gamma x ty, WFEnv Gamma -> List.In (x,TermV ty) Gamma -> WFTyp Gamma ty ->
                      has_type_source_alg Gamma (PFVar x) Inf ty (STFVar _ x)
  | ATyLit : forall Gamma x, WFEnv Gamma -> has_type_source_alg Gamma (PLit x) Inf PInt (STLit _ x)
  | ATyApp : forall Gamma A B t1 t2 E1 E2,
              has_type_source_alg Gamma t1 Inf (Fun A B) E1 ->
              has_type_source_alg Gamma t2 Chk A E2 ->
              has_type_source_alg Gamma (PApp t1 t2) Inf B (STApp _ E1 E2)
  | ATyMerge : forall Gamma A B t1 t2 E1 E2,
                has_type_source_alg Gamma t1 Inf A E1 ->
                has_type_source_alg Gamma t2 Inf B E2 ->
                Ortho Gamma A B ->
                has_type_source_alg Gamma (PMerge t1 t2) Inf (And A B) (STPair _ E1 E2)
  | ATyAnn : forall Gamma t1 A E, has_type_source_alg Gamma t1 Chk A E ->
                         has_type_source_alg Gamma (PAnn t1 A) Inf A E
  | ATyTApp : forall Gamma t A ty d E,
                WFTyp Gamma A ->
                has_type_source_alg Gamma t Inf (ForAll d ty) E ->
                Ortho Gamma A d ->
                has_type_source_alg Gamma (PTApp t A) Inf (open_typ_source ty A) (STTApp _ E (|A|))
  | ATyRec : forall Gamma l t A E,
               has_type_source_alg Gamma t Inf A E ->
               has_type_source_alg Gamma (PRec l t) Inf (Rec l A) E
  | ATyProjR : forall Gamma l t A E,
                 has_type_source_alg Gamma t Inf (Rec l A) E ->
                 has_type_source_alg Gamma (PProjR t l) Inf A E
  | ATyTLam : forall L Gamma t A d E,
               WFTyp Gamma d ->
               (forall x, not (In x L) ->
                     has_type_source_alg (extend x (TyDis d) Gamma)
                                         (open_typ_term_source t (PFVarT x))
                                         Inf
                                         (open_typ_source A (PFVarT x))
                                         (open_typ_term E (STFVarT x))) ->
               has_type_source_alg Gamma (PTLam d t) Inf (ForAll d A) (STTLam _ E)

  | ATyLam : forall L Gamma t A B E,
               (forall x, not (In x L) ->
                     has_type_source_alg (extend x (TermV A) Gamma) (open_source t (PFVar x)) Chk B (open E (STFVar _ x))) ->
               WFTyp Gamma A ->
               has_type_source_alg Gamma (PLam t) Chk (Fun A B) (STLam _ E)
  | ATySub : forall Gamma t A B C E,
               has_type_source_alg Gamma t Inf A E ->
               sub A B C ->
               WFTyp Gamma B ->
               has_type_source_alg Gamma t Chk B (STApp _ C E).

Definition body_wf_typ t d Gamma :=
  exists L, forall x, not (In x L) -> WFTyp Gamma d ->
            WFTyp (extend x (TyDis d) Gamma) (open_typ_source t (PFVarT x)).

End MTyping.
