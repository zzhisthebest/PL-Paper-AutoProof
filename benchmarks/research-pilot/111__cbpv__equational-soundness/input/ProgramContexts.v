Set Implicit Arguments.

Require Import Logic List Classes.Morphisms.

Import List Notations.

Require Export SyntacticTyping.

Inductive vctx (t: bool) (m: nat): nat -> Type :=
  | vctxHole : (if t then True else False) -> vctx t m m
  | vctxPairL n: vctx t m n -> value m -> vctx t m n
  | vctxPairR n : value m -> vctx t m n -> vctx t m n
  | vctxInj n : bool -> vctx t m n -> vctx t m n
  | vctxThunk n : cctx t m n -> vctx t m n


with cctx (t: bool) (m: nat) : nat -> Type :=
  | cctxHole: (if t then False else True) -> cctx t m m
  | cctxForce n : vctx t m n -> cctx t m n
  | cctxLambda n: cctx t (S m) n -> cctx t m n
  | cctxAppL n:  cctx t m n -> value m -> cctx t m n
  | cctxAppR n:  comp m -> vctx t m n -> cctx t m n
  | cctxTupleL n: cctx t m n -> comp m -> cctx t m n
  | cctxTupleR n: comp m -> cctx t m n -> cctx t m n
  | cctxRet n: vctx t m n -> cctx t m n
  | cctxLetinL n: cctx t m n -> comp (S m) -> cctx t m n
  | cctxLetinR n: comp m -> cctx t (S m) n -> cctx t m n
  | cctxProj n: bool -> cctx t m n -> cctx t m n
  | cctxCaseZ n: vctx t m n -> cctx t m n
  | cctxCaseSV n: vctx t m n -> comp (S m) -> comp (S m) -> cctx t m n
  | cctxCaseSL n: value m -> cctx t (S m) n -> comp (S m) -> cctx t m n
  | cctxCaseSR n: value m -> comp (S m) -> cctx t (S m) n -> cctx t m n
  | cctxCasePV n: vctx t m n -> comp (S (S m)) -> cctx t m n
  | cctxCasePC n: value m -> cctx t (S (S m)) n -> cctx t m n.

Scheme vctx_ind_2 := Induction for vctx Sort Prop
  with cctx_ind_2  := Induction for cctx Sort Prop.

Combined Scheme mutind_vctx_cctx from vctx_ind_2, cctx_ind_2.

Notation "'•__v'" := (vctxHole true _ I).

Notation "'•__c'" := (cctxHole false _ I).

Fixpoint fillv {m n: nat} {t: bool} (C: vctx t m n) : (if t then value n else comp n) -> value m :=
  match C in vctx _ _ n return (if t then value n else comp n) -> value m with
  | vctxHole _ _ H =>
    (match t return (if t then True else False) -> (if t then value m else comp m) -> value m with
    |  true => fun _ v' => v'
    | false => fun f _ => match f with end
    end) H
  | vctxPairL C v => fun v' => pair (fillv C v') v
  | vctxPairR v C => fun v' => pair v (fillv C v')
  | vctxInj b C => fun v' => inj b (fillv C v')
  | vctxThunk C => fun v' => <{ fillc C v' }>
  end
with fillc {m n: nat} {t: bool} (C: cctx t m n) : (if t then value n else comp n) -> comp m :=
  match C in cctx _ _ n return (if t then value n else comp n) -> comp m with
  | cctxHole _ _ H =>
    (match t return (if t then False else True) -> (if t then value m else comp m) -> comp m with
     | false => fun _ v' => v'
     | true => fun f _ => match f with end
     end) H
  | cctxForce C => fun v' => (fillv C v') !
  | cctxLambda C => fun v' => lambda (fillc C v')
  | cctxAppL C v => fun v' => (fillc C v') v
  | cctxAppR c C => fun v' => c (fillv C v')
  | cctxTupleL C c => fun v' => tuple (fillc C v') c
  | cctxTupleR c C => fun v' => tuple c (fillc C v')
  | cctxRet C => fun v' => ret (fillv C v')
  | cctxLetinL C c => fun v' => letin (fillc C v') c
  | cctxLetinR c C => fun v' => letin c (fillc C v')
  | cctxProj b C => fun v' => proj b (fillc C v')
  | cctxCaseZ C => fun v' => caseZ (fillv C v')
  | cctxCaseSV C c1 c2 => fun v' => caseS (fillv C v') c1 c2
  | cctxCaseSL v C c2 => fun v' => caseS v (fillc C v') c2
  | cctxCaseSR v c1 C => fun v' => caseS v c1 (fillc C v')
  | cctxCasePV C c => fun v' => caseP (fillv C v') c
  | cctxCasePC v C => fun v' => caseP v (fillc C v')
  end.

Reserved Notation "Gamma [[ Delta ]] ⊢ C : B ; T" (at level 53, C at level 99).

Reserved Notation "Gamma [[ Delta ]] ⊩ C : A ; T" (at level 53,  C at level 99).

Definition valtypeif (t: bool) (A: valtype):
  (if t then True else False) -> if t then valtype else comptype :=
  match t with
  | true => fun _ => A
  | false => fun f => match f with end
  end.

Definition comptypeif (t: bool) (B: comptype):
  (if t then False else True) -> if t then valtype else comptype :=
  match t with
  | false => fun _ => B
  | true => fun f => match f with end
  end.

Inductive vctxTyping {m: nat} {t: bool} (Gamma: ctx m) :
  forall n, ctx n -> vctx t m n -> valtype -> (if t then valtype else comptype) -> Type :=
| vctxTypingHole A H:
    Gamma [[ Gamma ]] ⊩ vctxHole t m H : A; valtypeif t A H
| vctxTypingPairL n (Delta: ctx n) (C: vctx t m n) A A1 A2 v:
    Gamma[[Delta]] ⊩ C : A1; A ->
    Gamma ⊩ v : A2  ->
    Gamma[[Delta]] ⊩ vctxPairL C v : A1 * A2; A
| vctxTypingPairR n (Delta: ctx n) (C: vctx t m n) A A1 A2 v:
    Gamma ⊩ v : A1  ->
    Gamma[[Delta]] ⊩ C : A2; A ->
    Gamma[[Delta]] ⊩ vctxPairR v C : A1 * A2; A
| vctxTypingInj n (Delta: ctx n) (C: vctx t m n) A A1 A2 (b: bool):
    Gamma[[Delta]] ⊩ C : (if b then A1 else A2); A ->
    Gamma[[Delta]] ⊩ vctxInj b C : Sigma A1 A2; A
| vctxTypingThunk n (Delta: ctx n) (C: cctx t m n) B A:
    Gamma[[Delta]] ⊢ C : B; A ->
    Gamma[[Delta]] ⊩ vctxThunk C : U B; A
where "Gamma [[ Delta ]] ⊩ C : A ; T " := (@vctxTyping _ _ Gamma _  Delta C A T)

with cctxTyping {m: nat} {t: bool} (Gamma: ctx m) :
  forall n, ctx n -> cctx t m n -> comptype -> (if t then valtype else comptype) -> Type :=
| cctxTypingHole A H:
    Gamma [[ Gamma ]] ⊢ cctxHole t m H : A; comptypeif t A H
| cctxTypingLambda n (Delta: ctx n) (C: cctx t (S m) n) A A' B:
    (A .: Gamma) [[Delta]] ⊢ C : B; A' ->
      Gamma [[Delta]] ⊢ cctxLambda C : A → B; A'
| cctxTypingForce n (Delta: ctx n) (C: vctx t m n) B A':
    Gamma [[Delta]] ⊩ C : U B; A' ->
    Gamma [[Delta]] ⊢ cctxForce C : B; A'
| cctxTypingAppL n (Delta: ctx n) (C: cctx t m n) A A' B v:
    Gamma[[Delta]] ⊢ C : A → B; A' ->
    Gamma ⊩ v : A  ->
    Gamma[[Delta]] ⊢ cctxAppL C v : B; A'
| cctxTypingAppR n (Delta: ctx n) c (C: vctx t m n) A A' B :
    Gamma ⊢ c : A → B  ->
    Gamma[[Delta]] ⊩ C : A; A' ->
    Gamma[[Delta]] ⊢ cctxAppR c C : B; A'
| cctxTypingTupleL n (Delta: ctx n) (C: cctx t m n) B1 B2 A c:
    Gamma[[Delta]] ⊢ C : B1; A ->
    Gamma ⊢ c : B2  ->
    Gamma[[Delta]] ⊢ cctxTupleL C c : Pi B1 B2; A
| cctxTypingTupleR n (Delta: ctx n) (C: cctx t m n) B1 B2 A c:
    Gamma ⊢ c : B1  ->
    Gamma[[Delta]] ⊢ C : B2; A ->
    Gamma[[Delta]] ⊢ cctxTupleR c C : Pi B1 B2; A
| cctxTypingRet n (Delta: ctx n) (C: vctx t m n) A A':
    Gamma [[Delta]] ⊩ C : A; A' ->
    Gamma [[Delta]] ⊢ cctxRet C : F A; A'
| cctxTypingLetinL n (Delta: ctx n) (C: cctx t m n) A A' B c:
    Gamma[[Delta]] ⊢ C : F A; A' ->
    A .: Gamma ⊢ c : B  ->
    Gamma[[Delta]] ⊢ cctxLetinL C c : B; A'
| cctxTypingLetinR n (Delta: ctx n) (C: cctx t (S m) n) A A' B c:
    Gamma ⊢ c : F A  ->
    (A .: Gamma)[[Delta]] ⊢ C : B; A' ->
    Gamma[[Delta]] ⊢ cctxLetinR c C : B; A'
| cctxTypingProj n (Delta: ctx n) (C: cctx t m n) A B1 B2 (b: bool):
    Gamma[[Delta]] ⊢ C : Pi B1 B2; A ->
    Gamma[[Delta]] ⊢ cctxProj b C : (if b then B1 else B2); A
| cctxTypingCaseZ n (Delta: ctx n) (C: vctx t m n) A A':
    Gamma[[Delta]] ⊩ C : zero; A' ->
    Gamma[[Delta]] ⊢ cctxCaseZ C : A; A'
| cctxTypingCaseSV n (Delta: ctx n) (C: vctx t m n) A1 A2 A' B c1 c2:
    Gamma[[Delta]] ⊩ C : Sigma A1 A2; A' ->
    A1 .: Gamma ⊢ c1 : B  ->
    A2 .: Gamma ⊢ c2 : B  ->
    Gamma[[Delta]] ⊢ cctxCaseSV C c1 c2 : B; A'
| cctxTypingCaseSL n (Delta: ctx n) (C: cctx t (S m) n) A1 A2 A' B v c2:
    Gamma ⊩ v : Sigma A1 A2  ->
    (A1 .: Gamma)[[Delta]] ⊢ C : B; A' ->
    A2 .: Gamma ⊢ c2 : B  ->
    Gamma[[Delta]] ⊢ cctxCaseSL v C c2 : B; A'
| cctxTypingCaseSR n (Delta: ctx n) (C: cctx t (S m) n) A1 A2 A' B v c1:
    Gamma ⊩ v : Sigma A1 A2  ->
    A1 .: Gamma ⊢ c1 : B  ->
    (A2 .: Gamma)[[Delta]] ⊢ C : B; A' ->
    Gamma[[Delta]] ⊢ cctxCaseSR v c1 C : B; A'
| cctxTypingCasePV n (Delta: ctx n) (C: vctx t m n) A1 A2 A' B c:
    Gamma[[Delta]] ⊩ C : A1 * A2; A' ->
    (A2 .: (A1 .: Gamma)) ⊢ c : B  ->
    Gamma[[Delta]] ⊢ cctxCasePV C c : B; A'
| cctxTypingCasePC n (Delta: ctx n) (C: cctx t (S (S m)) n) A1 A2 A' B v:
    Gamma ⊩ v : A1 * A2  ->
    (A2 .: (A1 .: Gamma))[[Delta]] ⊢ C : B; A' ->
    Gamma[[Delta]] ⊢ cctxCasePC v C : B; A'
where "Gamma [[ Delta ]] ⊢ C : B ; T " := (@cctxTyping _ _ Gamma _ Delta C B T).

Scheme vctx_typing_ind_2 := Minimality for vctxTyping Sort Prop
  with cctx_typing_ind_2  := Minimality for cctxTyping Sort Prop.

Combined Scheme mutind_vctx_cctx_typing from
         vctx_typing_ind_2, cctx_typing_ind_2.

Scheme vctx_typing_ind_3 := Induction for vctxTyping Sort Prop
  with cctx_typing_ind_3  := Induction for cctxTyping Sort Prop.

Combined Scheme mutindt_vctx_cctx_typing from
          vctx_typing_ind_3, cctx_typing_ind_3.

Fixpoint plugvctx {m n k: nat} {t1 t2: bool} (C: vctx t1 m n) :
  (if t1 then vctx t2 n k else cctx t2 n k) -> vctx t2 m k :=

  match C in vctx _ _ n return (if t1 then vctx t2 n k else cctx t2 n k) -> vctx t2 m k  with
  | vctxHole _ _ H =>
    match t1 return (if t1 then True else False) -> (if t1 then vctx t2 m k else cctx t2 m k)  -> vctx t2 m k with
    | true => fun _ v' => v'
    | false => fun f _ => match f with end
    end H
  | vctxPairL C v => fun C' => vctxPairL (plugvctx C C')  v
  | vctxPairR v C => fun C' => vctxPairR v (plugvctx C C')
  | vctxInj b C => fun C' => vctxInj b (plugvctx C C')
  | vctxThunk C => fun C' => vctxThunk (plugcctx C C')
  end

with plugcctx {m n k: nat} {t1 t2: bool} (C: cctx t1 m n) :
(if t1 then vctx t2 n k else cctx t2 n k) -> cctx t2 m k :=
  match C in cctx _ _ n return (if t1 then vctx t2 n k else cctx t2 n k)  -> cctx t2 m k with
  | cctxHole _ _ H =>
    match t1 return (if t1 then False else True) -> (if t1 then vctx t2 m k else cctx t2 m k)  -> cctx t2 m k  with
    | false => fun _ C' => C'
    | true => fun f _ => match f with end
    end H
  | cctxForce C => fun C' => cctxForce (plugvctx C C')
  | cctxLambda C => fun C' => cctxLambda (plugcctx C C')
  | cctxAppL C v => fun C' => cctxAppL (plugcctx C C') v
  | cctxAppR c C => fun C' => cctxAppR c (plugvctx C C')
  | cctxTupleL C c => fun C' => cctxTupleL (plugcctx C C') c
  | cctxTupleR c C => fun C' => cctxTupleR c (plugcctx C C')
  | cctxRet C => fun C' => cctxRet (plugvctx C C')
  | cctxLetinL C c => fun C' => cctxLetinL (plugcctx C C') c
  | cctxLetinR c C => fun C' => cctxLetinR c (plugcctx C C')
  | cctxProj b C => fun C' => cctxProj b (plugcctx C C')
  | cctxCaseZ C => fun C' => cctxCaseZ (plugvctx C C')
  | cctxCaseSV C c1 c2 => fun C' => cctxCaseSV (plugvctx C C') c1 c2
  | cctxCaseSL v C c2 => fun C' => cctxCaseSL v (plugcctx C C') c2
  | cctxCaseSR v c1 C => fun C' => cctxCaseSR v c1 (plugcctx C C')
  | cctxCasePV C c => fun C' => cctxCasePV (plugvctx C C') c
  | cctxCasePC v C => fun C' => cctxCasePC v (plugcctx C C')
  end.
