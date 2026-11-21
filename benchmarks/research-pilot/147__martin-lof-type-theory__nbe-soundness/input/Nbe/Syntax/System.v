Require Import Nbe.Utils.Notations.

Set Implicit Arguments.

Require Import Nbe.Syntax.Def.

Inductive WfCxt : Cxt -> Prop :=

| EMPTY:
  nil |--

| EXT : forall Gamma A,
  Gamma    |-- ->
  Gamma    |-- A ->
  Gamma,,A |--

where "Gamma |--" := (WfCxt Gamma)


with WfCxtEq : Cxt -> Cxt -> Prop :=

| EQ_CXT_REFL: forall Gamma,
  Gamma |-- ->
  |-- {Gamma} === {Gamma}

| EQ_CXT_EXT: forall Gamma Delta A B,
  |-- {Gamma} === {Delta} ->
  Gamma |-- A ->
  Delta |-- B ->
  Gamma |-- A === B ->
  |-- {Gamma,,A} === {Delta,,B}
where "|-- { Gamma } === { Delta } " := (WfCxtEq Gamma Delta)





with WfTp : Cxt -> Tm -> Prop :=

| UNIV_E : forall T Gamma,
  Gamma |-- T : TmUniv ->
  Gamma |-- T

| FUN_F: forall Gamma A B,
  Gamma    |-- A ->
  Gamma,,A |-- B ->
  Gamma    |-- TmFun A B

| SB_F: forall Gamma Delta A S,
  Gamma |-- [S] : Delta ->
  Delta |-- A ->
  Gamma |-- TmSb A S

| UNIV_F: forall Gamma,
  Gamma |-- ->
  Gamma |-- TmUniv

where "Gamma |-- A" := (WfTp Gamma A)




with WtTm : Cxt -> Tm -> Tm -> Prop :=

| UNIV_NAT_F: forall Gamma,
  Gamma |-- ->
  Gamma |-- TmNat : TmUniv

| UNIV_EMPTY_F: forall Gamma,
  Gamma |-- ->
  Gamma |-- TmEmpty : TmUniv

| UNIV_UNIT_F: forall Gamma,
  Gamma |-- ->
  Gamma |-- TmUnit : TmUniv

| UNIV_FUN_F: forall Gamma A B,
  Gamma    |-- A : TmUniv ->
  Gamma,,A |-- B : TmUniv ->
  Gamma    |-- TmFun A B : TmUniv


| HYP: forall Gamma T,
  Gamma ,, T |-- ->
  Gamma ,, T |-- TmVar : TmSb T Sup

| FUN_E: forall Gamma M N A B,
  Gamma |-- M : TmFun A B ->
  Gamma |-- N : A ->
  Gamma,, A |-- B ->
  Gamma |-- TmApp M N : TmSb B (Ssing N)

| FUN_I: forall Gamma M A B,
  Gamma    |-- A ->
  Gamma,,A |-- M : B ->
  Gamma    |-- TmAbs A M : TmFun A B

| N0: forall Gamma,
  Gamma |-- ->
  Gamma |-- Tm0 : TmNat

| NS: forall Gamma n,
  Gamma |-- n : TmNat ->
  Gamma |-- TmS n : TmNat

| SB: forall Gamma M A S Delta,
  Gamma |-- [S] : Delta ->
  Delta |-- M : A ->
  Gamma |-- (TmSb M S) : (TmSb A S)

| UNIT: forall Gamma,
  Gamma |-- ->
  Gamma |-- Tm1 : TmUnit

| CONV: forall Gamma t A B,
  Gamma |-- t : A ->
  Gamma |-- A === B ->
  Gamma |-- t : B

| EMPTY_E: forall Gamma A,
  Gamma |-- A ->
  Gamma |-- TmAbsurd A : TmArr TmEmpty A

where "Gamma |-- e : T" := (WtTm Gamma e T)





with WtSb : Cxt -> Sb -> Cxt -> Prop :=

| SID: forall Gamma,
  Gamma |-- ->
  Gamma |-- [Sid] : Gamma

| SUP: forall Gamma A,
  Gamma |-- A ->
  Gamma,,A |-- [Sup] : Gamma

| SSEQ: forall Gamma__0 Gamma__1 Gamma__2 S__1 S__2,
  Gamma__0 |-- [S__2] : Gamma__1 ->
  Gamma__1 |-- [S__1] : Gamma__2 ->
  Gamma__0 |-- [Sseq S__1 S__2] : Gamma__2

| SEXT: forall Gamma S Delta M A,
  Gamma |-- [S] : Delta ->
  Delta |-- A ->
  Gamma |-- M : TmSb A S ->
  Gamma |-- [Sext S M] : (Delta ,, A)

| SB_CONV: forall Gamma S Delta Psi,
  Gamma |-- [S] : Psi ->
  |-- {Psi} === {Delta} ->
  Gamma |-- [S] : Delta

where "Gamma |-- [ e ] : T" := (WtSb Gamma e T)




with WtTpEq : Cxt -> Tm -> Tm -> Prop :=

| EQ_TP_REFL: forall Gamma A,
  Gamma |-- A ->
  Gamma |-- A === A

| EQ_TP_SYM:  forall Gamma A B,
  Gamma |-- A === B ->
  Gamma |-- B === A

| EQ_TP_TRANS: forall Gamma A B C,
  Gamma |-- A === B ->
  Gamma |-- B === C ->
  Gamma |-- A === C






| EQ_TP_UNIV_ELEM: forall Gamma A B,
  Gamma |-- A === B : TmUniv ->
  Gamma |-- A === B






| EQ_TP_CONG_FUN: forall Gamma A A' B B',
  Gamma     |-- A === A' ->
  Gamma,,A  |-- B === B' ->
  Gamma |-- TmFun A B === TmFun A' B'

| EQ_TP_CONG_SB: forall Gamma Delta A1 A2 S1 S2,
  Gamma |-- [S1] === [S2] : Delta ->
  Delta |-- A1 === A2 ->
  Gamma |-- TmSb A1 S1 === TmSb A2 S2






| EQ_TP_SBSEQ: forall Gamma S1 S2 GammaS1 GammaS2 A,
  Gamma |-- [S1] : GammaS1 ->
  GammaS1 |-- [S2] : GammaS2 ->
  GammaS2 |-- A ->
  Gamma |-- TmSb (TmSb A S2) S1 === TmSb A (Sseq S2 S1)

| EQ_TP_SB_UNIV: forall Gamma Delta S,
  Gamma |-- [S] : Delta ->
  Gamma |-- TmSb TmUniv S === TmUniv

| EQ_TP_SB_FUN: forall Gamma Delta S A B,
  Gamma |-- [S] : Delta ->
  Delta |-- A ->
  Delta,,A |-- B ->
  Gamma |-- TmSb (TmFun A B) S === TmFun (TmSb A S) (TmSb B (Sext (Sseq S Sup) TmVar))

| EQ_TP_SBID: forall Gamma A,
  Gamma |-- A ->
  Gamma |-- (TmSb A Sid) === A

where "Gamma |-- A === B" := (WtTpEq Gamma A B)





with WtTmEq : Cxt -> Tm -> Tm -> Tm -> Prop :=

| EQ_REFL: forall Gamma M A,
  Gamma |-- M : A ->
  Gamma |-- M === M : A

| EQ_SYM:  forall Gamma M1 M2 A,
  Gamma |-- M1 === M2 : A ->
  Gamma |-- M2 === M1 : A

| EQ_TRANS: forall Gamma M1 M2 M3 A,
  Gamma |-- M1 === M2 : A ->
  Gamma |-- M2 === M3 : A ->
  Gamma |-- M1 === M3 : A






| EQ_UNIV_SB_NAT: forall Gamma Delta S,
  Gamma |-- [S] : Delta ->
  Gamma |-- TmSb TmNat S === TmNat : TmUniv

| EQ_UNIV_SB_EMPTY: forall Gamma Delta S,
  Gamma |-- [S] : Delta ->
  Gamma |-- TmSb TmEmpty S === TmEmpty : TmUniv

| EQ_UNIV_SB_UNIT: forall Gamma Delta S,
  Gamma |-- [S] : Delta ->
  Gamma |-- TmSb TmUnit S === TmUnit : TmUniv

| EQ_UNIV_SB_FUN: forall Gamma Delta S A B,
  Gamma |-- [S] : Delta ->
  Delta |-- A : TmUniv ->
  Delta,,A |-- B : TmUniv ->
  Gamma |-- TmSb (TmFun A B) S === TmFun (TmSb A S) (TmSb B (Sext (Sseq S Sup) TmVar)) : TmUniv

| EQ_UNIV_CONG_FUN: forall Gamma A A' B B',
  Gamma     |-- A === A' : TmUniv ->
  Gamma,,A  |-- B === B' : TmUniv ->
  Gamma |-- TmFun A B === TmFun A' B' : TmUniv






| EQ_CONV: forall Gamma M1 M2 A B,
  Gamma |-- M1 === M2 : A ->
  Gamma |-- A === B ->
  Gamma |-- M1 === M2 : B

| EQ_CONG_FUN_I: forall Gamma M1 M2 A1 A2 B,
  Gamma,,A1 |-- M1 === M2 : B ->
  Gamma     |-- A1 === A2 ->
  Gamma    |-- TmAbs A1 M1 === TmAbs A2 M2 : TmFun A1 B

| EQ_CONG_FUN_E: forall Gamma M1 N1 M2 N2 A B,
  Gamma |-- M1 === M2 : TmFun A B ->
  Gamma |-- N1 === N2 : A ->
  Gamma |-- TmApp M1 N1 === TmApp M2 N2 : TmSb B (Ssing N1)

| EQ_CONG_SB: forall Gamma M1 M2 A S1 S2 GammaS,
  Gamma |-- [S1] === [S2] : GammaS ->
  GammaS |-- M1 === M2 : A ->
  Gamma |-- TmSb M1 S1 === TmSb M2 S2 : TmSb A S1

| EQ_CONG_ABSURD: forall Gamma A1 A2,
  Gamma |-- A1 === A2 ->
  Gamma |-- TmAbsurd A1 === TmAbsurd A2 : TmArr TmEmpty A1

| EQ_CONG_S: forall Gamma n1 n2,
  Gamma |-- n1 === n2 : TmNat ->
  Gamma |-- TmS n1 === TmS n2 : TmNat






| EQ_FUN_Beta: forall Gamma M N A B,
  Gamma,,A |-- M : B  ->
  Gamma |-- N : A ->
  Gamma |-- TmApp (TmAbs A M) N === TmSb M (Ssing N) : TmSb B (Ssing N)

| EQ_SBVAR: forall Gamma S Delta M A,
  Gamma |-- [S] : Delta ->
  Delta |-- A ->
  Gamma |-- M : TmSb A S ->
  Gamma |-- (TmSb TmVar (Sext S M)) === M : TmSb A S

| EQ_SBID: forall Gamma M A,
  Gamma |-- M : A ->
  Gamma |-- (TmSb M Sid) === M : A






| EQ_SBAPP: forall Gamma S Delta M N A B,
  Gamma |-- [S] : Delta ->
  Delta |-- M : TmFun A B ->
  Delta |-- N : A ->
  Gamma |-- TmSb (TmApp M N) S === TmApp (TmSb M S) (TmSb N S) : TmSb B (Sext S (TmSb N S))

| EQ_SBABS: forall Gamma S Delta M A B,
  Gamma |-- [S] : Delta ->
  Delta,,A |-- M : B ->
  Gamma |-- TmSb (TmAbs A M) S === TmAbs (TmSb A S) (TmSb M (Sext (Sseq S Sup) TmVar)) : TmFun (TmSb A S) (TmSb B (Sext (Sseq S Sup) TmVar))

| EQ_SBUNIT: forall Gamma S Delta,
  Gamma |-- [S] : Delta ->
  Gamma |-- TmSb Tm1 S === Tm1 : TmUnit

| EQ_SBNAT0: forall Gamma S Delta,
  Gamma |-- [S] : Delta ->
  Gamma |-- TmSb Tm0 S === Tm0 : TmNat

| EQ_SBNATS: forall Gamma S n Delta,
  Gamma |-- [S] : Delta ->
  Delta |-- n : TmNat ->
  Gamma |-- TmSb (TmS n) S === TmS (TmSb n S) : TmNat

| EQ_SBABSURD: forall Gamma S Delta A,
  Gamma |-- [S] : Delta ->
  Delta |-- A ->
  Gamma |-- TmSb (TmAbsurd A) S === TmAbsurd (TmSb A S) : TmArr TmEmpty (TmSb A S)

| EQ_SBSEQ: forall Gamma S1 S2 GammaS1 GammaS2 M A,
  Gamma |-- [S1] : GammaS1 ->
  GammaS1 |-- [S2] : GammaS2 ->
  GammaS2 |-- M :  A ->
  Gamma |-- TmSb (TmSb M S2) S1 === TmSb M (Sseq S2 S1) : TmSb (TmSb A S2) S1







| EQ_FUN_Eta: forall Gamma M A B,
  Gamma |-- M : TmFun A B ->
  Gamma |-- M === TmAbs A (TmApp (TmSb M Sup) TmVar) : TmFun A B

| EQ_Unit_Eta: forall Gamma M,
  Gamma |-- M : TmUnit ->
  Gamma |-- M === Tm1 : TmUnit

where "Gamma |-- e1 === e2 : T" := (WtTmEq Gamma e1 e2 T)






with WtSbEq: Cxt -> Sb -> Sb -> Cxt -> Prop :=

| EQ_SB_REFL: forall Gamma S Delta,
  Gamma |-- [S] : Delta ->
  Gamma |-- [S] === [S] : Delta

| EQ_SB_SYM:  forall Gamma S1 S2 Delta,
  Gamma |-- [S1] === [S2] : Delta ->
  Gamma |-- [S2] === [S1] : Delta

| EQ_SB_TRANS: forall Gamma S1 S2 S3 Delta,
  Gamma |-- [S1] === [S2] : Delta ->
  Gamma |-- [S2] === [S3] : Delta ->
  Gamma |-- [S1] === [S3] : Delta

| EQ_SB_CONV: forall Gamma S1 S2 Delta Psi,
  Gamma |-- [S1] === [S2] : Psi ->
  |-- {Psi} === {Delta} ->
  Gamma |-- [S1] === [S2] : Delta







| EQ_SB_CONG_SSEQ: forall Gamma S1 S2 U1 U2 GammaS1 GammaS2,
  Gamma   |-- [S2] === [U2] : GammaS1 ->
  GammaS1 |-- [S1] === [U1] : GammaS2 ->
  Gamma   |-- [Sseq S1 S2] === [Sseq U1 U2] : GammaS2

| EQ_SB_CONG_SEXT: forall Gamma S1 S2 Delta M1 M2 A,
  Gamma |-- [S1] === [S2] : Delta ->
  Delta |-- A ->
  Gamma |-- M1 === M2 : TmSb A S1  ->
  Gamma |-- [Sext S1 M1] === [Sext S2 M2] : Delta ,, A






| EQ_SB_SEXT: forall Gamma S1 S2 GammaS1 GammaS2 M A,
  Gamma |-- [S1] : GammaS1 ->
  GammaS1 |-- [Sext S2 M] : GammaS2,,A ->
  Gamma |-- [Sseq (Sext S2 M) S1] === [Sext (Sseq S2 S1) (TmSb M S1)] : (GammaS2,,A)

| EQ_SB_SUP: forall Gamma S M A Delta,
  Gamma |-- [S] : Delta ->
  Delta |-- A ->
  Gamma |-- M : TmSb A S ->
  Gamma |-- [Sseq Sup (Sext S M)] === [S] : Delta






| EQ_SB_SIDSUP: forall Gamma A,
  Gamma |-- A ->
  Gamma,,A |-- [Sid] === [Sext Sup TmVar] : Gamma,,A

| EQ_SB_SIDL: forall Gamma S GammaS,
  Gamma |-- [S] : GammaS ->
  Gamma |-- [Sseq Sid S] === [S] : GammaS

| EQ_SB_SIDR: forall Gamma S GammaS,
  Gamma |-- [S] : GammaS ->
  Gamma |-- [Sseq S Sid] === [S] : GammaS

| EQ_SB_COMM: forall Gamma S1 S2 S3 GammaS1 GammaS2 GammaS3,
  Gamma   |-- [S3] : GammaS1 ->
  GammaS1 |-- [S2] : GammaS2 ->
  GammaS2 |-- [S1] : GammaS3 ->
  Gamma   |-- [Sseq (Sseq S1 S2) S3] === [Sseq S1 (Sseq S2 S3)] : GammaS3

where "Gamma |-- [ e1 ] === [ e2 ] : T" := (WtSbEq Gamma e1 e2 T)
.

Scheme WfCxt_dind   := Induction for WfCxt Sort Prop
 with  WfTp_dind    := Induction for WfTp Sort Prop
 with  WtTm_dind    := Induction for WtTm Sort Prop
 with  WtSb_dind    := Induction for WtSb Sort Prop
 with  WfCxtEq_dind  := Induction for WfCxtEq Sort Prop
 with  WtTpEq_dind  := Induction for WtTpEq Sort Prop
 with  WtTmEq_dind  := Induction for WtTmEq Sort Prop
 with  WtSbEq_dind  := Induction for WtSbEq Sort Prop
.

Combined Scheme System_ind from WfCxt_dind, WfTp_dind, WtTm_dind, WtSb_dind, WfCxtEq_dind, WtTpEq_dind, WtTmEq_dind, WtSbEq_dind.
