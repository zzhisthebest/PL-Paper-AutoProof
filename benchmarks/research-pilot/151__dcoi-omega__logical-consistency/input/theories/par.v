Require Import imports.

Module Type par_sig
  (Import lattice : Lattice)
  (Import syntax : syntax_sig lattice).

Reserved Infix "⇒" (at level 60, right associativity).

Inductive Par : tm -> tm -> Prop :=
| P_Var i :

  (var_tm i) ⇒ (var_tm i)
| P_Univ n :

  (tUniv n) ⇒ (tUniv n)
| P_Pi ℓ0 A0 A1 B0 B1 :
  (A0 ⇒ A1) ->
  (B0 ⇒ B1) ->

  (tPi ℓ0 A0 B0) ⇒ (tPi ℓ0 A1 B1)
| P_Abs ℓ0 a0 a1 :
  (a0 ⇒ a1) ->

  (tAbs ℓ0 a0) ⇒ (tAbs ℓ0 a1)
| P_App a0 a1 ℓ0 b0 b1 :
  (a0 ⇒ a1) ->
  (b0 ⇒ b1) ->

  (tApp a0 ℓ0 b0) ⇒ (tApp a1 ℓ0 b1)
| P_AppAbs a a0 b0 b1 ℓ0 :
  (a ⇒ a0) ->
  (b0 ⇒ b1) ->

  (tApp (tAbs ℓ0 a) ℓ0 b0) ⇒ (a0 [b1..])

| P_Void :
  tVoid ⇒ tVoid

| P_Absurd a b :
  a ⇒ b ->

  tAbsurd a ⇒ tAbsurd b

| P_Refl :

  tRefl ⇒ tRefl

| P_Eq ℓ0 a0 b0 a1 b1 :
  (a0 ⇒ a1) ->
  (b0 ⇒ b1) ->

  (tEq ℓ0 a0 b0) ⇒ (tEq ℓ0 a1 b1)

| P_J ℓp t0 p0 t1 p1 :
  (t0 ⇒ t1) ->
  (p0 ⇒ p1) ->

  (tJ ℓp t0 p0) ⇒ (tJ ℓp t1 p1)

| P_JRefl ℓp t0 t1 :
  (t0 ⇒ t1) ->

  (tJ ℓp t0 tRefl) ⇒ t1

| P_Sig ℓ A0 A1 B0 B1 :
  (A0 ⇒ A1) ->
  (B0 ⇒ B1) ->

  tSig ℓ A0 B0 ⇒ tSig ℓ A1 B1

| P_Pack ℓ a0 a1 b0 b1 :
  (a0 ⇒ a1) ->
  (b0 ⇒ b1) ->

  (tPack ℓ a0 b0) ⇒ (tPack ℓ a1 b1)

| P_Let ℓ0 ℓ1 a0 b0 a1 b1 :
  a0 ⇒ a1 ->
  b0 ⇒ b1 ->

  tLet ℓ0 ℓ1 a0 b0 ⇒ tLet ℓ0 ℓ1 a1 b1

| P_LetPack ℓ0 ℓ1 a0 b0 c0 a1 b1 c1 :
  a0 ⇒ a1 ->
  b0 ⇒ b1 ->
  c0 ⇒ c1 ->
  tLet ℓ0 ℓ1 (tPack ℓ0 a0 b0) c0 ⇒ c1[b1 .: a1 ..]

| P_Zero :

  tZero ⇒ tZero

| P_Suc a b :
  a ⇒ b ->

  tSuc a ⇒ tSuc b

| P_Ind ℓ a0 a1 b0 b1 c0 c1:
  a0 ⇒ a1 ->
  b0 ⇒ b1 ->
  c0 ⇒ c1 ->

  tInd ℓ a0 b0 c0 ⇒ tInd ℓ a1 b1 c1

| P_IndZero ℓ a0 a1 b:
  a0 ⇒ a1 ->

  tInd ℓ a0 b tZero ⇒ a1
| P_IndSuc ℓ a0 a1 b0 b1 c0 c1 :
  a0 ⇒ a1 ->
  b0 ⇒ b1 ->
  c0 ⇒ c1 ->

  tInd ℓ a0 b0 (tSuc c0) ⇒ b1 [(tInd ℓ a1 b1 c1) .: c1  ..]
| P_Nat :

  tNat ⇒ tNat

| P_TT :

  tTT ⇒ tTT

| P_Seq ℓ a0 a1 b0 b1 :
  a0 ⇒ a1 ->
  b0 ⇒ b1 ->

  tSeq ℓ a0 b0 ⇒ tSeq ℓ a1 b1

| P_SeqTT ℓ b0 b1 :
  b0 ⇒ b1 ->

  tSeq ℓ tTT b0 ⇒ b1

| P_Unit :

  tUnit ⇒ tUnit

where "A ⇒ B" := (Par A B).

Infix "⇒*" := (rtc Par) (at level 60, right associativity).

End par_sig.
