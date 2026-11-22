Require Export strictness.cbpv.syntax.

Require Import Psatz.

From Coq Require Import FunctionalExtensionality.

Definition context n : Type := fin n -> ValTy n.

Definition ctx_insert {n} (A : ValTy n) (Γ : context n) : context (S n) :=
    (Lazy A↑ A) .: (fun fn => Lazy A↑ (Γ fn)).

Inductive VWt {n} (γ : attrs n) (Γ : context n) : Val n -> ValTy n -> Prop :=
  | T_Var i A :
    A = Γ i ->
    γ = (lazyvector <- Strict @ i) ->

    VWt γ Γ (vVar i) A

  | T_Unit :
    γ = lazyvector ->

    VWt γ Γ vUnit VUnit

  | T_Thunk γ' M B :
    CWt γ' Γ M B ->
    γ = lazyvector ->

    VWt γ Γ (vThunk M) (VThunk γ' B)

  | T_Pair γ1 γ2 V1 V2 A1 A2 :
    VWt γ1 Γ V1 A1 ->
    VWt γ2 Γ V2 A2 ->
    γ = γ1 γ+ γ2 ->

    VWt γ Γ (vPair V1 V2) (VProd A1 A2)

  | T_Inl V1 A1 A2 :
    VWt γ Γ V1 A1 ->

    VWt γ Γ (vInl V1) (VSum A1 A2)

  | T_Inr V2 A1 A2 :
    VWt γ Γ V2 A2 ->

    VWt γ Γ (vInr V2) (VSum A1 A2)

with CWt {n} (γ : attrs n) (Γ : context n) : Comp n -> CompTy n -> Prop :=
  | T_Ret V A :
    VWt γ Γ V A ->

    CWt γ Γ (cRet V) (CF A)

  | T_Let q M M' A B B' γ1 γ2:
    CWt γ1 Γ M (CF A) ->
    CWt (q .: γ2) (ctx_insert A Γ) M' B' ->
    γ = γ1 γ+ γ2 ->
    B = (down_compTy_until B' n (Nat.le_succ_diag_r n)) ->

    CWt γ Γ (cLet M M') B

  | T_Force V B γ1 γ2 :
    VWt γ1 Γ V (VThunk γ2 B) ->
    γ = γ1 γ+ γ2 ->

    CWt γ Γ (cForce V) B

  | T_Seq V M B γ1 γ2 :
    VWt γ1 Γ V VUnit ->
    CWt γ2 Γ M B ->
    γ = γ1 γ+ γ2 ->

    CWt γ Γ (cSeq V M) B

  | T_Split q1 q2 V M γ1 γ2 A1 A2 B B':
    VWt γ1 Γ V (VProd A1 A2) ->
    CWt (q1 .: (q2 .: γ2)) (ctx_insert (Lazy A↑ A1) (ctx_insert A2 Γ)) M B' ->
    γ = γ1 γ+ γ2 ->
    B = (down_compTy_until B' n (le_succ_succ_diag_r n)) ->

    CWt γ Γ (cSplit V M) B

  | T_Case q1 q2 V M1 M2 γ1 γ2 A1 A2 B B1 B2:
    VWt γ1 Γ V (VSum A1 A2) ->
    CWt (q1 .: γ2) (ctx_insert A1 Γ) M1 B1 ->
    CWt (q2 .: γ2) (ctx_insert A2 Γ) M2 B2 ->
    γ = γ1 γ+ γ2 ->
    B = (down_compTy_until B1 n (Nat.le_succ_diag_r n)) ->
    B = (down_compTy_until B2 n (Nat.le_succ_diag_r n)) ->

    CWt γ Γ (cCase V M1 M2) B

  | T_Abs q M A B B' :
    CWt (q .: γ) (ctx_insert A Γ) M B' ->
    B = (down_compTy_until B' n (Nat.le_succ_diag_r n)) ->

    CWt γ Γ (cAbs M) (CAbs q A B)

  | T_App M q V γ1 γ2 A B:
    CWt γ1 Γ M (CAbs q A B) ->
    VWt γ2 Γ V A ->
    γ = γ1 γ+ γ2 ->

    CWt γ Γ (cApp M V) B

  | T_CSub M γ' B:
    CWt γ' Γ M B ->
    γ γ<= γ' ->

    CWt γ Γ (cSub M) B
.

Scheme VWt_ind' := Induction for VWt Sort Prop
    with CWt_ind' := Induction for CWt Sort Prop.

Combined Scheme Wt_mutual from VWt_ind', CWt_ind'.
