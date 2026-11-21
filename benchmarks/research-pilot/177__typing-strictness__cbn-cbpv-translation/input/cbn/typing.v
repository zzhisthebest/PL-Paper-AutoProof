Require Export strictness.cbn.syntax.

Require Export strictness.cbpv.typing.

Definition cbnContext n : Type := fin n -> CbnTy n * attrs n.

Definition cbnContext_insert {n} (T : CbnTy n) (γ : attrs n) (Γ : cbnContext n) : cbnContext (S n) :=
    (Lazy T↑ T, Lazy .: γ) .: (fun fn => let '(τ, γ) := Γ fn in (Lazy T↑ τ, Lazy .: γ)).

Inductive cbnWt {n} (γ : attrs n) (Γ : cbnContext n) : Term n -> CbnTy n -> Prop :=
  | CBN_T_Var i A γ' :
    (A, γ') = Γ i ->
    γ = (γ' <- Strict @ i) ->

    cbnWt γ Γ (tVar i) A

  | CBN_T_Unit :
    γ = lazyvector ->

    cbnWt γ Γ tUnit TUnit

  | CBN_T_Let q γ1 t1 t2 T1 T2 T :
    cbnWt γ1 Γ t1 T1 ->
    cbnWt (q .: γ) (cbnContext_insert T1 γ1 Γ) t2 T2 ->
    T = down_cbnTy T2 ->

    cbnWt γ Γ (tLet t1 t2) T

  | CBN_T_Pair γ1 γ2 t1 t2 T1 T2 :
    cbnWt γ1 Γ t1 T1 ->
    cbnWt γ2 Γ t2 T2 ->
    γ = lazyvector ->

    cbnWt γ Γ (tPair t1 t2) (TProd γ1 T1 γ2 T2)

  | CBN_T_Inl γ' γ'' t1 T1 T2 :
    cbnWt γ' Γ t1 T1 ->
    γ = lazyvector ->

    cbnWt γ Γ (tInl t1) (TSum γ' T1 γ'' T2)

  | CBN_T_Inr γ' γ'' t2 T1 T2 :
    cbnWt γ' Γ t2 T2 ->
    γ = lazyvector ->

    cbnWt γ Γ (tInr t2) (TSum γ'' T1 γ' T2)

  | CBN_T_Seq t1 t2 T γ1 γ2 :
    cbnWt γ1 Γ t1 TUnit ->
    cbnWt γ2 Γ t2 T ->
    γ = γ1 γ+ γ2 ->

    cbnWt γ Γ (tSeq t1 t2) T

  | CBN_T_Split t1 t2 q1 q2 γ1 γ2 γ1' γ2' T1 T2 T T':
    cbnWt γ1 Γ t1 (TProd γ1' T1 γ2' T2) ->
    cbnWt (q1 .: (q2 .: γ2))
      (cbnContext_insert (Lazy T↑ T1) (Lazy .: γ1') (cbnContext_insert T2 γ2' Γ)) t2 T' ->
    γ = γ1 γ+ γ2 ->
    T = down_cbnTy (down_cbnTy T') ->

    cbnWt γ Γ (tSplit t1 t2) T

  | CBN_T_Case t1 t2 t3 q1 q2 γ1 γ2 γ1' γ2' TL1 TR1 T T2 T3:
    cbnWt γ1 Γ t1 (TSum γ1' TL1 γ2' TR1) ->
    cbnWt (q1 .: γ2) (cbnContext_insert TL1 γ1' Γ) t2 T2 ->
    cbnWt (q2 .: γ2) (cbnContext_insert TR1 γ2' Γ) t3 T3 ->
    γ = γ1 γ+ γ2 ->
    T = down_cbnTy T2 ->
    T = down_cbnTy T3 ->

    cbnWt γ Γ (tCase t1 t2 t3) T

  | CBN_T_Abs q γInput γ' t T1 T2 :
    cbnWt (q .: γ') (cbnContext_insert T1 γInput Γ) t T2 ->
    γ = lazyvector ->

    cbnWt γ Γ (tAbs t) (TArrow γInput q γ' T1 T2)

  | CBN_T_App t1 t2 q γ1 γInput γ3 T1 T2 T2' :
    cbnWt γ1 Γ t1 (TArrow γInput q γ3 T1 T2') ->
    cbnWt γInput Γ t2 T1 ->
    γ = γ1 γ+ γ3 ->
    T2 = down_cbnTy T2' ->

    cbnWt γ Γ (tApp t1 t2) T2

  | CBN_T_Sub γ' t T :
    cbnWt γ' Γ t T ->
    γ γ<= γ' ->

    cbnWt γ Γ (tSub t) T
.
