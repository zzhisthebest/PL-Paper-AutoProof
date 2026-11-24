Require Import strictness.cbpv.typing.

Require Export strictness.cbn.typing.

Fixpoint translateType {n} (T : CbnTy n) : CompTy n * attrs n :=
    match T with
    | TUnit => (CF VUnit, lazyvector)
    | TSum γ1' T1 γ2' T2 =>
        let '(A1, γ1) := translateType T1 in
        let '(A2, γ2) := translateType T2 in
        (CF (VSum (VThunk (γ1' γ+ γ1) A1) (VThunk (γ2' γ+ γ2) A2)), lazyvector)
    | TProd γ1 T1 γ2 T2 =>
        let '(A1, γ1') := translateType T1 in
        let '(A2, γ2') := translateType T2 in
        (CF (VProd (VThunk (γ1 γ+ γ1') A1) (VThunk (γ2 γ+ γ2') A2)), lazyvector)
    | TArrow γInput q γ T1 T2 =>
        let '(A, γ1') := translateType T1 in
        let '(B, γ2') := translateType T2 in
        (CAbs (q C+ γ2' None) (VThunk (γInput γ+ γ1') A) (down_ty B), γ γ+ (γ↓ γ2'))
    end.

Definition translateContext {n} (Γ : cbnContext n) : context n :=
    fun (i : fin n) =>
        let '(τ, γ) := (Γ i) in
        let '(B, γ') := translateType τ in
        VThunk (γ γ+ γ') B.

Fixpoint translateTerm {n} (e : Term n) : Comp n :=
    match e with
    | tVar i => cForce (vVar i)
    | tAbs e => cAbs (translateTerm e)
    | tApp e1 e2 =>
        cApp (translateTerm e1) (vThunk (translateTerm e2))
    | tLet t1 t2 =>
        cLet (cRet (vThunk (translateTerm t1))) (translateTerm t2)
    | tUnit => cRet vUnit
    | tSeq e1 e2 =>
        cLet
            (translateTerm e1)
            (cSeq (vVar var_zero) ((ren_Comp shift) (translateTerm e2)))
    | tPair e1 e2 =>
        cRet (vPair (vThunk (translateTerm e1)) (vThunk (translateTerm e2)))
    | tInl e => cRet (vInl (vThunk (translateTerm e)))
    | tInr e => cRet (vInr (vThunk (translateTerm e)))
    | tSplit e1 e2 =>
        cLet
            (translateTerm e1)
            (cSplit
                (vVar var_zero)
                ((ren_Comp up2_ren') (translateTerm e2)))
    | tCase e e1 e2 =>
        cLet (translateTerm e)
            (cCase (vVar var_zero)
                ((ren_Comp up_ren') (translateTerm e1))
                ((ren_Comp up_ren') (translateTerm e2)))
    | tSub e => cSub (translateTerm e)
    end.

Theorem translation_correct_returner :
    forall n (γ : attrs n) (Γ : cbnContext n) e T A γ',
    cbnWt γ Γ e T ->
    (CF A, γ') = translateType T ->
    CWt γ (translateContext Γ) (translateTerm e) (CF A).
