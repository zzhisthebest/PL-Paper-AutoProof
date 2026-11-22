From Autosubst Require Export Autosubst.

From logrel_ifc.lambda_sec Require Export lang lattice types.

Section lambda_sec_typing.

Context `{SecurityLattice label}.

Inductive subtype : type → type → Prop :=
  | TSubRefl t :
      subtype t t
  | TSubTrans t1 t2 t3 :
      subtype t1 t2 → subtype t2 t3 → subtype t1 t3
  | TArrowSub τ1 τ1' τ2 τ2' ℓₑ1 ℓₑ2 :
      secsubtype τ1' τ1 →
      secsubtype τ2 τ2' →
      ℓₑ2 ⊑ₛ ℓₑ1 →
      subtype (TArrow ℓₑ1 τ1 τ2) (TArrow ℓₑ2 τ1' τ2')
  | TForallSub τ1 τ2 ℓₑ1 ℓₑ2 :
      ℓₑ2 ⊑ₛ ℓₑ1 →
      secsubtype τ1 τ2 →
      subtype (TForall ℓₑ1 τ1) (TForall ℓₑ2 τ2)
  | TLForallSub τ1 τ2 ℓₑ1 ℓₑ2 :
      ℓₑ2 ⊑ₛ ℓₑ1 →
      secsubtype τ1 τ2 →
      subtype (TLForall ℓₑ1 τ1) (TLForall ℓₑ2 τ2)
  | TProdSub τ1 τ1' τ2 τ2' :
      secsubtype τ1 τ1' → secsubtype τ2 τ2' → subtype (TProd τ1 τ2) (TProd τ1' τ2')
  | TSumSub τ1 τ1' τ2 τ2' :
      secsubtype τ1 τ1' → secsubtype τ2 τ2' → subtype (TSum τ1 τ2) (TSum τ1' τ2')

  | TRecSub τ1 τ2 :


      secsubtype τ1.|[TRec τ1/] τ2.|[TRec τ2/] →
      subtype (TRec τ1) (TRec τ2)
  with secsubtype :  sectype → sectype → Prop :=
  | TSubsec (ℓ ℓ' : label_term) (t t' : type) :
      ℓ ⊑ₛ ℓ' → subtype t t' → secsubtype (t @ ℓ) (t' @ ℓ').

Scheme subtype_mut := Induction for subtype Sort Prop
    with secsubtype_mut := Induction for secsubtype Sort Prop.

Notation "t1 '<:' t2" := (subtype t1 t2) (at level 70).

Notation "τ1 '<:ₛ' τ2" := (secsubtype τ1 τ2) (at level 70).

Definition type_flowsto τ ℓ :=
    let: t @ ℓ' := τ in ℓ ⊑ₛ ℓ'.

Notation "τ ↘ ℓ" := (type_flowsto τ ℓ) (at level 70).

Definition binop_type (op : binop) : type :=
    match op with
    | Add | Sub | Mult => TNat
    | Eq | Le | Lt => TBool
  end.

Reserved Notation "Γ # pc ⊢ₜ e : τ" (at level 74, e, τ at next level).

Inductive typed (Γ : list sectype) (pc : label_term) : expr → sectype → Prop :=
  | Unit_typed : Γ # pc ⊢ₜ Unit : TUnit @ ⊥ₛ
  | Bool_typed b :
      Γ # pc ⊢ₜ Bool b : TBool @ ⊥ₛ
  | Nat_typed n :
      Γ # pc ⊢ₜ Nat n : TNat @ ⊥ₛ
  | Var_typed x τ :
      Γ !! x = Some τ →
      Γ # pc ⊢ₜ Var x : τ
  | Lam_typed e ℓₑ τ1 τ2 :
      τ1 :: Γ # ℓₑ ⊢ₜ e : τ2 →
      Γ # pc ⊢ₜ Lam e : (TArrow ℓₑ τ1 τ2) @ ⊥ₛ
  | BinOp_typed e1 e2 op ℓ1 ℓ2 :
      Γ # pc ⊢ₜ e1 : TNat @ ℓ1 →
      Γ # pc ⊢ₜ e2 : TNat @ ℓ2 →
      Γ # pc ⊢ₜ BinOp op e1 e2 : (binop_type op) @ (ℓ1 ⊔ₛ ℓ2)
  | App_typed e1 e2 τ1 τ2 ℓ ℓₑ :
      Γ # pc ⊢ₜ e1 : (TArrow ℓₑ τ1 τ2) @ ℓ →
      Γ # pc ⊢ₜ e2 : τ1 →
      τ2 ↘ ℓ →
      pc ⊔ₛ ℓ ⊑ₛ ℓₑ →
      Γ # pc ⊢ₜ App e1 e2 : τ2
  | LetIn_typed e1 e2 τ1 τ2 :
      Γ # pc ⊢ₜ e1 : τ1 →
      τ1 :: Γ # pc ⊢ₜ e2 : τ2 →
      Γ # pc ⊢ₜ LetIn e1 e2 : τ2
  | Seq_typed e1 e2 τ1 τ2 :
      Γ # pc ⊢ₜ e1 : τ1 →
      Γ # pc ⊢ₜ e2 : τ2 →
      Γ # pc ⊢ₜ Seq e1 e2 : τ2
  | TLam_typed e τ ℓₑ :
      hsubst_sectype (ren (+1)) <$> Γ # ℓₑ ⊢ₜ e : τ →
      Γ # pc ⊢ₜ TLam e : (TForall ℓₑ τ) @ ⊥ₛ
  | TApp_typed e τ t' ℓ ℓₑ :
      pc ⊔ₛ ℓ ⊑ₛ ℓₑ →
      τ.|[t'/] ↘ ℓ →
      Γ # pc ⊢ₜ e : (TForall ℓₑ τ) @ ℓ →
      Γ # pc ⊢ₜ TApp e : τ.|[t'/]
  | TLLam_typed e τ ℓₑ :
      hsubst_label_sectype (ren (+1)) <$> Γ # ℓₑ ⊢ₜ e : τ →
      Γ # pc ⊢ₜ TLLam e : (TLForall ℓₑ τ) @ ⊥ₛ
  | TLApp_typed e τ (ℓ ℓ' ℓₑ : label_term) :
      pc ⊔ₛ ℓ ⊑ₛ ℓₑ.[ℓ'/] →
      τ.|[ℓ'/] ↘ ℓ →
      Γ # pc ⊢ₜ e : (TLForall ℓₑ τ) @ ℓ →
      Γ # pc ⊢ₜ TLApp e : τ.|[ℓ'/]
  | Cond_typed e e1 e2 τ ℓ :
      Γ # pc ⊢ₜ e : TBool @ ℓ →
      Γ # pc ⊔ₛ ℓ ⊢ₜ e1 : τ →
      Γ # pc ⊔ₛ ℓ ⊢ₜ e2 : τ →
      τ ↘ ℓ →
      Γ # pc ⊢ₜ If e e1 e2 : τ
  | Pair_typed e1 e2 τ1 τ2 :
      Γ # pc ⊢ₜ e1 : τ1 →
      Γ # pc ⊢ₜ e2 : τ2 →
      Γ # pc ⊢ₜ Pair e1 e2 : TProd τ1 τ2 @ ⊥ₛ
  | Proj1_typed e τ1 τ2 ℓ :
      Γ # pc ⊢ₜ e : TProd τ1 τ2 @ ℓ →
      τ1 ↘ ℓ →
      Γ # pc ⊢ₜ Proj1 e : τ1
  | Proj2_typed e τ1 τ2 ℓ :
      Γ # pc ⊢ₜ e : TProd τ1 τ2 @ ℓ →
      τ2 ↘ ℓ →
      Γ # pc ⊢ₜ Proj2 e : τ2
  | InjL_typed e τ1 τ2 :
      Γ # pc ⊢ₜ e : τ1 →
      Γ # pc ⊢ₜ InjL e : TSum τ1 τ2 @ ⊥ₛ
  | InjR_typed e τ1 τ2 :
      Γ # pc ⊢ₜ e : τ2 →
      Γ # pc ⊢ₜ InjR e : TSum τ1 τ2 @ ⊥ₛ
  | Case_typed e e1 e2 τ1 τ2 τ ℓ :
      Γ # pc ⊢ₜ e : TSum τ1 τ2 @ ℓ →
       τ1 :: Γ # pc ⊔ₛ ℓ ⊢ₜ e1 : τ →
       τ2 :: Γ # pc ⊔ₛ ℓ ⊢ₜ e2 : τ →
      τ ↘ ℓ →
      Γ # pc ⊢ₜ Case e e1 e2 : τ
  | Alloc_typed e τ :
      Γ # pc ⊢ₜ e : τ →
      τ ↘ pc →
      Γ # pc ⊢ₜ Alloc e : TRef τ @ ⊥ₛ
  | Store_typed e1 e2 τ ℓ :
      Γ # pc ⊢ₜ e1 : TRef τ @ ℓ →
      Γ # pc ⊢ₜ e2 : τ →
      τ ↘ pc ⊔ₛ ℓ →
      Γ # pc ⊢ₜ Store e1 e2 : TUnit @ ⊥ₛ
  | Load_typed e τ τ' ℓ :
      Γ # pc ⊢ₜ e : TRef τ @ ℓ →
      τ <:ₛ τ' →
      τ' ↘ ℓ →
      Γ # pc ⊢ₜ Load e : τ'
  | TPack e τ t :
      Γ # pc ⊢ₜ e : τ.|[t/] →
      Γ # pc ⊢ₜ Pack e : TExist τ @ ⊥ₛ
  | TUnpack e1 e2 τ1 τ2 ℓ :
      τ2 ↘ ℓ →
      Γ # pc ⊢ₜ e1 : TExist τ1 @ ℓ →
      τ1 :: (hsubst_sectype (ren (+1)) <$> Γ) # pc ⊔ₛ ℓ ⊢ₜ e2 : (hsubst_sectype (ren (+1)) τ2) →
      Γ # pc ⊢ₜ Unpack e1 e2 : τ2
  | TFold e τ :
      Γ # pc ⊢ₜ e : τ.|[TRec τ/] →
      Γ # pc ⊢ₜ Fold e : TRec τ @ ⊥ₛ
  | TUnfold e τ ℓ :
      τ.|[TRec τ/] ↘ ℓ →
      Γ # pc ⊢ₜ e : TRec τ @ ℓ →
      Γ # pc ⊢ₜ Unfold e : τ.|[TRec τ/]
  | Sub_typed e τ τ' pc' :
      Γ # pc' ⊢ₜ e : τ' →
      pc ⊑ₛ pc' →
      τ' <:ₛ τ →
      Γ # pc ⊢ₜ e : τ
  where "Γ # pc ⊢ₜ e : τ" := (typed Γ pc e τ).

Fixpoint env_subst (vs : list val) : var → expr :=
    match vs with
    | [] => ids
    | v :: vs' => #v .: env_subst vs'
    end.

End lambda_sec_typing.

Notation "τ ↘ ℓ" := (type_flowsto τ ℓ) (at level 70).

Notation "t1 '<:' t2" := (subtype t1 t2) (at level 70).

Notation "τ1 '<:ₛ' τ2" := (secsubtype τ1 τ2) (at level 70).

Notation "Γ # pc ⊢ₜ e : τ" := (typed Γ pc e τ) (at level 74, e, τ at next level).
