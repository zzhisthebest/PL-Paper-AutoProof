From Autosubst Require Export Autosubst.

From logrel_ifc.lambda_sec Require Export lang lattice.

Section syntactic_flowsto.

Inductive label_term `{SecurityLattice label} :=
  | LVar (x : var)
  | LJoin (l l' : label_term)
  | LLabel (ℓ : label).

Context `{SecurityLattice label}.

Global Instance label_term_ids : Ids label_term := ltac:(derive).
Global Instance label_term_rename : Rename label_term := ltac:(derive).
Global Instance label_term_subst : Subst label_term := ltac:(derive).

Inductive flowsto : label_term → label_term  → Prop :=
  | FRefl l :
      flowsto l l
  | FTrans l1 l2 l3 :
      flowsto l1 l2 →
      flowsto l2 l3 →
      flowsto l1 l3
  | FBottom l :
      flowsto (LLabel ⊥) l
  | FTop l :
      flowsto l (LLabel ⊤)
  | FLabel ℓ1 ℓ2 :
      ℓ1 ⊑ ℓ2 →
      flowsto (LLabel ℓ1) (LLabel ℓ2)
  | FJoin l1 l2 l3 :
      flowsto l1 l3 →
      flowsto l2 l3 →
      flowsto (LJoin l1 l2) l3.

End syntactic_flowsto.

Notation "a ⊑ₛ b" := (flowsto a b) (at level 70) : stdpp_scope.

Infix "⊔ₛ" := (LJoin) (at level 50) : stdpp_scope.

Notation "⊥ₛ" := (LLabel bot) : stdpp_scope.

Notation "⊤ₛ" := (LLabel top) : stdpp_scope.

Section lambda_sec_types.

Context `{SecurityLattice label}.

Inductive type :=
  | TUnit
  | TBool
  | TNat
  | TVar (x : var)
  | TRef (τ : sectype)
  | TArrow (ℓₑ : label_term) (τ1 τ2 : sectype)
  | TProd (τ1 τ2 : sectype)
  | TSum (τ1 τ2 : sectype)
  | TForall (ℓₑ : label_term) (τ : sectype)
  | TLForall (ℓₑ : label_term) (τ : sectype)
  | TExist (τ : sectype)
  | TRec (τ : sectype)
  with sectype :=
  | TSec (ℓ : label_term) (t : type).

Global Instance Ids_type : Ids type := ltac:(derive).
Global Instance Ids_sectype : Ids sectype := λ n, TSec ⊥ₛ TUnit.

Implicit Types t : type.

Implicit Types τ : sectype.

Scheme type_mut := Induction for type Sort Prop
    with sectype_mut := Induction for sectype Sort Prop.

Notation "t @ ℓ" := (TSec ℓ t) (at level 40).

Fixpoint hsubst_label_type (sigma : var → label_term) (t : type) : type :=
    let _ := hsubst_label_sectype : HSubst label_term sectype in
    match t with
    | TUnit
    | TBool | TNat => t
    | TVar x => TVar x
    | TRef τ => TRef (hsubst sigma τ)
    | TArrow ℓ' τ1 τ2 => TArrow ℓ'.[sigma] (hsubst sigma τ1) (hsubst sigma τ2)
    | TProd τ1 τ2 => TProd (hsubst sigma τ1) (hsubst sigma τ2)
    | TSum τ1 τ2 => TSum (hsubst sigma τ1) (hsubst sigma τ2)
    | TForall ℓ τ => TForall ℓ.[sigma] (hsubst sigma τ)
    | TLForall ℓ τ => TLForall ℓ.[up sigma] (hsubst (up sigma) τ)
    | TExist τ => TExist (hsubst sigma τ)
    | TRec τ => TRec (hsubst sigma τ)
    end
  with hsubst_label_sectype (sigma : var → label_term) (τ : sectype) : sectype :=
    let _ := hsubst_label_type : HSubst label_term type in
    match τ with
    | t @ ℓ => (hsubst sigma t) @ ℓ.[sigma]
    end.

Global Instance HSubst_label_type : HSubst label_term type := hsubst_label_type.
Global Instance HSubst_label_sectype : HSubst label_term sectype := hsubst_label_sectype.

Fixpoint rename_type (xi : var → var) (t : type) : type :=
    let _ := rename_sectype : Rename sectype in
    match t with
    | TUnit
    | TBool | TNat => t
    | TVar x => TVar (xi x)
    | TRef τ => TRef (rename xi τ)
    | TArrow ℓ' τ1 τ2 => TArrow ℓ' (rename xi τ1) (rename xi τ2)
    | TProd τ1 τ2 => TProd (rename xi τ1) (rename xi τ2)
    | TSum τ1 τ2 => TSum (rename xi τ1) (rename xi τ2)
    | TForall ℓ τ => TForall ℓ (rename (upren xi) τ)
    | TLForall ℓ τ => TLForall ℓ (rename xi τ)
    | TExist τ => TExist (rename (upren xi) τ)
    | TRec τ => TRec (rename (upren xi) τ)
    end
  with rename_sectype (xi : var → var) (τ : sectype) : sectype :=
    let _ := rename_type : Rename type in
    match τ with
    | t @ ℓ => (rename xi t) @ ℓ
    end.

Global Instance Rename_type : Rename type := rename_type.
Global Instance Rename_sectype : Rename sectype := rename_sectype.

Fixpoint subst_type (sigma : var → type) (t : type) : type :=
    let _ := hsubst_sectype : HSubst type sectype in
    match t with
    | TUnit
    | TBool | TNat => t
    | TVar x => sigma x
    | TRef τ => TRef (hsubst sigma τ)
    | TArrow ℓ' τ1 τ2 => TArrow ℓ' (hsubst sigma τ1) (hsubst sigma τ2)
    | TProd τ1 τ2 => TProd (hsubst sigma τ1) (hsubst sigma τ2)
    | TSum τ1 τ2 => TSum (hsubst sigma τ1) (hsubst sigma τ2)
    | TForall ℓ τ => TForall ℓ (hsubst (up sigma) τ)
    | TLForall ℓ τ => TLForall ℓ (hsubst (sigma >>| ren (+1)) τ)
    | TExist τ => TExist (hsubst (up sigma) τ)
    | TRec τ => TRec (hsubst (up sigma) τ)
    end
  with hsubst_sectype (sigma : var → type) (τ : sectype) : sectype :=
    let _ := subst_type : Subst type in
    match τ with
    | t @ ℓ => (subst sigma t) @ ℓ
    end.

Global Instance Subst_type : Subst type := subst_type.
Global Instance HSubst_type : HSubst type sectype := hsubst_sectype.

End lambda_sec_types.

Notation "τ @ ℓ" := (TSec ℓ τ) (at level 60).
