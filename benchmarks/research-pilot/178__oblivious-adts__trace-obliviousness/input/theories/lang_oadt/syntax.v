From oadt Require Import lang_oadt.base.

Implicit Types (b : bool) (x X y Y : atom) (L : aset).

Open Scope type_scope.

Notation olabel := bool (only parsing).

Notation LObliv := true (only parsing).

Notation LPub := false (only parsing).

Notation llabel := bool (only parsing).

Notation LLeak := true (only parsing).

Notation LSafe := false (only parsing).

Inductive expr :=

| EBVar (k : nat)

| EFVar (x : atom)

| EGVar (x : atom)

| EUnitT

| EBool (l : olabel)
| EProd (τ1 τ2 : expr)

| ESum (l : olabel) (τ1 τ2 : expr)

| EPi (l : llabel) (τ1 τ2: expr)

| EUnitV
| ELit (b : bool)

| EAbs (l : llabel) (τ e : expr)

| EApp (e1 e2 : expr)

| ELet (e1 e2 : expr)

| EIte (l : olabel) (e0 e1 e2 : expr)

| EPair (e1 e2 : expr)
| EProj (b : bool) (e : expr)

| EInj (l : olabel) (b : bool) (τ e : expr)

| ECase (l : olabel) (e0 : expr) (e1 : expr) (e2 : expr)

| EFold (X : atom) (e : expr)
| EUnfold (X : atom) (e : expr)

| ESec (e : expr)

| ETape (e : expr)

| EMux (e0 e1 e2 : expr)

| EBoxedLit (b : bool)
| EBoxedInj (b : bool) (τ e : expr)
.

Definition lexpr := (llabel * expr).

Definition lexpr_label : lexpr -> llabel := fst.

Arguments lexpr_label /.

Definition lexpr_expr : lexpr -> expr := snd.

Arguments lexpr_expr /.

Variant gdef :=
| DADT (e : expr)
| DFun (T : lexpr) (e : expr)
| DOADT (τ e : expr)
.

Notation gctx := (amap gdef).

Notation program := (gctx * expr).

Module expr_notations.

Coercion ELit : bool >-> expr.

Coercion lexpr_expr : lexpr >-> expr.

Notation "<{ e }>" := e (e custom oadt at level 99).

Notation "',(' e ')'" := e (in custom oadt at level 0,
                               e constr at level 0).

Notation "( x )" := x (in custom oadt, x at level 99).

Notation "x" := x (in custom oadt at level 0, x constr at level 0).

Notation "'bvar' x" := (EBVar x) (in custom oadt at level 0, x constr at level 0).

Notation "'fvar' x" := (EFVar x) (in custom oadt at level 0, x constr at level 0,
                                     only parsing).

Notation "'gvar' x" := (EGVar x) (in custom oadt at level 0, x constr at level 0).

Notation "'lit' b" := (ELit b) (in custom oadt at level 0, b constr at level 0,
                                   only parsing).

Notation "'𝟙'" := EUnitT (in custom oadt at level 0).

Notation "'Unit'" := EUnitT (in custom oadt at level 0, only parsing).

Notation "'𝔹{' l '}'" := (EBool l) (in custom oadt at level 0,
                                       l constr at level 0,
                                       format "'𝔹{' l '}'").

Notation "'𝔹'" := (EBool LPub) (in custom oadt at level 0).

Notation "'Bool'" := (EBool LPub) (in custom oadt at level 0, only parsing).

Notation "'~𝔹'" := (EBool LObliv) (in custom oadt at level 0).

Notation "'~Bool'" := (EBool LObliv) (in custom oadt at level 0, only parsing).

Notation "τ1 * τ2" := (EProd τ1 τ2) (in custom oadt at level 3,
                                        τ1 custom oadt,
                                        τ2 custom oadt at level 0).

Notation "τ1 '+{' l '}' τ2" := (ESum l τ1 τ2) (in custom oadt at level 4,
                                                  l constr at level 0,
                                                  left associativity,
                                                  format "τ1  '+{' l '}'  τ2").

Notation "τ1 + τ2" := (ESum LPub τ1 τ2) (in custom oadt at level 4,
                                            left associativity).

Notation "τ1 ~+ τ2" := (ESum LObliv τ1 τ2) (in custom oadt at level 4,
                                               left associativity).

Notation "'Π' :{ l } τ1 , τ2" := (EPi l τ1 τ2)
                                   (in custom oadt at level 50,
                                       right associativity,
                                       format "Π :{ l } τ1 ,  τ2").

Notation "'Π' : τ1 , τ2" := (EPi LSafe τ1 τ2)
                              (in custom oadt at level 50,
                                  right associativity,
                                  format "Π : τ1 ,  τ2").

Notation "'Π' ~: τ1 , τ2" := (EPi LLeak τ1 τ2)
                               (in custom oadt at level 50,
                                   right associativity,
                                   format "Π ~: τ1 ,  τ2").

Notation "\ :{ l } τ '=>' e" := (EAbs l τ e)
                                  (in custom oadt at level 90,
                                      τ custom oadt at level 99,
                                      e custom oadt at level 99,
                                      left associativity,
                                      format "\ :{ l } τ  =>  e").

Notation "\ : τ '=>' e" := (EAbs LSafe τ e)
                             (in custom oadt at level 90,
                                 τ custom oadt at level 99,
                                 e custom oadt at level 99,
                                 left associativity,
                                 format "\ : τ  =>  e").

Notation "\ ~: τ '=>' e" := (EAbs LLeak τ e)
                              (in custom oadt at level 90,
                                  τ custom oadt at level 99,
                                  e custom oadt at level 99,
                                  left associativity,
                                  format "\ ~: τ  =>  e").

Notation "e1 e2" := (EApp e1 e2) (in custom oadt at level 2, left associativity).

Notation "()" := EUnitV (in custom oadt at level 0).

Notation "( x , y , .. , z )" := (EPair .. (EPair x y) .. z)
                                   (in custom oadt at level 0,
                                       x custom oadt at level 99,
                                       y custom oadt at level 99,
                                       z custom oadt at level 99).

Notation "'π@' b e" := (EProj b e) (in custom oadt at level 2,
                                       b constr at level 0,
                                       format "π@ b  e").

Notation "'π1' e" := (EProj true e) (in custom oadt at level 2).

Notation "'π2' e" := (EProj false e) (in custom oadt at level 2).

Notation "'s𝔹' e" := (ESec e) (in custom oadt at level 2).

Notation "'if{' l '}' e0 'then' e1 'else' e2" := (EIte l e0 e1 e2)
                                                   (in custom oadt at level 89,
                                                       l constr at level 0,
                                                       e0 custom oadt at level 99,
                                                       e1 custom oadt at level 99,
                                                       e2 custom oadt at level 99,
                                                       left associativity,
                                                       format "'if{' l '}'  e0  'then'  e1  'else'  e2").

Notation "'if' e0 'then' e1 'else' e2" := (EIte LPub e0 e1 e2)
                                            (in custom oadt at level 89,
                                                e0 custom oadt at level 99,
                                                e1 custom oadt at level 99,
                                                e2 custom oadt at level 99,
                                                left associativity).

Notation "'~if' e0 'then' e1 'else' e2" := (EIte LObliv e0 e1 e2)
                                             (in custom oadt at level 89,
                                                 e0 custom oadt at level 99,
                                                 e1 custom oadt at level 99,
                                                 e2 custom oadt at level 99).

Notation "'let' e1 'in' e2" := (ELet e1 e2)
                                 (in custom oadt at level 0,
                                     e1 custom oadt at level 99,
                                     e2 custom oadt at level 99).

Notation "'inj{' l '}@' b < τ > e" := (EInj l b τ e) (in custom oadt at level 2,
                                                         l constr at level 0,
                                                         b constr at level 0,
                                                         τ custom oadt at level 0,
                                                         format "'inj{' l '}@' b < τ >  e").

Notation "'inl{' l '}' < τ > e" := (EInj l true τ e) (in custom oadt at level 2,
                                                         τ custom oadt at level 0,
                                                         format "inl{ l } < τ >  e").

Notation "'inr{' l '}' < τ > e" := (EInj l false τ e) (in custom oadt at level 2,
                                                          τ custom oadt at level 0,
                                                          format "inr{ l } < τ >  e").

Notation "'inj@' b < τ > e" := (EInj LPub b τ e) (in custom oadt at level 2,
                                                     b constr at level 0,
                                                     τ custom oadt at level 0,
                                                     format "inj@ b < τ >  e").

Notation "'inl' < τ > e" := (EInj LPub true τ e) (in custom oadt at level 2,
                                                     τ custom oadt at level 0,
                                                     format "inl < τ >  e").

Notation "'inr' < τ > e" := (EInj LPub false τ e) (in custom oadt at level 2,
                                                      τ custom oadt at level 0,
                                                      format "inr < τ >  e").

Notation "'~inj@' b < τ > e" := (EInj LObliv b τ e) (in custom oadt at level 2,
                                                        b constr at level 0,
                                                        τ custom oadt at level 0,
                                                        format "~inj@ b < τ >  e").

Notation "'~inl' < τ > e" := (EInj LObliv true τ e) (in custom oadt at level 2,
                                                        τ custom oadt at level 0,
                                                        format "~inl < τ >  e").

Notation "'~inr' < τ > e" := (EInj LObliv false τ e) (in custom oadt at level 2,
                                                         τ custom oadt at level 0,
                                                         format "~inr < τ >  e").

Notation "'case{' l '}' e0 'of' e1 '|' e2" :=
  (ECase l e0 e1 e2) (in custom oadt at level 89,
                         l constr at level 0,
                         e0 custom oadt at level 99,
                         e1 custom oadt at level 99,
                         e2 custom oadt at level 99,
                         left associativity,
                         format "'case{' l '}'  e0  'of'  e1  '|'  e2").

Notation "'case' e0 'of' e1 '|' e2" :=
  (ECase LPub e0 e1 e2) (in custom oadt at level 89,
                            e0 custom oadt at level 99,
                            e1 custom oadt at level 99,
                            e2 custom oadt at level 99,
                            left associativity).

Notation "'~case' e0 'of' e1 '|' e2" :=
  (ECase LObliv e0 e1 e2) (in custom oadt at level 89,
                              e0 custom oadt at level 99,
                              e1 custom oadt at level 99,
                              e2 custom oadt at level 99,
                              left associativity).

Notation "'fold' < X > e" := (EFold X e) (in custom oadt at level 2,
                                             X custom oadt at level 0,
                                             format "fold < X >  e").

Notation "'unfold' < X > e" := (EUnfold X e) (in custom oadt at level 2,
                                                 X custom oadt at level 0,
                                                 format "unfold < X >  e").

Notation "'tape' e" := (ETape e) (in custom oadt at level 2).

Notation "'mux' e0 e1 e2" := (EMux e0 e1 e2) (in custom oadt at level 2,
                                                 e0 custom oadt at level 0,
                                                 e1 custom oadt at level 0,
                                                 e2 custom oadt at level 0).

Notation "[ b ]" := (EBoxedLit b) (in custom oadt at level 0,
                                      b constr at level 0).

Notation "[ 'inj@' b < τ > e ]" := (EBoxedInj b τ e)
                                     (in custom oadt at level 0,
                                         b constr at level 0,
                                         τ custom oadt at level 0,
                                         e custom oadt at level 0,
                                         format "[ inj@ b < τ >  e ]").

Notation "[ 'inl' < τ > e ]" := (EBoxedInj true τ e)
                                  (in custom oadt at level 0,
                                      τ custom oadt at level 0,
                                      e custom oadt at level 0,
                                      format "[ inl < τ >  e ]").

Notation "[ 'inr' < τ > e ]" := (EBoxedInj false τ e)
                                  (in custom oadt at level 0,
                                      τ custom oadt at level 0,
                                      e custom oadt at level 0,
                                      format "[ inr < τ >  e ]").

Notation "'ite' e0 e1 e2" := (if e0 then e1 else e2)
                               (in custom oadt at level 2,
                                   e0 constr at level 0,
                                   e1 custom oadt at level 0,
                                   e2 custom oadt at level 0).

Notation "'r𝔹' e" := <{ ~if e then true else false }> (in custom oadt at level 2).

End expr_notations.

Section definitions.

Import expr_notations.

#[local]
Coercion EFVar : atom >-> expr.

Reserved Notation "e '≈' e'" (at level 40).

Inductive indistinguishable : expr -> expr -> Prop :=
| IBVar k : <{ bvar k }> ≈ <{ bvar k }>
| IFVar x : <{ fvar x }> ≈ <{ fvar x }>
| IGVar x : <{ gvar x }> ≈ <{ gvar x }>
| IPi l τ1 τ1' τ2 τ2' :
    τ1 ≈ τ1' ->
    τ2 ≈ τ2' ->
    <{ Π:{l}τ1, τ2 }> ≈ <{ Π:{l}τ1', τ2' }>
| IAbs l τ τ' e e' :
    τ ≈ τ' ->
    e ≈ e' ->
    <{ \:{l}τ => e }> ≈ <{ \:{l}τ' => e' }>
| IApp e1 e1' e2 e2' :
    e1 ≈ e1' ->
    e2 ≈ e2' ->
    <{ e1 e2 }> ≈ <{ e1' e2' }>
| ILet e1 e1' e2 e2' :
    e1 ≈ e1' ->
    e2 ≈ e2' ->
    <{ let e1 in e2 }> ≈ <{ let e1' in e2' }>
| IUnitT : <{ 𝟙 }> ≈ <{ 𝟙 }>
| IUnitV : <{ () }> ≈ <{ () }>
| IBool l : <{ 𝔹{l} }> ≈ <{ 𝔹{l} }>
| ILit b : <{ lit b }> ≈ <{ lit b }>
| ISec e e' :
    e ≈ e' ->
    <{ s𝔹 e }> ≈ <{ s𝔹 e' }>
| IIte l e0 e0' e1 e1' e2 e2' :
    e0 ≈ e0' ->
    e1 ≈ e1' ->
    e2 ≈ e2' ->
    <{ if{l} e0 then e1 else e2 }> ≈ <{ if{l} e0' then e1' else e2' }>
| IProd τ1 τ1' τ2 τ2' :
    τ1 ≈ τ1' ->
    τ2 ≈ τ2' ->
    <{ τ1 * τ2 }> ≈ <{ τ1' * τ2' }>
| IPair e1 e1' e2 e2' :
    e1 ≈ e1' ->
    e2 ≈ e2' ->
    <{ (e1, e2) }> ≈ <{ (e1', e2') }>
| IProj b e e' :
    e ≈ e' ->
    <{ π@b e }> ≈ <{ π@b e' }>
| ISum l τ1 τ1' τ2 τ2' :
    τ1 ≈ τ1' ->
    τ2 ≈ τ2' ->
    <{ τ1 +{l} τ2 }> ≈ <{ τ1' +{l} τ2' }>
| IInj l b τ τ' e e' :
    τ ≈ τ' ->
    e ≈ e' ->
    <{ inj{l}@b<τ> e }> ≈ <{ inj{l}@b<τ'> e' }>
| ICase l e0 e0' e1 e1' e2 e2' :
    e0 ≈ e0' ->
    e1 ≈ e1' ->
    e2 ≈ e2' ->
    <{ case{l} e0 of e1 | e2 }> ≈ <{ case{l} e0' of e1' | e2' }>
| IFold X e e' :
    e ≈ e' ->
    <{ fold<X> e }> ≈ <{ fold<X> e' }>
| IUnfold X e e' :
    e ≈ e' ->
    <{ unfold<X> e }> ≈ <{ unfold<X> e' }>
| ITape e e' :
    e ≈ e' ->
    <{ tape e }> ≈ <{ tape e' }>
| IMux e0 e0' e1 e1' e2 e2' :
    e0 ≈ e0' ->
    e1 ≈ e1' ->
    e2 ≈ e2' ->
    <{ mux e0 e1 e2 }> ≈ <{ mux e0' e1' e2' }>

| IBoxedLit b b' :

    <{ [b] }> ≈ <{ [b'] }>
| IBoxedInj b b' τ e e' :

    <{ [inj@b<τ> e] }> ≈ <{ [inj@b'<τ> e'] }>

where "e '≈' e'" := (indistinguishable e e').

Reserved Notation "'{' k '~>' s '}' e" (in custom oadt at level 20, k constr).

Fixpoint open_ (k : nat) (s : expr) (e : expr) : expr :=
  match e with
  | <{ bvar n }> => if decide (k = n) then s else e
  | <{ Π:{l}τ1, τ2 }> => <{ Π:{l}({k~>s}τ1), {S k~>s}τ2 }>
  | <{ \:{l}τ => e }> => <{ \:{l}({k~>s}τ) => {S k~>s}e }>
  | <{ let e1 in e2 }> => <{ let {k~>s}e1 in {S k~>s}e2 }>
  | <{ case{l} e0 of e1 | e2 }> => <{ case{l} {k~>s}e0 of {S k~>s}e1 | {S k~>s}e2 }>

  | <{ e1 e2 }> => <{ ({k~>s}e1) ({k~>s}e2) }>
  | <{ s𝔹 e }> => <{ s𝔹 ({k~>s}e) }>
  | <{ if{l} e0 then e1 else e2 }> => <{ if{l} {k~>s}e0 then {k~>s}e1 else {k~>s}e2 }>
  | <{ τ1 * τ2 }> => <{ ({k~>s}τ1) * ({k~>s}τ2) }>
  | <{ (e1, e2) }> => <{ ({k~>s}e1, {k~>s}e2) }>
  | <{ π@b e }> => <{ π@b ({k~>s}e) }>
  | <{ τ1 +{l} τ2 }> => <{ ({k~>s}τ1) +{l} ({k~>s}τ2) }>
  | <{ inj{l}@b<τ> e }> => <{ inj{l}@b<({k~>s}τ)> ({k~>s}e) }>
  | <{ fold<X> e }> => <{ fold<X> ({k~>s}e) }>
  | <{ unfold<X> e }> => <{ unfold<X> ({k~>s}e) }>
  | <{ tape e }> => <{ tape ({k~>s}e) }>
  | <{ mux e0 e1 e2 }> => <{ mux ({k~>s}e0) ({k~>s}e1) ({k~>s}e2) }>
  | _ => e
  end

where "'{' k '~>' s '}' e" := (open_ k s e) (in custom oadt).

Definition open s e := open_ 0 s e.

Notation "e ^ s" := (open s e) (in custom oadt at level 20).

Reserved Notation "'{' x '↦' s '}' e" (in custom oadt at level 20, x constr).

Fixpoint subst (x : atom) (s : expr) (e : expr) : expr :=
  match e with
  | <{ fvar y }> => if decide (x = y) then s else e

  | <{ Π:{l}τ1, τ2 }> => <{ Π:{l}({x↦s}τ1), {x↦s}τ2 }>
  | <{ \:{l}τ => e }> => <{ \:{l}({x↦s}τ) => {x↦s}e }>
  | <{ e1 e2 }> => <{ ({x↦s}e1) ({x↦s}e2) }>
  | <{ let e1 in e2 }> => <{ let {x↦s}e1 in {x↦s}e2 }>
  | <{ s𝔹 e }> => <{ s𝔹 ({x↦s}e) }>
  | <{ if{l} e0 then e1 else e2 }> => <{ if{l} {x↦s}e0 then {x↦s}e1 else {x↦s}e2 }>
  | <{ τ1 * τ2 }> => <{ ({x↦s}τ1) * ({x↦s}τ2) }>
  | <{ (e1, e2) }> => <{ ({x↦s}e1, {x↦s}e2) }>
  | <{ π@b e }> => <{ π@b ({x↦s}e) }>
  | <{ τ1 +{l} τ2 }> => <{ ({x↦s}τ1) +{l} ({x↦s}τ2) }>
  | <{ inj{l}@b<τ> e }> => <{ inj{l}@b<({x↦s}τ)> ({x↦s}e) }>
  | <{ case{l} e0 of e1 | e2 }> => <{ case{l} {x↦s}e0 of {x↦s}e1 | {x↦s}e2 }>
  | <{ fold<X> e }> => <{ fold<X> ({x↦s}e) }>
  | <{ unfold<X> e }> => <{ unfold<X> ({x↦s}e) }>
  | <{ tape e }> => <{ tape ({x↦s}e) }>
  | <{ mux e0 e1 e2 }> => <{ mux ({x↦s}e0) ({x↦s}e1) ({x↦s}e2) }>
  | _ => e
  end

where "'{' x '↦' s '}' e" := (subst x s e) (in custom oadt).

Definition lexpr_subst x s (T : lexpr) := (T.1, subst x s T.2).

Inductive otval : expr -> Prop :=
| OVUnitT : otval <{ 𝟙 }>
| OVOBool : otval <{ ~𝔹 }>
| OVProd ω1 ω2 : otval ω1 -> otval ω2 -> otval <{ ω1 * ω2 }>
| OVOSum ω1 ω2 : otval ω1 -> otval ω2 -> otval <{ ω1 ~+ ω2 }>
.

Inductive oval : expr -> Prop :=
| OVUnitV : oval <{ () }>
| OVBoxedLit b : oval <{ [b] }>
| OVPair v1 v2 : oval v1 -> oval v2 -> oval <{ (v1, v2) }>
| OVBoxedInj b ω v : otval ω -> oval v -> oval <{ [inj@b<ω> v] }>
.

Inductive val : expr -> Prop :=
| VUnitV : val <{ () }>
| VLit b : val <{ lit b }>
| VPair v1 v2 : val v1 -> val v2 -> val <{ (v1, v2) }>
| VAbs l τ e : val <{ \:{l}τ => e }>
| VInj b τ v : val v -> val <{ inj@b<τ> v }>
| VFold X v : val v -> val <{ fold<X> v }>
| VBoxedLit b : val <{ [b] }>
| VBoxedInj b ω v : otval ω -> oval v -> val <{ [inj@b<ω> v] }>
.

Inductive lc : expr -> Prop :=
| LCFVar x : lc <{ fvar x }>
| LCGVar x : lc <{ gvar x }>
| LCPi l τ1 τ2 L :
    (forall x, x ∉ L -> lc <{ τ2^x }>) ->
    lc τ1 -> lc <{ Π:{l}τ1, τ2 }>
| LCAbs l τ e L :
    (forall x, x ∉ L -> lc <{ e^x }>) ->
    lc τ -> lc <{ \:{l}τ => e }>
| LCLet e1 e2 L :
    (forall x, x ∉ L -> lc <{ e2^x }>) ->
    lc e1 -> lc <{ let e1 in e2 }>
| LCCase l e0 e1 e2 L1 L2 :
    (forall x, x ∉ L1 -> lc <{ e1^x }>) ->
    (forall x, x ∉ L2 -> lc <{ e2^x }>) ->
    lc e0 -> lc <{ case{l} e0 of e1 | e2 }>

| LCUnitT : lc <{ 𝟙 }>
| LCUnitV : lc <{ () }>
| LCBool l : lc <{ 𝔹{l} }>
| LCApp e1 e2 : lc e1 -> lc e2 -> lc <{ e1 e2 }>
| LCLit b : lc <{ lit b }>
| LCSec e : lc e -> lc <{ s𝔹 e }>
| LCIte l e0 e1 e2 : lc e0 -> lc e1 -> lc e2 -> lc <{ if{l} e0 then e1 else e2 }>
| LCProd τ1 τ2 : lc τ1 -> lc τ2 -> lc <{ τ1 * τ2 }>
| LCPair e1 e2 : lc e1 -> lc e2 -> lc <{ (e1, e2) }>
| LCProj b e : lc e -> lc <{ π@b e }>
| LCSum l τ1 τ2 : lc τ1 -> lc τ2 -> lc <{ τ1 +{l} τ2 }>
| LCInj l b τ e : lc τ -> lc e -> lc <{ inj{l}@b<τ> e }>
| LCFold X e : lc e -> lc <{ fold<X> e }>
| LCUnfold X e : lc e -> lc <{ unfold<X> e }>
| LCTape e : lc e -> lc <{ tape e }>
| LCMux e0 e1 e2 : lc e0 -> lc e1 -> lc e2 -> lc <{ mux e0 e1 e2 }>
| LCBoxedLit b : lc <{ [b] }>

| LCBoxedInj b ω v : otval ω -> oval v -> lc <{ [inj@b<ω> v] }>
.

End definitions.

Module notations.

Export expr_notations.

Notation "e '≈' e'" := (indistinguishable e e') (at level 40).

Notation "'{' k '~>' s '}' e" := (open_ k s e)
                                   (in custom oadt at level 20, k constr).

Notation "e ^ s" := (open s e) (in custom oadt at level 20).

Notation "'{' x '↦' s '}' e" := (subst x s e)
                                  (in custom oadt at level 20, x constr).

Notation "{ x '↦' s }" := (lexpr_subst x s) (at level 20).

End notations.
