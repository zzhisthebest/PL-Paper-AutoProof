From PTSrk Require Export Semantics.

Inductive Ctx L: nat -> Type :=
| ε: Ctx L 0
| cons {n}: Ctx L n -> Term L n -> Ctx L (S n).
Arguments ε {_}.
Arguments cons [_] [_] _ _.
Infix "&" := cons (at level 50, left associativity).

Definition ctx_pred {L n} (Γ: Ctx L (S n)): Ctx L n :=
match Γ with | Γ & _ => Γ end.

Definition ctx_top {L n} (Γ: Ctx L (S n)): Term L n :=
match Γ with | _ & T => T end.

Fixpoint index {L n}: Ctx L n -> Fin n -> Term L n :=
match n with
| 0 => fun _ (i : Fin 0) => match i with end
| S n => fun (Γ : Ctx L (S n)) i =>
  shift (fin_match (ctx_top Γ) (index (ctx_pred Γ)) i)
end.
Infix "!!" := index (at level 55, left associativity).

Class Sort_sig (L: Type) :=
  { axiom: L -> L -> Prop
  ; rule: L -> L -> L -> Prop
  }.

Reserved Notation "Γ ⊢ t ⇐ T" (at level 60).
Inductive typ {L} {sig: Sort_sig L}:
  forall {n}, Ctx L n -> Term L n -> Term L n -> Prop :=
| typ_𝓤 {n} {Γ : Ctx L n} ℓ ℓ':
    axiom ℓ ℓ' ->
(* -------------- *)
   Γ ⊢ 𝓤 ℓ ⇐ 𝓤 ℓ'
| typ_Π {n} {Γ : Ctx L n} {T U} ℓₜ ℓᵤ ℓ:
   Γ ⊢ T ⇐ 𝓤 ℓₜ -> Γ & T ⊢ U ⇐ 𝓤 ℓᵤ -> rule ℓₜ ℓᵤ ℓ ->
(* -------------------------------------------------- *)
                   Γ ⊢ Π T U ⇐ 𝓤 ℓ
| typ_var {n} {Γ : Ctx L n} i:
(* ------------------ *)
   Γ ⊢ var i ⇐ Γ !! i
| typ_λ {n} {Γ : Ctx L n} {U t T} ℓ:
   Γ ⊢ U ⇐ 𝓤 ℓ -> Γ & U ⊢ t ⇐ T ->
(* ------------------------------- *)
         Γ ⊢ [U] t ⇐ Π U T
| typ_app {n} {Γ : Ctx L n} {t T u} U:
   Γ ⊢ t ⇐ Π U T -> Γ ⊢ u ⇐ U ->
(* ----------------------------- *)
         Γ ⊢ t $ u ⇐ T ◁ u
| typ_conv {n} {Γ: Ctx L n} {t T'} T ℓ:
   Γ ⊢ t ⇐ T -> Γ ⊢ T' ⇐ 𝓤 ℓ -> T =ᵝ T' ->
(* --------------------------------------- *)
                Γ ⊢ t ⇐ T'
where "Γ ⊢ t ⇐ T" := (typ Γ t T).

Inductive wf {L} {sig: Sort_sig L}:
  forall {n}, Ctx L n -> Type :=
| wf_empty: wf ε
| wf_cons {n} {Γ : Ctx L n} {T} ℓ:
   wf Γ -> Γ ⊢ T ⇐ 𝓤 ℓ ->
(* ---------------------- *)
        wf (Γ & T).


#[export] Instance RankSorts : Sort_sig nat :=
  { axiom := fun x y => y = 0
  ; rule := fun x y z => z = max (S x) y
  }.
