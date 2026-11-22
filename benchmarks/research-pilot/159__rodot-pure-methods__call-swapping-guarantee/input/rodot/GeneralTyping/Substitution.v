Set Implicit Arguments.

Require Import Coq.Program.Equality.

Require Import DotTactics LibExtra.

Require Import AbstractSyntax TypingMode Equivalence GeneralTyping Weakening EWeakening Visibility.

Require Import Indep SubstCommon UnboundSubstitution.

Section WithTypingMode.

Context {typing_mode: Mode}.

Class Substitution (A B: Set) (su: SubstVar A) (sub: SubstVar B)
    (property: TypingProperty A B) :=
  substitution_obj (y: var) (S: typ) G1 x vk G2 Go e (a: A) (b: B):
      property (G1 § x / vk ~ S §& G2) Go (e & x ~ y) a b ->
      ctx_ok (G1 § x / vk ~ S §& G2 §§& Go) ->
      x \notin ctx_fv G1 ->
      renv_notin x e ->
      G1 §& G2 /[§ x->y] ⁏e ⊢ y ∶ S /[x -> y] ->

      (mode_has_visibility typing_mode ->
       ctx_vis (G1 § x / vk ~ S §& G2 §§& Go) x ->
       ctx_vis (G1 §& G2 /[§x->y] §§& (subst_objctx x y Go)) y) ->
      property (G1 §& G2 /[§x->y]) (subst_objctx x y Go) e a/[x->y] b/[x->y] .

Section SubstitutionLemmata.

Context (A B: Set) (AS: SubstVar A) (BS: SubstVar B)
  (property: TypingProperty A B)(AW: Substitution AS BS property){AEW: EWeakening property}.

End SubstitutionLemmata.

Section SubstitutionTyLemmata.

Context (A: Set)(AS: SubstVar A)(AT: Typing A)
  {AW: Substitution AS subst_var AT} {AEW: EWeakening (obj_typing)}.

End SubstitutionTyLemmata.

Definition SubstitutionInd (y: var) (S: typ) (A B: Set) (su: SubstVar A) (sub: SubstVar B) (property: TypingProperty A B) :=
  (forall G Go e (v: A) T,
    property G Go e v T ->
    forall G1 G2 e1 x vk,
      G = G1 § x / vk ~ S §& G2 ->
      e = (e1 & x ~ y) ->
      ctx_ok (G1 § x / vk ~ S §& G2 §§& Go) ->
      x \notin ctx_fv G1 ->
      renv_notin x e1 ->
      G1 §& G2 /[§ x -> y] ⁏ e1 ⊢ y ∶ S /[x -> y] ->
      (mode_has_visibility typing_mode ->
       ctx_vis (G1 § x / vk ~ S §& G2 §§& Go) x ->
       ctx_vis (G1 §& G2 /[§ x -> y] §§& (subst_objctx x y Go)) y) ->
      property (G1 §& G2 /[§ x -> y]) (subst_objctx x y Go) e1 (subst_var x y v) (subst_var x y T)) .

Definition SubstitutionEInd (y: var) (S: typ) (A: Set) (t: TypingEquiv A) (su: SubstVar A) :=
  SubstitutionInd y S (su) (su) (fun G Go e (a b: A) => typing_equiv e a b).

Definition SubstitutionTInd (y: var) (S: typ) (A: Set) (t: Typing A) (su: SubstVar A) :=
  SubstitutionInd y S (su) (TypSubstVar) (obj_typing).

Definition SubstitutionIncapInd (y: var) (S: typ) (_: ReferenceIncapacitate) :=
  SubstitutionInd y S TypSubstVar TypSubstVar obj_ref_incap.

Definition SubstitutionCapbndInd (y: var) (S: typ)
           (C : typ_refcap_label) (_ : CapabilityBound C) :=
  SubstitutionInd y S TypSubstVar TypSubstVar obj_cap_bnd.

Definition SubstitutionDInd (y: var) (S: typ) (A: Set) (t: DecTyping A) (su: SubstVar A) :=
  SubstitutionInd y S (su) (subst_dec) (obj_dec_typing).

Definition VKChangeInd x vk1 vk2 S G1 (A B: Set) (property: TypingProperty A B) :=
  forall G Go e (a: A) (b: B),
    property G Go e a b ->
    forall G2,
    G = G1 § x / vk1 ~ S §& G2 ->
    property (G1 § x / vk2 ~ S §& G2) Go e a b.

Definition VKChangeTInd x vk1 vk2 S G1 (A: Set) (AT: Typing A) := VKChangeInd x vk1 vk2 S G1 obj_typing.

Definition VKChangeIncapInd x vk1 vk2 S G1 (_: ReferenceIncapacitate) :=
  VKChangeInd x vk1 vk2 S G1 obj_ref_incap.

Definition VKChangeCapbndInd x vk1 vk2 S G1
           (C : typ_refcap_label)
           (_ : CapabilityBound C) :=
  VKChangeInd x vk1 vk2 S G1 obj_cap_bnd.

Definition VKChangeDInd x vk1 vk2 S G1 (A: Set) (AT: DecTyping A) := VKChangeInd x vk1 vk2 S G1 obj_dec_typing.

End WithTypingMode.

Inductive is_sealed_typ : nat -> typ -> Prop :=
| is_sealed_top : forall n, is_sealed_typ n typ_top
| is_sealed_bot : forall n, is_sealed_typ n typ_bot
| is_sealed_rcd : forall n D, is_sealed_dec n D -> is_sealed_typ n (typ_rcd D)
| is_sealed_and : forall n T1 T2, is_sealed_typ n T1 ->
                             is_sealed_typ n T2 ->
                             is_sealed_typ n (typ_and T1 T2)
| is_sealed_or : forall n T1 T2, is_sealed_typ n T1 ->
                             is_sealed_typ n T2 ->
                             is_sealed_typ n (typ_or T1 T2)
| is_sealed_sel : forall n a L a', (forall n', n' >= n ->
                                     (avar_b n') <> a /\ (avar_b n') <> a') ->
                              is_sealed_typ n (typ_sel a L a')
| is_sealed_bnd : forall n T, is_sealed_typ (S n) T ->
                         is_sealed_typ n (typ_bnd T)
| is_sealed_fun : forall n T1 T2, is_sealed_typ n T1 ->
                             is_sealed_typ (S n) T2 ->
                             is_sealed_typ n (typ_fun T1 T2)
| is_sealed_nocap : forall n, is_sealed_typ n typ_nocap
with is_sealed_dec : nat -> dec -> Prop :=
| is_sealed_dec_typ : forall n L T U, is_sealed_typ (S n) T ->
                                 is_sealed_typ (S n) U ->
                                 is_sealed_dec n (dec_typ L T U)
| is_sealed_dec_fld : forall n L T U, is_sealed_typ n T ->
                                 is_sealed_typ n U ->
                                 is_sealed_dec n (dec_fld L T U)
| is_sealed_dec_met : forall n L TC TZ TR, is_sealed_typ (S n) TC ->
                                      is_sealed_typ n TZ ->
                                      is_sealed_typ (S (S n)) TR ->
                                      is_sealed_dec n (dec_met L TC TZ TR).

Scheme is_sealed_typ_mut  := Induction for is_sealed_typ Sort Prop
with   is_sealed_dec_mut  := Induction for is_sealed_dec Sort Prop.

Combined Scheme is_sealed_mutind from is_sealed_typ_mut, is_sealed_dec_mut.

Class IsSealed (A : Set) := is_sealed : nat -> A -> Prop.
