Set Implicit Arguments.

Require Import Coq.Program.Equality.

Require Import LibExtra DotTactics.

Require Import AbstractSyntax TypingMode GeneralTyping.

Require Import RecordTypes InertContext PreciseTyping TightTyping Narrowing Env Equivalence EnvCorrespondence Subenvironments.

Section WithTypingMode.

Context {typing_mode: Mode}.

Context (Hm: mode_top_nm' typing_mode = mode_top_nm_none).

Inductive bnd_sup : ctx -> renv -> typ -> typ -> Prop :=
| bnd_sup_top : forall G e T,
    bnd_sup G e T typ_top
| bnd_sup_and : forall G e T T1 T2,
    bnd_sup G e T T1 ->
    bnd_sup G e T T2 ->
    bnd_sup G e T (typ_and T1 T2)
| bnd_sup_or1 : forall G e T T1 T2,
    bnd_sup G e T T1 ->
    bnd_sup G e T (typ_or T1 T2)
| bnd_sup_or2 : forall G e T T1 T2,
    bnd_sup G e T T2 ->
    bnd_sup G e T (typ_or T1 T2)
| bnd_sup_sel : forall G e T x A y U SL SU,
    G ⊢! x ∶ U ⪼ typ_rcd (dec_typ A SL SU) ->
    bnd_sup G e T (open y SL) ->
    bnd_sup G e T (typ_sel (avar_f x) A (avar_f y))
| bnd_sup_rec : forall G e T,
    bnd_sup G e (typ_bnd T) (typ_bnd T)
| bnd_sup_eq : forall G e T T1 T2,
    bnd_sup G e T T1 ->
    typing_equiv e T1 T2 ->
    bnd_sup G e T T2
.

Inductive fun_sup : ctx -> renv -> typ -> typ -> Prop :=
| fun_sup_top : forall G e T,
    fun_sup G e T typ_top
| fun_sup_and : forall G e T T1 T2,
    fun_sup G e T T1 ->
    fun_sup G e T T2 ->
    fun_sup G e T (typ_and T1 T2)
| fun_sup_or1 : forall G e T T1 T2,
    fun_sup G e T T1 ->
    fun_sup G e T (typ_or T1 T2)
| fun_sup_or2 : forall G e T T1 T2,
    fun_sup G e T T2 ->
    fun_sup G e T (typ_or T1 T2)
| fun_sup_sel : forall G e T x A y U S,
    G ⊢! x ∶ U ⪼ typ_rcd (dec_typ A S S) ->
    fun_sup G e T (open y S) ->
    fun_sup G e T (typ_sel (avar_f x) A (avar_f y))
| fun_sup_fun : forall L G e S1 T1 S2 T2,
    G⁏e ⊢# S2 <: S1 ->
    (forall x, x \notin L ->
       G § x / v_par ~ S2 ⁏e ⊢ open x T1 <: open x T2) ->
    fun_sup G e (typ_fun S1 T1) (typ_fun S2 T2)
| fun_sup_eq : forall G e T T1 T2,
    fun_sup G e T T1 ->
    typing_equiv e T1 T2 ->
    fun_sup G e T T2
.

End WithTypingMode.
