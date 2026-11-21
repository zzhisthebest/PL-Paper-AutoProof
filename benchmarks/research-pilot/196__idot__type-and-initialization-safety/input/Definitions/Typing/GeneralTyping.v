Set Implicit Arguments.

Require Import LibExtra AbstractSyntax PreTyping Typing.

Implicit Types (Gamma G : ctx) (T U : typ) (x y z : var) (t : trm).

Inductive ty_def : DecTyping def :=

| ty_def_typ : forall G A T,
    G ⊢ def_typ A T ∶d dec_typ A T T

| ty_def_trm : forall G a t T,
    G ⊢ def_trm a ∶d dec_trm a T T.

Existing Instance ty_def.

Inductive ty_trm : Typing trm :=

| ty_var : forall G x T,
    binds x T G ->
    G ⊢ trm_var (avar_f x) ∶ T

| ty_all_elim : forall G x z S T,
    G ⊢ trm_var (avar_f x) ∶ typ_all S T ->
    G ⊢ trm_var (avar_f z) ∶ S ->
    G ⊢ trm_app (avar_f x) (avar_f z) ∶ open z T

| ty_new : forall G x avs xs Ts is' T,
    G ⊢ trm_var (avar_f x) ∶ typ_con Ts is' T ->
    G ⊢ avs :: Ts ->
    vars_of_avars xs avs ->
    G ⊢ trm_new (avar_f x) avs ∶ typ_bnd (open_rec_vars 1 xs T)

| ty_rcd_elim : forall G x a S T,
    G ⊢ trm_var (avar_f x) ∶ typ_rcd (dec_trm a S T) ->
    G ⊢ trm_sel (avar_f x) a ∶ T

| ty_fld_asn : forall G x y a S T,
    G ⊢ trm_var (avar_f x) ∶ typ_rcd (dec_trm a S T) ->
    G ⊢ trm_var (avar_f y) ∶ S ->
    G ⊢ trm_asn (avar_f x) a (avar_f y) ∶ T

| ty_let : forall L G t u T U,
    G ⊢ t ∶ T ->
    (forall x, x \notin L ->
      G & x ~ T ⊢ open x u ∶ U) ->
    G ⊢ trm_let T t u ∶ U

| ty_llit : forall L G l u T U,
    G ⊢ l ∶ T ->
    (forall x, x \notin L ->
      G & x ~ T ⊢ open x u ∶ U) ->
    G ⊢ trm_lit T l u ∶ U

| ty_rec_intro : forall G x T,
    G ⊢ trm_var (avar_f x) ∶ open x T ->
    G ⊢ trm_var (avar_f x) ∶ typ_bnd T

| ty_rec_elim : forall G x T,
    G ⊢ trm_var (avar_f x) ∶ typ_bnd T ->
    G ⊢ trm_var (avar_f x) ∶ open x T

| ty_and_intro : forall G x T U,
    G ⊢ trm_var (avar_f x) ∶ T ->
    G ⊢ trm_var (avar_f x) ∶ U ->
    G ⊢ trm_var (avar_f x) ∶ typ_and T U

| ty_sub : forall G (t : trm) T U,
    G ⊢ t ∶ T ->
    G ⊢ T <: U ->
    G ⊢ t ∶ U

with ty_lit : Typing lit :=

| ty_all_intro : forall L G T t U,
    (forall x, x \notin L ->
      G & x ~ T ⊢ open x t ∶ open x U) ->
    G ⊢ lit_fun T t ∶ typ_all T U

| ty_con_intro : forall L G Ts is' T ds t T',
    (forall x ys,
        length ys = length_s Ts ->
        fresh L (S (length ys)) (cons x ys) ->
        G & (ys ~** (to_list Ts))
        & (x ~ open_vars (cons x ys) T)
            ⊢ (open_vars (cons x ys) ds)
            ∶ (open_vars (cons x ys) T)) ->
    (forall x ys,
        length ys = length_s Ts ->
        fresh L (S (length ys)) (cons x ys) ->
        (G & (ys ~** (to_list Ts)) & (x ~ open_vars (cons x ys) T)
            ⊢ (open_vars (cons x ys) t)
            ∶ (open_vars (cons x ys) T'))) ->
    G ⊢ lit_con Ts is' T ds t ∶ typ_con Ts is' T

with subtyp : Subtyping :=

| subtyp_top: forall G T,
    G ⊢ T <: typ_top

| subtyp_bot: forall G T,
    G ⊢ typ_bot <: T

| subtyp_refl: forall G T,
    G ⊢ T <: T

| subtyp_trans: forall G S T U,
    G ⊢ S <: T ->
    G ⊢ T <: U ->
    G ⊢ S <: U

| subtyp_and11: forall G T U,
    G ⊢ typ_and T U <: T

| subtyp_and12: forall G T U,
    G ⊢ typ_and T U <: U

| subtyp_and2: forall G S T U,
    G ⊢ S <: T ->
    G ⊢ S <: U ->
    G ⊢ S <: typ_and T U

| subtyp_fld: forall G a T1 T2 U1 U2,
    G ⊢ T1 <: T2 ->
    G ⊢ U1 <: U2 ->
    G ⊢ typ_rcd (dec_trm a T2 U1) <: typ_rcd (dec_trm a T1 U2)

| subtyp_typ: forall G A S1 T1 S2 T2,
    G ⊢ S2 <: S1 ->
    G ⊢ T1 <: T2 ->
    G ⊢ typ_rcd (dec_typ A S1 T1) <: typ_rcd (dec_typ A S2 T2)

| subtyp_sel2: forall G x A S T,
    G ⊢ trm_var (avar_f x) ∶ typ_rcd (dec_typ A S T) ->
    G ⊢ S <: typ_sel (avar_f x) A

| subtyp_sel1: forall G x A S T,
    G ⊢ trm_var (avar_f x) ∶ typ_rcd (dec_typ A S T) ->
    G ⊢ typ_sel (avar_f x) A <: T

| subtyp_all: forall L G S1 T1 S2 T2,
    G ⊢ S2 <: S1 ->
    (forall x, x \notin L ->
       G & x ~ S2 ⊢ open x T1 <: open x T2) ->
    G ⊢ typ_all S1 T1 <: typ_all S2 T2

with ty_avars : Typings (list avar) :=
     | typ_avars_nil : forall G,
         G ⊢ nil :: typs_nil

     | typ_avars_cons : forall G x T avs Ts,
         G ⊢ (trm_var (avar_f x)) ∶ T ->
         G ⊢ avs :: Ts ->
         G ⊢ (cons (avar_f x) avs) :: (typs_cons T Ts).

Existing Instance ty_trm.

Existing Instance ty_avars.

Existing Instance subtyp.

Existing Instance ty_lit | 1.

Scheme ts_ty_trm_mut := Induction for ty_trm Sort Prop
with   ts_subtyp     := Induction for subtyp Sort Prop
with   ts_ty_avars   := Induction for ty_avars Sort Prop.

Combined Scheme ts_mutind from ts_ty_trm_mut, ts_subtyp, ts_ty_avars.

Scheme rules_trm_mut    := Induction for ty_trm Sort Prop
with   rules_lit_mut    := Induction for ty_lit Sort Prop
with   rules_subtyp     := Induction for subtyp Sort Prop
with   rules_avars_mut  := Induction for ty_avars Sort Prop.

Combined Scheme rules_mutind from rules_trm_mut, rules_lit_mut,
rules_subtyp, rules_avars_mut.
