Set Implicit Arguments.

Require Import Coq.Program.Equality.

Require Import Definitions PreciseTyping.

Reserved Notation "G '⊢#' t ':' T" (at level 40, t at level 59).

Reserved Notation "G '⊢#' T '<:' U" (at level 40, T at level 59).

Inductive ty_trm_t : ctx -> trm -> typ -> Prop :=




| ty_var_t : forall G x T,
    binds x T G ->
    G ⊢# tvar x : T





| ty_all_intro_t : forall G t T U L,
    (forall x, x \notin L ->
      G & x ~ T ⊢ open_trm x t : open_typ x U) ->
    G ⊢# trm_val (λ(T) t) : ∀(T) U





| ty_all_elim_t : forall G p q S T,
    G ⊢# trm_path p : ∀(S) T ->
    G ⊢# trm_path q : S ->
    G ⊢# trm_app p q : open_typ_p q T





| ty_new_intro_t : forall G ds T L,
    (forall z, z \notin L ->
      z; nil; G & (z ~ open_typ z T) ⊢ open_defs z ds :: open_typ z T) ->
    G ⊢# trm_val (ν(T) ds) : μ T




| ty_new_elim_t : forall G p a T,
    G ⊢# trm_path p : typ_rcd {a ⦂ T} ->
    G ⊢# trm_path p • a : T




| ty_rec_intro_t : forall G p a T,
    G ⊢# trm_path p•a : T ->
    G ⊢# trm_path p : typ_rcd { a ⦂ T }






| ty_let_t : forall G t u T U L,
    G ⊢# t : T ->
    (forall x, x \notin L ->
      G & x ~ T ⊢ open_trm x u : U) ->
    G ⊢# trm_let t u : U





| ty_sngl_t : forall G p q T,
    G ⊢# trm_path p : {{ q }} ->
    G ⊢# trm_path q : T ->
    G ⊢# trm_path p : T




| ty_path_elim_t : forall G p q a T,
    G ⊢# trm_path p : {{ q }} ->
    G ⊢# trm_path q • a : T ->
    G ⊢# trm_path p • a : {{ q•a }}




| ty_rcd_intro_t : forall G p T,
    G ⊢# trm_path p : open_typ_p p T ->
    G ⊢# trm_path p : μ T




| ty_rec_elim_t : forall G p T,
    G ⊢# trm_path p : μ T ->
    G ⊢# trm_path p : open_typ_p p T





| ty_and_intro_t : forall G p T U,
    G ⊢# trm_path p : T ->
    G ⊢# trm_path p : U ->
    G ⊢# trm_path p : T ∧ U





| ty_sub_t : forall G t T U,
    G ⊢# t : T ->
    G ⊢# T <: U ->
    G ⊢# t : U
where "G '⊢#' t ':' T" := (ty_trm_t G t T)


with subtyp_t : ctx -> typ -> typ -> Prop :=


| subtyp_top_t: forall G T,
    G ⊢# T <: ⊤


| subtyp_bot_t: forall G T,
    G ⊢# ⊥ <: T


| subtyp_refl_t: forall G T,
    G ⊢# T <: T





| subtyp_trans_t: forall G S T U,
    G ⊢# S <: T ->
    G ⊢# T <: U ->
    G ⊢# S <: U


| subtyp_and11_t: forall G T U,
    G ⊢# T ∧ U <: T


| subtyp_and12_t: forall G T U,
    G ⊢# T ∧ U <: U





| subtyp_and2_t: forall G S T U,
    G ⊢# S <: T ->
    G ⊢# S <: U ->
    G ⊢# S <: T ∧ U




| subtyp_fld_t: forall G T U a,
    G ⊢# T <: U ->
    G ⊢# typ_rcd {a ⦂ T} <: typ_rcd {a ⦂ U}





| subtyp_typ_t: forall G S1 S2 T1 T2 A,
    G ⊢# S2 <: S1 ->
    G ⊢# T1 <: T2 ->
    G ⊢# typ_rcd { A >: S1 <: T1 } <: typ_rcd { A >: S2 <: T2 }





| subtyp_sngl_pq_t : forall G p q T T' U,
    G ⊢!!! p : {{ q }} ->
    G ⊢!!! q : U ->
    repl_typ p q T T' ->
    G ⊢# T <: T'





| subtyp_sngl_qp_t : forall G p q T T' U,
    G ⊢!!! p : {{ q }} ->
    G ⊢!!! q : U ->
    repl_typ q p T T' ->
    G ⊢# T <: T'




| subtyp_sel2_t: forall G p A T ,
    G ⊢!!! p : typ_rcd { A >: T <: T } ->
    G ⊢# T <: p ↓ A




| subtyp_sel1_t: forall G p A T,
    G ⊢!!! p : typ_rcd { A >: T <: T } ->
    G ⊢# p↓A <: T






| subtyp_all_t: forall G S1 S2 T1 T2 L,
    G ⊢# S2 <: S1 ->
    (forall x, x \notin L ->
       G & x ~ S2 ⊢ open_typ x T1 <: open_typ x T2) ->
    G ⊢# ∀(S1) T1 <: ∀(S2) T2
where "G '⊢#' T '<:' U" := (subtyp_t G T U).

Scheme ts_ty_trm_mut_ts  := Induction for ty_trm_t    Sort Prop
with   ts_subtyp_ts      := Induction for subtyp_t    Sort Prop.

Combined Scheme ts_mutind_ts from ts_ty_trm_mut_ts, ts_subtyp_ts.
