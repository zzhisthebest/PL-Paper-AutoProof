Set Implicit Arguments.

Require Import Definitions.

Require Import Step.

Require Import Misc.

Reserved Notation "[ L ] G ⊢k S <⦂ U" (at level 70).

Inductive subtykn : vars -> env -> typ -> typ -> Prop :=

| snf_vrefl : forall L G x,
    [ L ] G ⊢k typ_sel x <⦂ typ_sel x

| snf_top : forall L G T,
    [ L ] G ⊢k T <⦂ typ_top

| snf_bot : forall L G T,
    [ L ] G ⊢k typ_bot <⦂ T

| snf_bnd : forall L G S T1 T2 U,
    [ L ] G ⊢k S <⦂ T1 ->
    [ L ] G ⊢k T2 <⦂ U ->
    [ L ] G ⊢k typ_bnd T1 T2 <⦂ typ_bnd S U

| snf_all : forall L G T U1 U2 x,
    x `notin` union (fv G)
      (union (fv T) (union (fv U1) (union (fv U2) L))) ->
    [ union L (union (singleton x) (fv T)) ]
      x ~ T ++ G ⊢k open x U1 <⦂ open x U2 ->
    [ L ] G ⊢k typ_all T U1 <⦂ typ_all T U2

| snf_sel1 : forall L G x T S,
    binds x T G ->
    [ L ] G ⊢k T <⦂ typ_bnd S typ_top ->
    [ L ] G ⊢k S <⦂ (typ_sel $ avar_f x)

| snf_sel2 : forall L G x T U,
    binds x T G ->
    [ L ] G ⊢k T <⦂ typ_bnd typ_bot U ->
    [ L ] G ⊢k typ_sel $ avar_f x <⦂ U
where "[ L ] G ⊢k S <⦂ U" := (subtykn L G S U).

Theorem subtykn_equiv_stp_subty : forall L G S U,
    wf_env G ->
    fv S [<=] dom G -> lc S ->
    fv U [<=] dom G -> lc U ->
    [ L ] G ⊢k S <⦂ U <->
    [ L ] G ⊢s S <⦂ U.
