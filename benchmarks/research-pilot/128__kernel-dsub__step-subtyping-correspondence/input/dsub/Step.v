Set Implicit Arguments.

Require Import Definitions.
Require Import Misc.

Reserved Notation "G ⊢ S ⇑ U" (at level 90).

Inductive exposure : env -> typ -> typ -> Prop :=

| exp_stop : forall G T,
    ~is_sel T ->
    G ⊢ T ⇑ T

| exp_top : forall G T,
    G ⊢ T ⇑ typ_top

| exp_bot : forall G1 G2 T x,
    G1 ⊢ T ⇑ typ_bot ->
    G2 ++ x ~ T ++ G1 ⊢ typ_sel (avar_f x) ⇑ typ_bot

| exp_bnd : forall G1 G2 T x L U U',
    G1 ⊢ T ⇑ (typ_bnd L U) ->
    G1 ⊢ U ⇑ U' ->
    G2 ++ x ~ T ++ G1 ⊢ typ_sel (avar_f x) ⇑ U'
where "G ⊢ S ⇑ U" := (exposure G S U).

Reserved Notation "G ⊢ S ↗! U" (at level 90).

Inductive upcast_e : env -> avar -> typ -> Prop :=

| uce_top : forall G x,
    G ⊢ x ↗! typ_top

| uce_bot : forall G1 G2 x T ,
    G1 ⊢ T ⇑ typ_bot ->
    G2 ++ x ~ T ++ G1 ⊢ avar_f x ↗! typ_bot

| uce_bnd : forall G1 G2 x T L U,
    G1 ⊢ T ⇑ typ_bnd L U ->
    G2 ++ x ~ T ++ G1 ⊢ avar_f x ↗! U
where "G ⊢ S ↗! U" := (upcast_e G S U).

Reserved Notation "G ⊢ S ↘! U" (at level 90).

Inductive downcast_e : env -> avar -> typ -> Prop :=

| dce_bot : forall G x,
    G ⊢ x ↘! typ_bot

| dce_top : forall G1 G2 x T,
    G1 ⊢ T ⇑ typ_bot ->
    G2 ++ x ~ T ++ G1 ⊢ avar_f x ↘! typ_top

| dce_bnd : forall G1 G2 x T L U,
    G1 ⊢ T ⇑ (typ_bnd L U) ->
    G2 ++ x ~ T ++ G1 ⊢ avar_f x ↘! L
where "G ⊢ S ↘! U" := (downcast_e G S U).

Reserved Notation "[ L ] G ⊢s S <⦂ U" (at level 70).

Inductive stp_subty : vars -> env -> typ -> typ -> Prop :=

| ss_top : forall L G T,
    [ L ] G ⊢s T <⦂ typ_top

| ss_bot : forall L G T,
    [ L ] G ⊢s typ_bot <⦂ T

| ss_sel_refl : forall L G x,
    [ L ] G ⊢s typ_sel x <⦂ typ_sel x

| ss_sel_left : forall L G x T U,
    G ⊢ x ↗! T ->
    [ L ] G ⊢s T <⦂ U ->
    [ L ] G ⊢s typ_sel x <⦂ U

| ss_sel_right : forall L G x T U,
    G ⊢ x ↘! T ->
    [ L ] G ⊢s U <⦂ T ->
    [ L ] G ⊢s U <⦂ typ_sel x

| ss_bnd : forall L G S1 U1 S2 U2,
    [ L ] G ⊢s S2 <⦂ S1 ->
    [ L ] G ⊢s U1 <⦂ U2 ->
    [ L ] G ⊢s typ_bnd S1 U1 <⦂ typ_bnd S2 U2

| ss_all : forall L G T U1 U2 x,
    x `notin` fv G `union` fv T
      `union` fv U1 `union` fv U2 `union` L ->
    [ L  `union` singleton x `union` fv T ]
      x ~ T ++ G ⊢s open x U1 <⦂ open x U2 ->
    [ L ] G ⊢s typ_all T U1 <⦂ typ_all T U2
where "[ L ] G ⊢s S <⦂ U" := (stp_subty L G S U).
