Set Implicit Arguments.

Require Import Definitions.

Require Import Misc.

Reserved Notation "G1 ⊢ S ⤊ G2 ⊢! U" (at level 90).

Inductive revealing : env -> typ -> env -> typ -> Prop :=

| rv_stop : forall G T,
    ~is_sel T ->
    G ⊢ T ⤊ G ⊢! T

| rv_top : forall G T,
    G ⊢ T ⤊ nil ⊢! typ_top

| rv_bot : forall G1 G2 G1' T (x : var),
    G1 ⊢ T ⤊ G1' ⊢! typ_bot ->
    G2 ++ x ~ T ++ G1 ⊢ typ_sel (avar_f x) ⤊ nil ⊢! typ_bot

| rv_bnd : forall G1 G2 T G1' G1'' (x : var) L U U',
    G1 ⊢ T ⤊ G1' ⊢! typ_bnd L U ->
    G1' ⊢ U ⤊ G1'' ⊢! U' ->
    G2 ++ x ~ T ++ G1 ⊢ typ_sel (avar_f x) ⤊ G1'' ⊢! U'
where "G1 ⊢ S ⤊ G2 ⊢! U" := (revealing G1 S G2 U).

Reserved Notation "G1 ⊢ S ↗ G2 ⊢! U" (at level 90).

Inductive upcast : env -> avar -> env -> typ -> Prop :=

| uc_top : forall G x,
    G ⊢ x ↗ nil ⊢! typ_top

| uc_bot : forall G1 G2 x T G1',
    G1 ⊢ T ⤊ G1' ⊢! typ_bot ->
    G2 ++ x ~ T ++ G1 ⊢ avar_f x ↗ nil ⊢! typ_bot

| uc_bnd : forall G1 G2 x T G1' L U,
    G1 ⊢ T ⤊ G1' ⊢! typ_bnd L U ->
    G2 ++ x ~ T ++ G1 ⊢ avar_f x ↗ G1' ⊢! U
where "G1 ⊢ S ↗ G2 ⊢! U" := (upcast G1 S G2 U).

Reserved Notation "G1 ⊢ S ↘ G2 ⊢! U" (at level 90).

Inductive downcast : env -> avar -> env -> typ -> Prop :=

| dc_bot : forall G x,
    G ⊢ x ↘ nil ⊢! typ_bot

| dc_top : forall G1 G2 x T G1',
    G1 ⊢ T ⤊ G1' ⊢! typ_bot ->
    downcast (G2 ++ x ~ T ++ G1) (avar_f x) nil typ_top

| dc_bnd : forall G1 G2 x T G1' L U,
    revealing G1 T G1' (typ_bnd L U) ->
    downcast (G2 ++ x ~ T ++ G1) (avar_f x) G1' L
where "G1 ⊢ S ↘ G2 ⊢! U" := (downcast G1 S G2 U).

Reserved Notation "[ L ] G1 >> T '<⦂' U << G2" (at level 70).

Inductive stareat : atoms -> env -> typ -> typ -> env -> Prop :=

| sa_bot : forall L G1 T G2, [ L ] G1 >> typ_bot <⦂ T << G2

| sa_top : forall L G1 T G2, [ L ] G1 >> T <⦂ typ_top << G2

| sa_sel_refl : forall L G1 x G2, [ L ] G1 >> typ_sel x <⦂ typ_sel x << G2

| sa_sel_left : forall L G1 x G2 T U G1',
    G1 ⊢ x ↗ G1' ⊢! T ->
    [ L ] G1' >> T <⦂ U << G2 ->
    [ L ] G1 >> typ_sel x <⦂ U << G2

| sa_sel_right : forall L G1 x G2 T U G2',
    G2 ⊢ x ↘ G2' ⊢! U ->
    [ L ] G1 >> T <⦂ U << G2' ->
    [ L ] G1 >> T <⦂ typ_sel x << G2

| sa_all : forall L G1 T1 U1 G2 T2 U2 x,
    x `notin` fv G1 `union` fv T1 `union` fv T2
      `union` fv U1 `union` fv U2 `union` fv G2 `union` L ->
    [ L ] G2 >> T2 <⦂ T1 << G1 ->
    [ L  `union` singleton x `union` fv T2 ]
      x ~ T1 ++ G1 >> open x U1 <⦂ open x U2 << x ~ T2 ++ G2 ->
    [ L ] G1 >> typ_all T1 U1 <⦂ typ_all T2 U2 << G2

| sa_bnd : forall L G1 S1 U1 S2 U2 G2,
    [ L ] G2 >> S2 <⦂ S1 << G1 ->
    [ L ] G1 >> U1 <⦂ U2 << G2 ->
    [ L ] G1 >> typ_bnd S1 U1 <⦂ typ_bnd S2 U2 << G2
where "[ L ] G1 >> T '<⦂' U << G2" := (stareat L G1 T U G2)%type.
