Set Implicit Arguments.

Require Import Definitions.

Require Import Stareat.

Require Import Misc.

Reserved Notation "[ L ] G1 ⊢k S <⦂ U k⊣ G2" (at level 70).

Inductive subtysk : vars -> env -> typ -> typ -> env -> Prop :=

| ssk_refl : forall L G1 G2 x,
    [ L ] G1 ⊢k typ_sel x <⦂ typ_sel x k⊣ G2

| ssk_top : forall L G1 G2 T,
    [ L ] G1 ⊢k T <⦂ typ_top k⊣ G2

| ssk_bot : forall L G1 G2 T,
    [ L ] G1 ⊢k typ_bot <⦂ T k⊣ G2

| ssk_bnd : forall L G1 G2 S T1 T2 U,
    [ L ] G2 ⊢k S <⦂ T1 k⊣ G1 ->
    [ L ] G1 ⊢k T2 <⦂ U k⊣ G2 ->
    [ L ] G1 ⊢k typ_bnd T1 T2 <⦂ typ_bnd S U k⊣ G2

| ssk_all : forall L G1 G2 T1 T2 U1 U2 x,
    x `notin` fv G1 `union` fv T1 `union` fv T2
      `union` fv U1 `union` fv U2 `union` fv G2 `union` L ->
    [ L ] G2 ⊢k T2 <⦂ T1 k⊣ G1 ->
    [ union L (union (singleton x) (fv T2)) ]
      x ~ T1 ++ G1 ⊢k open x U1 <⦂ open x U2 k⊣ x ~ T2 ++ G2 ->
    [ L ] G1 ⊢k typ_all T1 U1 <⦂ typ_all T2 U2 k⊣ G2

| ssk_sel1 : forall L G1 G2 x T S,
    binds x T G2 ->
    [ L ] G2 ⊢k T <⦂ typ_bnd S typ_top k⊣ G1 ->
    [ L ] G1 ⊢k S <⦂ typ_sel $ avar_f x k⊣ G2

| ssk_sel2 : forall L G1 G2 x T U,
    binds x T G1 ->
    [ L ] G1 ⊢k T <⦂ typ_bnd typ_bot U k⊣ G2 ->
    [ L ] G1 ⊢k typ_sel $ avar_f x <⦂ U k⊣ G2
where "[ L ] G1 ⊢k S <⦂ U k⊣ G2" := (subtysk L G1 S U G2).

Reserved Notation "[ L ] G1 >> T '<⦂p' U << G2" (at level 70).

Inductive subtysk' : vars -> env -> typ -> typ -> env -> nat -> Prop :=
| ssk'_refl : forall L G1 G2 x, subtysk' L G1 (typ_sel x) (typ_sel x) G2 1
| ssk'_top : forall L G1 G2 T, subtysk' L G1 T typ_top G2 1
| ssk'_bot : forall L G1 G2 T, subtysk' L G1 typ_bot T G2 1
| ssk'_bnd : forall L G1 G2 S T1 T2 U n1 n2,
    subtysk' L G2 S T1 G1 n1 -> subtysk' L G1 T2 U G2 n2 ->
    subtysk' L G1 (typ_bnd T1 T2) (typ_bnd S U) G2 (1 + n1 + n2)
| ssk'_all : forall L G1 G2 T1 T2 U1 U2 x n1 n2,
    x `notin` fv G1 `union` fv T1 `union` fv T2
      `union` fv U1 `union` fv U2 `union` fv G2 `union` L ->
    subtysk' L G2 T2 T1 G1 n1 ->
    subtysk' (union L (union (singleton x) (fv T2)))
            (x ~ T1 ++ G1) (open x U1) (open x U2) (x ~ T2 ++ G2) n2 ->
    subtysk' L G1 (typ_all T1 U1) (typ_all T2 U2) G2 (1 + n1 + n2)
| ssk'_sel1 : forall L G1 G2 x T S n,
    binds x T G2 ->
    subtysk' L G2 T (typ_bnd S typ_top) G1 n ->
    subtysk' L G1 S (typ_sel $ avar_f x) G2 (1 + n)
| ssk'_sel2 : forall L G1 G2 x T U n,
    binds x T G1 ->
    subtysk' L G1 T (typ_bnd typ_bot U) G2 n ->
    subtysk' L G1 (typ_sel $ avar_f x) U G2 (1 + n).

Theorem subtysk_equiv_stareat : forall L G1 S U G2,
    wf_env G1 -> wf_env G2 ->
    fv S [<=] dom G1 -> lc S ->
    fv U [<=] dom G2 -> lc U ->
    [ L `union` fv G1 `union` fv G2 `union` fv S `union` fv U ]
      G1 ⊢k S <⦂ U k⊣ G2 <->
    [ L `union` fv G1 `union` fv G2 `union` fv S `union` fv U ]
      G1 >> S <⦂ U << G2.
