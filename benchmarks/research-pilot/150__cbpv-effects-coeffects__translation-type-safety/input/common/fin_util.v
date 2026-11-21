Require Export autosubst2.fintype.

Definition up_ren' {n} := (up_ren (shift (n := n))).

Definition up2_ren' {n} := (up_ren (up_ren' (n := n))).

Definition ren_inj {n m} (renamer : ren n m) :=
    (forall i1 i2, renamer i1 = renamer i2 -> i1 = i2).

Definition ren_match {n m X} (renamer : ren n m)
    (fn : fin n -> X) (fm : fin m -> X) :=
    forall i, fn i = fm (renamer i).

Definition default_or_preimage {n m X} (id : X) (fm : fin m -> X) (renamer : ren n m) :=
    (forall j, fm j = id \/ exists i, j = renamer i).

Inductive ren_preimage_cases {n m} (renamer : ren n m) (j : fin m) : Type :=
    | preimage (i : fin n) (H : j = renamer i) : ren_preimage_cases renamer j
    | no_preimage (H : forall (i : fin n), renamer i <> j) : ren_preimage_cases renamer j
    .

Definition env_map {n}{A B} (f : A -> B) (ρ : fin n -> A) : fin n -> B :=
  fun x => f (ρ (x)).
