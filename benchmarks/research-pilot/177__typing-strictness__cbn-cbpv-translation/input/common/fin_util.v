Require Export strictness.autosubst2.fintype.

Fixpoint fin_eqb {n : nat} : fin n -> fin n -> bool :=
  match n return fin n -> fin n -> bool with
  | O => fun i => match i with end
  | S m => fun i j =>
      match i, j with
      | None, None => true
      | Some i', Some j' => @fin_eqb m i' j'
      | _, _ => false
      end
  end.

Definition up_ren' {n} : ren (S n) (S (S n)) := (var_zero .: shift >> shift).

Definition up2_ren' {n} : ren (S (S n)) (S (S (S n))) := (var_zero .: (shift (var_zero) .: shift >> shift >> shift)).

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
