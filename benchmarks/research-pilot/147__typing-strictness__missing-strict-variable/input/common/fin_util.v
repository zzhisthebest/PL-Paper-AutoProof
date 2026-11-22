Require Export strictness.autosubst2.fintype.

Definition fin_eqb : forall {n : nat}, fin n -> fin n -> bool :=
fun n : nat =>
nat_rec (fun n0 : nat => fin n0 -> fin n0 -> bool)
  (fun _ H : fin 0 => False_rec bool H)
  (fun (n0 : nat) (IHn : fin n0 -> fin n0 -> bool) (i1 i2 : fin (S n0)) =>
   let f := i1 in
   let H1 : i1 = f := eq_refl in
   match f as o return (i1 = o -> bool) with
   | Some f0 =>
       (fun
          (i1' : (fix fin (n1 : nat) : Set :=
                    match n1 with
                    | 0 => False
                    | S m => option (fin m)
                    end)
                   n0)
          (_ : i1 = Some i1') =>
        let f1 := i2 in
        let H2 : i2 = f1 := eq_refl in
        match f1 as o return (i2 = o -> bool) with
        | Some f2 =>
            (fun
               (i2' : (fix fin (n1 : nat) : Set :=
                         match n1 with
                         | 0 => False
                         | S m => option (fin m)
                         end)
                        n0)
               (_ : i2 = Some i2') =>
             let b := IHn i1' i2' in
             let IHe : IHn i1' i2' = b := eq_refl in
             (if b as b0 return (IHn i1' i2' = b0 -> bool)
              then fun _ : IHn i1' i2' = true => true
              else fun _ : IHn i1' i2' = false => false) IHe) f2
        | None => fun _ : i2 = None => false
        end H2) f0
   | None =>
       fun _ : i1 = None =>
       let f0 := i2 in
       let H2 : i2 = f0 := eq_refl in
       match f0 as o return (i2 = o -> bool) with
       | Some f1 =>
           (fun
              (i2' : (fix fin (n1 : nat) : Set :=
                        match n1 with
                        | 0 => False
                        | S m => option (fin m)
                        end)
                       n0)
              (_ : i2 = Some i2') =>
            false) f1
       | None => fun _ : i2 = None => true
       end H2
   end H1)
  n.
Arguments fin_eqb {n} _ _.

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
