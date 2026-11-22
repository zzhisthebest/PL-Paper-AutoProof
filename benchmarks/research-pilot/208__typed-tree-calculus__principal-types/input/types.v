Require Import String Arith Lia Bool List Nat Datatypes.

Require Import terms.

Open Scope string_scope.

Open Scope nat_scope.

Open Scope tree_scope.

Set Default Proof Using "Type".

Inductive dtype : Set :=
  Var :  nat -> dtype
| Quant : dtype -> dtype
| Funty : dtype -> dtype -> dtype
| Leaf : dtype
| Stem : dtype -> dtype
| Fork : dtype -> dtype -> dtype
| Asf : dtype -> dtype
.

Fixpoint  program_type p :=
  match p with
  | Node => Leaf
  | p1 @ p2 =>
    match program_type p1 with
      Leaf => Stem (program_type p2)
    | Stem ty1 => Fork ty1 (program_type p2)
    | _ => Funty Leaf Leaf
    end
  | _ => Funty Leaf Leaf
  end.

Definition test : forall n m : nat, {n <= m} + {n > m} := ltac:(simple induction n; simple induction m; simpl in |- *; auto with arith;
intros m' H'; elim (H m'); auto with arith).

Definition le_lt : forall n m : nat, n <= m -> {n < m} + {n = m} := ltac:(simple induction n; simple induction m; simpl in |- *; auto with arith;
    intros m' H1 H2; elim (H m'); auto with arith).

Definition compare : forall n m : nat, {n < m} + {n = m} + {n > m} := ltac:(intros n m; elim (test n m); auto with arith;
    left; apply le_lt; trivial with arith).

Definition relocate (i k n : nat) :=
  match test k i with
     | left _ => n+i
     | _ => i
  end.

Definition relocatek1 k i := relocate i k 1.

Fixpoint lift_rec (L : dtype) : nat -> nat -> dtype :=
  fun k n =>
  match L with
  | Var i => Var (relocate i k n)
  | Leaf => Leaf
  | Stem ty => Stem (lift_rec ty k n)
  | Fork ty1 ty2 => Fork (lift_rec ty1 k n) (lift_rec ty2 k n)
  | Funty ty1 ty2 => Funty (lift_rec ty1 k n) (lift_rec ty2 k n)
  | Quant ty => Quant (lift_rec ty (S k) n)
  | Asf ty => Asf (lift_rec ty k n)
  end.

Definition lift (n : nat) (ty : dtype) := lift_rec ty 0 n.

Definition insert_Var (N : dtype) (i k : nat) :=
  match compare k i with

     | inleft (left _) => Var (Nat.pred i)
     | inleft _ => lift k N
     | _ => Var i
  end.

Fixpoint subst_rec (L : dtype) : dtype -> nat -> dtype :=
  fun (N : dtype) (k : nat) =>
  match L with
  | Var i => insert_Var N i k
  | Leaf => Leaf
  | Stem M => Stem (subst_rec M N k)
  | Fork M M' => Fork (subst_rec M N k) (subst_rec M' N k)
  | Funty M M' => Funty (subst_rec M N k) (subst_rec M' N k)
  | Quant M => Quant (subst_rec M N (S k))
  | Asf M => Asf (subst_rec M N k)
  end.

Definition subst (M N : dtype) := subst_rec M N 0.

Fixpoint get x (gamma: list (string * dtype)) :=
  match gamma with
  | (s,ty)::gamma1 => if (s =? x)%string then Some ty else get x gamma1
  | _ => None
  end.

Definition lift_rec_context n k := map (fun (p:string * dtype)  => (fst p, lift_rec (snd p) n k)).

Definition lift_context := lift_rec_context 0.

Definition subst_rec_context uty k := map (fun (p:string * dtype)  => (fst p, subst_rec (snd p) uty k)).

Fixpoint normal_type gamma t :=
  match t with
  | Ref x => get x gamma
  | Node => Some Leaf
  | Node @ t1 => match normal_type gamma t1 with | Some ty => Some (Stem ty) | _ => None end
  | Node @ t1 @ t2 =>
    match (normal_type gamma t1, normal_type gamma t2) with
    | (Some ty1, Some ty2) => Some (Fork ty1 ty2)
    | (_,_) => None
    end
  | _ => None
  end.

Fixpoint quant n ty :=
  match n with
  | 0 => ty
  | S n1 => quant n1 (Quant ty)
  end.

Fixpoint quantf n ty :=
  match n with
  | 0 => ty
  | S n1 => quantf n1 (Asf ty)
  end.

Fixpoint quanta bs ty :=
  match bs with
    nil => ty
  | true :: bs1 => quanta bs1 (Quant ty)
  | false :: bs1 => quanta bs1 (Asf ty)
  end.

Fixpoint quant_count bs :=
  match bs with
    nil => 0
  | true :: bs1 => S (quant_count bs1)
  | false :: bs1 => quant_count bs1
  end.

Fixpoint quant_to_quanta n :=
  match n with
  | 0 => nil
  | S n1 => true :: (quant_to_quanta n1)
  end.

Fixpoint variant pos k ty :=


  match ty with
  | Var n => if k=?n then pos else true
  | Quant ty1 => variant pos (S k) ty1
  | Funty ty1 ty2 => variant (negb pos) k ty1 && variant pos k ty2
  | Leaf => true
  | Stem ty1 => variant pos k ty1
  | Fork ty1 ty2 => variant pos k ty1 && variant pos k ty2
  | Asf ty1 => variant pos k ty1
   end.

Definition covariant ty := variant true 0 ty = true.
