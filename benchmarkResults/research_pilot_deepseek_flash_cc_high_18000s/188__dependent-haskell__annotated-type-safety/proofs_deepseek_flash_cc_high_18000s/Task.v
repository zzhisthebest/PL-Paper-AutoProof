Require Import Language.
Require Import Lia.
Require Import List.
Import ListNotations.
Inductive erased_sort : sort -> Prop :=
| erased_Tm : forall a, erased_tm a -> erased_sort (Tm a)
| erased_Co : forall a b A, erased_tm a -> erased_tm b -> erased_tm A -> erased_sort (Co (Eq a b A)).

Definition erased_context : context -> Prop :=
  Forall (fun p => match p with (a,s) => erased_sort s end).

Definition Good (G : context) (D : available_props):=
  erased_context G /\
  forall c1 A B1 T1,
    binds c1 (Co (Eq A B1 T1)) G
    -> c1 `in` D
    -> exists C, Par G D A C /\ Par G D B1 C.

Definition AnnGood G D := Good (erase_context G) D.

Definition irrelevant G D (a : tm) :=
  (forall x A, binds x (Tm A) G -> x `notin` fv_tm_tm_tm (erase_tm a)) /\ AnnGood G D.

Import ListNotations.

(** * Auxiliary machinery *)

Definition eq_var (x y : var) : bool :=
  if KeySetFacts.eq_dec x y then true else false.

Lemma eq_var_true : forall x y, eq_var x y = true -> x = y.
Proof.
  intros x y H. unfold eq_var in H.
  destruct (KeySetFacts.eq_dec x y); auto. discriminate.
Qed.

Lemma eq_var_false : forall x y, eq_var x y = false -> x <> y.
Proof.
  intros x y H. unfold eq_var in H.
  destruct (KeySetFacts.eq_dec x y); auto. discriminate.
Qed.

Lemma eq_var_true' : forall x, eq_var x x = true.
Proof.
  intros x. unfold eq_var. destruct (KeySetFacts.eq_dec x x); auto.
Qed.

(** ** "Closed up to level n" predicates.

    [clt_* n x] says that [x] has no bound *term* variable at level [n]
    or above (mirroring the index discipline of [open_*_wrt_tm_rec]).
    [clc_* n x] says the same for bound *coercion* variables
    (mirroring [open_*_wrt_co_rec]). *)

Fixpoint clt_tm (n:nat) (a:tm) : Prop :=
  match a with
  | a_Star => True
  | a_Var_b m => m < n
  | a_Var_f _ => True
  | a_Abs rho A b => clt_tm n A /\ clt_tm (S n) b
  | a_UAbs rho b => clt_tm (S n) b
  | a_App a _ b => clt_tm n a /\ clt_tm n b
  | a_Fam _ => True
  | a_Const _ => True
  | a_Pi rho A B => clt_tm n A /\ clt_tm (S n) B
  | a_Conv a g => clt_tm n a /\ clt_co n g
  | a_CPi phi B => clt_constraint n phi /\ clt_tm n B
  | a_CAbs phi b => clt_constraint n phi /\ clt_tm n b
  | a_UCAbs b => clt_tm n b
  | a_CApp a g => clt_tm n a /\ clt_co n g
  | a_Bullet => True
  | a_DataCon _ => True
  | a_Case a brs => clt_tm n a /\ clt_brs n brs
  end
with clt_brs (n:nat) (b:brs) : Prop :=
  match b with
  | br_None => True
  | br_One _ a b' => clt_tm n a /\ clt_brs n b'
  end
with clt_co (n:nat) (g:co) : Prop :=
  match g with
  | g_Triv => True
  | g_Var_b _ => True
  | g_Var_f _ => True
  | g_Beta a b => clt_tm n a /\ clt_tm n b
  | g_Refl a => clt_tm n a
  | g_Refl2 a b g' => clt_tm n a /\ clt_tm n b /\ clt_co n g'
  | g_Sym g' => clt_co n g'
  | g_Trans g1 g2 => clt_co n g1 /\ clt_co n g2
  | g_PiCong _ g1 g2 => clt_co n g1 /\ clt_co (S n) g2
  | g_AbsCong _ g1 g2 => clt_co n g1 /\ clt_co (S n) g2
  | g_AppCong g1 _ g2 => clt_co n g1 /\ clt_co n g2
  | g_PiFst g' => clt_co n g'
  | g_CPiFst g' => clt_co n g'
  | g_IsoSnd g' => clt_co n g'
  | g_PiSnd g1 g2 => clt_co n g1 /\ clt_co n g2
  | g_CPiCong g1 g3 => clt_co n g1 /\ clt_co n g3
  | g_CAbsCong g1 g3 g4 => clt_co n g1 /\ clt_co n g3 /\ clt_co n g4
  | g_CAppCong g g1 g2 => clt_co n g /\ clt_co n g1 /\ clt_co n g2
  | g_CPiSnd g g1 g2 => clt_co n g /\ clt_co n g1 /\ clt_co n g2
  | g_Cast g1 g2 => clt_co n g1 /\ clt_co n g2
  | g_EqCong g1 A g2 => clt_co n g1 /\ clt_tm n A /\ clt_co n g2
  | g_IsoConv phi1 phi2 g => clt_constraint n phi1 /\ clt_constraint n phi2 /\ clt_co n g
  | g_Eta a => clt_tm n a
  | g_Left g g' => clt_co n g /\ clt_co n g'
  | g_Right g g' => clt_co n g /\ clt_co n g'
  end
with clt_constraint (n:nat) (phi:constraint) : Prop :=
  match phi with
  | Eq a b A => clt_tm n a /\ clt_tm n b /\ clt_tm n A
  end.

Fixpoint clc_tm (n:nat) (a:tm) : Prop :=
  match a with
  | a_Star => True
  | a_Var_b _ => True
  | a_Var_f _ => True
  | a_Abs rho A b => clc_tm n A /\ clc_tm n b
  | a_UAbs rho b => clc_tm n b
  | a_App a _ b => clc_tm n a /\ clc_tm n b
  | a_Fam _ => True
  | a_Const _ => True
  | a_Pi rho A B => clc_tm n A /\ clc_tm n B
  | a_Conv a g => clc_tm n a /\ clc_co n g
  | a_CPi phi B => clc_constraint n phi /\ clc_tm (S n) B
  | a_CAbs phi b => clc_constraint n phi /\ clc_tm (S n) b
  | a_UCAbs b => clc_tm (S n) b
  | a_CApp a g => clc_tm n a /\ clc_co n g
  | a_Bullet => True
  | a_DataCon _ => True
  | a_Case a brs => clc_tm n a /\ clc_brs n brs
  end
with clc_brs (n:nat) (b:brs) : Prop :=
  match b with
  | br_None => True
  | br_One _ a b' => clc_tm n a /\ clc_brs n b'
  end
with clc_co (n:nat) (g:co) : Prop :=
  match g with
  | g_Triv => True
  | g_Var_b m => m < n
  | g_Var_f _ => True
  | g_Beta a b => clc_tm n a /\ clc_tm n b
  | g_Refl a => clc_tm n a
  | g_Refl2 a b g' => clc_tm n a /\ clc_tm n b /\ clc_co n g'
  | g_Sym g' => clc_co n g'
  | g_Trans g1 g2 => clc_co n g1 /\ clc_co n g2
  | g_PiCong _ g1 g2 => clc_co n g1 /\ clc_co n g2
  | g_AbsCong _ g1 g2 => clc_co n g1 /\ clc_co n g2
  | g_AppCong g1 _ g2 => clc_co n g1 /\ clc_co n g2
  | g_PiFst g' => clc_co n g'
  | g_CPiFst g' => clc_co n g'
  | g_IsoSnd g' => clc_co n g'
  | g_PiSnd g1 g2 => clc_co n g1 /\ clc_co n g2
  | g_CPiCong g1 g3 => clc_co n g1 /\ clc_co (S n) g3
  | g_CAbsCong g1 g3 g4 => clc_co n g1 /\ clc_co (S n) g3 /\ clc_co n g4
  | g_CAppCong g g1 g2 => clc_co n g /\ clc_co n g1 /\ clc_co n g2
  | g_CPiSnd g g1 g2 => clc_co n g /\ clc_co n g1 /\ clc_co n g2
  | g_Cast g1 g2 => clc_co n g1 /\ clc_co n g2
  | g_EqCong g1 A g2 => clc_co n g1 /\ clc_tm n A /\ clc_co n g2
  | g_IsoConv phi1 phi2 g => clc_constraint n phi1 /\ clc_constraint n phi2 /\ clc_co n g
  | g_Eta a => clc_tm n a
  | g_Left g g' => clc_co n g /\ clc_co n g'
  | g_Right g g' => clc_co n g /\ clc_co n g'
  end
with clc_constraint (n:nat) (phi:constraint) : Prop :=
  match phi with
  | Eq a b A => clc_tm n a /\ clc_tm n b /\ clc_tm n A
  end.

Scheme tm_ind' := Induction for tm Sort Prop
 with brs_ind' := Induction for brs Sort Prop
 with co_ind' := Induction for co Sort Prop
 with constraint_ind' := Induction for constraint Sort Prop.
Combined Scheme tm_mutind from tm_ind', brs_ind', co_ind', constraint_ind'.

Scheme lc_tm_ind' := Induction for lc_tm Sort Prop
 with lc_co_ind' := Induction for lc_co Sort Prop
 with lc_brs_ind' := Induction for lc_brs Sort Prop
 with lc_constraint_ind' := Induction for lc_constraint Sort Prop.
Combined Scheme lc_mutind from lc_tm_ind', lc_co_ind', lc_brs_ind', lc_constraint_ind'.

Ltac crush_conj :=
  repeat match goal with
  | H : _ /\ _ |- _ => destruct H
  | |- _ /\ _ => split
  end.

(** Monotonicity of the level predicates. *)

Lemma clt_mono :
  (forall a n m, n <= m -> clt_tm n a -> clt_tm m a) /\
  (forall b n m, n <= m -> clt_brs n b -> clt_brs m b) /\
  (forall g n m, n <= m -> clt_co n g -> clt_co m g) /\
  (forall phi n m, n <= m -> clt_constraint n phi -> clt_constraint m phi).
Proof.
  apply (tm_mutind
           (fun a => forall n m, n <= m -> clt_tm n a -> clt_tm m a)
           (fun b => forall n m, n <= m -> clt_brs n b -> clt_brs m b)
           (fun g => forall n m, n <= m -> clt_co n g -> clt_co m g)
           (fun phi => forall n m, n <= m -> clt_constraint n phi -> clt_constraint m phi)).
  all: try solve [exact I].
  all: intros; cbn [clt_tm clt_brs clt_co clt_constraint] in *;
       crush_conj; try split; try (eauto with arith); try lia.
Qed.

Lemma clt_tm_mono : forall a n m, n <= m -> clt_tm n a -> clt_tm m a.
Proof. intros; eapply clt_mono; eauto. Qed.
Lemma clt_brs_mono : forall b n m, n <= m -> clt_brs n b -> clt_brs m b.
Proof. intros; eapply clt_mono; eauto. Qed.
Lemma clt_co_mono : forall g n m, n <= m -> clt_co n g -> clt_co m g.
Proof. intros; eapply clt_mono; eauto. Qed.
Lemma clt_constraint_mono : forall phi n m, n <= m -> clt_constraint n phi -> clt_constraint m phi.
Proof. intros; eapply clt_mono; eauto. Qed.

Lemma clc_mono :
  (forall a n m, n <= m -> clc_tm n a -> clc_tm m a) /\
  (forall b n m, n <= m -> clc_brs n b -> clc_brs m b) /\
  (forall g n m, n <= m -> clc_co n g -> clc_co m g) /\
  (forall phi n m, n <= m -> clc_constraint n phi -> clc_constraint m phi).
Proof.
  apply (tm_mutind
           (fun a => forall n m, n <= m -> clc_tm n a -> clc_tm m a)
           (fun b => forall n m, n <= m -> clc_brs n b -> clc_brs m b)
           (fun g => forall n m, n <= m -> clc_co n g -> clc_co m g)
           (fun phi => forall n m, n <= m -> clc_constraint n phi -> clc_constraint m phi)).
  all: try solve [exact I].
  all: intros; cbn [clc_tm clc_brs clc_co clc_constraint] in *;
       crush_conj; try split; try (eauto with arith); try lia.
Qed.

Lemma clc_tm_mono : forall a n m, n <= m -> clc_tm n a -> clc_tm m a.
Proof. intros; eapply clc_mono; eauto. Qed.
Lemma clc_brs_mono : forall b n m, n <= m -> clc_brs n b -> clc_brs m b.
Proof. intros; eapply clc_mono; eauto. Qed.
Lemma clc_co_mono : forall g n m, n <= m -> clc_co n g -> clc_co m g.
Proof. intros; eapply clc_mono; eauto. Qed.
Lemma clc_constraint_mono : forall phi n m, n <= m -> clc_constraint n phi -> clc_constraint m phi.
Proof. intros; eapply clc_mono; eauto. Qed.

(** ** Invariance of the level predicates under opening with a *variable*.

    Opening with [a_Var_f x] / [g_Var_f c] never introduces bound variables,
    so the "no variable at level n" predicates are unchanged by it. *)

Ltac break_lt :=
  match goal with
  | H : context [lt_eq_lt_dec ?a ?b] |- _ => destruct (lt_eq_lt_dec a b) as [[Hlt|Heq]|Hgt]
  | |- context [lt_eq_lt_dec ?a ?b] => destruct (lt_eq_lt_dec a b) as [[Hlt|Heq]|Hgt]
  end.

Lemma clt_open_co_var :
  (forall a n k c, clt_tm n (open_tm_wrt_co_rec k (g_Var_f c) a) <-> clt_tm n a) /\
  (forall b n k c, clt_brs n (open_brs_wrt_co_rec k (g_Var_f c) b) <-> clt_brs n b) /\
  (forall g n k c, clt_co n (open_co_wrt_co_rec k (g_Var_f c) g) <-> clt_co n g) /\
  (forall phi n k c, clt_constraint n (open_constraint_wrt_co_rec k (g_Var_f c) phi) <-> clt_constraint n phi).
Proof.
  apply (tm_mutind
    (fun a => forall n k c, clt_tm n (open_tm_wrt_co_rec k (g_Var_f c) a) <-> clt_tm n a)
    (fun b => forall n k c, clt_brs n (open_brs_wrt_co_rec k (g_Var_f c) b) <-> clt_brs n b)
    (fun g => forall n k c, clt_co n (open_co_wrt_co_rec k (g_Var_f c) g) <-> clt_co n g)
    (fun phi => forall n k c, clt_constraint n (open_constraint_wrt_co_rec k (g_Var_f c) phi) <-> clt_constraint n phi)).
  all: intros.
  all: cbn [open_tm_wrt_co_rec open_brs_wrt_co_rec open_co_wrt_co_rec
            open_constraint_wrt_co_rec clt_tm clt_brs clt_co clt_constraint] in *.
  all: try break_lt.
  all: try (repeat match goal with
    | IH : forall (n0:nat) (k0:nat) (c0:covar), _ |- _ =>
        pose proof (IH n k c); pose proof (IH (S n) k c);
        pose proof (IH n (S k) c); pose proof (IH (S n) (S k) c); clear IH
    end).
  all: try tauto.
Qed.

Lemma clc_open_tm_var :
  (forall a n k x, clc_tm n (open_tm_wrt_tm_rec k (a_Var_f x) a) <-> clc_tm n a) /\
  (forall b n k x, clc_brs n (open_brs_wrt_tm_rec k (a_Var_f x) b) <-> clc_brs n b) /\
  (forall g n k x, clc_co n (open_co_wrt_tm_rec k (a_Var_f x) g) <-> clc_co n g) /\
  (forall phi n k x, clc_constraint n (open_constraint_wrt_tm_rec k (a_Var_f x) phi) <-> clc_constraint n phi).
Proof.
  apply (tm_mutind
    (fun a => forall n k x, clc_tm n (open_tm_wrt_tm_rec k (a_Var_f x) a) <-> clc_tm n a)
    (fun b => forall n k x, clc_brs n (open_brs_wrt_tm_rec k (a_Var_f x) b) <-> clc_brs n b)
    (fun g => forall n k x, clc_co n (open_co_wrt_tm_rec k (a_Var_f x) g) <-> clc_co n g)
    (fun phi => forall n k x, clc_constraint n (open_constraint_wrt_tm_rec k (a_Var_f x) phi) <-> clc_constraint n phi)).
  all: intros.
  all: cbn [open_tm_wrt_tm_rec open_brs_wrt_tm_rec open_co_wrt_tm_rec
            open_constraint_wrt_tm_rec clc_tm clc_brs clc_co clc_constraint] in *.
  all: try break_lt.
  all: try (repeat match goal with
    | IH : forall (n0:nat) (k0:nat) (x0:tmvar), _ |- _ =>
        pose proof (IH n k x); pose proof (IH (S n) k x);
        pose proof (IH n (S k) x); pose proof (IH (S n) (S k) x); clear IH
    end).
  all: try tauto.
Qed.

Lemma clt_open_tm_var_inv :
  (forall a k x, clt_tm k (open_tm_wrt_tm_rec k (a_Var_f x) a) -> clt_tm (S k) a) /\
  (forall b k x, clt_brs k (open_brs_wrt_tm_rec k (a_Var_f x) b) -> clt_brs (S k) b) /\
  (forall g k x, clt_co k (open_co_wrt_tm_rec k (a_Var_f x) g) -> clt_co (S k) g) /\
  (forall phi k x, clt_constraint k (open_constraint_wrt_tm_rec k (a_Var_f x) phi) -> clt_constraint (S k) phi).
Proof.
  apply (tm_mutind
    (fun a => forall k x, clt_tm k (open_tm_wrt_tm_rec k (a_Var_f x) a) -> clt_tm (S k) a)
    (fun b => forall k x, clt_brs k (open_brs_wrt_tm_rec k (a_Var_f x) b) -> clt_brs (S k) b)
    (fun g => forall k x, clt_co k (open_co_wrt_tm_rec k (a_Var_f x) g) -> clt_co (S k) g)
    (fun phi => forall k x, clt_constraint k (open_constraint_wrt_tm_rec k (a_Var_f x) phi) -> clt_constraint (S k) phi)).
  all: intros.
  all: cbn [open_tm_wrt_tm_rec open_brs_wrt_tm_rec open_co_wrt_tm_rec
            open_constraint_wrt_tm_rec clt_tm clt_brs clt_co clt_constraint] in *.
  all: try break_lt.
  all: try (cbn [clt_tm clt_brs clt_co clt_constraint] in *).
  all: crush_conj.
  all: try split.
  all: try (repeat match goal with
    | IH : forall (k0:nat) (x0:tmvar), _ |- _ =>
        pose proof (IH k x); pose proof (IH (S k) x); clear IH
    end).
  all: try eauto.
  all: try lia.
Qed.

Lemma clc_open_co_var_inv :
  (forall a k c, clc_tm k (open_tm_wrt_co_rec k (g_Var_f c) a) -> clc_tm (S k) a) /\
  (forall b k c, clc_brs k (open_brs_wrt_co_rec k (g_Var_f c) b) -> clc_brs (S k) b) /\
  (forall g k c, clc_co k (open_co_wrt_co_rec k (g_Var_f c) g) -> clc_co (S k) g) /\
  (forall phi k c, clc_constraint k (open_constraint_wrt_co_rec k (g_Var_f c) phi) -> clc_constraint (S k) phi).
Proof.
  apply (tm_mutind
    (fun a => forall k c, clc_tm k (open_tm_wrt_co_rec k (g_Var_f c) a) -> clc_tm (S k) a)
    (fun b => forall k c, clc_brs k (open_brs_wrt_co_rec k (g_Var_f c) b) -> clc_brs (S k) b)
    (fun g => forall k c, clc_co k (open_co_wrt_co_rec k (g_Var_f c) g) -> clc_co (S k) g)
    (fun phi => forall k c, clc_constraint k (open_constraint_wrt_co_rec k (g_Var_f c) phi) -> clc_constraint (S k) phi)).
  all: intros.
  all: cbn [open_tm_wrt_co_rec open_brs_wrt_co_rec open_co_wrt_co_rec
            open_constraint_wrt_co_rec clc_tm clc_brs clc_co clc_constraint] in *.
  all: try break_lt.
  all: try (cbn [clc_tm clc_brs clc_co clc_constraint] in *).
  all: crush_conj.
  all: try split.
  all: try (repeat match goal with
    | IH : forall (k0:nat) (c0:covar), _ |- _ =>
        pose proof (IH k c); pose proof (IH (S k) c); clear IH
    end).
  all: try eauto.
  all: try lia.
Qed.

(** Extracted projection lemmas for convenient use. *)

Lemma clt_tm_open_co_fwd : forall a n k c,
  clt_tm n (open_tm_wrt_co_rec k (g_Var_f c) a) -> clt_tm n a.
Proof. intros; exact (proj1 (proj1 clt_open_co_var a n k c) H). Qed.
Lemma clt_brs_open_co_fwd : forall b n k c,
  clt_brs n (open_brs_wrt_co_rec k (g_Var_f c) b) -> clt_brs n b.
Proof. intros; exact (proj1 (proj1 (proj2 clt_open_co_var) b n k c) H). Qed.
Lemma clt_co_open_co_fwd : forall g n k c,
  clt_co n (open_co_wrt_co_rec k (g_Var_f c) g) -> clt_co n g.
Proof. intros; exact (proj1 (proj1 (proj2 (proj2 clt_open_co_var)) g n k c) H). Qed.
Lemma clt_constraint_open_co_fwd : forall phi n k c,
  clt_constraint n (open_constraint_wrt_co_rec k (g_Var_f c) phi) -> clt_constraint n phi.
Proof. intros; exact (proj1 (proj2 (proj2 (proj2 clt_open_co_var)) phi n k c) H). Qed.

Lemma clc_tm_open_tm_fwd : forall a n k x,
  clc_tm n (open_tm_wrt_tm_rec k (a_Var_f x) a) -> clc_tm n a.
Proof. intros; exact (proj1 (proj1 clc_open_tm_var a n k x) H). Qed.
Lemma clc_brs_open_tm_fwd : forall b n k x,
  clc_brs n (open_brs_wrt_tm_rec k (a_Var_f x) b) -> clc_brs n b.
Proof. intros; exact (proj1 (proj1 (proj2 clc_open_tm_var) b n k x) H). Qed.
Lemma clc_co_open_tm_fwd : forall g n k x,
  clc_co n (open_co_wrt_tm_rec k (a_Var_f x) g) -> clc_co n g.
Proof. intros; exact (proj1 (proj1 (proj2 (proj2 clc_open_tm_var)) g n k x) H). Qed.
Lemma clc_constraint_open_tm_fwd : forall phi n k x,
  clc_constraint n (open_constraint_wrt_tm_rec k (a_Var_f x) phi) -> clc_constraint n phi.
Proof. intros; exact (proj1 (proj2 (proj2 (proj2 clc_open_tm_var)) phi n k x) H). Qed.

Lemma clt_tm_open_tm_var_inv : forall a k x,
  clt_tm k (open_tm_wrt_tm_rec k (a_Var_f x) a) -> clt_tm (S k) a.
Proof. intros; exact (proj1 clt_open_tm_var_inv a k x H). Qed.
Lemma clt_brs_open_tm_var_inv : forall b k x,
  clt_brs k (open_brs_wrt_tm_rec k (a_Var_f x) b) -> clt_brs (S k) b.
Proof. intros; exact (proj1 (proj2 clt_open_tm_var_inv) b k x H). Qed.
Lemma clt_co_open_tm_var_inv : forall g k x,
  clt_co k (open_co_wrt_tm_rec k (a_Var_f x) g) -> clt_co (S k) g.
Proof. intros; exact (proj1 (proj2 (proj2 clt_open_tm_var_inv)) g k x H). Qed.
Lemma clt_constraint_open_tm_var_inv : forall phi k x,
  clt_constraint k (open_constraint_wrt_tm_rec k (a_Var_f x) phi) -> clt_constraint (S k) phi.
Proof. intros; exact (proj2 (proj2 (proj2 clt_open_tm_var_inv)) phi k x H). Qed.

Lemma clc_tm_open_co_var_inv : forall a k c,
  clc_tm k (open_tm_wrt_co_rec k (g_Var_f c) a) -> clc_tm (S k) a.
Proof. intros; exact (proj1 clc_open_co_var_inv a k c H). Qed.
Lemma clc_brs_open_co_var_inv : forall b k c,
  clc_brs k (open_brs_wrt_co_rec k (g_Var_f c) b) -> clc_brs (S k) b.
Proof. intros; exact (proj1 (proj2 clc_open_co_var_inv) b k c H). Qed.
Lemma clc_co_open_co_var_inv : forall g k c,
  clc_co k (open_co_wrt_co_rec k (g_Var_f c) g) -> clc_co (S k) g.
Proof. intros; exact (proj1 (proj2 (proj2 clc_open_co_var_inv)) g k c H). Qed.
Lemma clc_constraint_open_co_var_inv : forall phi k c,
  clc_constraint k (open_constraint_wrt_co_rec k (g_Var_f c) phi) -> clc_constraint (S k) phi.
Proof. intros; exact (proj2 (proj2 (proj2 clc_open_co_var_inv)) phi k c H). Qed.

(** [lc] implies being closed at level 0, for both kinds of indices. *)

Lemma lc_clt_clc :
  (forall a (l:lc_tm a), clt_tm 0 a /\ clc_tm 0 a) /\
  (forall g (l:lc_co g), clt_co 0 g /\ clc_co 0 g) /\
  (forall b (l:lc_brs b), clt_brs 0 b /\ clc_brs 0 b) /\
  (forall phi (l:lc_constraint phi), clt_constraint 0 phi /\ clc_constraint 0 phi).
Proof.
  apply (lc_mutind
    (fun a _ => clt_tm 0 a /\ clc_tm 0 a)
    (fun g _ => clt_co 0 g /\ clc_co 0 g)
    (fun b _ => clt_brs 0 b /\ clc_brs 0 b)
    (fun phi _ => clt_constraint 0 phi /\ clc_constraint 0 phi)).
  all: intros.
  all: cbn [clt_tm clt_brs clt_co clt_constraint clc_tm clc_brs clc_co clc_constraint] in *.
  all: try (repeat match goal with
    | H : forall x : tmvar, _ |- _ => pose proof (H Fix); clear H
    | H : forall c : covar, _ |- _ => pose proof (H Fix); clear H
    end).
  all: crush_conj.
  all: try solve [exact I].
  all: try (eauto using clt_tm_open_tm_var_inv, clt_brs_open_tm_var_inv,
                          clt_co_open_tm_var_inv, clt_constraint_open_tm_var_inv,
                          clc_tm_open_tm_fwd, clc_brs_open_tm_fwd,
                          clc_co_open_tm_fwd, clc_constraint_open_tm_fwd,
                          clt_tm_open_co_fwd, clt_brs_open_co_fwd,
                          clt_co_open_co_fwd, clt_constraint_open_co_fwd,
                          clc_tm_open_co_var_inv, clc_brs_open_co_var_inv,
                          clc_co_open_co_var_inv, clc_constraint_open_co_var_inv).
Qed.

(** Opening at a level strictly above all unclosed indices is the identity. *)

Lemma open_tm_var_b_closed : forall m k u,
  m < k -> open_tm_wrt_tm_rec k u (a_Var_b m) = a_Var_b m.
Proof.
  intros m k u H. cbn [open_tm_wrt_tm_rec].
  destruct (lt_eq_lt_dec m k) as [[Hlt|Heq]|Hgt]; try reflexivity; lia.
Qed.

Lemma open_co_var_b_closed : forall m k g,
  m < k -> open_co_wrt_co_rec k g (g_Var_b m) = g_Var_b m.
Proof.
  intros m k g H. cbn [open_co_wrt_co_rec].
  destruct (lt_eq_lt_dec m k) as [[Hlt|Heq]|Hgt]; try reflexivity; lia.
Qed.

Lemma clt_closed_open :
  (forall a, clt_tm 0 a -> True) /\
  (forall b, clt_brs 0 b -> True).
Proof. auto. Qed.

Ltac solve_closed_open :=
  first
  [ reflexivity
  | match goal with
    | |- open_tm_wrt_tm_rec ?k ?u ?x = ?x =>
        match goal with H : forall n0, clt_tm n0 ?x -> _, Hc : clt_tm ?n ?x |- _ =>
          exact (H n Hc k ltac:(lia) u) end
    | |- open_brs_wrt_tm_rec ?k ?u ?x = ?x =>
        match goal with H : forall n0, clt_brs n0 ?x -> _, Hc : clt_brs ?n ?x |- _ =>
          exact (H n Hc k ltac:(lia) u) end
    | |- open_co_wrt_tm_rec ?k ?u ?x = ?x =>
        match goal with H : forall n0, clt_co n0 ?x -> _, Hc : clt_co ?n ?x |- _ =>
          exact (H n Hc k ltac:(lia) u) end
    | |- open_constraint_wrt_tm_rec ?k ?u ?x = ?x =>
        match goal with H : forall n0, clt_constraint n0 ?x -> _, Hc : clt_constraint ?n ?x |- _ =>
          exact (H n Hc k ltac:(lia) u) end
    | |- context [lt_eq_lt_dec ?a ?b] =>
        destruct (lt_eq_lt_dec a b) as [[Hlt|Heq]|Hgt]; try reflexivity; lia
    end ].

Lemma clt_closed_open_tm :
  (forall a, forall n, clt_tm n a -> forall k, n <= k -> forall u,
     open_tm_wrt_tm_rec k u a = a) /\
  (forall b, forall n, clt_brs n b -> forall k, n <= k -> forall u,
     open_brs_wrt_tm_rec k u b = b) /\
  (forall g, forall n, clt_co n g -> forall k, n <= k -> forall u,
     open_co_wrt_tm_rec k u g = g) /\
  (forall phi, forall n, clt_constraint n phi -> forall k, n <= k -> forall u,
     open_constraint_wrt_tm_rec k u phi = phi).
Proof.
  apply (tm_mutind
    (fun a => forall n, clt_tm n a -> forall k, n <= k -> forall u,
                open_tm_wrt_tm_rec k u a = a)
    (fun b => forall n, clt_brs n b -> forall k, n <= k -> forall u,
                open_brs_wrt_tm_rec k u b = b)
    (fun g => forall n, clt_co n g -> forall k, n <= k -> forall u,
                open_co_wrt_tm_rec k u g = g)
    (fun phi => forall n, clt_constraint n phi -> forall k, n <= k -> forall u,
                open_constraint_wrt_tm_rec k u phi = phi)).
  all: intros.
  all: cbn [clt_tm clt_brs clt_co clt_constraint] in *.
  all: crush_conj.
  all: cbn [open_tm_wrt_tm_rec open_brs_wrt_tm_rec open_co_wrt_tm_rec open_constraint_wrt_tm_rec].
  all: try reflexivity.
  all: try (repeat f_equal).
  all: try solve_closed_open.
Qed.

Ltac solve_closed_open_co :=
  first
  [ reflexivity
  | match goal with
    | |- open_tm_wrt_co_rec ?k ?u ?x = ?x =>
        match goal with H : forall n0, clc_tm n0 ?x -> _, Hc : clc_tm ?n ?x |- _ =>
          exact (H n Hc k ltac:(lia) u) end
    | |- open_brs_wrt_co_rec ?k ?u ?x = ?x =>
        match goal with H : forall n0, clc_brs n0 ?x -> _, Hc : clc_brs ?n ?x |- _ =>
          exact (H n Hc k ltac:(lia) u) end
    | |- open_co_wrt_co_rec ?k ?u ?x = ?x =>
        match goal with H : forall n0, clc_co n0 ?x -> _, Hc : clc_co ?n ?x |- _ =>
          exact (H n Hc k ltac:(lia) u) end
    | |- open_constraint_wrt_co_rec ?k ?u ?x = ?x =>
        match goal with H : forall n0, clc_constraint n0 ?x -> _, Hc : clc_constraint ?n ?x |- _ =>
          exact (H n Hc k ltac:(lia) u) end
    | |- context [lt_eq_lt_dec ?a ?b] =>
        destruct (lt_eq_lt_dec a b) as [[Hlt|Heq]|Hgt]; try reflexivity; lia
    end ].

Lemma clc_closed_open_co :
  (forall a, forall n, clc_tm n a -> forall k, n <= k -> forall g,
     open_tm_wrt_co_rec k g a = a) /\
  (forall b, forall n, clc_brs n b -> forall k, n <= k -> forall g,
     open_brs_wrt_co_rec k g b = b) /\
  (forall g, forall n, clc_co n g -> forall k, n <= k -> forall g0,
     open_co_wrt_co_rec k g0 g = g) /\
  (forall phi, forall n, clc_constraint n phi -> forall k, n <= k -> forall g,
     open_constraint_wrt_co_rec k g phi = phi).
Proof.
  apply (tm_mutind
    (fun a => forall n, clc_tm n a -> forall k, n <= k -> forall g,
                open_tm_wrt_co_rec k g a = a)
    (fun b => forall n, clc_brs n b -> forall k, n <= k -> forall g,
                open_brs_wrt_co_rec k g b = b)
    (fun g => forall n, clc_co n g -> forall k, n <= k -> forall g0,
                open_co_wrt_co_rec k g0 g = g)
    (fun phi => forall n, clc_constraint n phi -> forall k, n <= k -> forall g,
                open_constraint_wrt_co_rec k g phi = phi)).
  all: intros.
  all: cbn [clc_tm clc_brs clc_co clc_constraint] in *.
  all: crush_conj.
  all: cbn [open_tm_wrt_co_rec open_brs_wrt_co_rec open_co_wrt_co_rec open_constraint_wrt_co_rec].
  all: try reflexivity.
  all: try (repeat f_equal).
  all: try solve_closed_open_co.
Qed.

(** Accessors for [lc] implying closedness. *)

Lemma lc_clt_tm : forall a, lc_tm a -> clt_tm 0 a.
Proof. intros; exact (proj1 (proj1 lc_clt_clc a H)). Qed.
Lemma lc_clc_tm : forall a, lc_tm a -> clc_tm 0 a.
Proof. intros; exact (proj2 (proj1 lc_clt_clc a H)). Qed.
Lemma lc_clt_co : forall g, lc_co g -> clt_co 0 g.
Proof. intros; exact (proj1 (proj1 (proj2 lc_clt_clc) g H)). Qed.
Lemma lc_clc_co : forall g, lc_co g -> clc_co 0 g.
Proof. intros; exact (proj2 (proj1 (proj2 lc_clt_clc) g H)). Qed.
Lemma lc_clt_brs : forall b, lc_brs b -> clt_brs 0 b.
Proof. intros; exact (proj1 (proj1 (proj2 (proj2 lc_clt_clc)) b H)). Qed.
Lemma lc_clc_brs : forall b, lc_brs b -> clc_brs 0 b.
Proof. intros; exact (proj2 (proj1 (proj2 (proj2 lc_clt_clc)) b H)). Qed.
Lemma lc_clt_constraint : forall phi, lc_constraint phi -> clt_constraint 0 phi.
Proof. intros; exact (proj1 (proj2 (proj2 (proj2 lc_clt_clc)) phi H)). Qed.
Lemma lc_clc_constraint : forall phi, lc_constraint phi -> clc_constraint 0 phi.
Proof. intros; exact (proj2 (proj2 (proj2 (proj2 lc_clt_clc)) phi H)). Qed.

(** A. Opening a locally closed object at level 0 changes nothing. *)

Lemma lc_open_id :
  (forall a, lc_tm a -> forall u, open_tm_wrt_tm a u = a) /\
  (forall a, lc_tm a -> forall g, open_tm_wrt_co a g = a) /\
  (forall b, lc_brs b -> forall u, open_brs_wrt_tm_rec 0 u b = b) /\
  (forall b, lc_brs b -> forall g, open_brs_wrt_co_rec 0 g b = b) /\
  (forall g, lc_co g -> forall u, open_co_wrt_tm g u = g) /\
  (forall g, lc_co g -> forall g0, open_co_wrt_co g g0 = g) /\
  (forall phi, lc_constraint phi -> forall u, open_constraint_wrt_tm_rec 0 u phi = phi) /\
  (forall phi, lc_constraint phi -> forall g, open_constraint_wrt_co_rec 0 g phi = phi).
Proof.
  repeat split.
  - intros a Hl u. unfold open_tm_wrt_tm.
    exact (proj1 clt_closed_open_tm a 0 (lc_clt_tm a Hl) 0 (le_n 0) u).
  - intros a Hl g. unfold open_tm_wrt_co.
    exact (proj1 clc_closed_open_co a 0 (lc_clc_tm a Hl) 0 (le_n 0) g).
  - intros b Hl u.
    exact (proj1 (proj2 clt_closed_open_tm) b 0 (lc_clt_brs b Hl) 0 (le_n 0) u).
  - intros b Hl g.
    exact (proj1 (proj2 clc_closed_open_co) b 0 (lc_clc_brs b Hl) 0 (le_n 0) g).
  - intros g Hl u. unfold open_co_wrt_tm.
    exact (proj1 (proj2 (proj2 clt_closed_open_tm)) g 0 (lc_clt_co g Hl) 0 (le_n 0) u).
  - intros g Hl g0. unfold open_co_wrt_co.
    exact (proj1 (proj2 (proj2 clc_closed_open_co)) g 0 (lc_clc_co g Hl) 0 (le_n 0) g0).
  - intros phi Hl u.
    exact (proj2 (proj2 (proj2 clt_closed_open_tm)) phi 0 (lc_clt_constraint phi Hl) 0 (le_n 0) u).
  - intros phi Hl g.
    exact (proj2 (proj2 (proj2 clc_closed_open_co)) phi 0 (lc_clc_constraint phi Hl) 0 (le_n 0) g).
Qed.


(* ==== substitution/renaming/closing defs from parallel work ==== *)


(* ------------------------------------------------------------------ *)
(* Free-name substitution (capture-free, since binders use bvars)      *)
(* ------------------------------------------------------------------ *)

Fixpoint subst_tm_tm (x:atom) (u:tm) (a:tm) {struct a} : tm :=
  match a with
  | a_Star => a_Star
  | a_Var_b n => a_Var_b n
  | a_Var_f y => if KeySetFacts.eq_dec y x then u else a_Var_f y
  | a_Abs rho A b => a_Abs rho (subst_tm_tm x u A) (subst_tm_tm x u b)
  | a_UAbs rho b => a_UAbs rho (subst_tm_tm x u b)
  | a_App p rho q => a_App (subst_tm_tm x u p) rho (subst_tm_tm x u q)
  | a_Fam F => a_Fam F
  | a_Const T => a_Const T
  | a_Pi rho A B => a_Pi rho (subst_tm_tm x u A) (subst_tm_tm x u B)
  | a_Conv p g => a_Conv (subst_tm_tm x u p) (subst_tm_co x u g)
  | a_CPi phi B => a_CPi (subst_tm_constraint x u phi) (subst_tm_tm x u B)
  | a_CAbs phi b => a_CAbs (subst_tm_constraint x u phi) (subst_tm_tm x u b)
  | a_UCAbs b => a_UCAbs (subst_tm_tm x u b)
  | a_CApp p g => a_CApp (subst_tm_tm x u p) (subst_tm_co x u g)
  | a_Bullet => a_Bullet
  | a_DataCon K => a_DataCon K
  | a_Case p br => a_Case (subst_tm_tm x u p) (subst_tm_brs x u br)
  end
with subst_tm_brs (x:atom) (u:tm) (b:brs) {struct b} : brs :=
  match b with
  | br_None => br_None
  | br_One K a rest => br_One K (subst_tm_tm x u a) (subst_tm_brs x u rest)
  end
with subst_tm_co (x:atom) (u:tm) (g:co) {struct g} : co :=
  match g with
  | g_Triv => g_Triv
  | g_Var_b n => g_Var_b n
  | g_Var_f c => g_Var_f c
  | g_Beta a b => g_Beta (subst_tm_tm x u a) (subst_tm_tm x u b)
  | g_Refl a => g_Refl (subst_tm_tm x u a)
  | g_Refl2 a b h => g_Refl2 (subst_tm_tm x u a) (subst_tm_tm x u b) (subst_tm_co x u h)
  | g_Sym h => g_Sym (subst_tm_co x u h)
  | g_Trans h1 h2 => g_Trans (subst_tm_co x u h1) (subst_tm_co x u h2)
  | g_PiCong rho h1 h2 => g_PiCong rho (subst_tm_co x u h1) (subst_tm_co x u h2)
  | g_AbsCong rho h1 h2 => g_AbsCong rho (subst_tm_co x u h1) (subst_tm_co x u h2)
  | g_AppCong h1 rho h2 => g_AppCong (subst_tm_co x u h1) rho (subst_tm_co x u h2)
  | g_PiFst h => g_PiFst (subst_tm_co x u h)
  | g_CPiFst h => g_CPiFst (subst_tm_co x u h)
  | g_IsoSnd h => g_IsoSnd (subst_tm_co x u h)
  | g_PiSnd h1 h2 => g_PiSnd (subst_tm_co x u h1) (subst_tm_co x u h2)
  | g_CPiCong h1 h3 => g_CPiCong (subst_tm_co x u h1) (subst_tm_co x u h3)
  | g_CAbsCong h1 h3 h4 => g_CAbsCong (subst_tm_co x u h1) (subst_tm_co x u h3) (subst_tm_co x u h4)
  | g_CAppCong h h1 h2 => g_CAppCong (subst_tm_co x u h) (subst_tm_co x u h1) (subst_tm_co x u h2)
  | g_CPiSnd h h1 h2 => g_CPiSnd (subst_tm_co x u h) (subst_tm_co x u h1) (subst_tm_co x u h2)
  | g_Cast h1 h2 => g_Cast (subst_tm_co x u h1) (subst_tm_co x u h2)
  | g_EqCong h1 A h2 => g_EqCong (subst_tm_co x u h1) (subst_tm_tm x u A) (subst_tm_co x u h2)
  | g_IsoConv p1 p2 h => g_IsoConv (subst_tm_constraint x u p1) (subst_tm_constraint x u p2) (subst_tm_co x u h)
  | g_Eta a => g_Eta (subst_tm_tm x u a)
  | g_Left h1 h2 => g_Left (subst_tm_co x u h1) (subst_tm_co x u h2)
  | g_Right h1 h2 => g_Right (subst_tm_co x u h1) (subst_tm_co x u h2)
  end
with subst_tm_constraint (x:atom) (u:tm) (p:constraint) {struct p} : constraint :=
  match p with
  | Eq a b A => Eq (subst_tm_tm x u a) (subst_tm_tm x u b) (subst_tm_tm x u A)
  end.

(* Coercion-variable substitution (capture-free) *)

Fixpoint subst_co_tm (c:atom) (g:co) (a:tm) {struct a} : tm :=
  match a with
  | a_Star => a_Star
  | a_Var_b n => a_Var_b n
  | a_Var_f y => a_Var_f y
  | a_Abs rho A b => a_Abs rho (subst_co_tm c g A) (subst_co_tm c g b)
  | a_UAbs rho b => a_UAbs rho (subst_co_tm c g b)
  | a_App p rho q => a_App (subst_co_tm c g p) rho (subst_co_tm c g q)
  | a_Fam F => a_Fam F
  | a_Const T => a_Const T
  | a_Pi rho A B => a_Pi rho (subst_co_tm c g A) (subst_co_tm c g B)
  | a_Conv p h => a_Conv (subst_co_tm c g p) (subst_co_co c g h)
  | a_CPi phi B => a_CPi (subst_co_constraint c g phi) (subst_co_tm c g B)
  | a_CAbs phi b => a_CAbs (subst_co_constraint c g phi) (subst_co_tm c g b)
  | a_UCAbs b => a_UCAbs (subst_co_tm c g b)
  | a_CApp p h => a_CApp (subst_co_tm c g p) (subst_co_co c g h)
  | a_Bullet => a_Bullet
  | a_DataCon K => a_DataCon K
  | a_Case p br => a_Case (subst_co_tm c g p) (subst_co_brs c g br)
  end
with subst_co_brs (c:atom) (g:co) (b:brs) {struct b} : brs :=
  match b with
  | br_None => br_None
  | br_One K a rest => br_One K (subst_co_tm c g a) (subst_co_brs c g rest)
  end
with subst_co_co (c:atom) (g:co) (h:co) {struct h} : co :=
  match h with
  | g_Triv => g_Triv
  | g_Var_b n => g_Var_b n
  | g_Var_f y => if KeySetFacts.eq_dec y c then g else g_Var_f y
  | g_Beta a b => g_Beta (subst_co_tm c g a) (subst_co_tm c g b)
  | g_Refl a => g_Refl (subst_co_tm c g a)
  | g_Refl2 a b h1 => g_Refl2 (subst_co_tm c g a) (subst_co_tm c g b) (subst_co_co c g h1)
  | g_Sym h1 => g_Sym (subst_co_co c g h1)
  | g_Trans h1 h2 => g_Trans (subst_co_co c g h1) (subst_co_co c g h2)
  | g_PiCong rho h1 h2 => g_PiCong rho (subst_co_co c g h1) (subst_co_co c g h2)
  | g_AbsCong rho h1 h2 => g_AbsCong rho (subst_co_co c g h1) (subst_co_co c g h2)
  | g_AppCong h1 rho h2 => g_AppCong (subst_co_co c g h1) rho (subst_co_co c g h2)
  | g_PiFst h1 => g_PiFst (subst_co_co c g h1)
  | g_CPiFst h1 => g_CPiFst (subst_co_co c g h1)
  | g_IsoSnd h1 => g_IsoSnd (subst_co_co c g h1)
  | g_PiSnd h1 h2 => g_PiSnd (subst_co_co c g h1) (subst_co_co c g h2)
  | g_CPiCong h1 h3 => g_CPiCong (subst_co_co c g h1) (subst_co_co c g h3)
  | g_CAbsCong h1 h3 h4 => g_CAbsCong (subst_co_co c g h1) (subst_co_co c g h3) (subst_co_co c g h4)
  | g_CAppCong h h1 h2 => g_CAppCong (subst_co_co c g h) (subst_co_co c g h1) (subst_co_co c g h2)
  | g_CPiSnd h h1 h2 => g_CPiSnd (subst_co_co c g h) (subst_co_co c g h1) (subst_co_co c g h2)
  | g_Cast h1 h2 => g_Cast (subst_co_co c g h1) (subst_co_co c g h2)
  | g_EqCong h1 A h2 => g_EqCong (subst_co_co c g h1) (subst_co_tm c g A) (subst_co_co c g h2)
  | g_IsoConv p1 p2 h => g_IsoConv (subst_co_constraint c g p1) (subst_co_constraint c g p2) (subst_co_co c g h)
  | g_Eta a => g_Eta (subst_co_tm c g a)
  | g_Left h1 h2 => g_Left (subst_co_co c g h1) (subst_co_co c g h2)
  | g_Right h1 h2 => g_Right (subst_co_co c g h1) (subst_co_co c g h2)
  end
with subst_co_constraint (c:atom) (g:co) (p:constraint) {struct p} : constraint :=
  match p with
  | Eq a b A => Eq (subst_co_tm c g a) (subst_co_tm c g b) (subst_co_tm c g A)
  end.

(* Renaming of free names (both tm and co variables) *)

Fixpoint ren_tm (f:atom->atom) (a:tm) {struct a} : tm :=
  match a with
  | a_Star => a_Star
  | a_Var_b n => a_Var_b n
  | a_Var_f y => a_Var_f (f y)
  | a_Abs rho A b => a_Abs rho (ren_tm f A) (ren_tm f b)
  | a_UAbs rho b => a_UAbs rho (ren_tm f b)
  | a_App p rho q => a_App (ren_tm f p) rho (ren_tm f q)
  | a_Fam F => a_Fam F
  | a_Const T => a_Const T
  | a_Pi rho A B => a_Pi rho (ren_tm f A) (ren_tm f B)
  | a_Conv p g => a_Conv (ren_tm f p) (ren_co f g)
  | a_CPi phi B => a_CPi (ren_constraint f phi) (ren_tm f B)
  | a_CAbs phi b => a_CAbs (ren_constraint f phi) (ren_tm f b)
  | a_UCAbs b => a_UCAbs (ren_tm f b)
  | a_CApp p g => a_CApp (ren_tm f p) (ren_co f g)
  | a_Bullet => a_Bullet
  | a_DataCon K => a_DataCon K
  | a_Case p br => a_Case (ren_tm f p) (ren_brs f br)
  end
with ren_brs (f:atom->atom) (b:brs) {struct b} : brs :=
  match b with
  | br_None => br_None
  | br_One K a rest => br_One K (ren_tm f a) (ren_brs f rest)
  end
with ren_co (f:atom->atom) (g:co) {struct g} : co :=
  match g with
  | g_Triv => g_Triv
  | g_Var_b n => g_Var_b n
  | g_Var_f c => g_Var_f (f c)
  | g_Beta a b => g_Beta (ren_tm f a) (ren_tm f b)
  | g_Refl a => g_Refl (ren_tm f a)
  | g_Refl2 a b h => g_Refl2 (ren_tm f a) (ren_tm f b) (ren_co f h)
  | g_Sym h => g_Sym (ren_co f h)
  | g_Trans h1 h2 => g_Trans (ren_co f h1) (ren_co f h2)
  | g_PiCong rho h1 h2 => g_PiCong rho (ren_co f h1) (ren_co f h2)
  | g_AbsCong rho h1 h2 => g_AbsCong rho (ren_co f h1) (ren_co f h2)
  | g_AppCong h1 rho h2 => g_AppCong (ren_co f h1) rho (ren_co f h2)
  | g_PiFst h => g_PiFst (ren_co f h)
  | g_CPiFst h => g_CPiFst (ren_co f h)
  | g_IsoSnd h => g_IsoSnd (ren_co f h)
  | g_PiSnd h1 h2 => g_PiSnd (ren_co f h1) (ren_co f h2)
  | g_CPiCong h1 h3 => g_CPiCong (ren_co f h1) (ren_co f h3)
  | g_CAbsCong h1 h3 h4 => g_CAbsCong (ren_co f h1) (ren_co f h3) (ren_co f h4)
  | g_CAppCong h h1 h2 => g_CAppCong (ren_co f h) (ren_co f h1) (ren_co f h2)
  | g_CPiSnd h h1 h2 => g_CPiSnd (ren_co f h) (ren_co f h1) (ren_co f h2)
  | g_Cast h1 h2 => g_Cast (ren_co f h1) (ren_co f h2)
  | g_EqCong h1 A h2 => g_EqCong (ren_co f h1) (ren_tm f A) (ren_co f h2)
  | g_IsoConv p1 p2 h => g_IsoConv (ren_constraint f p1) (ren_constraint f p2) (ren_co f h)
  | g_Eta a => g_Eta (ren_tm f a)
  | g_Left h1 h2 => g_Left (ren_co f h1) (ren_co f h2)
  | g_Right h1 h2 => g_Right (ren_co f h1) (ren_co f h2)
  end
with ren_constraint (f:atom->atom) (p:constraint) {struct p} : constraint :=
  match p with
  | Eq a b A => Eq (ren_tm f a) (ren_tm f b) (ren_tm f A)
  end.

(* Closing a free name into a bvar at the given depth *)

Fixpoint close_tm (x:atom) (n:nat) (a:tm) {struct a} : tm :=
  match a with
  | a_Star => a_Star
  | a_Var_b m => a_Var_b m
  | a_Var_f y => if KeySetFacts.eq_dec y x then a_Var_b n else a_Var_f y
  | a_Abs rho A b => a_Abs rho (close_tm x n A) (close_tm x (S n) b)
  | a_UAbs rho b => a_UAbs rho (close_tm x (S n) b)
  | a_App p rho q => a_App (close_tm x n p) rho (close_tm x n q)
  | a_Fam F => a_Fam F
  | a_Const T => a_Const T
  | a_Pi rho A B => a_Pi rho (close_tm x n A) (close_tm x (S n) B)
  | a_Conv p g => a_Conv (close_tm x n p) (close_tm_co x n g)
  | a_CPi phi B => a_CPi (close_tm_constraint x n phi) (close_tm x n B)
  | a_CAbs phi b => a_CAbs (close_tm_constraint x n phi) (close_tm x n b)
  | a_UCAbs b => a_UCAbs (close_tm x n b)
  | a_CApp p g => a_CApp (close_tm x n p) (close_tm_co x n g)
  | a_Bullet => a_Bullet
  | a_DataCon K => a_DataCon K
  | a_Case p br => a_Case (close_tm x n p) (close_tm_brs x n br)
  end
with close_tm_brs (x:atom) (n:nat) (b:brs) {struct b} : brs :=
  match b with
  | br_None => br_None
  | br_One K a rest => br_One K (close_tm x n a) (close_tm_brs x n rest)
  end
with close_tm_co (x:atom) (n:nat) (g:co) {struct g} : co :=
  match g with
  | g_Triv => g_Triv
  | g_Var_b m => g_Var_b m
  | g_Var_f c => g_Var_f c
  | g_Beta a b => g_Beta (close_tm x n a) (close_tm x n b)
  | g_Refl a => g_Refl (close_tm x n a)
  | g_Refl2 a b h => g_Refl2 (close_tm x n a) (close_tm x n b) (close_tm_co x n h)
  | g_Sym h => g_Sym (close_tm_co x n h)
  | g_Trans h1 h2 => g_Trans (close_tm_co x n h1) (close_tm_co x n h2)
  | g_PiCong rho h1 h2 => g_PiCong rho (close_tm_co x n h1) (close_tm_co x (S n) h2)
  | g_AbsCong rho h1 h2 => g_AbsCong rho (close_tm_co x n h1) (close_tm_co x (S n) h2)
  | g_AppCong h1 rho h2 => g_AppCong (close_tm_co x n h1) rho (close_tm_co x n h2)
  | g_PiFst h => g_PiFst (close_tm_co x n h)
  | g_CPiFst h => g_CPiFst (close_tm_co x n h)
  | g_IsoSnd h => g_IsoSnd (close_tm_co x n h)
  | g_PiSnd h1 h2 => g_PiSnd (close_tm_co x n h1) (close_tm_co x n h2)
  | g_CPiCong h1 h3 => g_CPiCong (close_tm_co x n h1) (close_tm_co x n h3)
  | g_CAbsCong h1 h3 h4 => g_CAbsCong (close_tm_co x n h1) (close_tm_co x n h3) (close_tm_co x n h4)
  | g_CAppCong h h1 h2 => g_CAppCong (close_tm_co x n h) (close_tm_co x n h1) (close_tm_co x n h2)
  | g_CPiSnd h h1 h2 => g_CPiSnd (close_tm_co x n h) (close_tm_co x n h1) (close_tm_co x n h2)
  | g_Cast h1 h2 => g_Cast (close_tm_co x n h1) (close_tm_co x n h2)
  | g_EqCong h1 A h2 => g_EqCong (close_tm_co x n h1) (close_tm x n A) (close_tm_co x n h2)
  | g_IsoConv p1 p2 h => g_IsoConv (close_tm_constraint x n p1) (close_tm_constraint x n p2) (close_tm_co x n h)
  | g_Eta a => g_Eta (close_tm x n a)
  | g_Left h1 h2 => g_Left (close_tm_co x n h1) (close_tm_co x n h2)
  | g_Right h1 h2 => g_Right (close_tm_co x n h1) (close_tm_co x n h2)
  end
with close_tm_constraint (x:atom) (n:nat) (p:constraint) {struct p} : constraint :=
  match p with
  | Eq a b A => Eq (close_tm x n a) (close_tm x n b) (close_tm x n A)
  end.

Fixpoint close_co_tm (c:atom) (n:nat) (a:tm) {struct a} : tm :=
  match a with
  | a_Star => a_Star
  | a_Var_b m => a_Var_b m
  | a_Var_f y => a_Var_f y
  | a_Abs rho A b => a_Abs rho (close_co_tm c n A) (close_co_tm c n b)
  | a_UAbs rho b => a_UAbs rho (close_co_tm c n b)
  | a_App p rho q => a_App (close_co_tm c n p) rho (close_co_tm c n q)
  | a_Fam F => a_Fam F
  | a_Const T => a_Const T
  | a_Pi rho A B => a_Pi rho (close_co_tm c n A) (close_co_tm c n B)
  | a_Conv p g => a_Conv (close_co_tm c n p) (close_co_co c n g)
  | a_CPi phi B => a_CPi (close_co_constraint c n phi) (close_co_tm c (S n) B)
  | a_CAbs phi b => a_CAbs (close_co_constraint c n phi) (close_co_tm c (S n) b)
  | a_UCAbs b => a_UCAbs (close_co_tm c (S n) b)
  | a_CApp p g => a_CApp (close_co_tm c n p) (close_co_co c n g)
  | a_Bullet => a_Bullet
  | a_DataCon K => a_DataCon K
  | a_Case p br => a_Case (close_co_tm c n p) (close_co_brs c n br)
  end
with close_co_brs (c:atom) (n:nat) (b:brs) {struct b} : brs :=
  match b with
  | br_None => br_None
  | br_One K a rest => br_One K (close_co_tm c n a) (close_co_brs c n rest)
  end
with close_co_co (c:atom) (n:nat) (g:co) {struct g} : co :=
  match g with
  | g_Triv => g_Triv
  | g_Var_b m => g_Var_b m
  | g_Var_f y => if KeySetFacts.eq_dec y c then g_Var_b n else g_Var_f y
  | g_Beta a b => g_Beta (close_co_tm c n a) (close_co_tm c n b)
  | g_Refl a => g_Refl (close_co_tm c n a)
  | g_Refl2 a b h => g_Refl2 (close_co_tm c n a) (close_co_tm c n b) (close_co_co c n h)
  | g_Sym h => g_Sym (close_co_co c n h)
  | g_Trans h1 h2 => g_Trans (close_co_co c n h1) (close_co_co c n h2)
  | g_PiCong rho h1 h2 => g_PiCong rho (close_co_co c n h1) (close_co_co c n h2)
  | g_AbsCong rho h1 h2 => g_AbsCong rho (close_co_co c n h1) (close_co_co c n h2)
  | g_AppCong h1 rho h2 => g_AppCong (close_co_co c n h1) rho (close_co_co c n h2)
  | g_PiFst h => g_PiFst (close_co_co c n h)
  | g_CPiFst h => g_CPiFst (close_co_co c n h)
  | g_IsoSnd h => g_IsoSnd (close_co_co c n h)
  | g_PiSnd h1 h2 => g_PiSnd (close_co_co c n h1) (close_co_co c n h2)
  | g_CPiCong h1 h3 => g_CPiCong (close_co_co c n h1) (close_co_co c (S n) h3)
  | g_CAbsCong h1 h3 h4 => g_CAbsCong (close_co_co c n h1) (close_co_co c (S n) h3) (close_co_co c n h4)
  | g_CAppCong h h1 h2 => g_CAppCong (close_co_co c n h) (close_co_co c n h1) (close_co_co c n h2)
  | g_CPiSnd h h1 h2 => g_CPiSnd (close_co_co c n h) (close_co_co c n h1) (close_co_co c n h2)
  | g_Cast h1 h2 => g_Cast (close_co_co c n h1) (close_co_co c n h2)
  | g_EqCong h1 A h2 => g_EqCong (close_co_co c n h1) (close_co_tm c n A) (close_co_co c n h2)
  | g_IsoConv p1 p2 h => g_IsoConv (close_co_constraint c n p1) (close_co_constraint c n p2) (close_co_co c n h)
  | g_Eta a => g_Eta (close_co_tm c n a)
  | g_Left h1 h2 => g_Left (close_co_co c n h1) (close_co_co c n h2)
  | g_Right h1 h2 => g_Right (close_co_co c n h1) (close_co_co c n h2)
  end
with close_co_constraint (c:atom) (n:nat) (p:constraint) {struct p} : constraint :=
  match p with
  | Eq a b A => Eq (close_co_tm c n a) (close_co_tm c n b) (close_co_tm c n A)
  end.

(* ------------------------------------------------------------------ *)
(* Mutual induction principles and sizes                               *)
(* ------------------------------------------------------------------ *)



(* ================= Our helper lemmas ================= *)

Lemma subst_tm_var_eq : forall x u, subst_tm_tm x u (a_Var_f x) = u.
Proof. intros. cbn [subst_tm_tm]. destruct (KeySetFacts.eq_dec x x) as [e|e]; [reflexivity|exfalso; auto]. Qed.
Lemma subst_tm_var_neq : forall x y u, x <> y -> subst_tm_tm x u (a_Var_f y) = a_Var_f y.
Proof. intros. cbn [subst_tm_tm]. destruct (KeySetFacts.eq_dec y x) as [e|e]; [exfalso; auto|reflexivity]. Qed.

Ltac close_lc_hyp :=
  match goal with
  | H : lc_co ?w |- ?l = open_co_wrt_co_rec ?k _ ?w =>
      symmetry; apply (proj1 (proj2 (proj2 clc_closed_open_co)) w 0 (lc_clc_co w H) k (Nat.le_0_l k))
  | H : lc_co ?w |- ?l = open_co_wrt_tm_rec ?k _ ?w =>
      symmetry; apply (proj1 (proj2 (proj2 clt_closed_open_tm)) w 0 (lc_clt_co w H) k (Nat.le_0_l k))
  | H : lc_tm ?w |- ?l = open_tm_wrt_tm_rec ?k _ ?w =>
      symmetry; apply (proj1 clt_closed_open_tm w 0 (lc_clt_tm w H) k (Nat.le_0_l k))
  | H : lc_tm ?w |- ?l = open_tm_wrt_co_rec ?k _ ?w =>
      symmetry; apply (proj1 clc_closed_open_co w 0 (lc_clc_tm w H) k (Nat.le_0_l k))
  end.

Ltac crush_comm :=
  repeat
    (try reflexivity);
  repeat
    (try (repeat f_equal));
  repeat
    (match goal with
     | |- context [KeySetFacts.eq_dec ?a ?b] =>
         destruct (KeySetFacts.eq_dec a b) as [Heq|Hneq]; cbn
     | |- context [lt_eq_lt_dec ?a ?b] =>
         destruct (lt_eq_lt_dec a b) as [[Hlt|Heq]|Hgt]; cbn
     end);
  repeat (try reflexivity);
  repeat (try (repeat f_equal));
  repeat (try close_lc_hyp).

Lemma subst_tm_open_tm :
  (forall a x u y k, lc_tm u ->
     subst_tm_tm x u (open_tm_wrt_tm_rec k (a_Var_f y) a)
     = open_tm_wrt_tm_rec k (subst_tm_tm x u (a_Var_f y)) (subst_tm_tm x u a))
  /\ (forall b x u y k, lc_tm u ->
     subst_tm_brs x u (open_brs_wrt_tm_rec k (a_Var_f y) b)
     = open_brs_wrt_tm_rec k (subst_tm_tm x u (a_Var_f y)) (subst_tm_brs x u b))
  /\ (forall g x u y k, lc_tm u ->
     subst_tm_co x u (open_co_wrt_tm_rec k (a_Var_f y) g)
     = open_co_wrt_tm_rec k (subst_tm_tm x u (a_Var_f y)) (subst_tm_co x u g))
  /\ (forall p x u y k, lc_tm u ->
     subst_tm_constraint x u (open_constraint_wrt_tm_rec k (a_Var_f y) p)
     = open_constraint_wrt_tm_rec k (subst_tm_tm x u (a_Var_f y)) (subst_tm_constraint x u p)).
Proof.
  apply (tm_mutind
    (fun a => forall x u y k, lc_tm u ->
       subst_tm_tm x u (open_tm_wrt_tm_rec k (a_Var_f y) a)
       = open_tm_wrt_tm_rec k (subst_tm_tm x u (a_Var_f y)) (subst_tm_tm x u a))
    (fun b => forall x u y k, lc_tm u ->
       subst_tm_brs x u (open_brs_wrt_tm_rec k (a_Var_f y) b)
       = open_brs_wrt_tm_rec k (subst_tm_tm x u (a_Var_f y)) (subst_tm_brs x u b))
    (fun g => forall x u y k, lc_tm u ->
       subst_tm_co x u (open_co_wrt_tm_rec k (a_Var_f y) g)
       = open_co_wrt_tm_rec k (subst_tm_tm x u (a_Var_f y)) (subst_tm_co x u g))
    (fun p => forall x u y k, lc_tm u ->
       subst_tm_constraint x u (open_constraint_wrt_tm_rec k (a_Var_f y) p)
       = open_constraint_wrt_tm_rec k (subst_tm_tm x u (a_Var_f y)) (subst_tm_constraint x u p))).
  all: intros.
  all: cbn [open_tm_wrt_tm_rec open_brs_wrt_tm_rec open_co_wrt_tm_rec
            open_constraint_wrt_tm_rec subst_tm_tm subst_tm_brs subst_tm_co
            subst_tm_constraint] in *.
  all: try reflexivity.
  all: try (repeat f_equal; eauto).
  (* Var_f case *)
  all: try (destruct (KeySetFacts.eq_dec x x0) as [Heq|Hneq]).
  all: try (subst x0; rewrite subst_tm_var_eq).
  all: try (match goal with
            | Hlc : lc_tm ?w |- ?l = open_tm_wrt_tm_rec ?k _ ?w =>
                symmetry; apply (proj1 clt_closed_open_tm w 0 (lc_clt_tm w Hlc) k (Nat.le_0_l k))
            end).
  all: try reflexivity.
  (* Var_b case for co *)
  all: try (destruct (lt_eq_lt_dec n k) as [[?|?]|?]; reflexivity).
Qed.

Lemma open_tm_closed : forall u k r, lc_tm u -> open_tm_wrt_tm_rec k r u = u.
Proof. intros; apply (proj1 clt_closed_open_tm u 0 (lc_clt_tm u H) k (Nat.le_0_l k)). Qed.
Lemma open_co_tm_closed : forall g k r, lc_co g -> open_co_wrt_tm_rec k r g = g.
Proof. intros; apply (proj1 (proj2 (proj2 clt_closed_open_tm)) g 0 (lc_clt_co g H) k (Nat.le_0_l k)). Qed.
Lemma open_tm_co_closed : forall u k r, lc_tm u -> open_tm_wrt_co_rec k r u = u.
Proof. intros; apply (proj1 clc_closed_open_co u 0 (lc_clc_tm u H) k (Nat.le_0_l k)). Qed.
Lemma open_co_co_closed : forall g k r, lc_co g -> open_co_wrt_co_rec k r g = g.
Proof. intros; apply (proj1 (proj2 (proj2 clc_closed_open_co)) g 0 (lc_clc_co g H) k (Nat.le_0_l k)). Qed.

Lemma subst_tm_open_co_tm :
  (forall a x u v k, lc_tm u ->
     subst_tm_tm x u (open_tm_wrt_tm_rec k v a)
     = open_tm_wrt_tm_rec k (subst_tm_tm x u v) (subst_tm_tm x u a))
  /\ (forall b x u v k, lc_tm u ->
     subst_tm_brs x u (open_brs_wrt_tm_rec k v b)
     = open_brs_wrt_tm_rec k (subst_tm_tm x u v) (subst_tm_brs x u b))
  /\ (forall g x u v k, lc_tm u ->
     subst_tm_co x u (open_co_wrt_tm_rec k v g)
     = open_co_wrt_tm_rec k (subst_tm_tm x u v) (subst_tm_co x u g))
  /\ (forall p x u v k, lc_tm u ->
     subst_tm_constraint x u (open_constraint_wrt_tm_rec k v p)
     = open_constraint_wrt_tm_rec k (subst_tm_tm x u v) (subst_tm_constraint x u p)).
Proof.
  apply (tm_mutind
    (fun a => forall x u v k, lc_tm u ->
       subst_tm_tm x u (open_tm_wrt_tm_rec k v a)
       = open_tm_wrt_tm_rec k (subst_tm_tm x u v) (subst_tm_tm x u a))
    (fun b => forall x u v k, lc_tm u ->
       subst_tm_brs x u (open_brs_wrt_tm_rec k v b)
       = open_brs_wrt_tm_rec k (subst_tm_tm x u v) (subst_tm_brs x u b))
    (fun g => forall x u v k, lc_tm u ->
       subst_tm_co x u (open_co_wrt_tm_rec k v g)
       = open_co_wrt_tm_rec k (subst_tm_tm x u v) (subst_tm_co x u g))
    (fun p => forall x u v k, lc_tm u ->
       subst_tm_constraint x u (open_constraint_wrt_tm_rec k v p)
       = open_constraint_wrt_tm_rec k (subst_tm_tm x u v) (subst_tm_constraint x u p))).
  all: intros.
  all: cbn [open_tm_wrt_tm_rec open_brs_wrt_tm_rec open_co_wrt_tm_rec
            open_constraint_wrt_tm_rec subst_tm_tm subst_tm_brs subst_tm_co
            subst_tm_constraint] in *.
  all: try reflexivity.
  all: try (repeat f_equal; eauto).
  all: try (destruct (KeySetFacts.eq_dec x x0) as [Heq|Hneq]).
  all: try (subst x0; rewrite subst_tm_var_eq).
  all: try (match goal with
            | Hlc : lc_tm ?w |- ?l = open_tm_wrt_tm_rec ?k _ ?w =>
                symmetry; apply (open_tm_closed w k _ Hlc)
            end).
  all: try reflexivity.
  all: try (destruct (lt_eq_lt_dec n k) as [[?|?]|?]; reflexivity).
Qed.

Lemma subst_tm_open_tm_co :
  (forall a x u g k, lc_tm u ->
     subst_tm_tm x u (open_tm_wrt_co_rec k g a)
     = open_tm_wrt_co_rec k (subst_tm_co x u g) (subst_tm_tm x u a))
  /\ (forall b x u g k, lc_tm u ->
     subst_tm_brs x u (open_brs_wrt_co_rec k g b)
     = open_brs_wrt_co_rec k (subst_tm_co x u g) (subst_tm_brs x u b))
  /\ (forall h x u g k, lc_tm u ->
     subst_tm_co x u (open_co_wrt_co_rec k g h)
     = open_co_wrt_co_rec k (subst_tm_co x u g) (subst_tm_co x u h))
  /\ (forall p x u g k, lc_tm u ->
     subst_tm_constraint x u (open_constraint_wrt_co_rec k g p)
     = open_constraint_wrt_co_rec k (subst_tm_co x u g) (subst_tm_constraint x u p)).
Proof.
  apply (tm_mutind
    (fun a => forall x u g k, lc_tm u ->
       subst_tm_tm x u (open_tm_wrt_co_rec k g a)
       = open_tm_wrt_co_rec k (subst_tm_co x u g) (subst_tm_tm x u a))
    (fun b => forall x u g k, lc_tm u ->
       subst_tm_brs x u (open_brs_wrt_co_rec k g b)
       = open_brs_wrt_co_rec k (subst_tm_co x u g) (subst_tm_brs x u b))
    (fun h => forall x u g k, lc_tm u ->
       subst_tm_co x u (open_co_wrt_co_rec k g h)
       = open_co_wrt_co_rec k (subst_tm_co x u g) (subst_tm_co x u h))
    (fun p => forall x u g k, lc_tm u ->
       subst_tm_constraint x u (open_constraint_wrt_co_rec k g p)
       = open_constraint_wrt_co_rec k (subst_tm_co x u g) (subst_tm_constraint x u p))).
  all: intros.
  all: cbn [open_tm_wrt_co_rec open_brs_wrt_co_rec open_co_wrt_co_rec
            open_constraint_wrt_co_rec subst_tm_tm subst_tm_brs subst_tm_co
            subst_tm_constraint] in *.
  all: try reflexivity.
  all: try (repeat f_equal; eauto).
  (* Var_f case *)
  all: try (destruct (KeySetFacts.eq_dec x x0) as [Heq|Hneq]).
  all: try (subst x0; rewrite subst_tm_var_eq).
  all: try (match goal with
            | Hlc : lc_tm ?w |- ?l = open_tm_wrt_co_rec ?k _ ?w =>
                symmetry; apply (open_tm_co_closed w k _ Hlc)
            end).
  all: try reflexivity.
  all: try (destruct (lt_eq_lt_dec n k) as [[?|?]|?]; reflexivity).
Qed.

Lemma subst_co_open_tm :
  (forall a c g v k, lc_co g ->
     subst_co_tm c g (open_tm_wrt_tm_rec k v a)
     = open_tm_wrt_tm_rec k (subst_co_tm c g v) (subst_co_tm c g a))
  /\ (forall b c g v k, lc_co g ->
     subst_co_brs c g (open_brs_wrt_tm_rec k v b)
     = open_brs_wrt_tm_rec k (subst_co_tm c g v) (subst_co_brs c g b))
  /\ (forall h c g v k, lc_co g ->
     subst_co_co c g (open_co_wrt_tm_rec k v h)
     = open_co_wrt_tm_rec k (subst_co_tm c g v) (subst_co_co c g h))
  /\ (forall p c g v k, lc_co g ->
     subst_co_constraint c g (open_constraint_wrt_tm_rec k v p)
     = open_constraint_wrt_tm_rec k (subst_co_tm c g v) (subst_co_constraint c g p)).
Proof.
  apply (tm_mutind
    (fun a => forall c g v k, lc_co g ->
       subst_co_tm c g (open_tm_wrt_tm_rec k v a)
       = open_tm_wrt_tm_rec k (subst_co_tm c g v) (subst_co_tm c g a))
    (fun b => forall c g v k, lc_co g ->
       subst_co_brs c g (open_brs_wrt_tm_rec k v b)
       = open_brs_wrt_tm_rec k (subst_co_tm c g v) (subst_co_brs c g b))
    (fun h => forall c g v k, lc_co g ->
       subst_co_co c g (open_co_wrt_tm_rec k v h)
       = open_co_wrt_tm_rec k (subst_co_tm c g v) (subst_co_co c g h))
    (fun p => forall c g v k, lc_co g ->
       subst_co_constraint c g (open_constraint_wrt_tm_rec k v p)
       = open_constraint_wrt_tm_rec k (subst_co_tm c g v) (subst_co_constraint c g p))).
  all: intros.
  all: cbn [open_tm_wrt_tm_rec open_brs_wrt_tm_rec open_co_wrt_tm_rec
            open_constraint_wrt_tm_rec subst_co_tm subst_co_brs subst_co_co
            subst_co_constraint] in *.
  all: try reflexivity.
  all: try (repeat f_equal; eauto).
  all: try (destruct (KeySetFacts.eq_dec c c0) as [Heq|Hneq]).
  all: try (subst c0).
  all: try (match goal with
            | Hlc : lc_co ?w |- ?l = open_co_wrt_tm_rec ?k _ ?w =>
                symmetry; apply (open_co_tm_closed w k _ Hlc)
            end).
  all: try reflexivity.
  all: try (destruct (lt_eq_lt_dec n k) as [[?|?]|?]; reflexivity).
Qed.

Lemma subst_co_open_co :
  (forall a c g d k, lc_co g ->
     subst_co_tm c g (open_tm_wrt_co_rec k (g_Var_f d) a)
     = open_tm_wrt_co_rec k (subst_co_co c g (g_Var_f d)) (subst_co_tm c g a))
  /\ (forall b c g d k, lc_co g ->
     subst_co_brs c g (open_brs_wrt_co_rec k (g_Var_f d) b)
     = open_brs_wrt_co_rec k (subst_co_co c g (g_Var_f d)) (subst_co_brs c g b))
  /\ (forall h c g d k, lc_co g ->
     subst_co_co c g (open_co_wrt_co_rec k (g_Var_f d) h)
     = open_co_wrt_co_rec k (subst_co_co c g (g_Var_f d)) (subst_co_co c g h))
  /\ (forall p c g d k, lc_co g ->
     subst_co_constraint c g (open_constraint_wrt_co_rec k (g_Var_f d) p)
     = open_constraint_wrt_co_rec k (subst_co_co c g (g_Var_f d)) (subst_co_constraint c g p)).
Proof.
  apply (tm_mutind
    (fun a => forall c g d k, lc_co g ->
       subst_co_tm c g (open_tm_wrt_co_rec k (g_Var_f d) a)
       = open_tm_wrt_co_rec k (subst_co_co c g (g_Var_f d)) (subst_co_tm c g a))
    (fun b => forall c g d k, lc_co g ->
       subst_co_brs c g (open_brs_wrt_co_rec k (g_Var_f d) b)
       = open_brs_wrt_co_rec k (subst_co_co c g (g_Var_f d)) (subst_co_brs c g b))
    (fun h => forall c g d k, lc_co g ->
       subst_co_co c g (open_co_wrt_co_rec k (g_Var_f d) h)
       = open_co_wrt_co_rec k (subst_co_co c g (g_Var_f d)) (subst_co_co c g h))
    (fun p => forall c g d k, lc_co g ->
       subst_co_constraint c g (open_constraint_wrt_co_rec k (g_Var_f d) p)
       = open_constraint_wrt_co_rec k (subst_co_co c g (g_Var_f d)) (subst_co_constraint c g p))).
  all: intros.
  all: cbn [open_tm_wrt_co_rec open_brs_wrt_co_rec open_co_wrt_co_rec
            open_constraint_wrt_co_rec subst_co_tm subst_co_brs subst_co_co
            subst_co_constraint] in *.
  all: try reflexivity.
  all: try (repeat f_equal; eauto).
  all: try (destruct (KeySetFacts.eq_dec c c0) as [Heq|Hneq]).
  all: try (subst c0).
  all: try (destruct (KeySetFacts.eq_dec c c) as [e|e]; [|exfalso; auto]).
  all: try (destruct (KeySetFacts.eq_dec d c) as [e|e]; subst; cbn).
  all: try (match goal with
            | H : lc_co ?w |- ?l = open_co_wrt_co_rec ?k _ ?w =>
                symmetry; apply (open_co_co_closed w k _ H)
            end).
  all: try reflexivity.
  all: try (destruct (lt_eq_lt_dec n k) as [[?|?]|?]; cbn [subst_co_co]).
  all: try (destruct (KeySetFacts.eq_dec d c) as [Heq|Hneq]; subst; cbn; try reflexivity).
  all: try (match goal with
            | H : lc_co ?w |- ?l = open_co_wrt_co_rec ?k _ ?w =>
                symmetry; apply (open_co_co_closed w k _ H)
            end).
  all: try reflexivity.
  all: try crush_comm.
Qed.

Lemma subst_co_open_tm_co :
  (forall a c g h k, lc_co g ->
     subst_co_tm c g (open_tm_wrt_co_rec k h a)
     = open_tm_wrt_co_rec k (subst_co_co c g h) (subst_co_tm c g a))
  /\ (forall b c g h k, lc_co g ->
     subst_co_brs c g (open_brs_wrt_co_rec k h b)
     = open_brs_wrt_co_rec k (subst_co_co c g h) (subst_co_brs c g b))
  /\ (forall h0 c g h k, lc_co g ->
     subst_co_co c g (open_co_wrt_co_rec k h h0)
     = open_co_wrt_co_rec k (subst_co_co c g h) (subst_co_co c g h0))
  /\ (forall p c g h k, lc_co g ->
     subst_co_constraint c g (open_constraint_wrt_co_rec k h p)
     = open_constraint_wrt_co_rec k (subst_co_co c g h) (subst_co_constraint c g p)).
Proof.
  apply (tm_mutind
    (fun a => forall c g h k, lc_co g ->
       subst_co_tm c g (open_tm_wrt_co_rec k h a)
       = open_tm_wrt_co_rec k (subst_co_co c g h) (subst_co_tm c g a))
    (fun b => forall c g h k, lc_co g ->
       subst_co_brs c g (open_brs_wrt_co_rec k h b)
       = open_brs_wrt_co_rec k (subst_co_co c g h) (subst_co_brs c g b))
    (fun h0 => forall c g h k, lc_co g ->
       subst_co_co c g (open_co_wrt_co_rec k h h0)
       = open_co_wrt_co_rec k (subst_co_co c g h) (subst_co_co c g h0))
    (fun p => forall c g h k, lc_co g ->
       subst_co_constraint c g (open_constraint_wrt_co_rec k h p)
       = open_constraint_wrt_co_rec k (subst_co_co c g h) (subst_co_constraint c g p))).
  all: intros.
  all: cbn [open_tm_wrt_co_rec open_brs_wrt_co_rec open_co_wrt_co_rec
            open_constraint_wrt_co_rec subst_co_tm subst_co_brs subst_co_co
            subst_co_constraint] in *.
  all: try reflexivity.
  all: try (repeat f_equal; eauto).
  all: try (destruct (KeySetFacts.eq_dec c c0) as [Heq|Hneq]).
  all: try (subst c0).
  all: try (destruct (KeySetFacts.eq_dec c c) as [e|e]; [|exfalso; auto]).
  all: try (match goal with
            | H : lc_co ?w |- ?l = open_co_wrt_co_rec ?k _ ?w =>
                symmetry; apply (open_co_co_closed w k _ H)
            end).
  all: try reflexivity.
  all: try (symmetry; apply open_co_co_closed; assumption).
  all: try (destruct (lt_eq_lt_dec n k) as [[?|?]|?]; reflexivity).
Qed.

(* key substitution/open identities *)
Lemma subst_tm_open_tm_id : forall a x u, lc_tm u ->
  subst_tm_tm x u (open_tm_wrt_tm a (a_Var_f x))
  = open_tm_wrt_tm (subst_tm_tm x u a) u.
Proof.
  intros. unfold open_tm_wrt_tm.
  pose proof (proj1 subst_tm_open_tm a x u x 0 H).
  rewrite subst_tm_var_eq in H0. exact H0.
Qed.

Lemma subst_co_var_eq : forall c g, subst_co_co c g (g_Var_f c) = g.
Proof. intros. cbn [subst_co_co]. destruct (KeySetFacts.eq_dec c c) as [e|e]; [reflexivity|exfalso; auto]. Qed.

Lemma subst_co_open_co_id : forall a c g, lc_co g ->
  subst_co_co c g (open_co_wrt_co a (g_Var_f c))
  = open_co_wrt_co (subst_co_co c g a) g.
Proof.
  intros. unfold open_co_wrt_co.
  pose proof (proj1 (proj2 (proj2 subst_co_open_co)) a c g c 0 H).
  rewrite subst_co_var_eq in H0. exact H0.
Qed.

Lemma subst_co_tm_open_co_id : forall a c g, lc_co g ->
  subst_co_tm c g (open_tm_wrt_co a (g_Var_f c))
  = open_tm_wrt_co (subst_co_tm c g a) g.
Proof.
  intros. unfold open_tm_wrt_co.
  pose proof (proj1 subst_co_open_co a c g c 0 H).
  rewrite subst_co_var_eq in H0. exact H0.
Qed.

(* opening with a variable is injective, provided the variable is not free *)
Lemma notin_union_elim : forall x s t, x `notin` (s \u t) -> x `notin` s /\ x `notin` t.
Proof.
  intros x s t H. split; intros Hc.
  - apply H. apply AtomSetImpl.union_2. exact Hc.
  - apply H. apply AtomSetImpl.union_3. exact Hc.
Qed.

Ltac notin_destruct :=
  repeat match goal with
  | H : _ `notin` (_ \u _) |- _ => apply notin_union_elim in H; destruct H
  end.

Lemma open_tm_var_inj :
  (forall a k x, x `notin` fv_tm_tm_tm a ->
     forall bb, x `notin` fv_tm_tm_tm bb ->
       open_tm_wrt_tm_rec k (a_Var_f x) a = open_tm_wrt_tm_rec k (a_Var_f x) bb -> a = bb)
  /\ (forall a k x, x `notin` fv_tm_tm_brs a ->
     forall bb, x `notin` fv_tm_tm_brs bb ->
       open_brs_wrt_tm_rec k (a_Var_f x) a = open_brs_wrt_tm_rec k (a_Var_f x) bb -> a = bb)
  /\ (forall a k x, x `notin` fv_tm_tm_co a ->
     forall bb, x `notin` fv_tm_tm_co bb ->
       open_co_wrt_tm_rec k (a_Var_f x) a = open_co_wrt_tm_rec k (a_Var_f x) bb -> a = bb)
  /\ (forall a k x, x `notin` fv_tm_tm_constraint a ->
     forall bb, x `notin` fv_tm_tm_constraint bb ->
       open_constraint_wrt_tm_rec k (a_Var_f x) a = open_constraint_wrt_tm_rec k (a_Var_f x) bb -> a = bb).
Proof.
  apply (tm_mutind
    (fun a => forall k x, x `notin` fv_tm_tm_tm a ->
       forall bb, x `notin` fv_tm_tm_tm bb ->
         open_tm_wrt_tm_rec k (a_Var_f x) a = open_tm_wrt_tm_rec k (a_Var_f x) bb -> a = bb)
    (fun a => forall k x, x `notin` fv_tm_tm_brs a ->
       forall bb, x `notin` fv_tm_tm_brs bb ->
         open_brs_wrt_tm_rec k (a_Var_f x) a = open_brs_wrt_tm_rec k (a_Var_f x) bb -> a = bb)
    (fun a => forall k x, x `notin` fv_tm_tm_co a ->
       forall bb, x `notin` fv_tm_tm_co bb ->
         open_co_wrt_tm_rec k (a_Var_f x) a = open_co_wrt_tm_rec k (a_Var_f x) bb -> a = bb)
    (fun a => forall k x, x `notin` fv_tm_tm_constraint a ->
       forall bb, x `notin` fv_tm_tm_constraint bb ->
         open_constraint_wrt_tm_rec k (a_Var_f x) a = open_constraint_wrt_tm_rec k (a_Var_f x) bb -> a = bb)).
  all: intros.
  all: try (destruct bb; cbn [open_tm_wrt_tm_rec open_brs_wrt_tm_rec
        open_co_wrt_tm_rec open_constraint_wrt_tm_rec fv_tm_tm_tm fv_tm_tm_brs
        fv_tm_tm_co fv_tm_tm_constraint] in *; try discriminate).
  (* reduce matched indices *)
  all: try (repeat match goal with
    | H : context [lt_eq_lt_dec ?a ?b] |- _ =>
        destruct (lt_eq_lt_dec a b) as [[?|?]|?]; cbn in *
    | |- context [lt_eq_lt_dec ?a ?b] =>
        destruct (lt_eq_lt_dec a b) as [[?|?]|?]; cbn
    end).
  all: try discriminate.
  (* contradictions from fresh-variable hypotheses *)
  all: try (exfalso; match goal with
            | H : ?xx `notin` singleton ?yy |- _ =>
                exact (notin_singleton_1 yy xx H)
            end).
  (* inject the constructor equality *)
  all: try (match goal with
            | H : _ = _ |- _ => injection H; intros; subst; auto
            end).
  all: try (repeat match goal with
            | H : _ = _ |- _ => try (injection H; intros; subst)
            end).
  all: try (notin_destruct).
  all: try solve [subst; reflexivity].
  all: try solve [assumption].
  all: try solve [eauto 50].
  all: try solve [exfalso; match goal with
                  | H : ?xx `notin` singleton ?yy |- _ =>
                      exact (notin_singleton_1 yy xx H)
                  end].
  all: try solve [exfalso; eauto 50].
  all: try solve [f_equal; eauto 60].
  all: try solve [f_equal; lia].
  all: try solve [lia].

Qed.
Import ListNotations.


Scheme tm_mut := Induction for tm Sort Prop
  with brs_mut := Induction for brs Sort Prop
  with co_mut := Induction for co Sort Prop
  with constraint_mut := Induction for constraint Sort Prop.

Fixpoint sz_tm (a:tm) {struct a} : nat :=
  match a with
  | a_Star => 1
  | a_Var_b n => 1
  | a_Var_f x => 1
  | a_Abs rho A b => 1 + sz_tm A + sz_tm b
  | a_UAbs rho b => 1 + sz_tm b
  | a_App p rho q => 1 + sz_tm p + sz_tm q
  | a_Fam F => 1
  | a_Const T => 1
  | a_Pi rho A B => 1 + sz_tm A + sz_tm B
  | a_Conv p g => 1 + sz_tm p + sz_co g
  | a_CPi phi B => 1 + sz_constraint phi + sz_tm B
  | a_CAbs phi b => 1 + sz_constraint phi + sz_tm b
  | a_UCAbs b => 1 + sz_tm b
  | a_CApp p g => 1 + sz_tm p + sz_co g
  | a_Bullet => 1
  | a_DataCon K => 1
  | a_Case p br => 1 + sz_tm p + sz_brs br
  end
with sz_brs (b:brs) {struct b} : nat :=
  match b with
  | br_None => 1
  | br_One K a rest => 1 + sz_tm a + sz_brs rest
  end
with sz_co (g:co) {struct g} : nat :=
  match g with
  | g_Triv => 1
  | g_Var_b n => 1
  | g_Var_f c => 1
  | g_Beta a b => 1 + sz_tm a + sz_tm b
  | g_Refl a => 1 + sz_tm a
  | g_Refl2 a b h => 1 + sz_tm a + sz_tm b + sz_co h
  | g_Sym h => 1 + sz_co h
  | g_Trans h1 h2 => 1 + sz_co h1 + sz_co h2
  | g_PiCong rho h1 h2 => 1 + sz_co h1 + sz_co h2
  | g_AbsCong rho h1 h2 => 1 + sz_co h1 + sz_co h2
  | g_AppCong h1 rho h2 => 1 + sz_co h1 + sz_co h2
  | g_PiFst h => 1 + sz_co h
  | g_CPiFst h => 1 + sz_co h
  | g_IsoSnd h => 1 + sz_co h
  | g_PiSnd h1 h2 => 1 + sz_co h1 + sz_co h2
  | g_CPiCong h1 h3 => 1 + sz_co h1 + sz_co h3
  | g_CAbsCong h1 h3 h4 => 1 + sz_co h1 + sz_co h3 + sz_co h4
  | g_CAppCong h h1 h2 => 1 + sz_co h + sz_co h1 + sz_co h2
  | g_CPiSnd h h1 h2 => 1 + sz_co h + sz_co h1 + sz_co h2
  | g_Cast h1 h2 => 1 + sz_co h1 + sz_co h2
  | g_EqCong h1 A h2 => 1 + sz_co h1 + sz_tm A + sz_co h2
  | g_IsoConv p1 p2 h => 1 + sz_constraint p1 + sz_constraint p2 + sz_co h
  | g_Eta a => 1 + sz_tm a
  | g_Left h1 h2 => 1 + sz_co h1 + sz_co h2
  | g_Right h1 h2 => 1 + sz_co h1 + sz_co h2
  end
with sz_constraint (p:constraint) {struct p} : nat :=
  match p with
  | Eq a b A => 1 + sz_tm a + sz_tm b + sz_tm A
  end.

Inductive syn : Type :=
| SyTm (a:tm) | SyBr (b:brs) | SyCo (g:co) | SyCon (p:constraint).

Definition sz_syn (s:syn) : nat :=
  match s with
  | SyTm a => sz_tm a
  | SyBr b => sz_brs b
  | SyCo g => sz_co g
  | SyCon p => sz_constraint p
  end.

Lemma sz_nonzero_mut :
  (forall a, sz_tm a > 0) /\
  (forall b, sz_brs b > 0) /\
  (forall g, sz_co g > 0) /\
  (forall p, sz_constraint p > 0).
Proof.
  split.
  - apply (tm_mut
      (fun a => sz_tm a > 0)
      (fun b => sz_brs b > 0)
      (fun g => sz_co g > 0)
      (fun p => sz_constraint p > 0));
    intros; simpl; lia.
  - split.
    + apply (brs_mut
        (fun a => sz_tm a > 0)
        (fun b => sz_brs b > 0)
        (fun g => sz_co g > 0)
        (fun p => sz_constraint p > 0));
      intros; simpl; lia.
    + split.
      * apply (co_mut
          (fun a => sz_tm a > 0)
          (fun b => sz_brs b > 0)
          (fun g => sz_co g > 0)
          (fun p => sz_constraint p > 0));
        intros; simpl; lia.
      * apply (constraint_mut
          (fun a => sz_tm a > 0)
          (fun b => sz_brs b > 0)
          (fun g => sz_co g > 0)
          (fun p => sz_constraint p > 0));
        intros; simpl; lia.
Qed.

(* opening at a variable preserves size *)

Ltac sz_open_var_solve :=
  intros; simpl;
  try (destruct (lt_eq_lt_dec _ _) as [[?|?]|?]); simpl;
  repeat match goal with
  | IH : forall x k, sz_tm (open_tm_wrt_tm_rec k (a_Var_f x) ?a) = sz_tm ?a
      |- context [sz_tm (open_tm_wrt_tm_rec ?k (a_Var_f ?x) ?a)] => rewrite (IH x k)
  | IH : forall x k, sz_brs (open_brs_wrt_tm_rec k (a_Var_f x) ?b) = sz_brs ?b
      |- context [sz_brs (open_brs_wrt_tm_rec ?k (a_Var_f ?x) ?b)] => rewrite (IH x k)
  | IH : forall x k, sz_co (open_co_wrt_tm_rec k (a_Var_f x) ?g) = sz_co ?g
      |- context [sz_co (open_co_wrt_tm_rec ?k (a_Var_f ?x) ?g)] => rewrite (IH x k)
  | IH : forall x k, sz_constraint (open_constraint_wrt_tm_rec k (a_Var_f x) ?p) = sz_constraint ?p
      |- context [sz_constraint (open_constraint_wrt_tm_rec ?k (a_Var_f ?x) ?p)] => rewrite (IH x k)
  end; try lia.

Lemma sz_open_var_tm : forall a x k,
  sz_tm (open_tm_wrt_tm_rec k (a_Var_f x) a) = sz_tm a.
Proof.
  apply (tm_mut
    (fun a => forall x k, sz_tm (open_tm_wrt_tm_rec k (a_Var_f x) a) = sz_tm a)
    (fun b => forall x k, sz_brs (open_brs_wrt_tm_rec k (a_Var_f x) b) = sz_brs b)
    (fun g => forall x k, sz_co (open_co_wrt_tm_rec k (a_Var_f x) g) = sz_co g)
    (fun p => forall x k, sz_constraint (open_constraint_wrt_tm_rec k (a_Var_f x) p) = sz_constraint p)).
  all: sz_open_var_solve.
Qed.

Lemma sz_open_var_brs : forall b x k,
  sz_brs (open_brs_wrt_tm_rec k (a_Var_f x) b) = sz_brs b.
Proof.
  apply (brs_mut
    (fun a => forall x k, sz_tm (open_tm_wrt_tm_rec k (a_Var_f x) a) = sz_tm a)
    (fun b => forall x k, sz_brs (open_brs_wrt_tm_rec k (a_Var_f x) b) = sz_brs b)
    (fun g => forall x k, sz_co (open_co_wrt_tm_rec k (a_Var_f x) g) = sz_co g)
    (fun p => forall x k, sz_constraint (open_constraint_wrt_tm_rec k (a_Var_f x) p) = sz_constraint p)).
  all: sz_open_var_solve.
Qed.

Lemma sz_open_var_co : forall g x k,
  sz_co (open_co_wrt_tm_rec k (a_Var_f x) g) = sz_co g.
Proof.
  apply (co_mut
    (fun a => forall x k, sz_tm (open_tm_wrt_tm_rec k (a_Var_f x) a) = sz_tm a)
    (fun b => forall x k, sz_brs (open_brs_wrt_tm_rec k (a_Var_f x) b) = sz_brs b)
    (fun g => forall x k, sz_co (open_co_wrt_tm_rec k (a_Var_f x) g) = sz_co g)
    (fun p => forall x k, sz_constraint (open_constraint_wrt_tm_rec k (a_Var_f x) p) = sz_constraint p)).
  all: sz_open_var_solve.
Qed.

Lemma sz_open_var_constraint : forall p x k,
  sz_constraint (open_constraint_wrt_tm_rec k (a_Var_f x) p) = sz_constraint p.
Proof.
  apply (constraint_mut
    (fun a => forall x k, sz_tm (open_tm_wrt_tm_rec k (a_Var_f x) a) = sz_tm a)
    (fun b => forall x k, sz_brs (open_brs_wrt_tm_rec k (a_Var_f x) b) = sz_brs b)
    (fun g => forall x k, sz_co (open_co_wrt_tm_rec k (a_Var_f x) g) = sz_co g)
    (fun p => forall x k, sz_constraint (open_constraint_wrt_tm_rec k (a_Var_f x) p) = sz_constraint p)).
  all: sz_open_var_solve.
Qed.
(* ===== end ParLemmas.v ===== *)

(* ======================= More closure/opening lemmas ======================= *)

Ltac crush_conj2 :=
  repeat match goal with
  | H : _ /\ _ |- _ => destruct H
  | |- _ /\ _ => split
  end.

Lemma clt_open_tm_fwd_gen :
  (forall a kt u, clt_tm (S kt) a -> clt_tm kt u -> clt_tm kt (open_tm_wrt_tm_rec kt u a)) /\
  (forall b kt u, clt_brs (S kt) b -> clt_tm kt u -> clt_brs kt (open_brs_wrt_tm_rec kt u b)) /\
  (forall g kt u, clt_co (S kt) g -> clt_tm kt u -> clt_co kt (open_co_wrt_tm_rec kt u g)) /\
  (forall p kt u, clt_constraint (S kt) p -> clt_tm kt u -> clt_constraint kt (open_constraint_wrt_tm_rec kt u p)).
Proof.
  apply (tm_mutind
    (fun a => forall kt u, clt_tm (S kt) a -> clt_tm kt u -> clt_tm kt (open_tm_wrt_tm_rec kt u a))
    (fun b => forall kt u, clt_brs (S kt) b -> clt_tm kt u -> clt_brs kt (open_brs_wrt_tm_rec kt u b))
    (fun g => forall kt u, clt_co (S kt) g -> clt_tm kt u -> clt_co kt (open_co_wrt_tm_rec kt u g))
    (fun p => forall kt u, clt_constraint (S kt) p -> clt_tm kt u -> clt_constraint kt (open_constraint_wrt_tm_rec kt u p))).
  all: intros.
  all: cbn [clt_tm clt_brs clt_co clt_constraint] in *.
  all: cbn [open_tm_wrt_tm_rec open_brs_wrt_tm_rec open_co_wrt_tm_rec open_constraint_wrt_tm_rec].
  all: try solve [exact I].
  all: try solve [lia].
  all: crush_conj2.
  all: try split.
  all: try (repeat match goal with
    | IH : forall (kt0:nat) (u0:tm), _ |- _ =>
        pose proof (IH kt u); pose proof (IH (S kt) u); clear IH
    end).
  all: try eauto using clt_tm_mono, clt_co_mono, clt_brs_mono, clt_constraint_mono.
  all: try (eauto with arith).
  all: try (cbn [clt_co clt_tm clt_brs clt_constraint] in *; eauto).
  all: try (destruct (lt_eq_lt_dec n kt) as [[H1|H2]|H3]; try subst; try lia; auto).
Qed.

Lemma clt_open_co_fwd_gen :
  (forall a kt kc g, clt_tm kt a -> clt_co kt g -> clt_tm kt (open_tm_wrt_co_rec kc g a)) /\
  (forall b kt kc g, clt_brs kt b -> clt_co kt g -> clt_brs kt (open_brs_wrt_co_rec kc g b)) /\
  (forall h kt kc g, clt_co kt h -> clt_co kt g -> clt_co kt (open_co_wrt_co_rec kc g h)) /\
  (forall p kt kc g, clt_constraint kt p -> clt_co kt g -> clt_constraint kt (open_constraint_wrt_co_rec kc g p)).
Proof.
  apply (tm_mutind
    (fun a => forall kt kc g, clt_tm kt a -> clt_co kt g -> clt_tm kt (open_tm_wrt_co_rec kc g a))
    (fun b => forall kt kc g, clt_brs kt b -> clt_co kt g -> clt_brs kt (open_brs_wrt_co_rec kc g b))
    (fun h => forall kt kc g, clt_co kt h -> clt_co kt g -> clt_co kt (open_co_wrt_co_rec kc g h))
    (fun p => forall kt kc g, clt_constraint kt p -> clt_co kt g -> clt_constraint kt (open_constraint_wrt_co_rec kc g p))).
  all: intros.
  all: cbn [clt_tm clt_brs clt_co clt_constraint] in *.
  all: cbn [open_tm_wrt_co_rec open_brs_wrt_co_rec open_co_wrt_co_rec open_constraint_wrt_co_rec].
  all: try solve [exact I].
  all: try solve [lia].
  all: crush_conj2.
  all: try split.
  all: try (eauto 20 using clt_tm_mono, clt_co_mono, clt_brs_mono, clt_constraint_mono).
  all: try (cbn [clt_co clt_tm clt_brs clt_constraint] in *; eauto 20).
  all: try (destruct (lt_eq_lt_dec n kc) as [[H1|H2]|H3]; try subst; try lia; auto).
Qed.


Lemma open_tm_var_b_clt : forall n kt u,
  clt_tm kt (open_tm_wrt_tm_rec kt u (a_Var_b n)) -> clt_tm kt u -> clt_tm (S kt) (a_Var_b n).
Proof.
  intros n kt u H Hu. cbn [open_tm_wrt_tm_rec] in H.
  destruct (lt_eq_lt_dec n kt) as [[H1|H2]|H3].
  - cbn [clt_tm] in *. lia.
  - subst. cbn [clt_tm]. lia.
  - cbn [clt_tm] in H. lia.
Qed.

Lemma clt_open_tm_inv_gen :
  (forall a kt u, clt_tm kt (open_tm_wrt_tm_rec kt u a) -> clt_tm kt u -> clt_tm (S kt) a) /\
  (forall b kt u, clt_brs kt (open_brs_wrt_tm_rec kt u b) -> clt_tm kt u -> clt_brs (S kt) b) /\
  (forall h kt u, clt_co kt (open_co_wrt_tm_rec kt u h) -> clt_tm kt u -> clt_co (S kt) h) /\
  (forall p kt u, clt_constraint kt (open_constraint_wrt_tm_rec kt u p) -> clt_tm kt u -> clt_constraint (S kt) p).
Proof.
  apply (tm_mutind
    (fun a => forall kt u, clt_tm kt (open_tm_wrt_tm_rec kt u a) -> clt_tm kt u -> clt_tm (S kt) a)
    (fun b => forall kt u, clt_brs kt (open_brs_wrt_tm_rec kt u b) -> clt_tm kt u -> clt_brs (S kt) b)
    (fun h => forall kt u, clt_co kt (open_co_wrt_tm_rec kt u h) -> clt_tm kt u -> clt_co (S kt) h)
    (fun p => forall kt u, clt_constraint kt (open_constraint_wrt_tm_rec kt u p) -> clt_tm kt u -> clt_constraint (S kt) p)).
  all: intros.
  all: cbn [open_tm_wrt_tm_rec open_brs_wrt_tm_rec open_co_wrt_tm_rec open_constraint_wrt_tm_rec] in *.
  all: try break_lt.
  all: try cbn [clt_tm clt_brs clt_co clt_constraint] in *.
  all: crush_conj2.
  all: try split.
  all: try (eauto 20 using clt_tm_mono, clt_co_mono, clt_brs_mono, clt_constraint_mono).
  all: try (cbn [clt_co clt_tm clt_brs clt_constraint] in *; eauto 20).
  all: try lia.
  all: try (match goal with
    | |- clc_tm ?m ?v => apply (clc_tm_mono v 0 m); [lia|assumption]
    | |- clc_co ?m ?v => apply (clc_co_mono v 0 m); [lia|assumption]
    | |- clc_brs ?m ?v => apply (clc_brs_mono v 0 m); [lia|assumption]
    | |- clc_constraint ?m ?v => apply (clc_constraint_mono v 0 m); [lia|assumption]
    | |- clt_tm ?m ?v => apply (clt_tm_mono v 0 m); [lia|assumption]
    | |- clt_co ?m ?v => apply (clt_co_mono v 0 m); [lia|assumption]
    | |- clt_brs ?m ?v => apply (clt_brs_mono v 0 m); [lia|assumption]
    | |- clt_constraint ?m ?v => apply (clt_constraint_mono v 0 m); [lia|assumption]
    end).
Qed.

Lemma clt_open_co_inv_gen :
  (forall a kt kc g, clt_tm kt (open_tm_wrt_co_rec kc g a) -> clt_co kt g -> clt_tm kt a) /\
  (forall b kt kc g, clt_brs kt (open_brs_wrt_co_rec kc g b) -> clt_co kt g -> clt_brs kt b) /\
  (forall h kt kc g, clt_co kt (open_co_wrt_co_rec kc g h) -> clt_co kt g -> clt_co kt h) /\
  (forall p kt kc g, clt_constraint kt (open_constraint_wrt_co_rec kc g p) -> clt_co kt g -> clt_constraint kt p).
Proof.
  apply (tm_mutind
    (fun a => forall kt kc g, clt_tm kt (open_tm_wrt_co_rec kc g a) -> clt_co kt g -> clt_tm kt a)
    (fun b => forall kt kc g, clt_brs kt (open_brs_wrt_co_rec kc g b) -> clt_co kt g -> clt_brs kt b)
    (fun h => forall kt kc g, clt_co kt (open_co_wrt_co_rec kc g h) -> clt_co kt g -> clt_co kt h)
    (fun p => forall kt kc g, clt_constraint kt (open_constraint_wrt_co_rec kc g p) -> clt_co kt g -> clt_constraint kt p)).
  all: intros.
  all: cbn [open_tm_wrt_co_rec open_brs_wrt_co_rec open_co_wrt_co_rec open_constraint_wrt_co_rec] in *.
  all: try break_lt.
  all: try cbn [clt_tm clt_brs clt_co clt_constraint] in *.
  all: crush_conj2.
  all: try split.
  all: try (eauto 20 using clt_tm_mono, clt_co_mono, clt_brs_mono, clt_constraint_mono).
  all: try (cbn [clt_co clt_tm clt_brs clt_constraint] in *; eauto 20).
  all: try lia.
  all: try (match goal with
    | |- clc_tm ?m ?v => apply (clc_tm_mono v 0 m); [lia|assumption]
    | |- clc_co ?m ?v => apply (clc_co_mono v 0 m); [lia|assumption]
    | |- clc_brs ?m ?v => apply (clc_brs_mono v 0 m); [lia|assumption]
    | |- clc_constraint ?m ?v => apply (clc_constraint_mono v 0 m); [lia|assumption]
    | |- clt_tm ?m ?v => apply (clt_tm_mono v 0 m); [lia|assumption]
    | |- clt_co ?m ?v => apply (clt_co_mono v 0 m); [lia|assumption]
    | |- clt_brs ?m ?v => apply (clt_brs_mono v 0 m); [lia|assumption]
    | |- clt_constraint ?m ?v => apply (clt_constraint_mono v 0 m); [lia|assumption]
    end).
Qed.

Lemma clc_open_tm_fwd_gen :
  (forall a n k u, clc_tm n a -> clc_tm 0 u -> clc_tm n (open_tm_wrt_tm_rec k u a)) /\
  (forall b n k u, clc_brs n b -> clc_tm 0 u -> clc_brs n (open_brs_wrt_tm_rec k u b)) /\
  (forall h n k u, clc_co n h -> clc_tm 0 u -> clc_co n (open_co_wrt_tm_rec k u h)) /\
  (forall p n k u, clc_constraint n p -> clc_tm 0 u -> clc_constraint n (open_constraint_wrt_tm_rec k u p)).
Proof.
  apply (tm_mutind
    (fun a => forall n k u, clc_tm n a -> clc_tm 0 u -> clc_tm n (open_tm_wrt_tm_rec k u a))
    (fun b => forall n k u, clc_brs n b -> clc_tm 0 u -> clc_brs n (open_brs_wrt_tm_rec k u b))
    (fun h => forall n k u, clc_co n h -> clc_tm 0 u -> clc_co n (open_co_wrt_tm_rec k u h))
    (fun p => forall n k u, clc_constraint n p -> clc_tm 0 u -> clc_constraint n (open_constraint_wrt_tm_rec k u p))).
  all: intros.
  all: cbn [open_tm_wrt_tm_rec open_brs_wrt_tm_rec open_co_wrt_tm_rec open_constraint_wrt_tm_rec] in *.
  all: try break_lt.
  all: try cbn [clc_tm clc_brs clc_co clc_constraint] in *.
  all: crush_conj2.
  all: try split.
  all: try (eauto 20 using clc_tm_mono, clc_co_mono, clc_brs_mono, clc_constraint_mono).
  all: try (cbn [clc_co clc_tm clc_brs clc_constraint] in *; eauto 20).
  all: try lia.
  all: try (match goal with
    | |- clc_tm ?m ?v => apply (clc_tm_mono v 0 m); [lia|assumption]
    | |- clc_co ?m ?v => apply (clc_co_mono v 0 m); [lia|assumption]
    | |- clc_brs ?m ?v => apply (clc_brs_mono v 0 m); [lia|assumption]
    | |- clc_constraint ?m ?v => apply (clc_constraint_mono v 0 m); [lia|assumption]
    | |- clt_tm ?m ?v => apply (clt_tm_mono v 0 m); [lia|assumption]
    | |- clt_co ?m ?v => apply (clt_co_mono v 0 m); [lia|assumption]
    | |- clt_brs ?m ?v => apply (clt_brs_mono v 0 m); [lia|assumption]
    | |- clt_constraint ?m ?v => apply (clt_constraint_mono v 0 m); [lia|assumption]
    end).
Qed.

Lemma clc_open_co_fwd_gen :
  (forall a n k g, clc_tm n a -> clc_co 0 g -> clc_tm n (open_tm_wrt_co_rec k g a)) /\
  (forall b n k g, clc_brs n b -> clc_co 0 g -> clc_brs n (open_brs_wrt_co_rec k g b)) /\
  (forall h n k g, clc_co n h -> clc_co 0 g -> clc_co n (open_co_wrt_co_rec k g h)) /\
  (forall p n k g, clc_constraint n p -> clc_co 0 g -> clc_constraint n (open_constraint_wrt_co_rec k g p)).
Proof.
  apply (tm_mutind
    (fun a => forall n k g, clc_tm n a -> clc_co 0 g -> clc_tm n (open_tm_wrt_co_rec k g a))
    (fun b => forall n k g, clc_brs n b -> clc_co 0 g -> clc_brs n (open_brs_wrt_co_rec k g b))
    (fun h => forall n k g, clc_co n h -> clc_co 0 g -> clc_co n (open_co_wrt_co_rec k g h))
    (fun p => forall n k g, clc_constraint n p -> clc_co 0 g -> clc_constraint n (open_constraint_wrt_co_rec k g p))).
  all: intros.
  all: cbn [open_tm_wrt_co_rec open_brs_wrt_co_rec open_co_wrt_co_rec open_constraint_wrt_co_rec] in *.
  all: try break_lt.
  all: try cbn [clc_tm clc_brs clc_co clc_constraint] in *.
  all: crush_conj2.
  all: try split.
  all: try (eauto 20 using clc_tm_mono, clc_co_mono, clc_brs_mono, clc_constraint_mono).
  all: try (cbn [clc_co clc_tm clc_brs clc_constraint] in *; eauto 20).
  all: try lia.
  all: try (match goal with
    | |- clc_tm ?m ?v => apply (clc_tm_mono v 0 m); [lia|assumption]
    | |- clc_co ?m ?v => apply (clc_co_mono v 0 m); [lia|assumption]
    | |- clc_brs ?m ?v => apply (clc_brs_mono v 0 m); [lia|assumption]
    | |- clc_constraint ?m ?v => apply (clc_constraint_mono v 0 m); [lia|assumption]
    | |- clt_tm ?m ?v => apply (clt_tm_mono v 0 m); [lia|assumption]
    | |- clt_co ?m ?v => apply (clt_co_mono v 0 m); [lia|assumption]
    | |- clt_brs ?m ?v => apply (clt_brs_mono v 0 m); [lia|assumption]
    | |- clt_constraint ?m ?v => apply (clt_constraint_mono v 0 m); [lia|assumption]
    end).
Qed.

Lemma clc_open_tm_inv_gen :
  (forall a n k u, clc_tm n (open_tm_wrt_tm_rec k u a) -> clc_tm 0 u -> clc_tm n a) /\
  (forall b n k u, clc_brs n (open_brs_wrt_tm_rec k u b) -> clc_tm 0 u -> clc_brs n b) /\
  (forall h n k u, clc_co n (open_co_wrt_tm_rec k u h) -> clc_tm 0 u -> clc_co n h) /\
  (forall p n k u, clc_constraint n (open_constraint_wrt_tm_rec k u p) -> clc_tm 0 u -> clc_constraint n p).
Proof.
  apply (tm_mutind
    (fun a => forall n k u, clc_tm n (open_tm_wrt_tm_rec k u a) -> clc_tm 0 u -> clc_tm n a)
    (fun b => forall n k u, clc_brs n (open_brs_wrt_tm_rec k u b) -> clc_tm 0 u -> clc_brs n b)
    (fun h => forall n k u, clc_co n (open_co_wrt_tm_rec k u h) -> clc_tm 0 u -> clc_co n h)
    (fun p => forall n k u, clc_constraint n (open_constraint_wrt_tm_rec k u p) -> clc_tm 0 u -> clc_constraint n p)).
  all: intros.
  all: cbn [open_tm_wrt_tm_rec open_brs_wrt_tm_rec open_co_wrt_tm_rec open_constraint_wrt_tm_rec] in *.
  all: try break_lt.
  all: try cbn [clc_tm clc_brs clc_co clc_constraint] in *.
  all: crush_conj2.
  all: try split.
  all: try (eauto 20 using clc_tm_mono, clc_co_mono, clc_brs_mono, clc_constraint_mono).
  all: try (cbn [clc_co clc_tm clc_brs clc_constraint] in *; eauto 20).
  all: try lia.
  all: try (match goal with
    | |- clc_tm ?m ?v => apply (clc_tm_mono v 0 m); [lia|assumption]
    | |- clc_co ?m ?v => apply (clc_co_mono v 0 m); [lia|assumption]
    | |- clc_brs ?m ?v => apply (clc_brs_mono v 0 m); [lia|assumption]
    | |- clc_constraint ?m ?v => apply (clc_constraint_mono v 0 m); [lia|assumption]
    | |- clt_tm ?m ?v => apply (clt_tm_mono v 0 m); [lia|assumption]
    | |- clt_co ?m ?v => apply (clt_co_mono v 0 m); [lia|assumption]
    | |- clt_brs ?m ?v => apply (clt_brs_mono v 0 m); [lia|assumption]
    | |- clt_constraint ?m ?v => apply (clt_constraint_mono v 0 m); [lia|assumption]
    end).
Qed.

Lemma clc_open_co_inv_gen :
  (forall a k g, clc_tm k (open_tm_wrt_co_rec k g a) -> clc_co 0 g -> clc_tm (S k) a) /\
  (forall b k g, clc_brs k (open_brs_wrt_co_rec k g b) -> clc_co 0 g -> clc_brs (S k) b) /\
  (forall h k g, clc_co k (open_co_wrt_co_rec k g h) -> clc_co 0 g -> clc_co (S k) h) /\
  (forall p k g, clc_constraint k (open_constraint_wrt_co_rec k g p) -> clc_co 0 g -> clc_constraint (S k) p).
Proof.
  apply (tm_mutind
    (fun a => forall k g, clc_tm k (open_tm_wrt_co_rec k g a) -> clc_co 0 g -> clc_tm (S k) a)
    (fun b => forall k g, clc_brs k (open_brs_wrt_co_rec k g b) -> clc_co 0 g -> clc_brs (S k) b)
    (fun h => forall k g, clc_co k (open_co_wrt_co_rec k g h) -> clc_co 0 g -> clc_co (S k) h)
    (fun p => forall k g, clc_constraint k (open_constraint_wrt_co_rec k g p) -> clc_co 0 g -> clc_constraint (S k) p)).
  all: intros.
  all: cbn [open_tm_wrt_co_rec open_brs_wrt_co_rec open_co_wrt_co_rec open_constraint_wrt_co_rec] in *.
  all: try break_lt.
  all: try cbn [clc_tm clc_brs clc_co clc_constraint] in *.
  all: crush_conj2.
  all: try split.
  all: try (eauto 20 using clc_tm_mono, clc_co_mono, clc_brs_mono, clc_constraint_mono).
  all: try (cbn [clc_co clc_tm clc_brs clc_constraint] in *; eauto 20).
  all: try lia.
  all: try (match goal with
    | |- clc_tm ?m ?v => apply (clc_tm_mono v 0 m); [lia|assumption]
    | |- clc_co ?m ?v => apply (clc_co_mono v 0 m); [lia|assumption]
    | |- clc_brs ?m ?v => apply (clc_brs_mono v 0 m); [lia|assumption]
    | |- clc_constraint ?m ?v => apply (clc_constraint_mono v 0 m); [lia|assumption]
    end).
Qed.

(* Accessors for the forward/inverse opening lemmas *)
Lemma clt_tm_open_tm_fwd_gen : forall a kt u,
  clt_tm kt u -> clt_tm (S kt) a -> clt_tm kt (open_tm_wrt_tm_rec kt u a).
Proof. intros; exact (proj1 clt_open_tm_fwd_gen a kt u H0 H). Qed.
Lemma clt_brs_open_tm_fwd_gen : forall b kt u,
  clt_tm kt u -> clt_brs (S kt) b -> clt_brs kt (open_brs_wrt_tm_rec kt u b).
Proof. intros; exact (proj1 (proj2 clt_open_tm_fwd_gen) b kt u H0 H). Qed.
Lemma clt_co_open_tm_fwd_gen : forall g kt u,
  clt_tm kt u -> clt_co (S kt) g -> clt_co kt (open_co_wrt_tm_rec kt u g).
Proof. intros; exact (proj1 (proj2 (proj2 clt_open_tm_fwd_gen)) g kt u H0 H). Qed.
Lemma clt_constraint_open_tm_fwd_gen : forall p kt u,
  clt_tm kt u -> clt_constraint (S kt) p -> clt_constraint kt (open_constraint_wrt_tm_rec kt u p).
Proof. intros; exact (proj2 (proj2 (proj2 clt_open_tm_fwd_gen)) p kt u H0 H). Qed.

Lemma clt_tm_open_co_fwd_gen : forall a kt kc g,
  clt_co kt g -> clt_tm kt a -> clt_tm kt (open_tm_wrt_co_rec kc g a).
Proof. intros; exact (proj1 clt_open_co_fwd_gen a kt kc g H0 H). Qed.
Lemma clt_brs_open_co_fwd_gen : forall b kt kc g,
  clt_co kt g -> clt_brs kt b -> clt_brs kt (open_brs_wrt_co_rec kc g b).
Proof. intros; exact (proj1 (proj2 clt_open_co_fwd_gen) b kt kc g H0 H). Qed.
Lemma clt_co_open_co_fwd_gen : forall h kt kc g,
  clt_co kt g -> clt_co kt h -> clt_co kt (open_co_wrt_co_rec kc g h).
Proof. intros; exact (proj1 (proj2 (proj2 clt_open_co_fwd_gen)) h kt kc g H0 H). Qed.
Lemma clt_constraint_open_co_fwd_gen : forall p kt kc g,
  clt_co kt g -> clt_constraint kt p -> clt_constraint kt (open_constraint_wrt_co_rec kc g p).
Proof. intros; exact (proj2 (proj2 (proj2 clt_open_co_fwd_gen)) p kt kc g H0 H). Qed.

Lemma clt_tm_open_tm_inv_gen : forall a kt u,
  clt_tm kt (open_tm_wrt_tm_rec kt u a) -> clt_tm kt u -> clt_tm (S kt) a.
Proof. intros; exact (proj1 clt_open_tm_inv_gen a kt u H H0). Qed.
Lemma clt_brs_open_tm_inv_gen : forall b kt u,
  clt_brs kt (open_brs_wrt_tm_rec kt u b) -> clt_tm kt u -> clt_brs (S kt) b.
Proof. intros; exact (proj1 (proj2 clt_open_tm_inv_gen) b kt u H H0). Qed.
Lemma clt_co_open_tm_inv_gen : forall g kt u,
  clt_co kt (open_co_wrt_tm_rec kt u g) -> clt_tm kt u -> clt_co (S kt) g.
Proof. intros; exact (proj1 (proj2 (proj2 clt_open_tm_inv_gen)) g kt u H H0). Qed.
Lemma clt_constraint_open_tm_inv_gen : forall p kt u,
  clt_constraint kt (open_constraint_wrt_tm_rec kt u p) -> clt_tm kt u -> clt_constraint (S kt) p.
Proof. intros; exact (proj2 (proj2 (proj2 clt_open_tm_inv_gen)) p kt u H H0). Qed.

Lemma clt_tm_open_co_inv_gen : forall a kt kc g,
  clt_tm kt (open_tm_wrt_co_rec kc g a) -> clt_co kt g -> clt_tm kt a.
Proof. intros; exact (proj1 clt_open_co_inv_gen a kt kc g H H0). Qed.
Lemma clt_brs_open_co_inv_gen : forall b kt kc g,
  clt_brs kt (open_brs_wrt_co_rec kc g b) -> clt_co kt g -> clt_brs kt b.
Proof. intros; exact (proj1 (proj2 clt_open_co_inv_gen) b kt kc g H H0). Qed.
Lemma clt_co_open_co_inv_gen : forall h kt kc g,
  clt_co kt (open_co_wrt_co_rec kc g h) -> clt_co kt g -> clt_co kt h.
Proof. intros; exact (proj1 (proj2 (proj2 clt_open_co_inv_gen)) h kt kc g H H0). Qed.
Lemma clt_constraint_open_co_inv_gen : forall p kt kc g,
  clt_constraint kt (open_constraint_wrt_co_rec kc g p) -> clt_co kt g -> clt_constraint kt p.
Proof. intros; exact (proj2 (proj2 (proj2 clt_open_co_inv_gen)) p kt kc g H H0). Qed.

Lemma clc_tm_open_tm_fwd_gen : forall a n k u,
  clc_tm 0 u -> clc_tm n a -> clc_tm n (open_tm_wrt_tm_rec k u a).
Proof. intros; exact (proj1 clc_open_tm_fwd_gen a n k u H0 H). Qed.
Lemma clc_brs_open_tm_fwd_gen : forall b n k u,
  clc_tm 0 u -> clc_brs n b -> clc_brs n (open_brs_wrt_tm_rec k u b).
Proof. intros; exact (proj1 (proj2 clc_open_tm_fwd_gen) b n k u H0 H). Qed.
Lemma clc_co_open_tm_fwd_gen : forall g n k u,
  clc_tm 0 u -> clc_co n g -> clc_co n (open_co_wrt_tm_rec k u g).
Proof. intros; exact (proj1 (proj2 (proj2 clc_open_tm_fwd_gen)) g n k u H0 H). Qed.
Lemma clc_constraint_open_tm_fwd_gen : forall p n k u,
  clc_tm 0 u -> clc_constraint n p -> clc_constraint n (open_constraint_wrt_tm_rec k u p).
Proof. intros; exact (proj2 (proj2 (proj2 clc_open_tm_fwd_gen)) p n k u H0 H). Qed.

Lemma clc_tm_open_co_fwd_gen : forall a n k g,
  clc_co 0 g -> clc_tm n a -> clc_tm n (open_tm_wrt_co_rec k g a).
Proof. intros; exact (proj1 clc_open_co_fwd_gen a n k g H0 H). Qed.
Lemma clc_brs_open_co_fwd_gen : forall b n k g,
  clc_co 0 g -> clc_brs n b -> clc_brs n (open_brs_wrt_co_rec k g b).
Proof. intros; exact (proj1 (proj2 clc_open_co_fwd_gen) b n k g H0 H). Qed.
Lemma clc_co_open_co_fwd_gen : forall h n k g,
  clc_co 0 g -> clc_co n h -> clc_co n (open_co_wrt_co_rec k g h).
Proof. intros; exact (proj1 (proj2 (proj2 clc_open_co_fwd_gen)) h n k g H0 H). Qed.
Lemma clc_constraint_open_co_fwd_gen : forall p n k g,
  clc_co 0 g -> clc_constraint n p -> clc_constraint n (open_constraint_wrt_co_rec k g p).
Proof. intros; exact (proj2 (proj2 (proj2 clc_open_co_fwd_gen)) p n k g H0 H). Qed.

Lemma clc_tm_open_tm_inv_gen : forall a n k u,
  clc_tm n (open_tm_wrt_tm_rec k u a) -> clc_tm 0 u -> clc_tm n a.
Proof. intros; exact (proj1 clc_open_tm_inv_gen a n k u H H0). Qed.
Lemma clc_brs_open_tm_inv_gen : forall b n k u,
  clc_brs n (open_brs_wrt_tm_rec k u b) -> clc_tm 0 u -> clc_brs n b.
Proof. intros; exact (proj1 (proj2 clc_open_tm_inv_gen) b n k u H H0). Qed.
Lemma clc_co_open_tm_inv_gen : forall g n k u,
  clc_co n (open_co_wrt_tm_rec k u g) -> clc_tm 0 u -> clc_co n g.
Proof. intros; exact (proj1 (proj2 (proj2 clc_open_tm_inv_gen)) g n k u H H0). Qed.
Lemma clc_constraint_open_tm_inv_gen : forall p n k u,
  clc_constraint n (open_constraint_wrt_tm_rec k u p) -> clc_tm 0 u -> clc_constraint n p.
Proof. intros; exact (proj2 (proj2 (proj2 clc_open_tm_inv_gen)) p n k u H H0). Qed.

Lemma clc_tm_open_co_inv_gen : forall a k g,
  clc_tm k (open_tm_wrt_co_rec k g a) -> clc_co 0 g -> clc_tm (S k) a.
Proof. intros; exact (proj1 clc_open_co_inv_gen a k g H H0). Qed.
Lemma clc_brs_open_co_inv_gen : forall b k g,
  clc_brs k (open_brs_wrt_co_rec k g b) -> clc_co 0 g -> clc_brs (S k) b.
Proof. intros; exact (proj1 (proj2 clc_open_co_inv_gen) b k g H H0). Qed.
Lemma clc_co_open_co_inv_gen : forall h k g,
  clc_co k (open_co_wrt_co_rec k g h) -> clc_co 0 g -> clc_co (S k) h.
Proof. intros; exact (proj1 (proj2 (proj2 clc_open_co_inv_gen)) h k g H H0). Qed.
Lemma clc_constraint_open_co_inv_gen : forall p k g,
  clc_constraint k (open_constraint_wrt_co_rec k g p) -> clc_co 0 g -> clc_constraint (S k) p.
Proof. intros; exact (proj2 (proj2 (proj2 clc_open_co_inv_gen)) p k g H H0). Qed.

Lemma sz_open_tm_var_all :
  (forall a x k, sz_tm (open_tm_wrt_tm_rec k (a_Var_f x) a) = sz_tm a) /\
  (forall b x k, sz_brs (open_brs_wrt_tm_rec k (a_Var_f x) b) = sz_brs b) /\
  (forall g x k, sz_co (open_co_wrt_tm_rec k (a_Var_f x) g) = sz_co g) /\
  (forall p x k, sz_constraint (open_constraint_wrt_tm_rec k (a_Var_f x) p) = sz_constraint p).
Proof.
  apply (tm_mutind
    (fun a => forall x k, sz_tm (open_tm_wrt_tm_rec k (a_Var_f x) a) = sz_tm a)
    (fun b => forall x k, sz_brs (open_brs_wrt_tm_rec k (a_Var_f x) b) = sz_brs b)
    (fun g => forall x k, sz_co (open_co_wrt_tm_rec k (a_Var_f x) g) = sz_co g)
    (fun p => forall x k, sz_constraint (open_constraint_wrt_tm_rec k (a_Var_f x) p) = sz_constraint p)).
  all: intros.
  all: cbn [open_tm_wrt_tm_rec open_brs_wrt_tm_rec open_co_wrt_tm_rec open_constraint_wrt_tm_rec sz_tm sz_brs sz_co sz_constraint].
  all: try break_lt.
  all: try reflexivity.
  all: repeat match goal with
    | IH : forall (z:tmvar) (k0:nat), _ |- _ =>
        progress (try rewrite (IH x k); try rewrite (IH x (S k)))
    end.
  all: try reflexivity.
Qed.

Lemma sz_open_co_var_all :
  (forall a c k, sz_tm (open_tm_wrt_co_rec k (g_Var_f c) a) = sz_tm a) /\
  (forall b c k, sz_brs (open_brs_wrt_co_rec k (g_Var_f c) b) = sz_brs b) /\
  (forall g c k, sz_co (open_co_wrt_co_rec k (g_Var_f c) g) = sz_co g) /\
  (forall p c k, sz_constraint (open_constraint_wrt_co_rec k (g_Var_f c) p) = sz_constraint p).
Proof.
  apply (tm_mutind
    (fun a => forall c k, sz_tm (open_tm_wrt_co_rec k (g_Var_f c) a) = sz_tm a)
    (fun b => forall c k, sz_brs (open_brs_wrt_co_rec k (g_Var_f c) b) = sz_brs b)
    (fun g => forall c k, sz_co (open_co_wrt_co_rec k (g_Var_f c) g) = sz_co g)
    (fun p => forall c k, sz_constraint (open_constraint_wrt_co_rec k (g_Var_f c) p) = sz_constraint p)).
  all: intros.
  all: cbn [open_tm_wrt_co_rec open_brs_wrt_co_rec open_co_wrt_co_rec open_constraint_wrt_co_rec sz_tm sz_brs sz_co sz_constraint].
  all: try break_lt.
  all: try reflexivity.
  all: repeat match goal with
    | IH : forall (z:covar) (k0:nat), _ |- _ =>
        progress (try rewrite (IH c k); try rewrite (IH c (S k)))
    end.
  all: try reflexivity.
Qed.

Lemma sz_tm_open_tm_var : forall a x k,
  sz_tm (open_tm_wrt_tm_rec k (a_Var_f x) a) = sz_tm a.
Proof. intros; exact (proj1 sz_open_tm_var_all a x k). Qed.
Lemma sz_brs_open_tm_var : forall b x k,
  sz_brs (open_brs_wrt_tm_rec k (a_Var_f x) b) = sz_brs b.
Proof. intros; exact (proj1 (proj2 sz_open_tm_var_all) b x k). Qed.
Lemma sz_co_open_tm_var : forall g x k,
  sz_co (open_co_wrt_tm_rec k (a_Var_f x) g) = sz_co g.
Proof. intros; exact (proj1 (proj2 (proj2 sz_open_tm_var_all)) g x k). Qed.
Lemma sz_constraint_open_tm_var : forall p x k,
  sz_constraint (open_constraint_wrt_tm_rec k (a_Var_f x) p) = sz_constraint p.
Proof. intros; exact (proj2 (proj2 (proj2 sz_open_tm_var_all)) p x k). Qed.

Lemma sz_tm_open_co_var : forall a c k,
  sz_tm (open_tm_wrt_co_rec k (g_Var_f c) a) = sz_tm a.
Proof. intros; exact (proj1 sz_open_co_var_all a c k). Qed.
Lemma sz_brs_open_co_var : forall b c k,
  sz_brs (open_brs_wrt_co_rec k (g_Var_f c) b) = sz_brs b.
Proof. intros; exact (proj1 (proj2 sz_open_co_var_all) b c k). Qed.
Lemma sz_co_open_co_var : forall g c k,
  sz_co (open_co_wrt_co_rec k (g_Var_f c) g) = sz_co g.
Proof. intros; exact (proj1 (proj2 (proj2 sz_open_co_var_all)) g c k). Qed.
Lemma sz_constraint_open_co_var : forall p c k,
  sz_constraint (open_constraint_wrt_co_rec k (g_Var_f c) p) = sz_constraint p.
Proof. intros; exact (proj2 (proj2 (proj2 sz_open_co_var_all)) p c k). Qed.

Definition sz_tm_pos : forall a, 0 < sz_tm a := fun a => proj1 sz_nonzero_mut a.
Definition sz_brs_pos : forall b, 0 < sz_brs b := fun b => proj1 (proj2 sz_nonzero_mut) b.
Definition sz_co_pos : forall g, 0 < sz_co g := fun g => proj1 (proj2 (proj2 sz_nonzero_mut)) g.
Definition sz_constraint_pos : forall p, 0 < sz_constraint p := fun p => proj2 (proj2 (proj2 sz_nonzero_mut)) p.

Lemma clc_open_co_fwd_gen_sharp :
  (forall a k g, clc_tm (S k) a -> clc_co 0 g -> clc_tm k (open_tm_wrt_co_rec k g a)) /\
  (forall b k g, clc_brs (S k) b -> clc_co 0 g -> clc_brs k (open_brs_wrt_co_rec k g b)) /\
  (forall h k g, clc_co (S k) h -> clc_co 0 g -> clc_co k (open_co_wrt_co_rec k g h)) /\
  (forall p k g, clc_constraint (S k) p -> clc_co 0 g -> clc_constraint k (open_constraint_wrt_co_rec k g p)).
Proof.
  apply (tm_mutind
    (fun a => forall k g, clc_tm (S k) a -> clc_co 0 g -> clc_tm k (open_tm_wrt_co_rec k g a))
    (fun b => forall k g, clc_brs (S k) b -> clc_co 0 g -> clc_brs k (open_brs_wrt_co_rec k g b))
    (fun h => forall k g, clc_co (S k) h -> clc_co 0 g -> clc_co k (open_co_wrt_co_rec k g h))
    (fun p => forall k g, clc_constraint (S k) p -> clc_co 0 g -> clc_constraint k (open_constraint_wrt_co_rec k g p))).
  all: intros.
  all: cbn [open_tm_wrt_co_rec open_brs_wrt_co_rec open_co_wrt_co_rec open_constraint_wrt_co_rec] in *.
  all: try break_lt.
  all: try cbn [clc_tm clc_brs clc_co clc_constraint] in *.
  all: crush_conj2.
  all: try split.
  all: try (eauto 20 using clc_tm_mono, clc_co_mono, clc_brs_mono, clc_constraint_mono).
  all: try (cbn [clc_co clc_tm clc_brs clc_constraint] in *; eauto 20).
  all: try lia.
  all: try (match goal with
    | |- clc_tm ?m ?v => apply (clc_tm_mono v 0 m); [lia|assumption]
    | |- clc_co ?m ?v => apply (clc_co_mono v 0 m); [lia|assumption]
    | |- clc_brs ?m ?v => apply (clc_brs_mono v 0 m); [lia|assumption]
    | |- clc_constraint ?m ?v => apply (clc_constraint_mono v 0 m); [lia|assumption]
    end).
Qed.

Lemma clc_tm_open_co_fwd_sharp : forall a k g,
  clc_co 0 g -> clc_tm (S k) a -> clc_tm k (open_tm_wrt_co_rec k g a).
Proof. intros; exact (proj1 clc_open_co_fwd_gen_sharp a k g H0 H). Qed.
Lemma clc_co_open_co_fwd_sharp : forall h k g,
  clc_co 0 g -> clc_co (S k) h -> clc_co k (open_co_wrt_co_rec k g h).
Proof. intros; exact (proj1 (proj2 (proj2 clc_open_co_fwd_gen_sharp)) h k g H0 H). Qed.

Lemma closed_lc_all : forall n,
  (forall a, sz_tm a <= n -> clt_tm 0 a -> clc_tm 0 a -> lc_tm a) /\
  (forall b, sz_brs b <= n -> clt_brs 0 b -> clc_brs 0 b -> lc_brs b) /\
  (forall g, sz_co g <= n -> clt_co 0 g -> clc_co 0 g -> lc_co g) /\
  (forall p, sz_constraint p <= n -> clt_constraint 0 p -> clc_constraint 0 p -> lc_constraint p).
Proof.
  induction n as [|n IH].
  - split.
    + intros a Hle Ht Hc. exfalso. pose proof (sz_tm_pos a). lia.
    + split.
      * intros b Hle Ht Hc. exfalso. pose proof (sz_brs_pos b). lia.
      * split.
        -- intros g Hle Ht Hc. exfalso. pose proof (sz_co_pos g). lia.
        -- intros p Hle Ht Hc. exfalso. pose proof (sz_constraint_pos p). lia.
  - destruct IH as [IHtm [IHbrs [IHco IHcon]]].
    split.
    + intros a Hle Ht Hc.
      destruct a as [ |m |x |rho A b |rho b |a1 rho b |F |T |rho A B |a1 g |phi B |phi b |b |a1 g | |K |a1 brs ];
        cbn [clt_tm] in Ht; cbn [clc_tm] in Hc; simpl in Hle.
      * constructor.
      * lia.
      * constructor.
      * destruct Ht as [HtA Htb]; destruct Hc as [HcA Hcb].
        constructor.
        -- apply IHtm; [simpl in *; lia | exact HtA | exact HcA].
        -- intro x. apply (IHtm (open_tm_wrt_tm_rec 0 (a_Var_f x) b)).
           ++ rewrite sz_tm_open_tm_var; simpl in Hle; lia.
           ++ apply clt_tm_open_tm_fwd_gen; [cbn; exact I | exact Htb].
           ++ apply clc_tm_open_tm_fwd_gen; [cbn; exact I | exact Hcb].
      * constructor. intro x. apply (IHtm (open_tm_wrt_tm_rec 0 (a_Var_f x) b)).
        -- rewrite sz_tm_open_tm_var; simpl in Hle; lia.
        -- apply clt_tm_open_tm_fwd_gen; [cbn; exact I | exact Ht].
        -- apply clc_tm_open_tm_fwd_gen; [cbn; exact I | exact Hc].
      * destruct Ht as [Hta Htb]; destruct Hc as [Hca Hcb].
        constructor.
        -- apply IHtm; [simpl in *; lia | exact Hta | exact Hca].
        -- apply IHtm; [simpl in *; lia | exact Htb | exact Hcb].
      * constructor.
      * constructor.
      * destruct Ht as [HtA HtB]; destruct Hc as [HcA HcB].
        constructor.
        -- apply IHtm; [simpl in *; lia | exact HtA | exact HcA].
        -- intro x. apply (IHtm (open_tm_wrt_tm_rec 0 (a_Var_f x) B)).
           ++ rewrite sz_tm_open_tm_var; simpl in Hle; lia.
           ++ apply clt_tm_open_tm_fwd_gen; [cbn; exact I | exact HtB].
           ++ apply clc_tm_open_tm_fwd_gen; [cbn; exact I | exact HcB].
      * destruct Ht as [Hta Htg]; destruct Hc as [Hca Hcg].
        constructor.
        -- apply IHtm; [simpl in *; lia | exact Hta | exact Hca].
        -- apply IHco; [simpl in *; lia | exact Htg | exact Hcg].
      * destruct Ht as [Htp HtB]; destruct Hc as [Hcp HcB].
        constructor.
        -- apply IHcon; [simpl in *; lia | exact Htp | exact Hcp].
        -- intro c. apply (IHtm (open_tm_wrt_co_rec 0 (g_Var_f c) B)).
           ++ rewrite sz_tm_open_co_var; simpl in Hle; lia.
           ++ apply clt_tm_open_co_fwd_gen; [cbn; exact I | exact HtB].
           ++ apply clc_tm_open_co_fwd_sharp; [cbn; exact I | exact HcB].
      * destruct Ht as [Htp Htb]; destruct Hc as [Hcp Hcb].
        constructor.
        -- apply IHcon; [simpl in *; lia | exact Htp | exact Hcp].
        -- intro c. apply (IHtm (open_tm_wrt_co_rec 0 (g_Var_f c) b)).
           ++ rewrite sz_tm_open_co_var; simpl in Hle; lia.
           ++ apply clt_tm_open_co_fwd_gen; [cbn; exact I | exact Htb].
           ++ apply clc_tm_open_co_fwd_sharp; [cbn; exact I | exact Hcb].
      * constructor. intro c. apply (IHtm (open_tm_wrt_co_rec 0 (g_Var_f c) b)).
        -- rewrite sz_tm_open_co_var; simpl in Hle; lia.
        -- apply clt_tm_open_co_fwd_gen; [cbn; exact I | exact Ht].
        -- apply clc_tm_open_co_fwd_sharp; [cbn; exact I | exact Hc].
      * destruct Ht as [Hta Htg]; destruct Hc as [Hca Hcg].
        constructor.
        -- apply IHtm; [simpl in *; lia | exact Hta | exact Hca].
        -- apply IHco; [simpl in *; lia | exact Htg | exact Hcg].
      * constructor.
      * constructor.
      * destruct Ht as [Hta Htbr]; destruct Hc as [Hca Hcbr].
        constructor.
        -- apply IHtm; [simpl in *; lia | exact Hta | exact Hca].
        -- apply IHbrs; [simpl in *; lia | exact Htbr | exact Hcbr].
    + split.
      * intros b Hle Ht Hc. destruct b as [ |K a rest]; cbn [clt_brs] in Ht; cbn [clc_brs] in Hc; simpl in Hle.
        -- constructor.
        -- destruct Ht as [Hta Htbr]; destruct Hc as [Hca Hcbr].
           constructor.
           ++ apply IHtm; [simpl in *; lia | exact Hta | exact Hca].
           ++ apply IHbrs; [simpl in *; lia | exact Htbr | exact Hcbr].
      * split.
        -- intros g Hle Ht Hc.
           destruct g as [ |m |c |a1 b |a1 |a1 b g0 |g0 |g1 g2 |rho g1 g2 |rho g1 g2 |g1 rho g2 |g0 |g0 |g0 |g1 g2 |g1 g3 |g1 g3 g4 |g0 g1 g2 |g0 g1 g2 |g1 g2 |g1 A g2 |phi1 phi2 g0 |a1 |g0 g' |g0 g' ];
             cbn [clt_co] in Ht; cbn [clc_co] in Hc; simpl in Hle.
           ++ constructor.
           ++ lia.
           ++ constructor.
           ++ destruct Ht as [Hta Htb]; destruct Hc as [Hca Hcb]. constructor;
                 [ apply IHtm; [simpl in *; lia | exact Hta | exact Hca]
                 | apply IHtm; [simpl in *; lia | exact Htb | exact Hcb] ].
           ++ constructor; apply IHtm; [simpl in *; lia | exact Ht | exact Hc].
           ++ destruct Ht as [Hta [Htb Htg]]; destruct Hc as [Hca [Hcb Hcg]]. constructor;
                 [ apply IHtm; [simpl in *; lia | exact Hta | exact Hca]
                 | apply IHtm; [simpl in *; lia | exact Htb | exact Hcb]
                 | apply IHco; [simpl in *; lia | exact Htg | exact Hcg] ].
           ++ constructor; apply IHco; [simpl in *; lia | exact Ht | exact Hc].
           ++ destruct Ht as [Ht1 Ht2]; destruct Hc as [Hc1 Hc2]. constructor;
                 [ apply IHco; [simpl in *; lia | exact Ht1 | exact Hc1]
                 | apply IHco; [simpl in *; lia | exact Ht2 | exact Hc2] ].
           ++ destruct Ht as [Ht1 Ht2]; destruct Hc as [Hc1 Hc2]. constructor.
              ** apply IHco; [simpl in *; lia | exact Ht1 | exact Hc1].
              ** intro x. apply (IHco (open_co_wrt_tm_rec 0 (a_Var_f x) g2)).
                 --- rewrite sz_co_open_tm_var; simpl in Hle; lia.
                 --- apply clt_co_open_tm_fwd_gen; [cbn; exact I | exact Ht2].
                 --- apply clc_co_open_tm_fwd_gen; [cbn; exact I | exact Hc2].
           ++ destruct Ht as [Ht1 Ht2]; destruct Hc as [Hc1 Hc2]. constructor.
              ** apply IHco; [simpl in *; lia | exact Ht1 | exact Hc1].
              ** intro x. apply (IHco (open_co_wrt_tm_rec 0 (a_Var_f x) g2)).
                 --- rewrite sz_co_open_tm_var; simpl in Hle; lia.
                 --- apply clt_co_open_tm_fwd_gen; [cbn; exact I | exact Ht2].
                 --- apply clc_co_open_tm_fwd_gen; [cbn; exact I | exact Hc2].
           ++ destruct Ht as [Ht1 Ht2]; destruct Hc as [Hc1 Hc2]. constructor;
                 [ apply IHco; [simpl in *; lia | exact Ht1 | exact Hc1]
                 | apply IHco; [simpl in *; lia | exact Ht2 | exact Hc2] ].
           ++ constructor; apply IHco; [simpl in *; lia | exact Ht | exact Hc].
           ++ constructor; apply IHco; [simpl in *; lia | exact Ht | exact Hc].
           ++ constructor; apply IHco; [simpl in *; lia | exact Ht | exact Hc].
           ++ destruct Ht as [Ht1 Ht2]; destruct Hc as [Hc1 Hc2]. constructor;
                 [ apply IHco; [simpl in *; lia | exact Ht1 | exact Hc1]
                 | apply IHco; [simpl in *; lia | exact Ht2 | exact Hc2] ].
           ++ destruct Ht as [Ht1 Ht3]; destruct Hc as [Hc1 Hc3]. constructor.
              ** apply IHco; [simpl in *; lia | exact Ht1 | exact Hc1].
              ** intro c. apply (IHco (open_co_wrt_co_rec 0 (g_Var_f c) g3)).
                 --- rewrite sz_co_open_co_var; simpl in Hle; lia.
                 --- apply clt_co_open_co_fwd_gen; [cbn; exact I | exact Ht3].
                 --- apply clc_co_open_co_fwd_sharp; [cbn; exact I | exact Hc3].
           ++ destruct Ht as [Ht1 [Ht3 Ht4]]; destruct Hc as [Hc1 [Hc3 Hc4]]. constructor.
              ** apply IHco; [simpl in *; lia | exact Ht1 | exact Hc1].
              ** intro c. apply (IHco (open_co_wrt_co_rec 0 (g_Var_f c) g3)).
                 --- rewrite sz_co_open_co_var; simpl in Hle; lia.
                 --- apply clt_co_open_co_fwd_gen; [cbn; exact I | exact Ht3].
                 --- apply clc_co_open_co_fwd_sharp; [cbn; exact I | exact Hc3].
              ** apply IHco; [simpl in *; lia | exact Ht4 | exact Hc4].
           ++ destruct Ht as [Ht0 [Ht1 Ht2]]; destruct Hc as [Hc0 [Hc1 Hc2]]. constructor;
                 [ apply IHco; [simpl in *; lia | exact Ht0 | exact Hc0]
                 | apply IHco; [simpl in *; lia | exact Ht1 | exact Hc1]
                 | apply IHco; [simpl in *; lia | exact Ht2 | exact Hc2] ].
           ++ destruct Ht as [Ht0 [Ht1 Ht2]]; destruct Hc as [Hc0 [Hc1 Hc2]]. constructor;
                 [ apply IHco; [simpl in *; lia | exact Ht0 | exact Hc0]
                 | apply IHco; [simpl in *; lia | exact Ht1 | exact Hc1]
                 | apply IHco; [simpl in *; lia | exact Ht2 | exact Hc2] ].
           ++ destruct Ht as [Ht1 Ht2]; destruct Hc as [Hc1 Hc2]. constructor;
                 [ apply IHco; [simpl in *; lia | exact Ht1 | exact Hc1]
                 | apply IHco; [simpl in *; lia | exact Ht2 | exact Hc2] ].
           ++ destruct Ht as [Ht1 [HtA Ht2]]; destruct Hc as [Hc1 [HcA Hc2]]. constructor;
                 [ apply IHco; [simpl in *; lia | exact Ht1 | exact Hc1]
                 | apply IHtm; [simpl in *; lia | exact HtA | exact HcA]
                 | apply IHco; [simpl in *; lia | exact Ht2 | exact Hc2] ].
           ++ destruct Ht as [Htp1 [Htp2 Htg]]; destruct Hc as [Hcp1 [Hcp2 Hcg]]. constructor;
                 [ apply IHcon; [simpl in *; lia | exact Htp1 | exact Hcp1]
                 | apply IHcon; [simpl in *; lia | exact Htp2 | exact Hcp2]
                 | apply IHco; [simpl in *; lia | exact Htg | exact Hcg] ].
           ++ constructor; apply IHtm; [simpl in *; lia | exact Ht | exact Hc].
           ++ destruct Ht as [Ht1 Ht2]; destruct Hc as [Hc1 Hc2]. constructor;
                 [ apply IHco; [simpl in *; lia | exact Ht1 | exact Hc1]
                 | apply IHco; [simpl in *; lia | exact Ht2 | exact Hc2] ].
           ++ destruct Ht as [Ht1 Ht2]; destruct Hc as [Hc1 Hc2]. constructor;
                 [ apply IHco; [simpl in *; lia | exact Ht1 | exact Hc1]
                 | apply IHco; [simpl in *; lia | exact Ht2 | exact Hc2] ].
        -- intros p Hle Ht Hc. destruct p as [a b A]; cbn [clt_constraint] in Ht; cbn [clc_constraint] in Hc; simpl in Hle.
           destruct Ht as [Hta [Htb HtA]]; destruct Hc as [Hca [Hcb HcA]].
           constructor;
             [ apply IHtm; [simpl in *; lia | exact Hta | exact Hca]
             | apply IHtm; [simpl in *; lia | exact Htb | exact Hcb]
             | apply IHtm; [simpl in *; lia | exact HtA | exact HcA] ].
Qed.


(* lc <-> both closedness predicates at level 0 *)
Lemma lc_tm_iff : forall a, lc_tm a <-> (clt_tm 0 a /\ clc_tm 0 a).
Proof.
  intros a; split.
  - intros H; split; [ apply lc_clt_tm | apply lc_clc_tm ]; exact H.
  - intros [H1 H2]. exact (proj1 (closed_lc_all (sz_tm a)) a (le_n _) H1 H2).
Qed.
Lemma lc_co_iff : forall g, lc_co g <-> (clt_co 0 g /\ clc_co 0 g).
Proof.
  intros g; split.
  - intros H; split; [ apply lc_clt_co | apply lc_clc_co ]; exact H.
  - intros [H1 H2]. exact (proj1 (proj2 (proj2 (closed_lc_all (sz_co g)))) g (le_n _) H1 H2).
Qed.
Lemma lc_brs_iff : forall b, lc_brs b <-> (clt_brs 0 b /\ clc_brs 0 b).
Proof.
  intros b; split.
  - intros H; split; [ apply lc_clt_brs | apply lc_clc_brs ]; exact H.
  - intros [H1 H2]. exact (proj1 (proj2 (closed_lc_all (sz_brs b))) b (le_n _) H1 H2).
Qed.
Lemma lc_constraint_iff : forall p, lc_constraint p <-> (clt_constraint 0 p /\ clc_constraint 0 p).
Proof.
  intros p; split.
  - intros H; split; [ apply lc_clt_constraint | apply lc_clc_constraint ]; exact H.
  - intros [H1 H2]. exact (proj2 (proj2 (proj2 (closed_lc_all (sz_constraint p)))) p (le_n _) H1 H2).
Qed.

Definition closed_to_lc_tm a (H1:clt_tm 0 a) (H2:clc_tm 0 a) : lc_tm a :=
  proj1 (closed_lc_all (sz_tm a)) a (le_n _) H1 H2.
Definition closed_to_lc_co g (H1:clt_co 0 g) (H2:clc_co 0 g) : lc_co g :=
  proj1 (proj2 (proj2 (closed_lc_all (sz_co g)))) g (le_n _) H1 H2.
Definition closed_to_lc_brs b (H1:clt_brs 0 b) (H2:clc_brs 0 b) : lc_brs b :=
  proj1 (proj2 (closed_lc_all (sz_brs b))) b (le_n _) H1 H2.
Definition closed_to_lc_constraint p (H1:clt_constraint 0 p) (H2:clc_constraint 0 p) : lc_constraint p :=
  proj2 (proj2 (proj2 (closed_lc_all (sz_constraint p)))) p (le_n _) H1 H2.

(* Opening locally closed objects with locally closed objects *)
Lemma lc_open_tm_tm : forall a u, lc_tm a -> lc_tm u -> lc_tm (open_tm_wrt_tm a u).
Proof.
  intros a u Ha Hu. unfold open_tm_wrt_tm.
  apply closed_to_lc_tm.
  - apply (clt_tm_open_tm_fwd_gen a 0 u);
      [ apply lc_clt_tm; exact Hu
      | apply lc_clt_tm in Ha; apply clt_tm_mono with (n:=0) (m:=1) in Ha; [exact Ha | lia] ].
  - apply (clc_tm_open_tm_fwd_gen a 0 0 u);
      [ apply lc_clc_tm; exact Hu | apply lc_clc_tm; exact Ha ].
Qed.

Lemma lc_open_tm_co : forall a g, lc_tm a -> lc_co g -> lc_tm (open_tm_wrt_co a g).
Proof.
  intros a g Ha Hg. unfold open_tm_wrt_co.
  apply closed_to_lc_tm.
  - apply (clt_tm_open_co_fwd_gen a 0 0 g);
      [ apply lc_clt_co; exact Hg | apply lc_clt_tm; exact Ha ].
  - apply (clc_tm_open_co_fwd_gen a 0 0 g);
      [ apply lc_clc_co; exact Hg | apply lc_clc_tm; exact Ha ].
Qed.

Lemma lc_open_co_co : forall h g, lc_co h -> lc_co g -> lc_co (open_co_wrt_co h g).
Proof.
  intros h g Hh Hg. unfold open_co_wrt_co.
  apply closed_to_lc_co.
  - apply (clt_co_open_co_fwd_gen h 0 0 g);
      [ apply lc_clt_co; exact Hg | apply lc_clt_co; exact Hh ].
  - apply (clc_co_open_co_fwd_gen h 0 0 g);
      [ apply lc_clc_co; exact Hg | apply lc_clc_co; exact Hh ].
Qed.

Lemma lc_open_co_tm : forall h u, lc_co h -> lc_tm u -> lc_co (open_co_wrt_tm h u).
Proof.
  intros h u Hh Hu. unfold open_co_wrt_tm.
  apply closed_to_lc_co.
  - apply (clt_co_open_tm_fwd_gen h 0 u);
      [ apply lc_clt_tm; exact Hu
      | apply lc_clt_co in Hh; apply clt_co_mono with (n:=0) (m:=1) in Hh; [exact Hh | lia] ].
  - apply (clc_co_open_tm_fwd_gen h 0 0 u);
      [ apply lc_clc_tm; exact Hu | apply lc_clc_co; exact Hh ].
Qed.

(* Opening invariance in the opening term *)
Lemma lc_open_tm_any : forall a u, lc_tm u -> lc_tm (open_tm_wrt_tm a u) ->
  forall x, lc_tm (open_tm_wrt_tm a (a_Var_f x)).
Proof.
  intros a u Hu Hopen x. unfold open_tm_wrt_tm in *.
  assert (Hclt : clt_tm 0 (open_tm_wrt_tm_rec 0 u a)) by (apply lc_clt_tm; exact Hopen).
  assert (Hclc : clc_tm 0 (open_tm_wrt_tm_rec 0 u a)) by (apply lc_clc_tm; exact Hopen).
  pose proof (clt_tm_open_tm_inv_gen a 0 u Hclt (lc_clt_tm u Hu)) as H1.
  pose proof (clc_tm_open_tm_inv_gen a 0 0 u Hclc (lc_clc_tm u Hu)) as H2.
  apply closed_to_lc_tm.
  - apply (clt_tm_open_tm_fwd_gen a 0 (a_Var_f x)); [cbn; exact I | exact H1].
  - apply (clc_tm_open_tm_fwd_gen a 0 0 (a_Var_f x)); [cbn; exact I | exact H2].
Qed.

Lemma lc_open_tm_co_any : forall a g, lc_co g -> lc_tm (open_tm_wrt_co a g) ->
  forall g', lc_co g' -> lc_tm (open_tm_wrt_co a g').
Proof.
  intros a g Hg Hopen g' Hg'. unfold open_tm_wrt_co in *.
  assert (Hclt : clt_tm 0 (open_tm_wrt_co_rec 0 g a)) by (apply lc_clt_tm; exact Hopen).
  assert (Hclc : clc_tm 0 (open_tm_wrt_co_rec 0 g a)) by (apply lc_clc_tm; exact Hopen).
  pose proof (clt_tm_open_co_inv_gen a 0 0 g Hclt (lc_clt_co g Hg)) as H1.
  pose proof (clc_tm_open_co_inv_gen a 0 g Hclc (lc_clc_co g Hg)) as H2.
  apply closed_to_lc_tm.
  - apply (clt_tm_open_co_fwd_gen a 0 0 g'); [apply lc_clt_co; exact Hg' | exact H1].
  - apply (clc_tm_open_co_fwd_sharp a 0 g'); [apply lc_clc_co; exact Hg' | exact H2].
Qed.

Lemma lc_open_co_tm_any : forall h u, lc_tm u -> lc_co (open_co_wrt_tm h u) ->
  forall x, lc_co (open_co_wrt_tm h (a_Var_f x)).
Proof.
  intros h u Hu Hopen x. unfold open_co_wrt_tm in *.
  assert (Hclt : clt_co 0 (open_co_wrt_tm_rec 0 u h)) by (apply lc_clt_co; exact Hopen).
  assert (Hclc : clc_co 0 (open_co_wrt_tm_rec 0 u h)) by (apply lc_clc_co; exact Hopen).
  pose proof (clt_co_open_tm_inv_gen h 0 u Hclt (lc_clt_tm u Hu)) as H1.
  pose proof (clc_co_open_tm_inv_gen h 0 0 u Hclc (lc_clc_tm u Hu)) as H2.
  apply closed_to_lc_co.
  - apply (clt_co_open_tm_fwd_gen h 0 (a_Var_f x)); [cbn; exact I | exact H1].
  - apply (clc_co_open_tm_fwd_gen h 0 0 (a_Var_f x)); [cbn; exact I | exact H2].
Qed.

Lemma lc_open_co_co_any : forall h g, lc_co g -> lc_co (open_co_wrt_co h g) ->
  forall g', lc_co g' -> lc_co (open_co_wrt_co h g').
Proof.
  intros h g Hg Hopen g' Hg'. unfold open_co_wrt_co in *.
  assert (Hclt : clt_co 0 (open_co_wrt_co_rec 0 g h)) by (apply lc_clt_co; exact Hopen).
  assert (Hclc : clc_co 0 (open_co_wrt_co_rec 0 g h)) by (apply lc_clc_co; exact Hopen).
  pose proof (clt_co_open_co_inv_gen h 0 0 g Hclt (lc_clt_co g Hg)) as H1.
  pose proof (clc_co_open_co_inv_gen h 0 g Hclc (lc_clc_co g Hg)) as H2.
  apply closed_to_lc_co.
  - apply (clt_co_open_co_fwd_gen h 0 0 g'); [apply lc_clt_co; exact Hg' | exact H1].
  - apply (clc_co_open_co_fwd_sharp h 0 g'); [apply lc_clc_co; exact Hg' | exact H2].
Qed.

(* ===================== Context predicates ===================== *)

Definition lc_sort (s:sort) : Prop :=
  match s with
  | Tm A => lc_tm A
  | Co p => lc_constraint p
  end.

Definition lc_context (G:context) : Prop :=
  Forall (fun p => lc_sort (snd p)) G.

Lemma lc_context_binds : forall G x s, lc_context G -> binds x s G -> lc_sort s.
Proof.
  intros G. induction G as [|[y t] G IH]; intros x s Hc Hb.
  - inversion Hb.
  - inversion Hc as [|? ? Ht HG]; subst.
    apply binds_cons_iff in Hb. destruct Hb as [[Heq Hsat]|Hb].
    + inversion Heq; inversion Hsat; subst; exact Ht.
    + eapply IH; eauto.
Qed.

Lemma lc_context_binds_tm : forall G x A,
  lc_context G -> binds x (Tm A) G -> lc_tm A.
Proof.
  intros G x A H Hb. pose proof (@lc_context_binds G x (Tm A) H Hb) as H1.
  cbn [lc_sort] in H1. exact H1.
Qed.

Lemma lc_context_binds_co : forall G c a b A,
  lc_context G -> binds c (Co (Eq a b A)) G -> lc_tm a /\ lc_tm b.
Proof.
  intros G c a b A H Hb. pose proof (@lc_context_binds G c (Co (Eq a b A)) H Hb) as H1.
  cbn [lc_sort] in H1. inversion H1; auto.
Qed.

(* ===================== Inversion helpers ===================== *)

Lemma lc_tm_pi_inv : forall rho A B, lc_tm (a_Pi rho A B) ->
  lc_tm A /\ (forall x, lc_tm (open_tm_wrt_tm B (a_Var_f x))).
Proof. intros. inversion H. auto. Qed.

Lemma lc_tm_abs_inv : forall rho A b, lc_tm (a_Abs rho A b) ->
  lc_tm A /\ (forall x, lc_tm (open_tm_wrt_tm b (a_Var_f x))).
Proof. intros. inversion H. auto. Qed.

Lemma lc_tm_uabs_inv : forall rho b, lc_tm (a_UAbs rho b) ->
  (forall x, lc_tm (open_tm_wrt_tm b (a_Var_f x))).
Proof. intros. inversion H. auto. Qed.

Lemma lc_tm_conv_inv : forall a g, lc_tm (a_Conv a g) -> lc_tm a /\ lc_co g.
Proof. intros. inversion H. auto. Qed.

Lemma lc_tm_cpi_inv : forall phi B, lc_tm (a_CPi phi B) ->
  lc_constraint phi /\ (forall c, lc_tm (open_tm_wrt_co B (g_Var_f c))).
Proof. intros. inversion H. auto. Qed.

Lemma lc_tm_cabs_inv : forall phi b, lc_tm (a_CAbs phi b) ->
  lc_constraint phi /\ (forall c, lc_tm (open_tm_wrt_co b (g_Var_f c))).
Proof. intros. inversion H. auto. Qed.

Lemma lc_tm_ucabs_inv : forall b, lc_tm (a_UCAbs b) ->
  (forall c, lc_tm (open_tm_wrt_co b (g_Var_f c))).
Proof. intros. inversion H. auto. Qed.

Lemma lc_tm_app_inv : forall a rho b, lc_tm (a_App a rho b) -> lc_tm a /\ lc_tm b.
Proof. intros. inversion H. auto. Qed.

Lemma lc_tm_capp_inv : forall a g, lc_tm (a_CApp a g) -> lc_tm a /\ lc_co g.
Proof. intros. inversion H. auto. Qed.

Lemma lc_constraint_eq_1 : forall a b A, lc_constraint (Eq a b A) -> lc_tm a.
Proof. intros. inversion H. auto. Qed.
Lemma lc_constraint_eq_2 : forall a b A, lc_constraint (Eq a b A) -> lc_tm b.
Proof. intros. inversion H. auto. Qed.
Lemma lc_constraint_eq_3 : forall a b A, lc_constraint (Eq a b A) -> lc_tm A.
Proof. intros. inversion H. auto. Qed.

(* ===================== Opening bodies with arbitrary lc arguments ==== *)

Lemma lc_open_body_pi : forall rho A B, lc_tm (a_Pi rho A B) ->
  forall u, lc_tm u -> lc_tm (open_tm_wrt_tm B u).
Proof.
  intros rho A B Hp u Hu. unfold open_tm_wrt_tm.
  apply closed_to_lc_tm.
  - assert (Hc : clt_tm 0 (a_Pi rho A B)) by (apply lc_clt_tm; exact Hp).
    cbn [clt_tm] in Hc. destruct Hc as [_ HcB].
    apply (clt_tm_open_tm_fwd_gen B 0 u); [apply lc_clt_tm; exact Hu | exact HcB].
  - assert (Hc : clc_tm 0 (a_Pi rho A B)) by (apply lc_clc_tm; exact Hp).
    cbn [clc_tm] in Hc. destruct Hc as [_ HcB].
    apply (clc_tm_open_tm_fwd_gen B 0 0 u); [apply lc_clc_tm; exact Hu | exact HcB].
Qed.

Lemma lc_open_body_abs : forall rho A b, lc_tm (a_Abs rho A b) ->
  forall u, lc_tm u -> lc_tm (open_tm_wrt_tm b u).
Proof.
  intros rho A b Hp u Hu. unfold open_tm_wrt_tm.
  apply closed_to_lc_tm.
  - assert (Hc : clt_tm 0 (a_Abs rho A b)) by (apply lc_clt_tm; exact Hp).
    cbn [clt_tm] in Hc. destruct Hc as [_ HcB].
    apply (clt_tm_open_tm_fwd_gen b 0 u); [apply lc_clt_tm; exact Hu | exact HcB].
  - assert (Hc : clc_tm 0 (a_Abs rho A b)) by (apply lc_clc_tm; exact Hp).
    cbn [clc_tm] in Hc. destruct Hc as [_ HcB].
    apply (clc_tm_open_tm_fwd_gen b 0 0 u); [apply lc_clc_tm; exact Hu | exact HcB].
Qed.

Lemma lc_open_body_uabs : forall rho b, lc_tm (a_UAbs rho b) ->
  forall u, lc_tm u -> lc_tm (open_tm_wrt_tm b u).
Proof.
  intros rho b Hp u Hu. unfold open_tm_wrt_tm.
  apply closed_to_lc_tm.
  - assert (Hc : clt_tm 0 (a_UAbs rho b)) by (apply lc_clt_tm; exact Hp).
    cbn [clt_tm] in Hc.
    apply (clt_tm_open_tm_fwd_gen b 0 u); [apply lc_clt_tm; exact Hu | exact Hc].
  - assert (Hc : clc_tm 0 (a_UAbs rho b)) by (apply lc_clc_tm; exact Hp).
    cbn [clc_tm] in Hc.
    apply (clc_tm_open_tm_fwd_gen b 0 0 u); [apply lc_clc_tm; exact Hu | exact Hc].
Qed.

Lemma lc_open_body_cpi : forall phi B, lc_tm (a_CPi phi B) ->
  forall g, lc_co g -> lc_tm (open_tm_wrt_co B g).
Proof.
  intros phi B Hp g Hg. unfold open_tm_wrt_co.
  apply closed_to_lc_tm.
  - assert (Hc : clt_tm 0 (a_CPi phi B)) by (apply lc_clt_tm; exact Hp).
    cbn [clt_tm] in Hc. destruct Hc as [_ HcB].
    apply (clt_tm_open_co_fwd_gen B 0 0 g); [apply lc_clt_co; exact Hg | exact HcB].
  - assert (Hc : clc_tm 0 (a_CPi phi B)) by (apply lc_clc_tm; exact Hp).
    cbn [clc_tm] in Hc. destruct Hc as [_ HcB].
    apply (clc_tm_open_co_fwd_sharp B 0 g); [apply lc_clc_co; exact Hg | exact HcB].
Qed.

Lemma lc_open_body_cabs : forall phi b, lc_tm (a_CAbs phi b) ->
  forall g, lc_co g -> lc_tm (open_tm_wrt_co b g).
Proof.
  intros phi b Hp g Hg. unfold open_tm_wrt_co.
  apply closed_to_lc_tm.
  - assert (Hc : clt_tm 0 (a_CAbs phi b)) by (apply lc_clt_tm; exact Hp).
    cbn [clt_tm] in Hc. destruct Hc as [_ HcB].
    apply (clt_tm_open_co_fwd_gen b 0 0 g); [apply lc_clt_co; exact Hg | exact HcB].
  - assert (Hc : clc_tm 0 (a_CAbs phi b)) by (apply lc_clc_tm; exact Hp).
    cbn [clc_tm] in Hc. destruct Hc as [_ HcB].
    apply (clc_tm_open_co_fwd_sharp b 0 g); [apply lc_clc_co; exact Hg | exact HcB].
Qed.

Lemma lc_open_body_ucabs : forall b, lc_tm (a_UCAbs b) ->
  forall g, lc_co g -> lc_tm (open_tm_wrt_co b g).
Proof.
  intros b Hp g Hg. unfold open_tm_wrt_co.
  apply closed_to_lc_tm.
  - assert (Hc : clt_tm 0 (a_UCAbs b)) by (apply lc_clt_tm; exact Hp).
    cbn [clt_tm] in Hc.
    apply (clt_tm_open_co_fwd_gen b 0 0 g); [apply lc_clt_co; exact Hg | exact Hc].
  - assert (Hc : clc_tm 0 (a_UCAbs b)) by (apply lc_clc_tm; exact Hp).
    cbn [clc_tm] in Hc.
    apply (clc_tm_open_co_fwd_sharp b 0 g); [apply lc_clc_co; exact Hg | exact Hc].
Qed.

(* ===================== Main mutual well-formedness theorem ===================== *)

Ltac fresh_notin L B :=
  let x := fresh "x0" in
  destruct (atom_fresh (L \u B)) as [x ?Hx];
  let HxL := fresh "HxL" in
  assert (HxL : x \notin L) by (apply notin_union_1 in Hx; exact Hx);
  let HxB := fresh "HxB" in
  assert (HxB : x \notin B) by (apply notin_union_2 in Hx; exact Hx).

Scheme AnnTyping_indA := Induction for AnnTyping Sort Prop
  with AnnPropWff_indA := Induction for AnnPropWff Sort Prop
  with AnnIso_indA := Induction for AnnIso Sort Prop
  with AnnDefEq_indA := Induction for AnnDefEq Sort Prop
  with AnnCtx_indA := Induction for AnnCtx Sort Prop
  with AnnSig_indA := Induction for AnnSig Sort Prop.
Combined Scheme AnnTyping_comb from AnnTyping_indA, AnnPropWff_indA, AnnIso_indA, AnnDefEq_indA, AnnCtx_indA, AnnSig_indA.

Lemma Ann_wf_all :
  (forall G a A (H:AnnTyping G a A), lc_tm a /\ lc_tm A) /\
  (forall G p (H:AnnPropWff G p), lc_constraint p) /\
  (forall G D g p q (H:AnnIso G D g p q), lc_co g /\ lc_constraint p /\ lc_constraint q) /\
  (forall G D g a b (H:AnnDefEq G D g a b), lc_co g /\ lc_tm a /\ lc_tm b) /\
  (forall G (H:AnnCtx G), (forall x s, binds x s G -> lc_sort s) /\ uniq G) /\
  (forall S (H:AnnSig S), True).
Proof.
  apply (AnnTyping_comb
    (fun G a A _ => lc_tm a /\ lc_tm A)
    (fun G p _ => lc_constraint p)
    (fun G D g p q _ => lc_co g /\ lc_constraint p /\ lc_constraint q)
    (fun G D g a b _ => lc_co g /\ lc_tm a /\ lc_tm b)
    (fun G _ => (forall x s, binds x s G -> lc_sort s) /\ uniq G)
    (fun S _ => True)).
  (* An_Star *)
  - intros G a IHctx. split; constructor.
  (* An_Var *)
  - intros G x A a IHctx b. destruct IHctx as [Hctx Huniq].
    split; [constructor | exact (Hctx x (Tm A) b)].
  (* An_Pi *)
  - intros L G rho A B body IHbody a0 IH0. split.
    + constructor.
      * exact (proj1 IH0).
      * intro y.
        fresh_notin L (fv_tm_tm_tm B);
        edestruct (IHbody x0 HxL) as [Hlc _];
        exact (@lc_open_tm_any B (a_Var_f x0) ltac:(constructor) Hlc y).
    + constructor.
  (* An_Abs *)
  - intros L G rho A a B a0 IH0 a1 IH1 r. split.
    + constructor.
      * exact (proj1 IH0).
      * intro y.
        fresh_notin L (fv_tm_tm_tm a);
        edestruct (IH1 x0 HxL) as [Hlc _];
        exact (@lc_open_tm_any a (a_Var_f x0) ltac:(constructor) Hlc y).
    + constructor.
      * exact (proj1 IH0).
      * intro y.
        fresh_notin L (fv_tm_tm_tm B);
        edestruct (IH1 x0 HxL) as [_ Hlc];
        exact (@lc_open_tm_any B (a_Var_f x0) ltac:(constructor) Hlc y).
  (* An_App *)
  - intros G b rho a B A a0 IH0 a1 IH1. split.
    + constructor; [exact (proj1 IH0) | exact (proj1 IH1)].
    + exact (lc_open_body_pi rho A B (proj2 IH0) a (proj1 IH1)).
  (* An_Conv *)
  - intros G a g B A a0 IH0 a1 IHdef a2 IH2. split.
    + constructor; [exact (proj1 IH0) | exact (proj1 IHdef)].
    + exact (proj1 IH2).
  (* An_CPi *)
  - intros L G phi B a IHprop a0 IHbody. split.
    + constructor.
      * exact IHprop.
      * intro y.
        fresh_notin L (fv_tm_tm_tm B);
        edestruct (IHbody x0 HxL) as [Hlc _];
        exact (@lc_open_tm_co_any B (g_Var_f x0) ltac:(constructor) Hlc (g_Var_f y) ltac:(constructor)).
    + constructor.
  (* An_CAbs *)
  - intros L G phi a B a0 IHprop a1 IHbody. split.
    + constructor.
      * exact IHprop.
      * intro y.
        fresh_notin L (fv_tm_tm_tm a);
        edestruct (IHbody x0 HxL) as [Hlc _];
        exact (@lc_open_tm_co_any a (g_Var_f x0) ltac:(constructor) Hlc (g_Var_f y) ltac:(constructor)).
    + constructor.
      * exact IHprop.
      * intro y.
        fresh_notin L (fv_tm_tm_tm B);
        edestruct (IHbody x0 HxL) as [_ Hlc];
        exact (@lc_open_tm_co_any B (g_Var_f x0) ltac:(constructor) Hlc (g_Var_f y) ltac:(constructor)).
  (* An_CApp *)
  - intros G a1 g B a b A1 a0 IH0 a1' IHdef. split.
    + constructor; [exact (proj1 IH0) | exact (proj1 IHdef)].
    + exact (lc_open_body_cpi (Eq a b A1) B (proj2 IH0) g (proj1 IHdef)).
  (* An_Fam *)
  - intros G F A a ctx IHctx b a1 IH1. split; [constructor| exact (proj1 IH1)].
  (* An_Wff *)
  - intros G a b A B a0 IH0 a1 IH1 Heq. constructor;
      [exact (proj1 IH0) | exact (proj1 IH1) | exact (proj2 IH0)].
  (* An_PropCong *)
  - intros G D g1 A g2 A1 B1 A2 B2 a0 IH0 a1 IH1 a2 IH2 a3 IH3.
    split; [|split].
    + constructor; [exact (proj1 IH0) | | exact (proj1 IH1)].
      exact (lc_constraint_eq_3 _ _ _ IH2).
    + exact IH2.
    + exact IH3.
  (* An_CPiFst *)
  - intros G D g phi1 phi2 A2 B2 a0 IH0. split; [|split].
    + constructor; exact (proj1 IH0).
    + exact (proj1 (lc_tm_cpi_inv _ _ (proj1 (proj2 IH0)))).
    + exact (proj1 (lc_tm_cpi_inv _ _ (proj2 (proj2 IH0)))).
  (* An_IsoSym *)
  - intros G D g phi2 phi1 a0 IH0. destruct IH0 as [Hg [Hp Hq]]. split; [|split].
    + constructor; exact Hg.
    + exact Hq.
    + exact Hp.
  (* An_IsoConv *)
  - intros G D a1 a2 A a1' a2' B g a0 IH0 a1'' IH1 a2'' IH2 Heq1 Heq2.
    split; [|split].
    + constructor; [exact IH1 | exact IH2 | exact (proj1 IH0)].
    + exact IH1.
    + exact IH2.
  (* An_Assn *)
  - intros G D c a b A a0 IHctx b0 Hin. destruct IHctx as [Hctx Huniq].
    split; [|split].
    + constructor.
    + pose proof (Hctx c (Co (Eq a b A)) b0) as H1; cbn [lc_sort] in H1.
      exact (lc_constraint_eq_1 a b A H1).
    + pose proof (Hctx c (Co (Eq a b A)) b0) as H1; cbn [lc_sort] in H1.
      exact (lc_constraint_eq_2 a b A H1).
  (* An_Refl *)
  - intros G D a A a0 IH0. split; [|split].
    + constructor; exact (proj1 IH0).
    + exact (proj1 IH0).
    + exact (proj1 IH0).
  (* An_EraseEq *)
  - intros G D a b g A B a0 IH0 a1 IH1 Heq a2 IH2. split; [|split].
    + constructor; [exact (proj1 IH0) | exact (proj1 IH1) | exact (proj1 IH2)].
    + exact (proj1 IH0).
    + exact (proj1 IH1).
  (* An_Sym *)
  - intros G D g a b B A g1 a0 IH0 a1 IH1 a2 IH2 a3 IH3. split; [|split].
    + constructor; exact (proj1 IH3).
    + exact (proj1 IH1).
    + exact (proj1 IH0).
  (* An_Trans *)
  - intros G D g1 g2 a b a1 A A1 g3 a0 IH0 a1' IH1 a2 IH2 a3 IH3 a4 IH4.
    split; [|split].
    + constructor; [exact (proj1 IH0) | exact (proj1 IH1)].
    + exact (proj1 (proj2 IH0)).
    + exact (proj2 (proj2 IH1)).
  (* An_Beta *)
  - intros G D a1 a2 B0 B1 a0 IH0 a1' IH1 Heq HB. split; [|split].
    + constructor; [exact (proj1 IH0) | exact (proj1 IH1)].
    + exact (proj1 IH0).
    + exact (proj1 IH1).
  (* An_PiCong *)
  - intros L G D rho g1 g2 A1 B1 A2 B3 B2 a0 IH0 a1 IH1 Heq a3 IH3 a4 IH4 a5 IH5.
    split; [|split].
    + constructor.
      * exact (proj1 IH0).
      * intro y.
        fresh_notin L (fv_tm_tm_co g2);
        edestruct (IH1 x0 HxL) as [Hlc _];
        exact (@lc_open_co_tm_any g2 (a_Var_f x0) ltac:(constructor) Hlc y).
    + exact (proj1 IH3).
    + exact (proj1 IH5).
  (* An_AbsCong *)
  - intros L G D rho g1 g2 A1 b1 A2 b3 b2 B a0 IH0 a1 IH1 Heq a3 IH3 a4 IH4 a5 a6 a7 IH7.
    split; [|split].
    + constructor.
      * exact (proj1 IH0).
      * intro y.
        fresh_notin L (fv_tm_tm_co g2);
        edestruct (IH1 x0 HxL) as [Hlc _];
        exact (@lc_open_co_tm_any g2 (a_Var_f x0) ltac:(constructor) Hlc y).
    + (* lc (a_Abs rho A1 b1) *)
      constructor.
      * exact (proj1 IH3).
      * intro y.
        fresh_notin L (fv_tm_tm_tm b1);
        edestruct (IH1 x0 HxL) as [_ [Hlc _]];
        exact (@lc_open_tm_any b1 (a_Var_f x0) ltac:(constructor) Hlc y).
    + (* lc (a_Abs rho A2 b3) *)
      constructor.
      * exact (proj1 IH4).
      * intro y.
        fresh_notin L (fv_tm_tm_tm b3 \u fv_tm_tm_tm b2);
        pose proof (Heq x0 HxL) as Hbx.
        assert (Hopen : lc_tm (open_tm_wrt_tm b3 (a_Var_f x0))).
        { rewrite Hbx.
          apply (lc_open_body_abs rho A1 b2 (proj1 IH7) (a_Conv (a_Var_f x0) (g_Sym g1))).
          constructor; [constructor | constructor; exact (proj1 IH0)]. }
        exact (@lc_open_tm_any b3 (a_Var_f x0) ltac:(constructor) Hopen y).
  (* An_AppCong *)
  - intros G D g1 rho g2 ta1 ta2 tb1 tb2 A B g3 a0 IH0 a1' IH1 a2 IH2 a3 IH3 a4 IH4.
    split; [|split].
    + constructor; [exact (proj1 IH0) | exact (proj1 IH1)].
    + exact (proj1 IH2).
    + exact (proj1 IH3).
  (* An_PiFst *)
  - intros G D g A1 A2 rho B1 B2 a0 IH0. split; [|split].
    + constructor; exact (proj1 IH0).
    + exact (proj1 (lc_tm_pi_inv _ _ _ (proj1 (proj2 IH0)))).
    + exact (proj1 (lc_tm_pi_inv _ _ _ (proj2 (proj2 IH0)))).
  (* An_PiSnd *)
  - intros G D g1 g2 B1 a1 B2 a2 rho A1 A2 a0 IH0 a1' IH1 a2' IH2 a3 IH3. split; [|split].
    + constructor; [exact (proj1 IH0) | exact (proj1 IH1)].
    + exact (lc_open_body_pi rho A1 B1 (proj1 (proj2 IH0)) a1 (proj1 (proj2 IH1))).
    + exact (lc_open_body_pi rho A2 B2 (proj2 (proj2 IH0)) a2 (proj2 (proj2 IH1))).
  (* An_CPiCong *)
  - intros L G D g1 g3 phi1 B1 phi2 B3 B2 a0 IH0 a1 IH1 Heq a3 IH3 a4 IH4 a5 IH5.
    split; [|split].
    + constructor.
      * exact (proj1 IH0).
      * intro y.
        fresh_notin L (fv_tm_tm_co g3);
        edestruct (IH1 x0 HxL) as [Hlc _];
        exact (@lc_open_co_co_any g3 (g_Var_f x0) ltac:(constructor) Hlc (g_Var_f y) ltac:(constructor)).
    + exact (proj1 IH3).
    + exact (proj1 IH4).
  (* An_CAbsCong *)
  - intros L G D g1 g3 g4 phi1 a1 phi2 a3 a2 B1 B B2 a0 IH0 a1' IH1 Heq a3' IH3 a4 IH4 a5 IH5 a6 IH6.
    split; [|split].
    + constructor.
      * exact (proj1 IH0).
      * intro y.
        fresh_notin L (fv_tm_tm_co g3);
        edestruct (IH1 x0 HxL) as [Hlc _];
        exact (@lc_open_co_co_any g3 (g_Var_f x0) ltac:(constructor) Hlc (g_Var_f y) ltac:(constructor)).
      * exact (proj1 IH6).
    + exact (proj1 IH3).
    + exact (proj1 IH5).
  (* An_CAppCong *)
  - intros G D g1 g2 g3 a1 b1 a2 b2 a3 b3 A B g4 a0 IH0 a1' IH1 a2' IH2 a3' IH3 a4 IH4 a5 IH5.
    split; [|split].
    + constructor; [exact (proj1 IH0) | exact (proj1 IH1) | exact (proj1 IH2)].
    + exact (proj1 IH3).
    + exact (proj1 IH4).
  (* An_CPiSnd *)
  - intros G D g1 g2 g3 B1 B2 a a' A b b' B a0 IH0 a1 IH1 a2 IH2. split; [|split].
    + constructor; [exact (proj1 IH0) | exact (proj1 IH1) | exact (proj1 IH2)].
    + exact (lc_open_body_cpi (Eq a a' A) B1 (proj1 (proj2 IH0)) g2 (proj1 IH1)).
    + exact (lc_open_body_cpi (Eq b b' B) B2 (proj2 (proj2 IH0)) g3 (proj1 IH2)).
  (* An_Cast *)
  - intros G D g1 g2 b b' a a' A B a0 IH0 a1 IH1. split; [|split].
    + constructor; [exact (proj1 IH0) | exact (proj1 IH1)].
    + exact (lc_constraint_eq_1 _ _ _ (proj2 (proj2 IH1))).
    + exact (lc_constraint_eq_2 _ _ _ (proj2 (proj2 IH1))).
  (* An_IsoSnd *)
  - intros G D g A B a a' b b' a0 IH0. split; [|split].
    + constructor; exact (proj1 IH0).
    + exact (lc_constraint_eq_3 _ _ _ (proj1 (proj2 IH0))).
    + exact (lc_constraint_eq_3 _ _ _ (proj2 (proj2 IH0))).
  (* An_Empty *)
  - split.
    + intros x s Hb. inversion Hb.
    + apply uniq_nil.
  (* An_ConsTm *)
  - intros G x A a IHctx a0 IH0 Hnotin. destruct IHctx as [Hctx Huniq]. split.
    + intros y s Hb. apply binds_cons_iff in Hb.
      destruct Hb as [[Heq Hsat]|Hb].
      * subst. cbn [lc_sort]. exact (proj1 IH0).
      * exact (Hctx y s Hb).
    + apply uniq_push; [exact Huniq | exact Hnotin].
  (* An_ConsCo *)
  - intros G c phi a IHctx a0 IH0 Hnotin. destruct IHctx as [Hctx Huniq]. split.
    + intros y s Hb. apply binds_cons_iff in Hb.
      destruct Hb as [[Heq Hsat]|Hb].
      * subst. cbn [lc_sort]. exact IH0.
      * exact (Hctx y s Hb).
    + apply uniq_push; [exact Huniq | exact Hnotin].
  (* An_Sig_Empty *)
  - exact I.
  (* An_Sig_ConsAx *)
  - intros; exact I.
Qed.

(* ===================== Projections / requested lemmas ===================== *)

Definition AnnTyping_wf : forall G a A, AnnTyping G a A -> lc_tm a /\ lc_tm A :=
  fun G a A H => (proj1 Ann_wf_all) G a A H.

Definition AnnPropWff_wf : forall G p, AnnPropWff G p -> lc_constraint p :=
  fun G p H => (proj1 (proj2 Ann_wf_all)) G p H.

Definition AnnIso_wf : forall G D g p q,
  AnnIso G D g p q -> lc_co g /\ lc_constraint p /\ lc_constraint q :=
  fun G D g p q H => (proj1 (proj2 (proj2 Ann_wf_all))) G D g p q H.

Definition AnnDefEq_wf : forall G D g a b,
  AnnDefEq G D g a b -> lc_co g /\ lc_tm a /\ lc_tm b :=
  fun G D g a b H => (proj1 (proj2 (proj2 (proj2 Ann_wf_all)))) G D g a b H.

Definition AnnCtx_binds_wf : forall G x s, AnnCtx G -> binds x s G -> lc_sort s :=
  fun G x s Hctx Hb =>
    proj1 ((proj1 (proj2 (proj2 (proj2 (proj2 Ann_wf_all))))) G Hctx) x s Hb.

Definition AnnCtx_uniq : forall G, AnnCtx G -> uniq G :=
  fun G H => proj2 ((proj1 (proj2 (proj2 (proj2 (proj2 Ann_wf_all))))) G H).

Lemma AnnCtx_lc_context : forall G, AnnCtx G -> lc_context G.
Proof.
  intros G H. unfold lc_context. apply Forall_forall.
  intros [x s] Hin. exact (AnnCtx_binds_wf G x s H Hin).
Qed.

Lemma AnnCtx_binds_Tm_lc : forall G x A, AnnCtx G -> binds x (Tm A) G -> lc_tm A.
Proof.
  intros G x A Hctx Hb. pose proof (@AnnCtx_binds_wf G x (Tm A) Hctx Hb) as H1.
  cbn [lc_sort] in H1. exact H1.
Qed.

Lemma AnnCtx_binds_Co_lc : forall G x p, AnnCtx G -> binds x (Co p) G -> lc_constraint p.
Proof.
  intros G x p Hctx Hb. pose proof (@AnnCtx_binds_wf G x (Co p) Hctx Hb) as H1.
  cbn [lc_sort] in H1. exact H1.
Qed.
Import ListNotations.

(** * Mutual induction principles for AnnDefEq / AnnIso *)
Scheme AnnDefEq_ind2 := Induction for AnnDefEq Sort Prop
with AnnIso_ind2 := Induction for AnnIso Sort Prop.

(** * Atom-collecting functions (free term and coercion variables alike) *)

Fixpoint fatm_tm (a:tm) : atoms :=
  match a with
  | a_Star => {}
  | a_Var_b _ => {}
  | a_Var_f x => {{x}}
  | a_Abs _ A b => fatm_tm A \u fatm_tm b
  | a_UAbs _ b => fatm_tm b
  | a_App a _ b => fatm_tm a \u fatm_tm b
  | a_Fam _ => {}
  | a_Const _ => {}
  | a_Pi _ A B => fatm_tm A \u fatm_tm B
  | a_Conv a g => fatm_tm a \u fatm_co g
  | a_CPi phi B => fatm_constraint phi \u fatm_tm B
  | a_CAbs phi b => fatm_constraint phi \u fatm_tm b
  | a_UCAbs b => fatm_tm b
  | a_CApp a g => fatm_tm a \u fatm_co g
  | a_Bullet => {}
  | a_DataCon _ => {}
  | a_Case a br => fatm_tm a \u fatm_brs br
  end
with fatm_brs (b:brs) : atoms :=
  match b with
  | br_None => {}
  | br_One _ a r => fatm_tm a \u fatm_brs r
  end
with fatm_co (g:co) : atoms :=
  match g with
  | g_Triv => {}
  | g_Var_b _ => {}
  | g_Var_f c => {{c}}
  | g_Beta a b => fatm_tm a \u fatm_tm b
  | g_Refl a => fatm_tm a
  | g_Refl2 a b g' => fatm_tm a \u fatm_tm b \u fatm_co g'
  | g_Sym g' => fatm_co g'
  | g_Trans g1 g2 => fatm_co g1 \u fatm_co g2
  | g_PiCong _ g1 g2 => fatm_co g1 \u fatm_co g2
  | g_AbsCong _ g1 g2 => fatm_co g1 \u fatm_co g2
  | g_AppCong g1 _ g2 => fatm_co g1 \u fatm_co g2
  | g_PiFst g' => fatm_co g'
  | g_CPiFst g' => fatm_co g'
  | g_IsoSnd g' => fatm_co g'
  | g_PiSnd g1 g2 => fatm_co g1 \u fatm_co g2
  | g_CPiCong g1 g3 => fatm_co g1 \u fatm_co g3
  | g_CAbsCong g1 g3 g4 => fatm_co g1 \u fatm_co g3 \u fatm_co g4
  | g_CAppCong g g1 g2 => fatm_co g \u fatm_co g1 \u fatm_co g2
  | g_CPiSnd g g1 g2 => fatm_co g \u fatm_co g1 \u fatm_co g2
  | g_Cast g1 g2 => fatm_co g1 \u fatm_co g2
  | g_EqCong g1 A g2 => fatm_co g1 \u fatm_tm A \u fatm_co g2
  | g_IsoConv phi1 phi2 g' => fatm_constraint phi1 \u fatm_constraint phi2 \u fatm_co g'
  | g_Eta a => fatm_tm a
  | g_Left g g' => fatm_co g \u fatm_co g'
  | g_Right g g' => fatm_co g \u fatm_co g'
  end
with fatm_constraint (p:constraint) : atoms :=
  match p with
  | Eq a b A => fatm_tm a \u fatm_tm b \u fatm_tm A
  end.

(** * Injectivity of opening with a fresh coercion variable *)

Lemma open_tm_co_inj :
  (forall a k c, c `notin` fatm_tm a ->
     forall bb, c `notin` fatm_tm bb ->
       open_tm_wrt_co_rec k (g_Var_f c) a = open_tm_wrt_co_rec k (g_Var_f c) bb -> a = bb)
  /\ (forall a k c, c `notin` fatm_brs a ->
     forall bb, c `notin` fatm_brs bb ->
       open_brs_wrt_co_rec k (g_Var_f c) a = open_brs_wrt_co_rec k (g_Var_f c) bb -> a = bb)
  /\ (forall a k c, c `notin` fatm_co a ->
     forall bb, c `notin` fatm_co bb ->
       open_co_wrt_co_rec k (g_Var_f c) a = open_co_wrt_co_rec k (g_Var_f c) bb -> a = bb)
  /\ (forall a k c, c `notin` fatm_constraint a ->
     forall bb, c `notin` fatm_constraint bb ->
       open_constraint_wrt_co_rec k (g_Var_f c) a = open_constraint_wrt_co_rec k (g_Var_f c) bb -> a = bb).
Proof.
  apply (tm_mutind
    (fun a => forall k c, c `notin` fatm_tm a ->
       forall bb, c `notin` fatm_tm bb ->
         open_tm_wrt_co_rec k (g_Var_f c) a = open_tm_wrt_co_rec k (g_Var_f c) bb -> a = bb)
    (fun a => forall k c, c `notin` fatm_brs a ->
       forall bb, c `notin` fatm_brs bb ->
         open_brs_wrt_co_rec k (g_Var_f c) a = open_brs_wrt_co_rec k (g_Var_f c) bb -> a = bb)
    (fun a => forall k c, c `notin` fatm_co a ->
       forall bb, c `notin` fatm_co bb ->
         open_co_wrt_co_rec k (g_Var_f c) a = open_co_wrt_co_rec k (g_Var_f c) bb -> a = bb)
    (fun a => forall k c, c `notin` fatm_constraint a ->
       forall bb, c `notin` fatm_constraint bb ->
         open_constraint_wrt_co_rec k (g_Var_f c) a = open_constraint_wrt_co_rec k (g_Var_f c) bb -> a = bb)).
  all: intros.
  all: try (repeat match goal with
    | IH : forall (k0:nat) (c0:covar), _ |- _ =>
        pose proof (IH k c); pose proof (IH (S k) c); clear IH
    end).
  all: try (destruct bb; cbn [open_tm_wrt_co_rec open_brs_wrt_co_rec open_co_wrt_co_rec
        open_constraint_wrt_co_rec fatm_tm fatm_brs fatm_co fatm_constraint] in *;
        try discriminate).
  all: try (repeat match goal with
    | H : context [lt_eq_lt_dec ?a ?b] |- _ =>
        destruct (lt_eq_lt_dec a b) as [[?|?]|?]; cbn in *
    | |- context [lt_eq_lt_dec ?a ?b] =>
        destruct (lt_eq_lt_dec a b) as [[?|?]|?]; cbn
    end).
  all: try discriminate.
  all: try (repeat match goal with
    | H : _ `notin` (_ \u _) |- _ => apply notin_union_elim in H; destruct H
    end).
  all: try (match goal with
    | H : ?l = ?r |- _ =>
        lazymatch l with
        | context [open_tm_wrt_co_rec] => injection H; intros
        | context [open_brs_wrt_co_rec] => injection H; intros
        | context [open_co_wrt_co_rec] => injection H; intros
        | context [open_constraint_wrt_co_rec] => injection H; intros
        | g_Var_b _ => injection H; intros
        | g_Var_f _ => injection H; intros
        | _ => fail 1
        end
    end).
  all: try reflexivity.
  all: try assumption.
  all: try (f_equal; eauto 100).
  all: try eauto 100.
  all: try (f_equal; lia).
  all: try lia.
  all: try discriminate.
  all: try (exfalso; eauto using notin_singleton_1).
Qed.

(** * AnnCtx gives uniqueness *)

Definition Pdef (G:context) (D:available_props) (g:co) (a b:tm) (_:AnnDefEq G D g a b) : Prop :=
  forall a2 b2, AnnDefEq G D g a2 b2 -> a = a2 /\ b = b2.

Definition Piso (G:context) (D:available_props) (g:co) (p q:constraint) (_:AnnIso G D g p q) : Prop :=
  forall p2 q2, AnnIso G D g p2 q2 -> p = p2 /\ q = q2.

Lemma case_An_Assn : forall G D c a b A
    (hctx:AnnCtx G) (hb:binds c (Co (Eq a b A)) G) (hi:c `in` D),
  Pdef G D (g_Var_f c) a b (An_Assn G D c a b A hctx hb hi).
Proof.
  intros. unfold Pdef. intros a2 b2 H2.
  inversion H2 as [G' D' c' a' b' A' hctx' hb' hi' | | | | | | | | | | | | | | | |].
  pose proof (AnnCtx_uniq G hctx) as Hun.
  pose proof (@binds_unique sort c (Co (Eq a b A)) (Co (Eq a2 b2 A')) G hb hb' Hun) as Heq.
  injection Heq; intros; subst; auto.
Qed.

Lemma case_An_Refl : forall G D a A (ht:AnnTyping G a A),
  Pdef G D (g_Refl a) a a (An_Refl G D a A ht).
Proof.
  intros. unfold Pdef. intros a2 b2 H2.
  inversion H2; subst; auto.
Qed.

(** * Case lemmas for determinacy *)

Lemma case_An_EraseEq : forall G D a b g A B
    (h1:AnnTyping G a A) (h2:AnnTyping G b B) (he:erase_tm a = erase_tm b)
    (h3:AnnDefEq G (dom G) g A B) (IH:Pdef G (dom G) g A B h3),
  Pdef G D (g_Refl2 a b g) a b (An_EraseEq G D a b g A B h1 h2 he h3).
Proof.
  intros. unfold Pdef. intros x y H2.
  inversion H2 as [ |  | G' D' a' b' g' A' B' h1' h2' he' h3' |  |  |  |  |  |  |  |  |  |  |  |  |  | ].
  subst. auto.
Qed.

Lemma case_An_Sym : forall G D g a b B A g1
    (h1:AnnTyping G b B) (h2:AnnTyping G a A)
    (h3:AnnDefEq G (dom G) g1 B A) (IH1:Pdef G (dom G) g1 B A h3)
    (h4:AnnDefEq G D g b a) (IH2:Pdef G D g b a h4),
  Pdef G D (g_Sym g) a b (An_Sym G D g a b B A g1 h1 h2 h3 h4).
Proof.
  intros. unfold Pdef in *. intros x y H2.
  inversion H2 as [ |  |  | G' D' g' a' b' B' A' g1' h1' h2' h3' h4' |  |  |  |  |  |  |  |  |  |  |  |  | ].
  subst.
  match goal with
  | H : AnnDefEq G D g ?y' ?x' |- _ =>
      destruct (IH2 y' x' H) as [E1 E2]; auto
  end.
Qed.

Lemma case_An_Trans : forall G D g1 g2 a b a1 A A1 g3
    (h1:AnnDefEq G D g1 a a1) (IH1:Pdef G D g1 a a1 h1)
    (h2:AnnDefEq G D g2 a1 b) (IH2:Pdef G D g2 a1 b h2)
    (h3:AnnTyping G a A) (h4:AnnTyping G a1 A1)
    (h5:AnnDefEq G (dom G) g3 A A1) (IH3:Pdef G (dom G) g3 A A1 h5),
  Pdef G D (g_Trans g1 g2) a b (An_Trans G D g1 g2 a b a1 A A1 g3 h1 h2 h3 h4 h5).
Proof.
  intros. unfold Pdef in *. intros x y H2.
  inversion H2 as [| | | | G' D' g1' g2' a' b' a1' A' A1' g3' h1' h2' h3' h4' h5' | | | | | | | | | | | |].
  subst.
  match goal with
  | H1 : AnnDefEq G D g1 ?x' ?m, H2 : AnnDefEq G D g2 ?m ?y' |- _ =>
      destruct (IH1 x' m H1) as [E1 E2];
      destruct (IH2 m y' H2) as [E3 E4]; auto
  end.
Qed.

Lemma case_An_Beta : forall G D a1 a2 B0 B1
    (h1:AnnTyping G a1 B0) (h2:AnnTyping G a2 B1) (he:erase_tm B0 = erase_tm B1)
    (hb:Beta (erase_tm a1) (erase_tm a2)),
  Pdef G D (g_Beta a1 a2) a1 a2 (An_Beta G D a1 a2 B0 B1 h1 h2 he hb).
Proof.
  intros. unfold Pdef. intros x y H2.
  inversion H2 as [| | | | | G' D' a1' a2' B0' B1' h1' h2' he' hb' | | | | | | | | | | |].
  subst. auto.
Qed.

Lemma case_An_AppCong : forall G D g1 rho g2 a1 a2 b1 b2 A B g3
    (h1:AnnDefEq G D g1 a1 b1) (IH1:Pdef G D g1 a1 b1 h1)
    (h2:AnnDefEq G D g2 a2 b2) (IH2:Pdef G D g2 a2 b2 h2)
    (h3:AnnTyping G (a_App a1 rho a2) A) (h4:AnnTyping G (a_App b1 rho b2) B)
    (h5:AnnDefEq G (dom G) g3 A B) (IH3:Pdef G (dom G) g3 A B h5),
  Pdef G D (g_AppCong g1 rho g2) (a_App a1 rho a2) (a_App b1 rho b2)
    (An_AppCong G D g1 rho g2 a1 a2 b1 b2 A B g3 h1 h2 h3 h4 h5).
Proof.
  intros. unfold Pdef in *. intros x y H2.
  inversion H2 as [| | | | | | | | G' D' g1' rho' g2' a1' a2' b1' b2' A' B' g3' h1' h2' h3' h4' h5' | | | | | | | |].
  subst.
  match goal with
  | H1 : AnnDefEq G D g1 ?u ?v, H2 : AnnDefEq G D g2 ?s ?t |- _ =>
      destruct (IH1 u v H1) as [E1 F1];
      destruct (IH2 s t H2) as [E2 F2]
  end.
  subst. auto.
Qed.

Lemma case_An_PiFst : forall G D g A1 A2 rho B1 B2
    (h1:AnnDefEq G D g (a_Pi rho A1 B1) (a_Pi rho A2 B2))
    (IH1:Pdef G D g (a_Pi rho A1 B1) (a_Pi rho A2 B2) h1),
  Pdef G D (g_PiFst g) A1 A2 (An_PiFst G D g A1 A2 rho B1 B2 h1).
Proof.
  intros. unfold Pdef in *. intros x y H2.
  inversion H2 as [| | | | | | | | | G' D' g' A1' A2' rho' B1' B2' h1' | | | | | | |].
  subst.
  match goal with
  | H : AnnDefEq G D g ?u ?v |- _ =>
      destruct (IH1 u v H) as [E1 E2]; injection E1; intros; injection E2; intros; subst; auto
  end.
Qed.

Lemma case_An_PiSnd : forall G D g1 g2 B1 a1 B2 a2 rho A1 A2
    (h1:AnnDefEq G D g1 (a_Pi rho A1 B1) (a_Pi rho A2 B2))
    (IH1:Pdef G D g1 (a_Pi rho A1 B1) (a_Pi rho A2 B2) h1)
    (h2:AnnDefEq G D g2 a1 a2) (IH2:Pdef G D g2 a1 a2 h2)
    (h3:AnnTyping G a1 A1) (h4:AnnTyping G a2 A2),
  Pdef G D (g_PiSnd g1 g2) (open_tm_wrt_tm B1 a1) (open_tm_wrt_tm B2 a2)
    (An_PiSnd G D g1 g2 B1 a1 B2 a2 rho A1 A2 h1 h2 h3 h4).
Proof.
  intros. unfold Pdef in *. intros x y H2.
  inversion H2 as [ |  |  |  |  |  |  |  |  |  | G' D' g1' g2' B1' a1' B2' a2' rho' A1' A2' h1' h2' h3' h4' |  |  |  |  |  | ].
  subst.
  match goal with
  | H1 : AnnDefEq G D g1 ?u ?v, H2 : AnnDefEq G D g2 ?s ?t |- _ =>
      destruct (IH1 u v H1) as [E1 E2];
      destruct (IH2 s t H2) as [E3 E4];
      injection E1; intros; injection E2; intros; subst; auto
  end.
Qed.

Lemma case_An_CAppCong : forall G D g1 g2 g3 a1 b1 a2 b2 a3 b3 A B g4
    (h1:AnnDefEq G D g1 a1 b1) (IH1:Pdef G D g1 a1 b1 h1)
    (h2:AnnDefEq G (dom G) g2 a2 b2) (IH2:Pdef G (dom G) g2 a2 b2 h2)
    (h3:AnnDefEq G (dom G) g3 a3 b3) (IH3:Pdef G (dom G) g3 a3 b3 h3)
    (h4:AnnTyping G (a_CApp a1 g2) A) (h5:AnnTyping G (a_CApp b1 g3) B)
    (h6:AnnDefEq G (dom G) g4 A B) (IH4:Pdef G (dom G) g4 A B h6),
  Pdef G D (g_CAppCong g1 g2 g3) (a_CApp a1 g2) (a_CApp b1 g3)
    (An_CAppCong G D g1 g2 g3 a1 b1 a2 b2 a3 b3 A B g4 h1 h2 h3 h4 h5 h6).
Proof.
  intros. unfold Pdef in *. intros x y H2.
  inversion H2 as [| | | | | | | | | | | | | G' D' g1' g2' g3' a1' b1' a2' b2' a3' b3' A' B' g4' h1' h2' h3' h4' h5' h6' | | |].
  subst.
  match goal with
  | H : AnnDefEq G D g1 ?u ?v |- _ =>
      destruct (IH1 u v H) as [E1 F1]
  end.
  subst. auto.
Qed.

Lemma case_An_CPiSnd : forall G D g1 g2 g3 B1 B2 a a' A b b' B
    (h1:AnnDefEq G D g1 (a_CPi (Eq a a' A) B1) (a_CPi (Eq b b' B) B2))
    (IH1:Pdef G D g1 (a_CPi (Eq a a' A) B1) (a_CPi (Eq b b' B) B2) h1)
    (h2:AnnDefEq G (dom G) g2 a a') (IH2:Pdef G (dom G) g2 a a' h2)
    (h3:AnnDefEq G (dom G) g3 b b') (IH3:Pdef G (dom G) g3 b b' h3),
  Pdef G D (g_CPiSnd g1 g2 g3) (open_tm_wrt_co B1 g2) (open_tm_wrt_co B2 g3)
    (An_CPiSnd G D g1 g2 g3 B1 B2 a a' A b b' B h1 h2 h3).
Proof.
  intros. unfold Pdef in *. intros x y H2.
  inversion H2 as [| | | | | | | | | | | | | | G' D' g1' g2' g3' B1' B2' a1' a1'' A' b1' b1'' B' h1' h2' h3' | |].
  subst.
  match goal with
  | H : AnnDefEq G D g1 ?u ?v |- _ =>
      destruct (IH1 u v H) as [E1 E2]; injection E1; intros; injection E2; intros; subst; auto
  end.
Qed.

Lemma case_An_Cast : forall G D g1 g2 b b' a a' A B
    (h1:AnnDefEq G D g1 a a') (IH1:Pdef G D g1 a a' h1)
    (h2:AnnIso G D g2 (Eq a a' A) (Eq b b' B))
    (IH2:Piso G D g2 (Eq a a' A) (Eq b b' B) h2),
  Pdef G D (g_Cast g1 g2) b b' (An_Cast G D g1 g2 b b' a a' A B h1 h2).
Proof.
  intros. unfold Pdef in *. intros x y H2.
  inversion H2 as [| | | | | | | | | | | | | | | G' D' g1' g2' b1' b2' a1' a1'' A' B' h1' h2' |].
  subst.
  match goal with
  | H : AnnIso G D g2 _ _ |- _ =>
      destruct (IH2 _ _ H) as [E1 E2]; injection E2; intros; auto
  end.
Qed.

Lemma case_An_IsoSnd : forall G D g A B a a' b b'
    (h1:AnnIso G D g (Eq a a' A) (Eq b b' B))
    (IH1:Piso G D g (Eq a a' A) (Eq b b' B) h1),
  Pdef G D (g_IsoSnd g) A B (An_IsoSnd G D g A B a a' b b' h1).
Proof.
  intros. unfold Pdef in *. intros x y H2.
  inversion H2 as [| | | | | | | | | | | | | | | | G' D' g' A' B' a1' a1'' b1' b1'' h1'].
  subst.
  match goal with
  | H : AnnIso G D g _ _ |- _ =>
      destruct (IH1 _ _ H) as [E1 E2]; injection E1; intros; injection E2; intros; subst; auto
  end.
Qed.

Lemma case_An_PiCong : forall L G D rho g1 g2 A1 B1 A2 B3 B2
    (h1:AnnDefEq G D g1 A1 A2) (IH1:Pdef G D g1 A1 A2 h1)
    (h2:forall x, x `notin` L -> AnnDefEq ((x ~ Tm A1) ++ G) D
          (open_co_wrt_tm g2 (a_Var_f x)) (open_tm_wrt_tm B1 (a_Var_f x)) (open_tm_wrt_tm B2 (a_Var_f x)))
    (IH2:forall x (Hx:x `notin` L), Pdef ((x ~ Tm A1) ++ G) D
          (open_co_wrt_tm g2 (a_Var_f x)) (open_tm_wrt_tm B1 (a_Var_f x)) (open_tm_wrt_tm B2 (a_Var_f x))
          (h2 x Hx))
    (he:forall x, x `notin` L -> open_tm_wrt_tm B3 (a_Var_f x) =
          open_tm_wrt_tm B2 (a_Conv (a_Var_f x) (g_Sym g1)))
    (h3:AnnTyping G (a_Pi rho A1 B1) a_Star)
    (h4:AnnTyping G (a_Pi rho A1 B2) a_Star)
    (h5:AnnTyping G (a_Pi rho A2 B3) a_Star),
  Pdef G D (g_PiCong rho g1 g2) (a_Pi rho A1 B1) (a_Pi rho A2 B3)
    (An_PiCong L G D rho g1 g2 A1 B1 A2 B3 B2 h1 h2 he h3 h4 h5).
Proof.
  intros. unfold Pdef in *. intros u v H2.
  inversion H2 as [ | | | | | | L' G' D' rho' g1' g2' A1' B1' A2' B3' B2' h1' h2' he' t1' t2' t3' | | | | | | | | | | ].
  destruct (IH1 A1' A2' h1') as [EA1 EA2].
  rewrite <- EA1 in h2'.
  destruct (atom_fresh (L \u L' \u fv_tm_tm_tm B1 \u fv_tm_tm_tm B2 \u fv_tm_tm_tm B3
                          \u fv_tm_tm_tm B1' \u fv_tm_tm_tm B2' \u fv_tm_tm_tm B3')) as [x Hx].
  notin_destruct.
  destruct (IH2 x ltac:(assumption) (open_tm_wrt_tm B1' (a_Var_f x)) (open_tm_wrt_tm B2' (a_Var_f x))
             (h2' x ltac:(assumption))) as [EB1 EB2].
  pose proof (proj1 open_tm_var_inj B1 0 x ltac:(assumption) B1' ltac:(assumption) EB1) as EQB1.
  pose proof (proj1 open_tm_var_inj B2 0 x ltac:(assumption) B2' ltac:(assumption) EB2) as EQB2.
  assert (EB3 : open_tm_wrt_tm B3 (a_Var_f x) = open_tm_wrt_tm B3' (a_Var_f x)).
  { specialize (he x ltac:(assumption)). specialize (he' x ltac:(assumption)).
    rewrite EQB2 in he. rewrite <- he in he'. symmetry. exact he'. }
  pose proof (proj1 open_tm_var_inj B3 0 x ltac:(assumption) B3' ltac:(assumption) EB3) as EQB3.
  rewrite <- EA1, <- EQB1, <- EA2, <- EQB3. auto.
Qed.

Lemma case_An_AbsCong : forall L G D rho g1 g2 A1 b1 A2 b3 b2 B
    (h1:AnnDefEq G D g1 A1 A2) (IH1:Pdef G D g1 A1 A2 h1)
    (h2:forall x, x `notin` L -> AnnDefEq ((x ~ Tm A1) ++ G) D
          (open_co_wrt_tm g2 (a_Var_f x)) (open_tm_wrt_tm b1 (a_Var_f x)) (open_tm_wrt_tm b2 (a_Var_f x)))
    (IH2:forall x (Hx:x `notin` L), Pdef ((x ~ Tm A1) ++ G) D
          (open_co_wrt_tm g2 (a_Var_f x)) (open_tm_wrt_tm b1 (a_Var_f x)) (open_tm_wrt_tm b2 (a_Var_f x))
          (h2 x Hx))
    (he:forall x, x `notin` L -> open_tm_wrt_tm b3 (a_Var_f x) =
          open_tm_wrt_tm b2 (a_Conv (a_Var_f x) (g_Sym g1)))
    (t1:AnnTyping G A1 a_Star)
    (t2:AnnTyping G A2 a_Star)
    (r1:forall x, x `notin` L -> RhoCheck rho x (erase_tm (open_tm_wrt_tm b1 (a_Var_f x))))
    (r2:forall x, x `notin` L -> RhoCheck rho x (erase_tm (open_tm_wrt_tm b3 (a_Var_f x))))
    (t3:AnnTyping G (a_Abs rho A1 b2) B),
  Pdef G D (g_AbsCong rho g1 g2) (a_Abs rho A1 b1) (a_Abs rho A2 b3)
    (An_AbsCong L G D rho g1 g2 A1 b1 A2 b3 b2 B h1 h2 he t1 t2 r1 r2 t3).
Proof.
  intros. unfold Pdef in *. intros u v H2.
  inversion H2 as [ | | | | | | | L' G' D' rho' g1' g2' A1' b1' A2' b3' b2' B' h1' h2' he' t1' t2' r1' r2' t3' | | | | | | | | | ].
  destruct (IH1 A1' A2' h1') as [EA1 EA2].
  rewrite <- EA1 in h2'.
  destruct (atom_fresh (L \u L' \u fv_tm_tm_tm b1 \u fv_tm_tm_tm b2 \u fv_tm_tm_tm b3
                          \u fv_tm_tm_tm b1' \u fv_tm_tm_tm b2' \u fv_tm_tm_tm b3')) as [x Hx].
  notin_destruct.
  destruct (IH2 x ltac:(assumption) (open_tm_wrt_tm b1' (a_Var_f x)) (open_tm_wrt_tm b2' (a_Var_f x))
             (h2' x ltac:(assumption))) as [EB1 EB2].
  pose proof (proj1 open_tm_var_inj b1 0 x ltac:(assumption) b1' ltac:(assumption) EB1) as EQB1.
  pose proof (proj1 open_tm_var_inj b2 0 x ltac:(assumption) b2' ltac:(assumption) EB2) as EQB2.
  assert (EB3 : open_tm_wrt_tm b3 (a_Var_f x) = open_tm_wrt_tm b3' (a_Var_f x)).
  { specialize (he x ltac:(assumption)). specialize (he' x ltac:(assumption)).
    rewrite EQB2 in he. rewrite <- he in he'. symmetry. exact he'. }
  pose proof (proj1 open_tm_var_inj b3 0 x ltac:(assumption) b3' ltac:(assumption) EB3) as EQB3.
  rewrite <- EA1, <- EQB1, <- EA2, <- EQB3. auto.
Qed.

Lemma case_An_CPiCong : forall L G D g1 g3 phi1 B1 phi2 B3 B2
    (h1:AnnIso G D g1 phi1 phi2) (IH1:Piso G D g1 phi1 phi2 h1)
    (h2:forall c, c `notin` L -> AnnDefEq ((c ~ Co phi1) ++ G) D
          (open_co_wrt_co g3 (g_Var_f c)) (open_tm_wrt_co B1 (g_Var_f c)) (open_tm_wrt_co B2 (g_Var_f c)))
    (IH2:forall c (Hc:c `notin` L), Pdef ((c ~ Co phi1) ++ G) D
          (open_co_wrt_co g3 (g_Var_f c)) (open_tm_wrt_co B1 (g_Var_f c)) (open_tm_wrt_co B2 (g_Var_f c))
          (h2 c Hc))
    (he:forall c, c `notin` L -> open_tm_wrt_co B3 (g_Var_f c) =
          open_tm_wrt_co B2 (g_Cast (g_Var_f c) (g_Sym g1)))
    (t1:AnnTyping G (a_CPi phi1 B1) a_Star)
    (t2:AnnTyping G (a_CPi phi2 B3) a_Star)
    (t3:AnnTyping G (a_CPi phi1 B2) a_Star),
  Pdef G D (g_CPiCong g1 g3) (a_CPi phi1 B1) (a_CPi phi2 B3)
    (An_CPiCong L G D g1 g3 phi1 B1 phi2 B3 B2 h1 h2 he t1 t2 t3).
Proof.
  intros. unfold Pdef in *. intros u v H2.
  inversion H2 as [ | | | | | | | | | | | L' G' D' g1' g3' phi1' B1' phi2' B3' B2' h1' h2' he' t1' t2' t3' | | | | | ].
  destruct (IH1 phi1' phi2' h1') as [Ephi1 Ephi2].
  rewrite <- Ephi1 in h2'.
  destruct (atom_fresh (L \u L' \u fatm_tm B1 \u fatm_tm B2 \u fatm_tm B3
                          \u fatm_tm B1' \u fatm_tm B2' \u fatm_tm B3')) as [c Hc].
  notin_destruct.
  destruct (IH2 c ltac:(assumption) (open_tm_wrt_co B1' (g_Var_f c)) (open_tm_wrt_co B2' (g_Var_f c))
             (h2' c ltac:(assumption))) as [EB1 EB2].
  pose proof (proj1 open_tm_co_inj B1 0 c ltac:(assumption) B1' ltac:(assumption) EB1) as EQB1.
  pose proof (proj1 open_tm_co_inj B2 0 c ltac:(assumption) B2' ltac:(assumption) EB2) as EQB2.
  assert (EB3 : open_tm_wrt_co B3 (g_Var_f c) = open_tm_wrt_co B3' (g_Var_f c)).
  { specialize (he c ltac:(assumption)). specialize (he' c ltac:(assumption)).
    rewrite EQB2 in he. rewrite <- he in he'. symmetry. exact he'. }
  pose proof (proj1 open_tm_co_inj B3 0 c ltac:(assumption) B3' ltac:(assumption) EB3) as EQB3.
  rewrite <- Ephi1, <- EQB1, <- Ephi2, <- EQB3. auto.
Qed.

Lemma case_An_CAbsCong : forall L G D g1 g3 g4 phi1 a1 phi2 a3 a2 B1 B B2
    (h1:AnnIso G D g1 phi1 phi2) (IH1:Piso G D g1 phi1 phi2 h1)
    (h2:forall c, c `notin` L -> AnnDefEq ((c ~ Co phi1) ++ G) D
          (open_co_wrt_co g3 (g_Var_f c)) (open_tm_wrt_co a1 (g_Var_f c)) (open_tm_wrt_co a2 (g_Var_f c)))
    (IH2:forall c (Hc:c `notin` L), Pdef ((c ~ Co phi1) ++ G) D
          (open_co_wrt_co g3 (g_Var_f c)) (open_tm_wrt_co a1 (g_Var_f c)) (open_tm_wrt_co a2 (g_Var_f c))
          (h2 c Hc))
    (he:forall c, c `notin` L -> open_tm_wrt_co a3 (g_Var_f c) =
          open_tm_wrt_co a2 (g_Cast (g_Var_f c) (g_Sym g1)))
    (t1:AnnTyping G (a_CAbs phi1 a1) (a_CPi phi1 B1))
    (t2:AnnTyping G (a_CAbs phi1 a2) B)
    (t3:AnnTyping G (a_CAbs phi2 a3) (a_CPi phi2 B2))
    (h4:AnnDefEq G (dom G) g4 (a_CPi phi1 B1) (a_CPi phi2 B2))
    (IH4:Pdef G (dom G) g4 (a_CPi phi1 B1) (a_CPi phi2 B2) h4),
  Pdef G D (g_CAbsCong g1 g3 g4) (a_CAbs phi1 a1) (a_CAbs phi2 a3)
    (An_CAbsCong L G D g1 g3 g4 phi1 a1 phi2 a3 a2 B1 B B2 h1 h2 he t1 t2 t3 h4).
Proof.
  intros. unfold Pdef in *. intros u v H2.
  inversion H2 as [ | | | | | | | | | | | | L' G' D' g1' g3' g4' phi1' a1' phi2' a3' a2' B1' B' B2' h1' h2' he' t1' t2' t3' t4' h4' | | | | ].
  destruct (IH1 phi1' phi2' h1') as [Ephi1 Ephi2].
  rewrite <- Ephi1 in h2'.
  destruct (atom_fresh (L \u L' \u fatm_tm a1 \u fatm_tm a2 \u fatm_tm a3
                          \u fatm_tm a1' \u fatm_tm a2' \u fatm_tm a3')) as [c Hc].
  notin_destruct.
  destruct (IH2 c ltac:(assumption) (open_tm_wrt_co a1' (g_Var_f c)) (open_tm_wrt_co a2' (g_Var_f c))
             (h2' c ltac:(assumption))) as [EB1 EB2].
  pose proof (proj1 open_tm_co_inj a1 0 c ltac:(assumption) a1' ltac:(assumption) EB1) as EQB1.
  pose proof (proj1 open_tm_co_inj a2 0 c ltac:(assumption) a2' ltac:(assumption) EB2) as EQB2.
  assert (EB3 : open_tm_wrt_co a3 (g_Var_f c) = open_tm_wrt_co a3' (g_Var_f c)).
  { specialize (he c ltac:(assumption)). specialize (he' c ltac:(assumption)).
    rewrite EQB2 in he. rewrite <- he in he'. symmetry. exact he'. }
  pose proof (proj1 open_tm_co_inj a3 0 c ltac:(assumption) a3' ltac:(assumption) EB3) as EQB3.
  rewrite <- Ephi1, <- EQB1, <- Ephi2, <- EQB3. auto.
Qed.

Lemma case_An_PropCong : forall G D g1 A g2 A1 B1 A2 B2
    (h1:AnnDefEq G D g1 A1 A2) (IH1:Pdef G D g1 A1 A2 h1)
    (h2:AnnDefEq G D g2 B1 B2) (IH2:Pdef G D g2 B1 B2 h2)
    (w1:AnnPropWff G (Eq A1 B1 A)) (w2:AnnPropWff G (Eq A2 B2 A)),
  Piso G D (g_EqCong g1 A g2) (Eq A1 B1 A) (Eq A2 B2 A)
    (An_PropCong G D g1 A g2 A1 B1 A2 B2 h1 h2 w1 w2).
Proof.
  intros. unfold Piso in *. intros u v H2.
  inversion H2 as [G' D' g1' A' g2' A1' B1' A2' B2' h1' h2' w1' w2' | | |].
  destruct (IH1 A1' A2' h1') as [EA1 EA2].
  destruct (IH2 B1' B2' h2') as [EB1 EB2].
  rewrite <- EA1, <- EB1, <- EA2, <- EB2. auto.
Qed.

Lemma case_An_CPiFst : forall G D g phi1 phi2 A2 B2
    (h1:AnnDefEq G D g (a_CPi phi1 A2) (a_CPi phi2 B2))
    (IH1:Pdef G D g (a_CPi phi1 A2) (a_CPi phi2 B2) h1),
  Piso G D (g_CPiFst g) phi1 phi2 (An_CPiFst G D g phi1 phi2 A2 B2 h1).
Proof.
  intros. unfold Piso in *. intros u v H2.
  inversion H2 as [| G' D' g' phi1' phi2' A2' B2' h1' | |].
  destruct (IH1 (a_CPi u A2') (a_CPi v B2') h1') as [E1 E2].
  injection E1; intros; injection E2; intros; subst; auto.
Qed.

Lemma case_An_IsoSym : forall G D g phi2 phi1
    (h1:AnnIso G D g phi1 phi2) (IH1:Piso G D g phi1 phi2 h1),
  Piso G D (g_Sym g) phi2 phi1 (An_IsoSym G D g phi2 phi1 h1).
Proof.
  intros. unfold Piso in *. intros u v H2.
  inversion H2 as [| | G' D' g' phi2' phi1' h1' |].
  destruct (IH1 v u h1') as [E1 E2]. auto.
Qed.

Lemma case_An_IsoConv : forall G D a1 a2 A a1' a2' B g
    (h1:AnnDefEq G D g A B) (IH1:Pdef G D g A B h1)
    (w1:AnnPropWff G (Eq a1 a2 A)) (w2:AnnPropWff G (Eq a1' a2' B))
    (e1:erase_tm a1 = erase_tm a1') (e2:erase_tm a2 = erase_tm a2'),
  Piso G D (g_IsoConv (Eq a1 a2 A) (Eq a1' a2' B) g) (Eq a1 a2 A) (Eq a1' a2' B)
    (An_IsoConv G D a1 a2 A a1' a2' B g h1 w1 w2 e1 e2).
Proof.
  intros. unfold Piso in *. intros u v H2.
  inversion H2 as [| | | G' D' a1_2 a2_2 A_2 a1'_2 a2'_2 B_2 g_2 h1' w1' w2' e1' e2'].
  subst. auto.
Qed.

Theorem AnnDefEq_det : forall G D g a1 b1 a2 b2,
  AnnDefEq G D g a1 b1 -> AnnDefEq G D g a2 b2 -> a1 = a2 /\ b1 = b2.
Proof.
  intros G D g a1 b1 a2 b2 H1 H2.
  apply (AnnDefEq_ind2 Pdef Piso
    case_An_Assn case_An_Refl case_An_EraseEq case_An_Sym case_An_Trans
    case_An_Beta case_An_PiCong case_An_AbsCong case_An_AppCong
    case_An_PiFst case_An_PiSnd case_An_CPiCong case_An_CAbsCong
    case_An_CAppCong case_An_CPiSnd case_An_Cast case_An_IsoSnd
    case_An_PropCong case_An_CPiFst case_An_IsoSym case_An_IsoConv
    G D g a1 b1 H1 a2 b2 H2).
Qed.

Theorem AnnIso_det : forall G D g p1 q1 p2 q2,
  AnnIso G D g p1 q1 -> AnnIso G D g p2 q2 -> p1 = p2 /\ q1 = q2.
Proof.
  intros G D g p1 q1 p2 q2 H1 H2.
  apply (AnnIso_ind2 Pdef Piso
    case_An_Assn case_An_Refl case_An_EraseEq case_An_Sym case_An_Trans
    case_An_Beta case_An_PiCong case_An_AbsCong case_An_AppCong
    case_An_PiFst case_An_PiSnd case_An_CPiCong case_An_CAbsCong
    case_An_CAppCong case_An_CPiSnd case_An_Cast case_An_IsoSnd
    case_An_PropCong case_An_CPiFst case_An_IsoSym case_An_IsoConv
    G D g p1 q1 H1 p2 q2 H2).
Qed.

(** ** Explicit co-opening injectivity corollaries *)

Lemma inj_open_tm_co : forall (a:tm) k c, c `notin` fatm_tm a ->
    forall bb, c `notin` fatm_tm bb ->
      open_tm_wrt_co_rec k (g_Var_f c) a = open_tm_wrt_co_rec k (g_Var_f c) bb -> a = bb.
Proof. exact (proj1 open_tm_co_inj). Qed.

Lemma inj_open_brs_co : forall (a:brs) k c, c `notin` fatm_brs a ->
    forall bb, c `notin` fatm_brs bb ->
      open_brs_wrt_co_rec k (g_Var_f c) a = open_brs_wrt_co_rec k (g_Var_f c) bb -> a = bb.
Proof. exact (proj1 (proj2 open_tm_co_inj)). Qed.

Lemma inj_open_co_co : forall (a:co) k c, c `notin` fatm_co a ->
    forall bb, c `notin` fatm_co bb ->
      open_co_wrt_co_rec k (g_Var_f c) a = open_co_wrt_co_rec k (g_Var_f c) bb -> a = bb.
Proof. exact (proj1 (proj2 (proj2 open_tm_co_inj))). Qed.

Lemma inj_open_constraint_co : forall (a:constraint) k c, c `notin` fatm_constraint a ->
    forall bb, c `notin` fatm_constraint bb ->
      open_constraint_wrt_co_rec k (g_Var_f c) a = open_constraint_wrt_co_rec k (g_Var_f c) bb -> a = bb.
Proof. exact (proj2 (proj2 (proj2 open_tm_co_inj))). Qed.

(* fvx definitions copied from Base *)
Fixpoint fvx_tm (a:tm) : vars :=
  match a with
  | a_Star => {}
  | a_Var_b _ => {}
  | a_Var_f x => {{x}}
  | a_Abs rho A b => fvx_tm A \u fvx_tm b
  | a_UAbs rho b => fvx_tm b
  | a_App a rho b => fvx_tm a \u fvx_tm b
  | a_Fam _ => {}
  | a_Const _ => {}
  | a_Pi rho A B => fvx_tm A \u fvx_tm B
  | a_Conv a g => fvx_tm a \u fvx_co g
  | a_CPi phi B => fvx_constraint phi \u fvx_tm B
  | a_CAbs phi b => fvx_constraint phi \u fvx_tm b
  | a_UCAbs b => fvx_tm b
  | a_CApp a g => fvx_tm a \u fvx_co g
  | a_Bullet => {}
  | a_DataCon _ => {}
  | a_Case a brs5 => fvx_tm a \u fvx_brs brs5
  end
with fvx_brs (b:brs) : vars :=
  match b with
  | br_None => {}
  | br_One _ a b' => fvx_tm a \u fvx_brs b'
  end
with fvx_co (g:co) : vars :=
  match g with
  | g_Triv => {}
  | g_Var_b _ => {}
  | g_Var_f c => {{c}}
  | g_Beta a b => fvx_tm a \u fvx_tm b
  | g_Refl a => fvx_tm a
  | g_Refl2 a b g' => fvx_tm a \u fvx_tm b \u fvx_co g'
  | g_Sym g' => fvx_co g'
  | g_Trans g1 g2 => fvx_co g1 \u fvx_co g2
  | g_PiCong _ g1 g2 => fvx_co g1 \u fvx_co g2
  | g_AbsCong _ g1 g2 => fvx_co g1 \u fvx_co g2
  | g_AppCong g1 _ g2 => fvx_co g1 \u fvx_co g2
  | g_PiFst g' => fvx_co g'
  | g_CPiFst g' => fvx_co g'
  | g_IsoSnd g' => fvx_co g'
  | g_PiSnd g1 g2 => fvx_co g1 \u fvx_co g2
  | g_CPiCong g1 g3 => fvx_co g1 \u fvx_co g3
  | g_CAbsCong g1 g3 g4 => fvx_co g1 \u fvx_co g3 \u fvx_co g4
  | g_CAppCong g g1 g2 => fvx_co g \u fvx_co g1 \u fvx_co g2
  | g_CPiSnd g g1 g2 => fvx_co g \u fvx_co g1 \u fvx_co g2
  | g_Cast g1 g2 => fvx_co g1 \u fvx_co g2
  | g_EqCong g1 A g2 => fvx_co g1 \u fvx_tm A \u fvx_co g2
  | g_IsoConv phi1 phi2 g => fvx_constraint phi1 \u fvx_constraint phi2 \u fvx_co g
  | g_Eta a => fvx_tm a
  | g_Left g g' => fvx_co g \u fvx_co g'
  | g_Right g g' => fvx_co g \u fvx_co g'
  end
with fvx_constraint (phi:constraint) : vars :=
  match phi with
  | Eq a b A => fvx_tm a \u fvx_tm b \u fvx_tm A
  end.

(* fvx opening subset/notin *)
Ltac mem_solve :=
  unfold AtomSetImpl.Subset in *;
  intros ? Hx;
  repeat match goal with
  | H : _ `in` (_ \u _) |- _ => apply AtomSetImpl.union_1 in H
  | H : _ \/ _ |- _ => destruct H
  | H : ?y `in` singleton ?x |- _ => apply singleton_iff in H
  | H : ?y `in` empty |- _ => exfalso; exact (AtomSetImpl.empty_1 y H)
  | H : forall _ _, _, Hx : _ `in` _ |- _ => eapply H in Hx
  end;
  eauto 10 using AtomSetImpl.union_2, AtomSetImpl.union_3,
                   AtomSetImpl.singleton_2.

(** D (subset part).  Opening can only add the free variables of the
    replacement, both for term-opening and for co-opening. *)

Lemma fv_open_tm_subset :
  (forall a, forall k u,
     AtomSetImpl.Subset (fvx_tm (open_tm_wrt_tm_rec k u a))
                        (fvx_tm a \u fvx_tm u)) /\
  (forall b, forall k u,
     AtomSetImpl.Subset (fvx_brs (open_brs_wrt_tm_rec k u b))
                        (fvx_brs b \u fvx_tm u)) /\
  (forall g, forall k u,
     AtomSetImpl.Subset (fvx_co (open_co_wrt_tm_rec k u g))
                        (fvx_co g \u fvx_tm u)) /\
  (forall phi, forall k u,
     AtomSetImpl.Subset (fvx_constraint (open_constraint_wrt_tm_rec k u phi))
                        (fvx_constraint phi \u fvx_tm u)).
Proof.
  apply (tm_mutind
    (fun a => forall k u, AtomSetImpl.Subset (fvx_tm (open_tm_wrt_tm_rec k u a))
                           (fvx_tm a \u fvx_tm u))
    (fun b => forall k u, AtomSetImpl.Subset (fvx_brs (open_brs_wrt_tm_rec k u b))
                           (fvx_brs b \u fvx_tm u))
    (fun g => forall k u, AtomSetImpl.Subset (fvx_co (open_co_wrt_tm_rec k u g))
                           (fvx_co g \u fvx_tm u))
    (fun phi => forall k u, AtomSetImpl.Subset (fvx_constraint (open_constraint_wrt_tm_rec k u phi))
                           (fvx_constraint phi \u fvx_tm u))).
  all: intros.
  all: cbn [fvx_tm fvx_brs fvx_co fvx_constraint
            open_tm_wrt_tm_rec open_brs_wrt_tm_rec
            open_co_wrt_tm_rec open_constraint_wrt_tm_rec].
  all: try (match goal with |- context [lt_eq_lt_dec ?a ?b] =>
              destruct (lt_eq_lt_dec a b) as [[Hlt|Heq]|Hgt];
              cbn [fvx_tm] end).
  all: try mem_solve.
Qed.

Lemma fv_open_co_subset :
  (forall a, forall k g,
     AtomSetImpl.Subset (fvx_tm (open_tm_wrt_co_rec k g a))
                        (fvx_tm a \u fvx_co g)) /\
  (forall b, forall k g,
     AtomSetImpl.Subset (fvx_brs (open_brs_wrt_co_rec k g b))
                        (fvx_brs b \u fvx_co g)) /\
  (forall g0, forall k g,
     AtomSetImpl.Subset (fvx_co (open_co_wrt_co_rec k g g0))
                        (fvx_co g0 \u fvx_co g)) /\
  (forall phi, forall k g,
     AtomSetImpl.Subset (fvx_constraint (open_constraint_wrt_co_rec k g phi))
                        (fvx_constraint phi \u fvx_co g)).
Proof.
  apply (tm_mutind
    (fun a => forall k g, AtomSetImpl.Subset (fvx_tm (open_tm_wrt_co_rec k g a))
                           (fvx_tm a \u fvx_co g))
    (fun b => forall k g, AtomSetImpl.Subset (fvx_brs (open_brs_wrt_co_rec k g b))
                           (fvx_brs b \u fvx_co g))
    (fun g0 => forall k g, AtomSetImpl.Subset (fvx_co (open_co_wrt_co_rec k g g0))
                           (fvx_co g0 \u fvx_co g))
    (fun phi => forall k g, AtomSetImpl.Subset (fvx_constraint (open_constraint_wrt_co_rec k g phi))
                           (fvx_constraint phi \u fvx_co g))).
  all: intros.
  all: cbn [fvx_tm fvx_brs fvx_co fvx_constraint
            open_tm_wrt_co_rec open_brs_wrt_co_rec
            open_co_wrt_co_rec open_constraint_wrt_co_rec].
  all: try (match goal with |- context [lt_eq_lt_dec ?a ?b] =>
              destruct (lt_eq_lt_dec a b) as [[Hlt|Heq]|Hgt];
              cbn [fvx_co] end).
  all: try mem_solve.
Qed.

(** Projections of the two subset lemmas. *)

Lemma fv_open_tm_subset_tm : forall a k u,
  AtomSetImpl.Subset (fvx_tm (open_tm_wrt_tm_rec k u a))
                     (fvx_tm a \u fvx_tm u).
Proof. intros; exact (proj1 fv_open_tm_subset a k u). Qed.
Lemma fv_open_tm_subset_brs : forall b k u,
  AtomSetImpl.Subset (fvx_brs (open_brs_wrt_tm_rec k u b))
                     (fvx_brs b \u fvx_tm u).
Proof. intros; exact (proj1 (proj2 fv_open_tm_subset) b k u). Qed.
Lemma fv_open_tm_subset_co : forall g k u,
  AtomSetImpl.Subset (fvx_co (open_co_wrt_tm_rec k u g))
                     (fvx_co g \u fvx_tm u).
Proof. intros; exact (proj1 (proj2 (proj2 fv_open_tm_subset)) g k u). Qed.
Lemma fv_open_tm_subset_constraint : forall phi k u,
  AtomSetImpl.Subset (fvx_constraint (open_constraint_wrt_tm_rec k u phi))
                     (fvx_constraint phi \u fvx_tm u).
Proof. intros; exact (proj2 (proj2 (proj2 fv_open_tm_subset)) phi k u). Qed.

Lemma fv_open_co_subset_tm : forall a k g,
  AtomSetImpl.Subset (fvx_tm (open_tm_wrt_co_rec k g a))
                     (fvx_tm a \u fvx_co g).
Proof. intros; exact (proj1 fv_open_co_subset a k g). Qed.
Lemma fv_open_co_subset_brs : forall b k g,
  AtomSetImpl.Subset (fvx_brs (open_brs_wrt_co_rec k g b))
                     (fvx_brs b \u fvx_co g).
Proof. intros; exact (proj1 (proj2 fv_open_co_subset) b k g). Qed.
Lemma fv_open_co_subset_co : forall g0 k g,
  AtomSetImpl.Subset (fvx_co (open_co_wrt_co_rec k g g0))
                     (fvx_co g0 \u fvx_co g).
Proof. intros; exact (proj1 (proj2 (proj2 fv_open_co_subset)) g0 k g). Qed.
Lemma fv_open_co_subset_constraint : forall phi k g,
  AtomSetImpl.Subset (fvx_constraint (open_constraint_wrt_co_rec k g phi))
                     (fvx_constraint phi \u fvx_co g).
Proof. intros; exact (proj2 (proj2 (proj2 fv_open_co_subset)) phi k g). Qed.

(** D (notin part). *)

Lemma notin_subset : forall (x:atom) s t,
  AtomSetImpl.Subset s t -> x `notin` t -> x `notin` s.
Proof. intros x s t Hsub Hnt Hin. apply Hnt. apply Hsub. exact Hin. Qed.

Lemma fv_open_tm_notin : forall a k u x,
  x `notin` fvx_tm a -> x `notin` fvx_tm u ->
  x `notin` fvx_tm (open_tm_wrt_tm_rec k u a).
Proof.
  intros. eapply notin_subset; [apply fv_open_tm_subset_tm |].
  apply notin_union_3; assumption.
Qed.

Lemma fv_open_tm_notin_brs : forall b k u x,
  x `notin` fvx_brs b -> x `notin` fvx_tm u ->
  x `notin` fvx_brs (open_brs_wrt_tm_rec k u b).
Proof.
  intros. eapply notin_subset; [apply fv_open_tm_subset_brs |].
  apply notin_union_3; assumption.
Qed.

Lemma fv_open_tm_notin_co : forall g k u x,
  x `notin` fvx_co g -> x `notin` fvx_tm u ->
  x `notin` fvx_co (open_co_wrt_tm_rec k u g).
Proof.
  intros. eapply notin_subset; [apply fv_open_tm_subset_co |].
  apply notin_union_3; assumption.
Qed.

Lemma fv_open_tm_notin_constraint : forall phi k u x,
  x `notin` fvx_constraint phi -> x `notin` fvx_tm u ->
  x `notin` fvx_constraint (open_constraint_wrt_tm_rec k u phi).
Proof.
  intros. eapply notin_subset; [apply fv_open_tm_subset_constraint |].
  apply notin_union_3; assumption.
Qed.

Lemma fv_open_co_notin : forall a k g x,
  x `notin` fvx_tm a -> x `notin` fvx_co g ->
  x `notin` fvx_tm (open_tm_wrt_co_rec k g a).
Proof.
  intros. eapply notin_subset; [apply fv_open_co_subset_tm |].
  apply notin_union_3; assumption.
Qed.

Lemma fv_open_co_notin_brs : forall b k g x,
  x `notin` fvx_brs b -> x `notin` fvx_co g ->
  x `notin` fvx_brs (open_brs_wrt_co_rec k g b).
Proof.
  intros. eapply notin_subset; [apply fv_open_co_subset_brs |].
  apply notin_union_3; assumption.
Qed.

Lemma fv_open_co_notin_co : forall g0 k g x,
  x `notin` fvx_co g0 -> x `notin` fvx_co g ->
  x `notin` fvx_co (open_co_wrt_co_rec k g g0).
Proof.
  intros. eapply notin_subset; [apply fv_open_co_subset_co |].
  apply notin_union_3; assumption.
Qed.

Lemma fv_open_co_notin_constraint : forall phi k g x,
  x `notin` fvx_constraint phi -> x `notin` fvx_co g ->
  x `notin` fvx_constraint (open_constraint_wrt_co_rec k g phi).
Proof.
  intros. eapply notin_subset; [apply fv_open_co_subset_constraint |].
  apply notin_union_3; assumption.
Qed.

(** D, special case: opening with a free variable can only add that
    variable to the free variables. *)

Lemma fv_open_tm_var_subset : forall a k y,
  AtomSetImpl.Subset (fvx_tm (open_tm_wrt_tm_rec k (a_Var_f y) a))
                     (fvx_tm a \u singleton y).
Proof.
  intros. pose proof (fv_open_tm_subset_tm a k (a_Var_f y)) as H.
  cbn [fvx_tm] in H. exact H.
Qed.

Lemma fv_open_tm_var_notin : forall a k y x,
  x `notin` fvx_tm a -> x <> y ->
  x `notin` fvx_tm (open_tm_wrt_tm_rec k (a_Var_f y) a).
Proof.
  intros a k y x Ha Hxy.
  eapply notin_subset; [apply fv_open_tm_var_subset |].
  apply notin_union_3; [exact Ha |].
  apply notin_singleton_2. intro Hyx. apply Hxy. symmetry. exact Hyx.
Qed.

(** D (equality part): when the opened object is locally closed at level 0,
    opening is the identity and hence does not change free variables. *)

Lemma fv_open_tm_closed_tm : forall a k u, lc_tm a ->
  fvx_tm (open_tm_wrt_tm_rec k u a) = fvx_tm a.
Proof.
  intros. rewrite (proj1 clt_closed_open_tm a 0 (lc_clt_tm a H) k (le_0_n k) u).
  reflexivity.
Qed.
Lemma fv_open_tm_closed_brs : forall b k u, lc_brs b ->
  fvx_brs (open_brs_wrt_tm_rec k u b) = fvx_brs b.
Proof.
  intros. rewrite (proj1 (proj2 clt_closed_open_tm) b 0 (lc_clt_brs b H) k (le_0_n k) u).
  reflexivity.
Qed.
Lemma fv_open_tm_closed_co : forall g k u, lc_co g ->
  fvx_co (open_co_wrt_tm_rec k u g) = fvx_co g.
Proof.
  intros. rewrite (proj1 (proj2 (proj2 clt_closed_open_tm)) g 0 (lc_clt_co g H) k (le_0_n k) u).
  reflexivity.
Qed.
Lemma fv_open_tm_closed_constraint : forall phi k u, lc_constraint phi ->
  fvx_constraint (open_constraint_wrt_tm_rec k u phi) = fvx_constraint phi.
Proof.
  intros. rewrite (proj2 (proj2 (proj2 clt_closed_open_tm)) phi 0 (lc_clt_constraint phi H) k (le_0_n k) u).
  reflexivity.
Qed.

Lemma fv_open_co_closed_tm : forall a k g, lc_tm a ->
  fvx_tm (open_tm_wrt_co_rec k g a) = fvx_tm a.
Proof.
  intros. rewrite (proj1 clc_closed_open_co a 0 (lc_clc_tm a H) k (le_0_n k) g).
  reflexivity.
Qed.
Lemma fv_open_co_closed_brs : forall b k g, lc_brs b ->
  fvx_brs (open_brs_wrt_co_rec k g b) = fvx_brs b.
Proof.
  intros. rewrite (proj1 (proj2 clc_closed_open_co) b 0 (lc_clc_brs b H) k (le_0_n k) g).
  reflexivity.
Qed.
Lemma fv_open_co_closed_co : forall g0 k g, lc_co g0 ->
  fvx_co (open_co_wrt_co_rec k g g0) = fvx_co g0.
Proof.
  intros. rewrite (proj1 (proj2 (proj2 clc_closed_open_co)) g0 0 (lc_clc_co g0 H) k (le_0_n k) g).
  reflexivity.
Qed.
Lemma fv_open_co_closed_constraint : forall phi k g, lc_constraint phi ->
  fvx_constraint (open_constraint_wrt_co_rec k g phi) = fvx_constraint phi.
Proof.
  intros. rewrite (proj2 (proj2 (proj2 clc_closed_open_co)) phi 0 (lc_clc_constraint phi H) k (le_0_n k) g).
  reflexivity.
Qed.

(* two-function renaming *)
Fixpoint rename_tm (st:tmvar -> tmvar) (sc:covar -> covar) (a:tm) {struct a} : tm :=
  match a with
  | a_Star => a_Star
  | a_Var_b n => a_Var_b n
  | a_Var_f x => a_Var_f (st x)
  | a_Abs rho A b => a_Abs rho (rename_tm st sc A) (rename_tm st sc b)
  | a_UAbs rho b => a_UAbs rho (rename_tm st sc b)
  | a_App a r b => a_App (rename_tm st sc a) r (rename_tm st sc b)
  | a_Fam F => a_Fam F
  | a_Const T => a_Const T
  | a_Pi rho A B => a_Pi rho (rename_tm st sc A) (rename_tm st sc B)
  | a_Conv a g => a_Conv (rename_tm st sc a) (rename_co st sc g)
  | a_CPi phi B => a_CPi (rename_constraint st sc phi) (rename_tm st sc B)
  | a_CAbs phi b => a_CAbs (rename_constraint st sc phi) (rename_tm st sc b)
  | a_UCAbs b => a_UCAbs (rename_tm st sc b)
  | a_CApp a g => a_CApp (rename_tm st sc a) (rename_co st sc g)
  | a_Bullet => a_Bullet
  | a_DataCon K => a_DataCon K
  | a_Case a brs5 => a_Case (rename_tm st sc a) (rename_brs st sc brs5)
  end
with rename_brs (st:tmvar -> tmvar) (sc:covar -> covar) (b:brs) {struct b} : brs :=
  match b with
  | br_None => br_None
  | br_One K a b' => br_One K (rename_tm st sc a) (rename_brs st sc b')
  end
with rename_co (st:tmvar -> tmvar) (sc:covar -> covar) (g:co) {struct g} : co :=
  match g with
  | g_Triv => g_Triv
  | g_Var_b n => g_Var_b n
  | g_Var_f c => g_Var_f (sc c)
  | g_Beta a b => g_Beta (rename_tm st sc a) (rename_tm st sc b)
  | g_Refl a => g_Refl (rename_tm st sc a)
  | g_Refl2 a b g' => g_Refl2 (rename_tm st sc a) (rename_tm st sc b) (rename_co st sc g')
  | g_Sym g' => g_Sym (rename_co st sc g')
  | g_Trans g1 g2 => g_Trans (rename_co st sc g1) (rename_co st sc g2)
  | g_PiCong rho g1 g2 => g_PiCong rho (rename_co st sc g1) (rename_co st sc g2)
  | g_AbsCong rho g1 g2 => g_AbsCong rho (rename_co st sc g1) (rename_co st sc g2)
  | g_AppCong g1 r g2 => g_AppCong (rename_co st sc g1) r (rename_co st sc g2)
  | g_PiFst g' => g_PiFst (rename_co st sc g')
  | g_CPiFst g' => g_CPiFst (rename_co st sc g')
  | g_IsoSnd g' => g_IsoSnd (rename_co st sc g')
  | g_PiSnd g1 g2 => g_PiSnd (rename_co st sc g1) (rename_co st sc g2)
  | g_CPiCong g1 g3 => g_CPiCong (rename_co st sc g1) (rename_co st sc g3)
  | g_CAbsCong g1 g3 g4 => g_CAbsCong (rename_co st sc g1) (rename_co st sc g3) (rename_co st sc g4)
  | g_CAppCong g g1 g2 => g_CAppCong (rename_co st sc g) (rename_co st sc g1) (rename_co st sc g2)
  | g_CPiSnd g g1 g2 => g_CPiSnd (rename_co st sc g) (rename_co st sc g1) (rename_co st sc g2)
  | g_Cast g1 g2 => g_Cast (rename_co st sc g1) (rename_co st sc g2)
  | g_EqCong g1 A g2 => g_EqCong (rename_co st sc g1) (rename_tm st sc A) (rename_co st sc g2)
  | g_IsoConv phi1 phi2 g => g_IsoConv (rename_constraint st sc phi1) (rename_constraint st sc phi2) (rename_co st sc g)
  | g_Eta a => g_Eta (rename_tm st sc a)
  | g_Left g g' => g_Left (rename_co st sc g) (rename_co st sc g')
  | g_Right g g' => g_Right (rename_co st sc g) (rename_co st sc g')
  end
with rename_constraint (st:tmvar -> tmvar) (sc:covar -> covar) (phi:constraint) {struct phi} : constraint :=
  match phi with
  | Eq a b A => Eq (rename_tm st sc a) (rename_tm st sc b) (rename_tm st sc A)
  end.

Ltac rename_open_tm_auto :=
  first
  [ match goal with
    | |- rename_tm ?st ?sc (open_tm_wrt_tm_rec ?k ?u ?x) =
         open_tm_wrt_tm_rec ?k (rename_tm ?st ?sc ?u) (rename_tm ?st ?sc ?x) =>
        match goal with H : forall st0 sc0 k0 u0,
          rename_tm st0 sc0 (open_tm_wrt_tm_rec k0 u0 ?x) =
          open_tm_wrt_tm_rec k0 (rename_tm st0 sc0 u0) (rename_tm st0 sc0 ?x) |- _ =>
          exact (H st sc k u) end
    | |- rename_brs ?st ?sc (open_brs_wrt_tm_rec ?k ?u ?x) =
         open_brs_wrt_tm_rec ?k (rename_tm ?st ?sc ?u) (rename_brs ?st ?sc ?x) =>
        match goal with H : forall st0 sc0 k0 u0,
          rename_brs st0 sc0 (open_brs_wrt_tm_rec k0 u0 ?x) =
          open_brs_wrt_tm_rec k0 (rename_tm st0 sc0 u0) (rename_brs st0 sc0 ?x) |- _ =>
          exact (H st sc k u) end
    | |- rename_co ?st ?sc (open_co_wrt_tm_rec ?k ?u ?x) =
         open_co_wrt_tm_rec ?k (rename_tm ?st ?sc ?u) (rename_co ?st ?sc ?x) =>
        match goal with H : forall st0 sc0 k0 u0,
          rename_co st0 sc0 (open_co_wrt_tm_rec k0 u0 ?x) =
          open_co_wrt_tm_rec k0 (rename_tm st0 sc0 u0) (rename_co st0 sc0 ?x) |- _ =>
          exact (H st sc k u) end
    | |- rename_constraint ?st ?sc (open_constraint_wrt_tm_rec ?k ?u ?x) =
         open_constraint_wrt_tm_rec ?k (rename_tm ?st ?sc ?u) (rename_constraint ?st ?sc ?x) =>
        match goal with H : forall st0 sc0 k0 u0,
          rename_constraint st0 sc0 (open_constraint_wrt_tm_rec k0 u0 ?x) =
          open_constraint_wrt_tm_rec k0 (rename_tm st0 sc0 u0) (rename_constraint st0 sc0 ?x) |- _ =>
          exact (H st sc k u) end
    end
  | reflexivity
  | (match goal with |- context [lt_eq_lt_dec ?a ?b] =>
       destruct (lt_eq_lt_dec a b) as [[Hlt|Heq]|Hgt];
       cbn [rename_tm]; reflexivity end)
  | (f_equal; rename_open_tm_auto) ].

Lemma rename_open_tm :
  (forall a st sc k u,
     rename_tm st sc (open_tm_wrt_tm_rec k u a) =
     open_tm_wrt_tm_rec k (rename_tm st sc u) (rename_tm st sc a)) /\
  (forall b st sc k u,
     rename_brs st sc (open_brs_wrt_tm_rec k u b) =
     open_brs_wrt_tm_rec k (rename_tm st sc u) (rename_brs st sc b)) /\
  (forall g st sc k u,
     rename_co st sc (open_co_wrt_tm_rec k u g) =
     open_co_wrt_tm_rec k (rename_tm st sc u) (rename_co st sc g)) /\
  (forall phi st sc k u,
     rename_constraint st sc (open_constraint_wrt_tm_rec k u phi) =
     open_constraint_wrt_tm_rec k (rename_tm st sc u) (rename_constraint st sc phi)).
Proof.
  apply (tm_mutind
    (fun a => forall st sc k u,
       rename_tm st sc (open_tm_wrt_tm_rec k u a) =
       open_tm_wrt_tm_rec k (rename_tm st sc u) (rename_tm st sc a))
    (fun b => forall st sc k u,
       rename_brs st sc (open_brs_wrt_tm_rec k u b) =
       open_brs_wrt_tm_rec k (rename_tm st sc u) (rename_brs st sc b))
    (fun g => forall st sc k u,
       rename_co st sc (open_co_wrt_tm_rec k u g) =
       open_co_wrt_tm_rec k (rename_tm st sc u) (rename_co st sc g))
    (fun phi => forall st sc k u,
       rename_constraint st sc (open_constraint_wrt_tm_rec k u phi) =
       open_constraint_wrt_tm_rec k (rename_tm st sc u) (rename_constraint st sc phi))).
  all: intros.
  all: cbn [rename_tm rename_brs rename_co rename_constraint
            open_tm_wrt_tm_rec open_brs_wrt_tm_rec
            open_co_wrt_tm_rec open_constraint_wrt_tm_rec].
  all: try rename_open_tm_auto.
Qed.

Ltac rename_open_co_auto :=
  first
  [ match goal with
    | |- rename_tm ?st ?sc (open_tm_wrt_co_rec ?k ?g ?x) =
         open_tm_wrt_co_rec ?k (rename_co ?st ?sc ?g) (rename_tm ?st ?sc ?x) =>
        match goal with H : forall st0 sc0 k0 g0,
          rename_tm st0 sc0 (open_tm_wrt_co_rec k0 g0 ?x) =
          open_tm_wrt_co_rec k0 (rename_co st0 sc0 g0) (rename_tm st0 sc0 ?x) |- _ =>
          exact (H st sc k g) end
    | |- rename_brs ?st ?sc (open_brs_wrt_co_rec ?k ?g ?x) =
         open_brs_wrt_co_rec ?k (rename_co ?st ?sc ?g) (rename_brs ?st ?sc ?x) =>
        match goal with H : forall st0 sc0 k0 g0,
          rename_brs st0 sc0 (open_brs_wrt_co_rec k0 g0 ?x) =
          open_brs_wrt_co_rec k0 (rename_co st0 sc0 g0) (rename_brs st0 sc0 ?x) |- _ =>
          exact (H st sc k g) end
    | |- rename_co ?st ?sc (open_co_wrt_co_rec ?k ?g ?x) =
         open_co_wrt_co_rec ?k (rename_co ?st ?sc ?g) (rename_co ?st ?sc ?x) =>
        match goal with H : forall st0 sc0 k0 g0,
          rename_co st0 sc0 (open_co_wrt_co_rec k0 g0 ?x) =
          open_co_wrt_co_rec k0 (rename_co st0 sc0 g0) (rename_co st0 sc0 ?x) |- _ =>
          exact (H st sc k g) end
    | |- rename_constraint ?st ?sc (open_constraint_wrt_co_rec ?k ?g ?x) =
         open_constraint_wrt_co_rec ?k (rename_co ?st ?sc ?g) (rename_constraint ?st ?sc ?x) =>
        match goal with H : forall st0 sc0 k0 g0,
          rename_constraint st0 sc0 (open_constraint_wrt_co_rec k0 g0 ?x) =
          open_constraint_wrt_co_rec k0 (rename_co st0 sc0 g0) (rename_constraint st0 sc0 ?x) |- _ =>
          exact (H st sc k g) end
    end
  | reflexivity
  | (match goal with |- context [lt_eq_lt_dec ?a ?b] =>
       destruct (lt_eq_lt_dec a b) as [[Hlt|Heq]|Hgt];
       cbn [rename_co]; reflexivity end)
  | (f_equal; rename_open_co_auto) ].

Lemma rename_open_co :
  (forall a st sc k g,
     rename_tm st sc (open_tm_wrt_co_rec k g a) =
     open_tm_wrt_co_rec k (rename_co st sc g) (rename_tm st sc a)) /\
  (forall b st sc k g,
     rename_brs st sc (open_brs_wrt_co_rec k g b) =
     open_brs_wrt_co_rec k (rename_co st sc g) (rename_brs st sc b)) /\
  (forall g0 st sc k g,
     rename_co st sc (open_co_wrt_co_rec k g g0) =
     open_co_wrt_co_rec k (rename_co st sc g) (rename_co st sc g0)) /\
  (forall phi st sc k g,
     rename_constraint st sc (open_constraint_wrt_co_rec k g phi) =
     open_constraint_wrt_co_rec k (rename_co st sc g) (rename_constraint st sc phi)).
Proof.
  apply (tm_mutind
    (fun a => forall st sc k g,
       rename_tm st sc (open_tm_wrt_co_rec k g a) =
       open_tm_wrt_co_rec k (rename_co st sc g) (rename_tm st sc a))
    (fun b => forall st sc k g,
       rename_brs st sc (open_brs_wrt_co_rec k g b) =
       open_brs_wrt_co_rec k (rename_co st sc g) (rename_brs st sc b))
    (fun g0 => forall st sc k g,
       rename_co st sc (open_co_wrt_co_rec k g g0) =
       open_co_wrt_co_rec k (rename_co st sc g) (rename_co st sc g0))
    (fun phi => forall st sc k g,
       rename_constraint st sc (open_constraint_wrt_co_rec k g phi) =
       open_constraint_wrt_co_rec k (rename_co st sc g) (rename_constraint st sc phi))).
  all: intros.
  all: cbn [rename_tm rename_brs rename_co rename_constraint
            open_tm_wrt_co_rec open_brs_wrt_co_rec
            open_co_wrt_co_rec open_constraint_wrt_co_rec].
  all: try rename_open_co_auto.
Qed.

Lemma rename_open_tm_tm : forall a st sc k u,
  rename_tm st sc (open_tm_wrt_tm_rec k u a) =
  open_tm_wrt_tm_rec k (rename_tm st sc u) (rename_tm st sc a).
Proof. intros; exact (proj1 rename_open_tm a st sc k u). Qed.
Lemma rename_open_tm_brs : forall b st sc k u,
  rename_brs st sc (open_brs_wrt_tm_rec k u b) =
  open_brs_wrt_tm_rec k (rename_tm st sc u) (rename_brs st sc b).
Proof. intros; exact (proj1 (proj2 rename_open_tm) b st sc k u). Qed.
Lemma rename_open_tm_co : forall g st sc k u,
  rename_co st sc (open_co_wrt_tm_rec k u g) =
  open_co_wrt_tm_rec k (rename_tm st sc u) (rename_co st sc g).
Proof. intros; exact (proj1 (proj2 (proj2 rename_open_tm)) g st sc k u). Qed.
Lemma rename_open_tm_constraint : forall phi st sc k u,
  rename_constraint st sc (open_constraint_wrt_tm_rec k u phi) =
  open_constraint_wrt_tm_rec k (rename_tm st sc u) (rename_constraint st sc phi).
Proof. intros; exact (proj2 (proj2 (proj2 rename_open_tm)) phi st sc k u). Qed.

Lemma rename_open_co_tm : forall a st sc k g,
  rename_tm st sc (open_tm_wrt_co_rec k g a) =
  open_tm_wrt_co_rec k (rename_co st sc g) (rename_tm st sc a).
Proof. intros; exact (proj1 rename_open_co a st sc k g). Qed.
Lemma rename_open_co_brs : forall b st sc k g,
  rename_brs st sc (open_brs_wrt_co_rec k g b) =
  open_brs_wrt_co_rec k (rename_co st sc g) (rename_brs st sc b).
Proof. intros; exact (proj1 (proj2 rename_open_co) b st sc k g). Qed.
Lemma rename_open_co_co : forall g0 st sc k g,
  rename_co st sc (open_co_wrt_co_rec k g g0) =
  open_co_wrt_co_rec k (rename_co st sc g) (rename_co st sc g0).
Proof. intros; exact (proj1 (proj2 (proj2 rename_open_co)) g0 st sc k g). Qed.
Lemma rename_open_co_constraint : forall phi st sc k g,
  rename_constraint st sc (open_constraint_wrt_co_rec k g phi) =
  open_constraint_wrt_co_rec k (rename_co st sc g) (rename_constraint st sc phi).
Proof. intros; exact (proj2 (proj2 (proj2 rename_open_co)) phi st sc k g). Qed.

(** Local closedness is invariant under a bijective renaming of free
    variables of either kind. *)

Ltac lc_tm_binder_tm :=
  intro x;
  match goal with
  | |- lc_tm (open_tm_wrt_tm (rename_tm ?st ?sc ?b) (a_Var_f ?x)) =>
      match goal with H : forall y, exists z, ?st z = y |- _ =>
        destruct (H x) as [z Hz];
        match goal with
        | IH : forall y, lc_tm (rename_tm ?st ?sc (open_tm_wrt_tm ?b (a_Var_f y))) |- _ =>
            specialize (IH z); unfold open_tm_wrt_tm in IH;
            rewrite rename_open_tm_tm in IH; cbn [rename_tm] in IH;
            rewrite Hz in IH; exact IH
        end
      end
  end.

Ltac lc_tm_binder_co :=
  intro c;
  match goal with
  | |- lc_tm (open_tm_wrt_co (rename_tm ?st ?sc ?B) (g_Var_f ?c)) =>
      match goal with H : forall y, exists z, ?sc z = y |- _ =>
        destruct (H c) as [d Hd];
        match goal with
        | IH : forall y, lc_tm (rename_tm ?st ?sc (open_tm_wrt_co ?B (g_Var_f y))) |- _ =>
            specialize (IH d); unfold open_tm_wrt_co in IH;
            rewrite rename_open_co_tm in IH; cbn [rename_tm rename_co] in IH;
            rewrite Hd in IH; exact IH
        end
      end
  end.

Ltac lc_co_binder_tm :=
  intro x;
  match goal with
  | |- lc_co (open_co_wrt_tm (rename_co ?st ?sc ?g) (a_Var_f ?x)) =>
      match goal with H : forall y, exists z, ?st z = y |- _ =>
        destruct (H x) as [z Hz];
        match goal with
        | IH : forall y, lc_co (rename_co ?st ?sc (open_co_wrt_tm ?g (a_Var_f y))) |- _ =>
            specialize (IH z); unfold open_co_wrt_tm in IH;
            rewrite rename_open_tm_co in IH; cbn [rename_co rename_tm] in IH;
            rewrite Hz in IH; exact IH
        end
      end
  end.

Ltac lc_co_binder_co :=
  intro c;
  match goal with
  | |- lc_co (open_co_wrt_co (rename_co ?st ?sc ?g) (g_Var_f ?c)) =>
      match goal with H : forall y, exists z, ?sc z = y |- _ =>
        destruct (H c) as [d Hd];
        match goal with
        | IH : forall y, lc_co (rename_co ?st ?sc (open_co_wrt_co ?g (g_Var_f y))) |- _ =>
            specialize (IH d); unfold open_co_wrt_co in IH;
            rewrite rename_open_co_co in IH; cbn [rename_co] in IH;
            rewrite Hd in IH; exact IH
        end
      end
  end.

Lemma lc_rename : forall st sc,
  (forall x, exists y, st y = x) ->
  (forall c, exists d, sc d = c) ->
  (forall a, lc_tm a -> lc_tm (rename_tm st sc a)) /\
  (forall g, lc_co g -> lc_co (rename_co st sc g)) /\
  (forall b, lc_brs b -> lc_brs (rename_brs st sc b)) /\
  (forall phi, lc_constraint phi -> lc_constraint (rename_constraint st sc phi)).
Proof.
  intros st sc Hst Hsc.
  apply (lc_mutind
    (fun a _ => lc_tm (rename_tm st sc a))
    (fun g _ => lc_co (rename_co st sc g))
    (fun b _ => lc_brs (rename_brs st sc b))
    (fun phi _ => lc_constraint (rename_constraint st sc phi))).
  all: intros.
  all: cbn [rename_tm rename_co rename_brs rename_constraint].
  all: try constructor.
  all: try assumption.
  all: try lc_tm_binder_tm.
  all: try lc_tm_binder_co.
  all: try lc_co_binder_tm.
  all: try lc_co_binder_co.
Qed.

(* fvx rename freshness *)
Ltac rename_fresh_cond :=
  intros z Hz;
  match goal with
  | |- ?f z = z =>
      match goal with
      | H : forall y, y `in` ?t -> ?f y = y |- _ =>
          apply H; eauto 15 using AtomSetImpl.union_2, AtomSetImpl.union_3,
                                      AtomSetImpl.singleton_2
      end
  end.

Ltac rename_fresh_solve :=
  first
  [ reflexivity
  | match goal with
    | IH : forall st sc,
        (forall x, x `in` ?s -> st x = x) ->
        (forall c, c `in` ?s -> sc c = c) ->
        rename_tm st sc ?sub = ?sub |- _ =>
        apply (IH st sc); [ rename_fresh_cond | rename_fresh_cond ]
    | IH : forall st sc,
        (forall x, x `in` ?s -> st x = x) ->
        (forall c, c `in` ?s -> sc c = c) ->
        rename_brs st sc ?sub = ?sub |- _ =>
        apply (IH st sc); [ rename_fresh_cond | rename_fresh_cond ]
    | IH : forall st sc,
        (forall x, x `in` ?s -> st x = x) ->
        (forall c, c `in` ?s -> sc c = c) ->
        rename_co st sc ?sub = ?sub |- _ =>
        apply (IH st sc); [ rename_fresh_cond | rename_fresh_cond ]
    | IH : forall st sc,
        (forall x, x `in` ?s -> st x = x) ->
        (forall c, c `in` ?s -> sc c = c) ->
        rename_constraint st sc ?sub = ?sub |- _ =>
        apply (IH st sc); [ rename_fresh_cond | rename_fresh_cond ]
    end
  | match goal with
    | |- ?f ?x = ?x =>
        match goal with
        | H : forall y, y `in` ?t -> ?f y = y |- _ =>
            apply H; cbn [fvx_tm fvx_brs fvx_co fvx_constraint];
            eauto 10 using AtomSetImpl.singleton_2
        end
    end
  | (f_equal; rename_fresh_solve) ].

Lemma rename_fresh :
  (forall a st sc,
     (forall x, x `in` fvx_tm a -> st x = x) ->
     (forall c, c `in` fvx_tm a -> sc c = c) ->
     rename_tm st sc a = a) /\
  (forall b st sc,
     (forall x, x `in` fvx_brs b -> st x = x) ->
     (forall c, c `in` fvx_brs b -> sc c = c) ->
     rename_brs st sc b = b) /\
  (forall g st sc,
     (forall x, x `in` fvx_co g -> st x = x) ->
     (forall c, c `in` fvx_co g -> sc c = c) ->
     rename_co st sc g = g) /\
  (forall phi st sc,
     (forall x, x `in` fvx_constraint phi -> st x = x) ->
     (forall c, c `in` fvx_constraint phi -> sc c = c) ->
     rename_constraint st sc phi = phi).
Proof.
  apply (tm_mutind
    (fun a => forall st sc,
       (forall x, x `in` fvx_tm a -> st x = x) ->
       (forall c, c `in` fvx_tm a -> sc c = c) ->
       rename_tm st sc a = a)
    (fun b => forall st sc,
       (forall x, x `in` fvx_brs b -> st x = x) ->
       (forall c, c `in` fvx_brs b -> sc c = c) ->
       rename_brs st sc b = b)
    (fun g => forall st sc,
       (forall x, x `in` fvx_co g -> st x = x) ->
       (forall c, c `in` fvx_co g -> sc c = c) ->
       rename_co st sc g = g)
    (fun phi => forall st sc,
       (forall x, x `in` fvx_constraint phi -> st x = x) ->
       (forall c, c `in` fvx_constraint phi -> sc c = c) ->
       rename_constraint st sc phi = phi)).
  all: intros.
  all: cbn [rename_tm rename_brs rename_co rename_constraint
            fvx_tm fvx_brs fvx_co fvx_constraint].
  all: try rename_fresh_solve.
Qed.

(* swap *)
(** The transposition of two variables, and its elementary properties. *)

Definition sw (x y z:var) : var :=
  if eq_var z x then y else if eq_var z y then x else z.

Lemma sw_same : forall x y, sw x y x = y.
Proof. intros; unfold sw; rewrite eq_var_true'; reflexivity. Qed.

Lemma sw_same' : forall x y, x <> y -> sw x y y = x.
Proof.
  intros x y Hxy. unfold sw.
  assert (He : eq_var y x = false).
  { unfold eq_var. destruct (KeySetFacts.eq_dec y x) as [Heq|Hneq].
    - exfalso. apply Hxy. symmetry. exact Heq.
    - reflexivity. }
  rewrite He. rewrite eq_var_true'. reflexivity.
Qed.

Lemma sw_fix : forall x y z, z <> x -> z <> y -> sw x y z = z.
Proof.
  intros x y z Hx Hy. unfold sw.
  destruct (eq_var z x) eqn:Ex.
  - exfalso. apply Hx. apply eq_var_true. exact Ex.
  - destruct (eq_var z y) eqn:Ey.
    + exfalso. apply Hy. apply eq_var_true. exact Ey.
    + reflexivity.
Qed.

Lemma sw_surj : forall x y, x <> y -> forall z, exists w, sw x y w = z.
Proof.
  intros x y Hxy z.
  destruct (KeySetFacts.eq_dec z x) as [->|Hzx].
  - exists y. apply sw_same'. exact Hxy.
  - destruct (KeySetFacts.eq_dec z y) as [->|Hzy].
    + exists x. apply sw_same.
    + exists z. apply sw_fix; assumption.
Qed.

(** G: renaming the free variable used to open a locally closed term does
    not affect local closedness, provided both names are fresh for the
    opened body. *)

Check lc_rename.
Check rename_fresh.
Check rename_open_tm.
Check rename_open_co.

Lemma rename_tm_erase_FixDef : forall st sc,
  rename_tm st sc (erase_tm FixDef) = erase_tm FixDef.
Proof. intros. vm_compute. reflexivity. Qed.

Lemma rename_tm_erase_FixTy : forall st sc,
  rename_tm st sc (erase_tm FixTy) = erase_tm FixTy.
Proof. intros. vm_compute. reflexivity. Qed.

Lemma toplevel_binds_eq : forall (F:tyfam) (a A:tm),
  binds F (Ax a A) toplevel ->
  F = Fix /\ a = erase_tm FixDef /\ A = erase_tm FixTy.
Proof.
  intros F a A H.
  unfold toplevel, an_toplevel, erase_sig in H. simpl in H.
  destruct H as [Heq | Hnil].
  - inversion Heq. subst. repeat split; reflexivity.
  - contradiction.
Qed.


Lemma Par_rename_L : forall E st sc,
  (forall x, x `notin` E -> st x = x) ->
  (forall c, c `notin` E -> sc c = c) ->
  (forall x, exists y, st y = x) ->
  (forall c, exists d, sc d = c) ->
  forall G D a b, Par G D a b ->
    Par G D (rename_tm st sc a) (rename_tm st sc b).
Proof.
  intros E st sc HstE HscE Hst Hsc G D a b H.
  revert H.
  apply (Par_ind
    (fun G D a b => Par G D (rename_tm st sc a) (rename_tm st sc b))).
  - intros G0 D0 a0 Hl. cbn [rename_tm]. apply Par_Refl.
    exact (proj1 (lc_rename st sc Hst Hsc) a0 Hl).
  - intros G0 D0 a0 rho b0 a' b' Hfa IHfa Harg IHarg.
    cbn [rename_tm].
    unfold open_tm_wrt_tm.
    rewrite rename_open_tm_tm.
    cbn [rename_tm].
    eapply Par_Beta; [exact IHfa | exact IHarg].
  - intros G0 D0 a0 rho b0 a' b' Hfa IHfa Harg IHarg.
    cbn [rename_tm]. apply Par_App; assumption.
  - intros G0 D0 a0 a' Hfa IHfa.
    cbn [rename_tm].
    unfold open_tm_wrt_co.
    rewrite rename_open_co_tm.
    cbn [rename_tm].
    apply Par_CBeta. exact IHfa.
  - intros G0 D0 a0 a' Hfa IHfa.
    cbn [rename_tm]. apply Par_CApp. exact IHfa.
  - intros L G0 D0 rho a0 a' Hbody IHbody.
    cbn [rename_tm].
    refine (Par_Abs (L \u E) G0 D0 rho (rename_tm st sc a0) (rename_tm st sc a') _).
    intros y Hy.
    assert (HyL : y `notin` L) by (apply notin_union_1 in Hy; exact Hy).
    assert (HyE : y `notin` E) by (apply notin_union_2 in Hy; exact Hy).
    specialize (IHbody y HyL).
    unfold open_tm_wrt_tm in IHbody.
    rewrite !rename_open_tm_tm in IHbody.
    cbn [rename_tm] in IHbody.
    rewrite (HstE y HyE) in IHbody.
    exact IHbody.
  - intros L G0 D0 rho A B A' B' HA IHA HB IHB.
    cbn [rename_tm].
    refine (Par_Pi (L \u E) G0 D0 rho (rename_tm st sc A) (rename_tm st sc B)
              (rename_tm st sc A') (rename_tm st sc B') IHA _).
    intros x Hx.
    assert (HxL : x `notin` L) by (apply notin_union_1 in Hx; exact Hx).
    assert (HxE : x `notin` E) by (apply notin_union_2 in Hx; exact Hx).
    specialize (IHB x HxL).
    unfold open_tm_wrt_tm in IHB.
    rewrite !rename_open_tm_tm in IHB.
    cbn [rename_tm] in IHB.
    rewrite (HstE x HxE) in IHB.
    exact IHB.
  - intros L G0 D0 a0 a' Hbody IHbody.
    cbn [rename_tm].
    refine (Par_CAbs (L \u E) G0 D0 (rename_tm st sc a0) (rename_tm st sc a') _).
    intros c Hc.
    assert (HcL : c `notin` L) by (apply notin_union_1 in Hc; exact Hc).
    assert (HcE : c `notin` E) by (apply notin_union_2 in Hc; exact Hc).
    specialize (IHbody c HcL).
    unfold open_tm_wrt_co in IHbody.
    rewrite !rename_open_co_tm in IHbody.
    cbn [rename_tm rename_co] in IHbody.
    rewrite (HscE c HcE) in IHbody.
    exact IHbody.
  - intros L G0 D0 A B A1 a0 A' B' A1' a' HA IHA HB IHB Hbody IHbody HA1 IHA1.
    cbn [rename_tm].
    refine (Par_CPi (L \u E) G0 D0 (rename_tm st sc A) (rename_tm st sc B)
              (rename_tm st sc A1) (rename_tm st sc a0)
              (rename_tm st sc A') (rename_tm st sc B')
              (rename_tm st sc A1') (rename_tm st sc a') IHA IHB _ IHA1).
    intros c Hc.
    assert (HcL : c `notin` L) by (apply notin_union_1 in Hc; exact Hc).
    assert (HcE : c `notin` E) by (apply notin_union_2 in Hc; exact Hc).
    specialize (IHbody c HcL).
    unfold open_tm_wrt_co in IHbody.
    rewrite !rename_open_co_tm in IHbody.
    cbn [rename_tm rename_co] in IHbody.
    rewrite (HscE c HcE) in IHbody.
    exact IHbody.
  - intros G0 D0 F a0 A0 Hbinds.
    cbn [rename_tm].
    destruct (toplevel_binds_eq F a0 A0 Hbinds) as [HF [Ha HA]].
    subst F a0 A0.
    rewrite rename_tm_erase_FixDef.
    exact (Par_Axiom G0 D0 Fix (erase_tm FixDef) (erase_tm FixTy) Hbinds).
Qed.

Definition idv (z:atom) : atom := z.

Lemma open_close_rename_tm :
  (forall a k x y, clt_tm k a -> y `notin` fvx_tm a ->
     open_tm_wrt_tm_rec k (a_Var_f y) (close_tm x k a)
     = rename_tm (sw x y) idv a) /\
  (forall b k x y, clt_brs k b -> y `notin` fvx_brs b ->
     open_brs_wrt_tm_rec k (a_Var_f y) (close_tm_brs x k b)
     = rename_brs (sw x y) idv b) /\
  (forall g k x y, clt_co k g -> y `notin` fvx_co g ->
     open_co_wrt_tm_rec k (a_Var_f y) (close_tm_co x k g)
     = rename_co (sw x y) idv g) /\
  (forall p k x y, clt_constraint k p -> y `notin` fvx_constraint p ->
     open_constraint_wrt_tm_rec k (a_Var_f y) (close_tm_constraint x k p)
     = rename_constraint (sw x y) idv p).
Proof.
  apply (tm_mutind
    (fun a => forall k x y, clt_tm k a -> y `notin` fvx_tm a ->
       open_tm_wrt_tm_rec k (a_Var_f y) (close_tm x k a) =
       rename_tm (sw x y) idv a)
    (fun b => forall k x y, clt_brs k b -> y `notin` fvx_brs b ->
       open_brs_wrt_tm_rec k (a_Var_f y) (close_tm_brs x k b) =
       rename_brs (sw x y) idv b)
    (fun g => forall k x y, clt_co k g -> y `notin` fvx_co g ->
       open_co_wrt_tm_rec k (a_Var_f y) (close_tm_co x k g) =
       rename_co (sw x y) idv g)
    (fun p => forall k x y, clt_constraint k p -> y `notin` fvx_constraint p ->
       open_constraint_wrt_tm_rec k (a_Var_f y) (close_tm_constraint x k p) =
       rename_constraint (sw x y) idv p)).
  all: intros.
  all: cbn [close_tm close_tm_brs close_tm_co close_tm_constraint
            open_tm_wrt_tm_rec open_brs_wrt_tm_rec open_co_wrt_tm_rec
            open_constraint_wrt_tm_rec
            rename_tm rename_brs rename_co rename_constraint
            fvx_tm fvx_brs fvx_co fvx_constraint
            clt_tm clt_brs clt_co clt_constraint] in *.
  all: try (repeat match goal with H : _ /\ _ |- _ => destruct H end).
  all: try reflexivity.
  all: try (repeat break_lt; try reflexivity; try (exfalso; lia)).
  all: try (match goal with
    | Hnot : ?y `notin` singleton ?a |-
        open_tm_wrt_tm_rec ?k (a_Var_f ?y)
          (if KeySetFacts.eq_dec ?a ?v then a_Var_b ?k else a_Var_f ?a)
        = a_Var_f (sw ?v ?y ?a) =>
        destruct (KeySetFacts.eq_dec a v) as [Heq|Hne];
        [ subst v; cbn [open_tm_wrt_tm_rec];
          destruct (lt_eq_lt_dec k k) as [[Hlt|Heqk]|Hgt]; try lia;
          cbn [open_tm_wrt_tm_rec]; rewrite sw_same; reflexivity
        | cbn [open_tm_wrt_tm_rec]; rewrite (sw_fix v y a);
          [reflexivity
          | exact Hne
          | intro Hay; apply (notin_singleton_1 a y Hnot); exact Hay] ]
    end).
  all: try (f_equal; eauto).
Qed.



(* ===================== Context inclusion and D-monotonicity ===================== *)

Lemma in_dom_binds : forall (A:Type) (x:atom) (E:list (atom*A)),
  x `in` dom E -> exists a, binds x a E.
Proof.
  intros A x E. induction E as [|[y b] E IH]; intro H.
  - cbn [dom] in H. apply AtomSetFacts.empty_iff in H. contradiction.
  - cbn [dom] in H. apply AtomSetFacts.add_iff in H. destruct H as [Heq|Hin].
    + exists b. subst x. apply binds_cons_iff. left. auto.
    + destruct (IH Hin) as [a Ha]. exists a. apply binds_cons_iff. right. exact Ha.
Qed.

Definition ctx_sub (G G':context) := forall x s, binds x s G -> binds x s G'.

Lemma ctx_sub_refl : forall G, ctx_sub G G.
Proof. intros G x s H; exact H. Qed.

Lemma ctx_sub_cons : forall G G' x s, ctx_sub G G' -> ctx_sub ((x,s)::G) ((x,s)::G').
Proof.
  intros G G' x s H y t Hb. apply binds_cons_iff in Hb. apply binds_cons_iff.
  destruct Hb as [[Heq Hs]|Hb]; [left; auto | right; apply H; exact Hb].
Qed.

Lemma dom_sub : forall G G', ctx_sub G G' -> forall x, x `in` dom G -> x `in` dom G'.
Proof.
  intros G G' Hsub x Hx. destruct (@in_dom_binds sort x G Hx) as [s Hs].
  apply binds_In with (a:=s). apply Hsub. exact Hs.
Qed.

Definition Dsub (D D':available_props) := forall x, x `in` D -> x `in` D'.

Lemma Dsub_refl : forall D, Dsub D D.
Proof. intros D x H; exact H. Qed.
Lemma Dsub_trans : forall D1 D2 D3, Dsub D1 D2 -> Dsub D2 D3 -> Dsub D1 D3.
Proof. intros D1 D2 D3 H1 H2 x Hx. apply H2, H1, Hx. Qed.
Lemma Dsub_union_l : forall D D', Dsub D (D \u D').
Proof. intros D D' x H. apply AtomSetFacts.union_iff; auto. Qed.
Lemma Dsub_union_r : forall D D', Dsub D' (D \u D').
Proof. intros D D' x H. apply AtomSetFacts.union_iff; right; auto. Qed.
Lemma Dsub_add : forall D D' x, Dsub D D' -> Dsub D (add x D').
Proof. intros D D' x H y Hy. apply AtomSetFacts.add_iff; right; auto. Qed.

Lemma Dmono_all :
  (forall G D D' g a b, Dsub D D' -> AnnDefEq G D g a b -> AnnDefEq G D' g a b) /\
  (forall G D D' g p q, Dsub D D' -> AnnIso G D g p q -> AnnIso G D' g p q).
Proof.
  assert (Hc : (forall G a A (H:AnnTyping G a A), True) /\
    (forall G phi (H:AnnPropWff G phi), True) /\
    (forall G D g p q (H:AnnIso G D g p q), forall D', Dsub D D' -> AnnIso G D' g p q) /\
    (forall G D g a b (H:AnnDefEq G D g a b), forall D', Dsub D D' -> AnnDefEq G D' g a b) /\
    (forall G (H:AnnCtx G), True) /\
    (forall S (H:AnnSig S), True)).
  { apply (AnnTyping_comb
      (fun _ _ _ _ => True) (fun _ _ _ => True)
      (fun G D g p q _ => forall D', Dsub D D' -> AnnIso G D' g p q)
      (fun G D g a b _ => forall D', Dsub D D' -> AnnDefEq G D' g a b)
      (fun _ _ => True) (fun _ _ => True)).
    all: try solve [intros; exact I].
    all: try solve [intros D' Hs; econstructor; eauto 25].
    all: try solve [intros D' Hs; eapply An_Assn; eauto; apply Hs; eauto].
    all: try solve [intros D' Hs; econstructor; eauto 25; apply Dsub_refl].
  }
  destruct Hc as [_ [_ [Hiso [Hdef _]]]].
  split.
  - intros G D D' g a b Hs H. exact (Hdef G D g a b H D' Hs).
  - intros G D D' g p q Hs H. exact (Hiso G D g p q H D' Hs).
Qed.
Import ListNotations.

(* ============================================================ *)
(* Part A: every annotation judgment has a well-formed context   *)
(* ============================================================ *)

Lemma AnnTyping_AnnCtx_all :
  (forall G a A, AnnTyping G a A -> AnnCtx G) /\
  (forall G p, AnnPropWff G p -> AnnCtx G) /\
  (forall G D g p q, AnnIso G D g p q -> AnnCtx G) /\
  (forall G D g a b, AnnDefEq G D g a b -> AnnCtx G) /\
  (forall G, AnnCtx G -> AnnCtx G) /\
  (forall S, AnnSig S -> True).
Proof.
  apply AnnTyping_comb; intros; try solve [eauto 9].
  all: try apply An_Empty.
  all: try (eapply An_ConsTm; eauto 9).
  all: try (eapply An_ConsCo; eauto 9).
  all: try (econstructor; eauto 9).
Qed.

Lemma AnnTyping_AnnCtx : forall G a A, AnnTyping G a A -> AnnCtx G.
Proof. intros. exact (proj1 AnnTyping_AnnCtx_all G a A H). Qed.

Lemma AnnPropWff_AnnCtx : forall G p, AnnPropWff G p -> AnnCtx G.
Proof. intros. exact (proj1 (proj2 AnnTyping_AnnCtx_all) G p H). Qed.

Lemma AnnIso_AnnCtx : forall G D g p q, AnnIso G D g p q -> AnnCtx G.
Proof. intros. exact (proj1 (proj2 (proj2 AnnTyping_AnnCtx_all)) G D g p q H). Qed.

Lemma AnnDefEq_AnnCtx : forall G D g a b, AnnDefEq G D g a b -> AnnCtx G.
Proof. intros. exact (proj1 (proj2 (proj2 (proj2 AnnTyping_AnnCtx_all))) G D g a b H). Qed.


Lemma AnnTyping_pi_dom : forall G rho A B,
  AnnTyping G (a_Pi rho A B) a_Star -> AnnTyping G A a_Star.
Proof. intros G rho A B H. inversion H; subst; assumption. Qed.

Lemma AnnTyping_cpi_wff : forall G phi B,
  AnnTyping G (a_CPi phi B) a_Star -> AnnPropWff G phi.
Proof. intros G phi B H. inversion H; subst; assumption. Qed.

Lemma AnnTyping_cabs_wff : forall G phi b T,
  AnnTyping G (a_CAbs phi b) T -> AnnPropWff G phi.
Proof. intros G phi b T H. inversion H; subst; assumption. Qed.

Lemma ctx_sub_nil : forall G, ctx_sub nil G.
Proof. intros G x s H. inversion H. Qed.

Lemma AnnDefEq_Dmono : forall G D D' g a b,
  Dsub D D' -> AnnDefEq G D g a b -> AnnDefEq G D' g a b.
Proof. exact (proj1 Dmono_all). Qed.

Lemma AnnIso_Dmono : forall G D D' g p q,
  Dsub D D' -> AnnIso G D g p q -> AnnIso G D' g p q.
Proof. exact (proj2 Dmono_all). Qed.

Lemma Ann_weaken_all :
  (forall G a A (H:AnnTyping G a A),
     forall G', ctx_sub G G' -> AnnCtx G' -> AnnTyping G' a A) /\
  (forall G p (H:AnnPropWff G p),
     forall G', ctx_sub G G' -> AnnCtx G' -> AnnPropWff G' p) /\
  (forall G D g p q (H:AnnIso G D g p q),
     forall G', ctx_sub G G' -> AnnCtx G' -> AnnIso G' D g p q) /\
  (forall G D g a b (H:AnnDefEq G D g a b),
     forall G', ctx_sub G G' -> AnnCtx G' -> AnnDefEq G' D g a b) /\
  (forall G (H:AnnCtx G), True) /\
  (forall S (H:AnnSig S), True).
Proof.
  apply (AnnTyping_comb
    (fun G a A _ => forall G', ctx_sub G G' -> AnnCtx G' -> AnnTyping G' a A)
    (fun G p _ => forall G', ctx_sub G G' -> AnnCtx G' -> AnnPropWff G' p)
    (fun G D g p q _ => forall G', ctx_sub G G' -> AnnCtx G' -> AnnIso G' D g p q)
    (fun G D g a b _ => forall G', ctx_sub G G' -> AnnCtx G' -> AnnDefEq G' D g a b)
    (fun G _ => True)
    (fun S _ => True)).
  (* An_Star *)
  - intros G a IHctx G' Hsub Hctx. apply An_Star. exact Hctx.
  (* An_Var *)
  - intros G x A a IHctx b G' Hsub Hctx. apply An_Var.
    + exact Hctx.
    + exact (Hsub x (Tm A) b).
  (* An_Pi *)
  - intros L G rho A B body IHbody a0 IH0 G' Hsub Hctx.
    apply (An_Pi (L \u dom G') G' rho A B).
    + intros x Hx. apply notin_union_elim in Hx. destruct Hx as [HxL Hxdom].
      apply IHbody; [exact HxL | apply ctx_sub_cons; exact Hsub |].
      apply An_ConsTm; [exact Hctx | apply IH0; assumption | exact Hxdom].
    + apply IH0; assumption.
  (* An_Abs *)
  - intros L G rho A a B a0 IH0 a1 IH1 r G' Hsub Hctx.
    apply (An_Abs (L \u dom G') G' rho A a B).
    + apply IH0; assumption.
    + intros x Hx. apply notin_union_elim in Hx. destruct Hx as [HxL Hxdom].
      apply IH1; [exact HxL | apply ctx_sub_cons; exact Hsub |].
      apply An_ConsTm; [exact Hctx | apply IH0; assumption | exact Hxdom].
    + intros x Hx. apply r. apply notin_union_elim in Hx. tauto.
  (* An_App *)
  - intros G b rho a B A a0 IH0 a1 IH1 G' Hsub Hctx.
    apply (An_App G' b rho a B A); [apply IH0; assumption | apply IH1; assumption].
  (* An_Conv *)
  - intros G a g B A a0 IH0 a1 IHdef a2 IH2 G' Hsub Hctx.
    apply (An_Conv G' a g B A).
    + apply IH0; assumption.
    + apply (AnnDefEq_Dmono G' (dom G) (dom G') g A B).
      * intros x Hx. exact (dom_sub G G' Hsub x Hx).
      * apply IHdef; assumption.
    + apply IH2; assumption.
  (* An_CPi *)
  - intros L G phi B a IHprop a0 IHbody G' Hsub Hctx.
    apply (An_CPi (L \u dom G') G' phi B).
    + apply IHprop; assumption.
    + intros c Hc. apply notin_union_elim in Hc. destruct Hc as [HcL Hcdom].
      apply IHbody; [exact HcL | apply ctx_sub_cons; exact Hsub |].
      apply An_ConsCo; [exact Hctx | apply IHprop; assumption | exact Hcdom].
  (* An_CAbs *)
  - intros L G phi a B a0 IHprop a1 IHbody G' Hsub Hctx.
    apply (An_CAbs (L \u dom G') G' phi a B).
    + apply IHprop; assumption.
    + intros c Hc. apply notin_union_elim in Hc. destruct Hc as [HcL Hcdom].
      apply IHbody; [exact HcL | apply ctx_sub_cons; exact Hsub |].
      apply An_ConsCo; [exact Hctx | apply IHprop; assumption | exact Hcdom].
  (* An_CApp *)
  - intros G a1 g B a b A1 a0 IH0 a1' IHdef G' Hsub Hctx.
    apply (An_CApp G' a1 g B a b A1).
    + apply IH0; assumption.
    + apply (AnnDefEq_Dmono G' (dom G) (dom G') g a b).
      * intros x Hx. exact (dom_sub G G' Hsub x Hx).
      * apply IHdef; assumption.
  (* An_Fam *)
  - intros G F A a ctx IHctx b a1 IH1 G' Hsub Hctx.
    apply (An_Fam G' F A a).
    + exact Hctx.
    + exact b.
    + exact a1.
  (* An_Wff *)
  - intros G a b A B a0 IH0 a1 IH1 Heq G' Hsub Hctx.
    apply (An_Wff G' a b A B).
    + apply IH0; assumption.
    + apply IH1; assumption.
    + exact Heq.
  (* An_PropCong *)
  - intros G D g1 A g2 A1 B1 A2 B2 a0 IH0 a1 IH1 a2 IH2 a3 IH3
           G' Hsub Hctx.
    apply (An_PropCong G' D g1 A g2 A1 B1 A2 B2).
    + apply IH0; assumption.
    + apply IH1; assumption.
    + apply IH2; assumption.
    + apply IH3; assumption.
  (* An_CPiFst *)
  - intros G D g phi1 phi2 A2 B2 a0 IH0 G' Hsub Hctx.
    apply (An_CPiFst G' D g phi1 phi2 A2 B2). apply IH0; assumption.
  (* An_IsoSym *)
  - intros G D g phi2 phi1 a0 IH0 G' Hsub Hctx.
    apply (An_IsoSym G' D g phi2 phi1). apply IH0; assumption.
  (* An_IsoConv *)
  - intros G D a1 a2 A a1' a2' B g a0 IH0 a1'' IH1 a2'' IH2 Heq1 Heq2
           G' Hsub Hctx.
    apply (An_IsoConv G' D a1 a2 A a1' a2' B g).
    + apply IH0; assumption.
    + apply IH1; assumption.
    + apply IH2; assumption.
    + exact Heq1.
    + exact Heq2.
  (* An_Assn *)
  - intros G D c a b A a0 IHctx b0 Hin G' Hsub Hctx.
    apply (An_Assn G' D c a b A).
    + exact Hctx.
    + exact (Hsub c (Co (Eq a b A)) b0).
    + exact Hin.
  (* An_Refl *)
  - intros G D a A a0 IH0 G' Hsub Hctx.
    apply (An_Refl G' D a A). apply IH0; assumption.
  (* An_EraseEq *)
  - intros G D a b g A B a0 IH0 a1 IH1 Heq a2 IH2 G' Hsub Hctx.
    apply (An_EraseEq G' D a b g A B).
    + apply IH0; assumption.
    + apply IH1; assumption.
    + exact Heq.
    + apply (AnnDefEq_Dmono G' (dom G) (dom G') g A B).
      * intros x Hx. exact (dom_sub G G' Hsub x Hx).
      * apply IH2; assumption.
  (* An_Sym *)
  - intros G D g a b B A g1 a0 IH0 a1 IH1 a2 IH2 a3 IH3 G' Hsub Hctx.
    apply (An_Sym G' D g a b B A g1).
    + apply IH0; assumption.
    + apply IH1; assumption.
    + apply (AnnDefEq_Dmono G' (dom G) (dom G') g1 B A).
      * intros x Hx. exact (dom_sub G G' Hsub x Hx).
      * apply IH2; assumption.
    + apply IH3; assumption.
  (* An_Trans *)
  - intros G D g1 g2 a b a1 A A1 g3 a0 IH0 a1' IH1 a2 IH2 a3 IH3 a4 IH4
           G' Hsub Hctx.
    apply (An_Trans G' D g1 g2 a b a1 A A1 g3).
    + apply IH0; assumption.
    + apply IH1; assumption.
    + apply IH2; assumption.
    + apply IH3; assumption.
    + apply (AnnDefEq_Dmono G' (dom G) (dom G') g3 A A1).
      * intros x Hx. exact (dom_sub G G' Hsub x Hx).
      * apply IH4; assumption.
  (* An_Beta *)
  - intros G D a1 a2 B0 B1 a0 IH0 a1' IH1 Heq HB G' Hsub Hctx.
    apply (An_Beta G' D a1 a2 B0 B1).
    + apply IH0; assumption.
    + apply IH1; assumption.
    + exact Heq.
    + exact HB.
  (* An_PiCong *)
  - intros L G D rho g1 g2 A1 B1 A2 B3 B2 a0 IH0 a1 IH1 Heq
           a3 IH3 a4 IH4 a5 IH5 G' Hsub Hctx.
    apply (An_PiCong (L \u dom G') G' D rho g1 g2 A1 B1 A2 B3 B2).
    + apply IH0; assumption.
    + intros x Hx. apply notin_union_elim in Hx. destruct Hx as [HxL Hxdom].
      apply IH1; [exact HxL | apply ctx_sub_cons; exact Hsub |].
      apply An_ConsTm; [exact Hctx | | exact Hxdom].
      exact (AnnTyping_pi_dom G' rho A1 B1 (IH3 G' Hsub Hctx)).
    + intros x Hx. apply Heq. apply notin_union_elim in Hx. tauto.
    + apply IH3; assumption.
    + apply IH4; assumption.
    + apply IH5; assumption.
  (* An_AbsCong *)
  - intros L G D rho g1 g2 A1 b1 A2 b3 b2 B a0 IH0 a1 IH1 Heq
           a3 IH3 a4 IH4 a5 a6 a7 IH7 G' Hsub Hctx.
    apply (An_AbsCong (L \u dom G') G' D rho g1 g2 A1 b1 A2 b3 b2 B).
    + apply IH0; assumption.
    + intros x Hx. apply notin_union_elim in Hx. destruct Hx as [HxL Hxdom].
      apply IH1; [exact HxL | apply ctx_sub_cons; exact Hsub |].
      apply An_ConsTm; [exact Hctx | apply IH3; assumption | exact Hxdom].
    + intros x Hx. apply Heq. apply notin_union_elim in Hx. tauto.
    + apply IH3; assumption.
    + apply IH4; assumption.
    + intros x Hx. apply a5. apply notin_union_elim in Hx. tauto.
    + intros x Hx. apply a6. apply notin_union_elim in Hx. tauto.
    + apply IH7; assumption.
  (* An_AppCong *)
  - intros G D g1 rho g2 ta1 ta2 tb1 tb2 A B g3 a0 IH0 a1' IH1 a2 IH2 a3 IH3
           a4 IH4 G' Hsub Hctx.
    apply (An_AppCong G' D g1 rho g2 ta1 ta2 tb1 tb2 A B g3).
    + apply IH0; assumption.
    + apply IH1; assumption.
    + apply IH2; assumption.
    + apply IH3; assumption.
    + apply (AnnDefEq_Dmono G' (dom G) (dom G') g3 A B).
      * intros x Hx. exact (dom_sub G G' Hsub x Hx).
      * apply IH4; assumption.
  (* An_PiFst *)
  - intros G D g A1 A2 rho B1 B2 a0 IH0 G' Hsub Hctx.
    apply (An_PiFst G' D g A1 A2 rho B1 B2). apply IH0; assumption.
  (* An_PiSnd *)
  - intros G D g1 g2 B1 a1 B2 a2 rho A1 A2 a0 IH0 a1' IH1 a2' IH2 a3 IH3
           G' Hsub Hctx.
    apply (An_PiSnd G' D g1 g2 B1 a1 B2 a2 rho A1 A2).
    + apply IH0; assumption.
    + apply IH1; assumption.
    + apply IH2; assumption.
    + apply IH3; assumption.
  (* An_CPiCong *)
  - intros L G D g1 g3 phi1 B1 phi2 B3 B2 a0 IH0 a1 IH1 Heq
           a3 IH3 a4 IH4 a5 IH5 G' Hsub Hctx.
    apply (An_CPiCong (L \u dom G') G' D g1 g3 phi1 B1 phi2 B3 B2).
    + apply IH0; assumption.
    + intros c Hc. apply notin_union_elim in Hc. destruct Hc as [HcL Hcdom].
      apply IH1; [exact HcL | apply ctx_sub_cons; exact Hsub |].
      apply An_ConsCo; [exact Hctx | | exact Hcdom].
      exact (AnnTyping_cpi_wff G' phi1 B1 (IH3 G' Hsub Hctx)).
    + intros x Hx. apply Heq. apply notin_union_elim in Hx. tauto.
    + apply IH3; assumption.
    + apply IH4; assumption.
    + apply IH5; assumption.
  (* An_CAbsCong *)
  - intros L G D g1 g3 g4 phi1 a1 phi2 a3 a2 B1 B B2 a0 IH0 a1' IH1 Heq
           a3' IH3 a4 IH4 a5 IH5 a6 IH6 G' Hsub Hctx.
    apply (An_CAbsCong (L \u dom G') G' D g1 g3 g4 phi1 a1 phi2 a3 a2 B1 B B2).
    + apply IH0; assumption.
    + intros c Hc. apply notin_union_elim in Hc. destruct Hc as [HcL Hcdom].
      apply IH1; [exact HcL | apply ctx_sub_cons; exact Hsub |].
      apply An_ConsCo; [exact Hctx | | exact Hcdom].
      exact (AnnTyping_cabs_wff G' phi1 a1 (a_CPi phi1 B1) (IH3 G' Hsub Hctx)).
    + intros x Hx. apply Heq. apply notin_union_elim in Hx. tauto.
    + apply IH3; assumption.
    + apply IH4; assumption.
    + apply IH5; assumption.
    + apply (AnnDefEq_Dmono G' (dom G) (dom G') g4 (a_CPi phi1 B1) (a_CPi phi2 B2)).
      * intros x Hx. exact (dom_sub G G' Hsub x Hx).
      * apply IH6; assumption.
  (* An_CAppCong *)
  - intros G D g1 g2 g3 a1 b1 a2 b2 a3 b3 A B g4 a0 IH0 a1' IH1 a2' IH2
           a3' IH3 a4 IH4 a5 IH5 G' Hsub Hctx.
    apply (An_CAppCong G' D g1 g2 g3 a1 b1 a2 b2 a3 b3 A B g4).
    + apply IH0; assumption.
    + apply (AnnDefEq_Dmono G' (dom G) (dom G') g2 a2 b2).
      * intros x Hx. exact (dom_sub G G' Hsub x Hx).
      * apply IH1; assumption.
    + apply (AnnDefEq_Dmono G' (dom G) (dom G') g3 a3 b3).
      * intros x Hx. exact (dom_sub G G' Hsub x Hx).
      * apply IH2; assumption.
    + apply IH3; assumption.
    + apply IH4; assumption.
    + apply (AnnDefEq_Dmono G' (dom G) (dom G') g4 A B).
      * intros x Hx. exact (dom_sub G G' Hsub x Hx).
      * apply IH5; assumption.
  (* An_CPiSnd *)
  - intros G D g1 g2 g3 B1 B2 a a' A b b' B a0 IH0 a1 IH1 a2 IH2
           G' Hsub Hctx.
    apply (An_CPiSnd G' D g1 g2 g3 B1 B2 a a' A b b' B).
    + apply IH0; assumption.
    + apply (AnnDefEq_Dmono G' (dom G) (dom G') g2 a a').
      * intros x Hx. exact (dom_sub G G' Hsub x Hx).
      * apply IH1; assumption.
    + apply (AnnDefEq_Dmono G' (dom G) (dom G') g3 b b').
      * intros x Hx. exact (dom_sub G G' Hsub x Hx).
      * apply IH2; assumption.
  (* An_Cast *)
  - intros G D g1 g2 b b' a a' A B a0 IH0 a1 IH1 G' Hsub Hctx.
    apply (An_Cast G' D g1 g2 b b' a a' A B).
    + apply IH0; assumption.
    + apply IH1; assumption.
  (* An_IsoSnd *)
  - intros G D g A B a a' b b' a0 IH0 G' Hsub Hctx.
    apply (An_IsoSnd G' D g A B a a' b b'). apply IH0; assumption.
  (* An_Empty *)
  - exact I.
  (* An_ConsTm *)
  - intros; exact I.
  (* An_ConsCo *)
  - intros; exact I.
  (* An_Sig_Empty *)
  - exact I.
  (* An_Sig_ConsAx *)
  - intros; exact I.
Qed.

Definition AnnTyping_weaken : forall G a A, AnnTyping G a A ->
  forall G', ctx_sub G G' -> AnnCtx G' -> AnnTyping G' a A :=
  fun G a A H => (proj1 Ann_weaken_all) G a A H.

Definition AnnPropWff_weaken : forall G p, AnnPropWff G p ->
  forall G', ctx_sub G G' -> AnnCtx G' -> AnnPropWff G' p :=
  fun G p H => (proj1 (proj2 Ann_weaken_all)) G p H.

Definition AnnIso_weaken : forall G D g p q, AnnIso G D g p q ->
  forall G', ctx_sub G G' -> AnnCtx G' -> AnnIso G' D g p q :=
  fun G D g p q H => (proj1 (proj2 (proj2 Ann_weaken_all))) G D g p q H.

Definition AnnDefEq_weaken : forall G D g a b, AnnDefEq G D g a b ->
  forall G', ctx_sub G G' -> AnnCtx G' -> AnnDefEq G' D g a b :=
  fun G D g a b H => (proj1 (proj2 (proj2 (proj2 Ann_weaken_all)))) G D g a b H.

Lemma notin_dom_cons : forall (x y:atom) (b:sort) G,
  y `notin` {{x}} -> y `notin` dom G -> y `notin` dom (x ~ b ++ G).
Proof.
  intros x y b G Hx HG.
  intro Hin. cbn [dom] in Hin.
  apply HG.
  apply notin_singleton_1 in Hx.
  exact (@AtomSetImpl.add_3 (dom G) x y Hx Hin).
Qed.

Lemma AT_nil_Star : AnnTyping nil a_Star a_Star.
Proof. apply An_Star, An_Empty. Qed.

Lemma AnnCtx_var_Star : forall x, AnnCtx (x ~ Tm a_Star ++ nil).
Proof.
  intro x. apply An_ConsTm.
  - apply An_Empty.
  - apply AT_nil_Star.
  - apply notin_empty.
Qed.

Lemma AT_var_Star : forall x,
  AnnTyping (x ~ Tm a_Star ++ nil) (a_Var_f x) a_Star.
Proof.
  intro x. apply An_Var.
  - apply AnnCtx_var_Star.
  - simpl; left; reflexivity.
Qed.

Lemma open_tm_var_free : forall (x:atom) (u:tm),
  open_tm_wrt_tm (a_Var_f x) u = a_Var_f x.
Proof. intros; cbn [open_tm_wrt_tm open_tm_wrt_tm_rec]; reflexivity. Qed.

Lemma AT_var_pi : forall x,
  AnnTyping (x ~ Tm a_Star ++ nil)
    (a_Pi Rel (a_Var_f x) (a_Var_f x)) a_Star.
Proof.
  intro x.
  apply (An_Pi {{x}} (x ~ Tm a_Star ++ nil) Rel
                 (a_Var_f x) (a_Var_f x)).
  - intros y Hy.
    rewrite open_tm_var_free.
    apply An_Var.
    + apply An_ConsTm.
      * apply AnnCtx_var_Star.
      * apply AT_var_Star.
      * apply (notin_dom_cons x y (Tm a_Star) nil); [exact Hy | apply notin_empty].
    + simpl; right; left; reflexivity.
  - apply AT_var_Star.
Qed.

Lemma open_pi_ty : forall x,
  open_tm_wrt_tm (a_Pi Rel (a_Pi Rel (a_Var_b 0) (a_Var_b 1)) (a_Var_b 1)) (a_Var_f x)
  = a_Pi Rel (a_Pi Rel (a_Var_f x) (a_Var_f x)) (a_Var_f x).
Proof.
  intro x. cbn [open_tm_wrt_tm open_tm_wrt_tm_rec].
  repeat break_lt; try lia; reflexivity.
Qed.

Lemma AnnTyping_nil_FixTy : AnnTyping nil FixTy a_Star.
Proof.
  unfold FixTy.
  apply (An_Pi empty nil Irrel a_Star
    (a_Pi Rel (a_Pi Rel (a_Var_b 0) (a_Var_b 1)) (a_Var_b 1))).
  - intros x Hx.
    rewrite open_pi_ty.
    apply (An_Pi {{x}} (x ~ Tm a_Star ++ nil) Rel
                   (a_Pi Rel (a_Var_f x) (a_Var_f x)) (a_Var_f x)).
    + intros y Hy.
      rewrite open_tm_var_free.
      apply An_Var.
      * apply An_ConsTm.
        -- apply AnnCtx_var_Star.
        -- apply AT_var_pi.
        -- apply (notin_dom_cons x y (Tm a_Star) nil); [exact Hy | apply notin_empty].
      * simpl; right; left; reflexivity.
    + apply AT_var_pi.
  - apply AT_nil_Star.
Qed.

Lemma AnnTyping_nil_FixDef : AnnTyping nil FixDef FixTy.
Proof.
  unfold FixDef, FixTy.
  eapply (An_Abs empty).
  - apply AT_nil_Star.
  - intros x Hx.
    cbn [open_tm_wrt_tm open_tm_wrt_tm_rec].
    apply (An_Abs {{x}} (x ~ Tm a_Star ++ nil) Rel
      (a_Pi Rel (a_Var_f x) (a_Var_f x))
      (a_App (a_Var_b 0) Rel
        (a_App (a_App (a_Fam Fix) Irrel (a_Var_f x)) Rel (a_Var_b 0)))
      (a_Var_f x)).
    + apply AT_var_pi.
    + intros y Hy.
      cbn [open_tm_wrt_tm open_tm_wrt_tm_rec].
      assert (HC : AnnCtx
        (y ~ Tm (a_Pi Rel (a_Var_f x) (a_Var_f x)) ++ (x ~ Tm a_Star ++ nil))).
      { apply An_ConsTm.
        - apply AnnCtx_var_Star.
        - apply AT_var_pi.
        - apply (notin_dom_cons x y (Tm a_Star) nil); [exact Hy | apply notin_empty]. }
      assert (Hfam : AnnTyping
        (y ~ Tm (a_Pi Rel (a_Var_f x) (a_Var_f x)) ++ (x ~ Tm a_Star ++ nil))
        (a_Fam Fix) FixTy).
      { apply (An_Fam (y ~ Tm (a_Pi Rel (a_Var_f x) (a_Var_f x)) ++ (x ~ Tm a_Star ++ nil)) Fix FixTy FixDef).
        - exact HC.
        - unfold an_toplevel. simpl. left. reflexivity.
        - apply AnnTyping_nil_FixTy. }
      apply (An_App
        (y ~ Tm (a_Pi Rel (a_Var_f x) (a_Var_f x)) ++ (x ~ Tm a_Star ++ nil))
        (a_Var_f y) Rel
        (a_App (a_App (a_Fam Fix) Irrel (a_Var_f x)) Rel (a_Var_f y))
        (a_Var_f x) (a_Var_f x)).
      * apply An_Var.
        -- exact HC.
        -- simpl. left. reflexivity.
      * apply (An_App
          (y ~ Tm (a_Pi Rel (a_Var_f x) (a_Var_f x)) ++ (x ~ Tm a_Star ++ nil))
          (a_App (a_Fam Fix) Irrel (a_Var_f x)) Rel (a_Var_f y)
          (a_Var_f x) (a_Pi Rel (a_Var_f x) (a_Var_f x))).
        -- apply (An_App
             (y ~ Tm (a_Pi Rel (a_Var_f x) (a_Var_f x)) ++ (x ~ Tm a_Star ++ nil))
             (a_Fam Fix) Irrel (a_Var_f x)
             (a_Pi Rel (a_Pi Rel (a_Var_b 0) (a_Var_b 1)) (a_Var_b 1)) a_Star).
           ++ exact Hfam.
           ++ apply An_Var.
              ** exact HC.
              ** simpl. right. left. reflexivity.
        -- apply An_Var.
           ++ exact HC.
           ++ simpl. left. reflexivity.
    + intros y Hy. apply Rho_Rel. exact I.
  - intros z Hz. apply Rho_IrrRel.
    cbn [erase_tm erase_brs erase_constraint fv_tm_tm_tm fv_tm_tm_brs fv_tm_tm_co fv_tm_tm_constraint open_tm_wrt_tm open_tm_wrt_tm_rec].
    repeat (destruct (lt_eq_lt_dec 0 1) as [[Hlt|Heq]|Hgt]; [|exfalso;lia|exfalso;lia]).
    cbn [erase_tm fv_tm_tm_tm].
    repeat (apply notin_union || apply notin_empty).
Qed.

(* ===================== Canonical forms for progress ===================== *)

Lemma canonical_Pi : forall G v A rho B,
  Value v -> AnnTyping G v (a_Pi rho A B) ->
  exists A0 b, v = a_Abs rho A0 b.
Proof.
  intros G v A rho B Hv Ht. destruct Hv.
  - inversion Ht.
  - inversion Ht.
  - inversion Ht.
  - (* AbsRel *) inversion Ht; subst; eexists; eexists; reflexivity.
  - inversion Ht.
  - inversion Ht.
  - (* AbsIrrel *) inversion Ht; subst; eexists; eexists; reflexivity.
  - inversion Ht.
  - inversion Ht.
Qed.

Lemma canonical_CPi : forall G v phi B,
  Value v -> AnnTyping G v (a_CPi phi B) ->
  exists phi0 b, v = a_CAbs phi0 b.
Proof.
  intros G v phi B Hv Ht. destruct Hv.
  - inversion Ht.
  - inversion Ht.
  - inversion Ht.
  - inversion Ht.
  - inversion Ht.
  - inversion Ht.
  - inversion Ht.
  - (* CAbs *) inversion Ht; subst; eexists; eexists; reflexivity.
  - inversion Ht.
Qed.

Lemma canonical_star_value : forall G v A,
  Value v -> AnnTyping G v A ->
  (v = a_Star \/ (exists rho A0 B, v = a_Pi rho A0 B) \/
                 (exists phi B0, v = a_CPi phi B0)) ->
  A = a_Star.
Proof.
  intros G v A Hv Ht Hshape.
  destruct Hshape as [-> | [[rho [A0 [B0 ->]]] | [phi [B0 ->]]]].
  - inversion Ht; reflexivity.
  - inversion Ht; reflexivity.
  - inversion Ht; reflexivity.
Qed.

Lemma canonical_abs_pi : forall G rho A0 b A,
  AnnTyping G (a_Abs rho A0 b) A -> exists B, A = a_Pi rho A0 B.
Proof. intros. inversion H; subst. eauto. Qed.

Lemma canonical_cabs_cpi : forall G phi b A,
  AnnTyping G (a_CAbs phi b) A -> exists B, A = a_CPi phi B.
Proof. intros. inversion H; subst. eauto. Qed.

(* ===== agentPar/Par.v ===== *)

Import ListNotations.

(* ================================================================== *)
(* Definitions from Task.v                                            *)
(* ================================================================== *)


(* ================================================================== *)
(* Free coercion variables (copied from Cfv.v)                        *)
(* ================================================================== *)

Fixpoint cfv_tm (a:tm) : vars :=
  match a with
  | a_Star => {}
  | a_Var_b _ => {}
  | a_Var_f _ => {}
  | a_Abs _ A b => cfv_tm A \u cfv_tm b
  | a_UAbs _ b => cfv_tm b
  | a_App a _ b => cfv_tm a \u cfv_tm b
  | a_Fam _ => {}
  | a_Const _ => {}
  | a_Pi _ A B => cfv_tm A \u cfv_tm B
  | a_Conv a g => cfv_tm a \u cfv_co g
  | a_CPi phi B => cfv_constraint phi \u cfv_tm B
  | a_CAbs phi b => cfv_constraint phi \u cfv_tm b
  | a_UCAbs b => cfv_tm b
  | a_CApp a g => cfv_tm a \u cfv_co g
  | a_Bullet => {}
  | a_DataCon _ => {}
  | a_Case a brs => cfv_tm a \u cfv_brs brs
  end
with cfv_brs (b:brs) : vars :=
  match b with
  | br_None => {}
  | br_One _ a b' => cfv_tm a \u cfv_brs b'
  end
with cfv_co (g:co) : vars :=
  match g with
  | g_Triv => {}
  | g_Var_b _ => {}
  | g_Var_f c => {{c}}
  | g_Beta a b => cfv_tm a \u cfv_tm b
  | g_Refl a => cfv_tm a
  | g_Refl2 a b h => cfv_tm a \u cfv_tm b \u cfv_co h
  | g_Sym h => cfv_co h
  | g_Trans h1 h2 => cfv_co h1 \u cfv_co h2
  | g_PiCong _ h1 h2 => cfv_co h1 \u cfv_co h2
  | g_AbsCong _ h1 h2 => cfv_co h1 \u cfv_co h2
  | g_AppCong h1 _ h2 => cfv_co h1 \u cfv_co h2
  | g_PiFst h => cfv_co h
  | g_CPiFst h => cfv_co h
  | g_IsoSnd h => cfv_co h
  | g_PiSnd h1 h2 => cfv_co h1 \u cfv_co h2
  | g_CPiCong h1 h3 => cfv_co h1 \u cfv_co h3
  | g_CAbsCong h1 h3 h4 => cfv_co h1 \u cfv_co h3 \u cfv_co h4
  | g_CAppCong h h1 h2 => cfv_co h \u cfv_co h1 \u cfv_co h2
  | g_CPiSnd h h1 h2 => cfv_co h \u cfv_co h1 \u cfv_co h2
  | g_Cast h1 h2 => cfv_co h1 \u cfv_co h2
  | g_EqCong h1 A h2 => cfv_co h1 \u cfv_tm A \u cfv_co h2
  | g_IsoConv phi1 phi2 h => cfv_constraint phi1 \u cfv_constraint phi2 \u cfv_co h
  | g_Eta a => cfv_tm a
  | g_Left h h' => cfv_co h \u cfv_co h'
  | g_Right h h' => cfv_co h \u cfv_co h'
  end
with cfv_constraint (phi:constraint) : vars :=
  match phi with
  | Eq a b A => cfv_tm a \u cfv_tm b \u cfv_tm A
  end.

(* ================================================================== *)
(* Closing functions (copied from Closers.v)                          *)
(* ================================================================== *)

Fixpoint closeT_tm (x:atom) (k:nat) (a:tm) {struct a} : tm :=
  match a with
  | a_Star => a_Star
  | a_Var_b n => if le_lt_dec k n then a_Var_b (S n) else a_Var_b n
  | a_Var_f y => if eq_var x y then a_Var_b k else a_Var_f y
  | a_Abs rho A b => a_Abs rho (closeT_tm x k A) (closeT_tm x (S k) b)
  | a_UAbs rho b => a_UAbs rho (closeT_tm x (S k) b)
  | a_App a rho b => a_App (closeT_tm x k a) rho (closeT_tm x k b)
  | a_Fam F => a_Fam F
  | a_Const T => a_Const T
  | a_Pi rho A B => a_Pi rho (closeT_tm x k A) (closeT_tm x (S k) B)
  | a_Conv a g => a_Conv (closeT_tm x k a) (closeT_co x k g)
  | a_CPi phi B => a_CPi (closeT_constraint x k phi) (closeT_tm x k B)
  | a_CAbs phi b => a_CAbs (closeT_constraint x k phi) (closeT_tm x k b)
  | a_UCAbs b => a_UCAbs (closeT_tm x k b)
  | a_CApp a g => a_CApp (closeT_tm x k a) (closeT_co x k g)
  | a_Bullet => a_Bullet
  | a_DataCon K => a_DataCon K
  | a_Case a brs => a_Case (closeT_tm x k a) (closeT_brs x k brs)
  end
with closeT_brs (x:atom) (k:nat) (b:brs) {struct b} : brs :=
  match b with
  | br_None => br_None
  | br_One K a b' => br_One K (closeT_tm x k a) (closeT_brs x k b')
  end
with closeT_co (x:atom) (k:nat) (g:co) {struct g} : co :=
  match g with
  | g_Triv => g_Triv
  | g_Var_b n => g_Var_b n
  | g_Var_f c => g_Var_f c
  | g_Beta a b => g_Beta (closeT_tm x k a) (closeT_tm x k b)
  | g_Refl a => g_Refl (closeT_tm x k a)
  | g_Refl2 a b h => g_Refl2 (closeT_tm x k a) (closeT_tm x k b) (closeT_co x k h)
  | g_Sym h => g_Sym (closeT_co x k h)
  | g_Trans h1 h2 => g_Trans (closeT_co x k h1) (closeT_co x k h2)
  | g_PiCong rho h1 h2 => g_PiCong rho (closeT_co x k h1) (closeT_co x (S k) h2)
  | g_AbsCong rho h1 h2 => g_AbsCong rho (closeT_co x k h1) (closeT_co x (S k) h2)
  | g_AppCong h1 rho h2 => g_AppCong (closeT_co x k h1) rho (closeT_co x k h2)
  | g_PiFst h => g_PiFst (closeT_co x k h)
  | g_CPiFst h => g_CPiFst (closeT_co x k h)
  | g_IsoSnd h => g_IsoSnd (closeT_co x k h)
  | g_PiSnd h1 h2 => g_PiSnd (closeT_co x k h1) (closeT_co x k h2)
  | g_CPiCong h1 h3 => g_CPiCong (closeT_co x k h1) (closeT_co x k h3)
  | g_CAbsCong h1 h3 h4 => g_CAbsCong (closeT_co x k h1) (closeT_co x k h3) (closeT_co x k h4)
  | g_CAppCong h h1 h2 => g_CAppCong (closeT_co x k h) (closeT_co x k h1) (closeT_co x k h2)
  | g_CPiSnd h h1 h2 => g_CPiSnd (closeT_co x k h) (closeT_co x k h1) (closeT_co x k h2)
  | g_Cast h1 h2 => g_Cast (closeT_co x k h1) (closeT_co x k h2)
  | g_EqCong h1 A h2 => g_EqCong (closeT_co x k h1) (closeT_tm x k A) (closeT_co x k h2)
  | g_IsoConv phi1 phi2 h => g_IsoConv (closeT_constraint x k phi1) (closeT_constraint x k phi2) (closeT_co x k h)
  | g_Eta a => g_Eta (closeT_tm x k a)
  | g_Left h h' => g_Left (closeT_co x k h) (closeT_co x k h')
  | g_Right h h' => g_Right (closeT_co x k h) (closeT_co x k h')
  end
with closeT_constraint (x:atom) (k:nat) (phi:constraint) : constraint :=
  match phi with
  | Eq a b A => Eq (closeT_tm x k a) (closeT_tm x k b) (closeT_tm x k A)
  end.

Fixpoint closeC_tm (c:atom) (k:nat) (a:tm) {struct a} : tm :=
  match a with
  | a_Star => a_Star
  | a_Var_b n => a_Var_b n
  | a_Var_f y => a_Var_f y
  | a_Abs rho A b => a_Abs rho (closeC_tm c k A) (closeC_tm c k b)
  | a_UAbs rho b => a_UAbs rho (closeC_tm c k b)
  | a_App a rho b => a_App (closeC_tm c k a) rho (closeC_tm c k b)
  | a_Fam F => a_Fam F
  | a_Const T => a_Const T
  | a_Pi rho A B => a_Pi rho (closeC_tm c k A) (closeC_tm c k B)
  | a_Conv a g => a_Conv (closeC_tm c k a) (closeC_co c k g)
  | a_CPi phi B => a_CPi (closeC_constraint c k phi) (closeC_tm c (S k) B)
  | a_CAbs phi b => a_CAbs (closeC_constraint c k phi) (closeC_tm c (S k) b)
  | a_UCAbs b => a_UCAbs (closeC_tm c (S k) b)
  | a_CApp a g => a_CApp (closeC_tm c k a) (closeC_co c k g)
  | a_Bullet => a_Bullet
  | a_DataCon K => a_DataCon K
  | a_Case a brs => a_Case (closeC_tm c k a) (closeC_brs c k brs)
  end
with closeC_brs (c:atom) (k:nat) (b:brs) {struct b} : brs :=
  match b with
  | br_None => br_None
  | br_One K a b' => br_One K (closeC_tm c k a) (closeC_brs c k b')
  end
with closeC_co (c:atom) (k:nat) (g:co) {struct g} : co :=
  match g with
  | g_Triv => g_Triv
  | g_Var_b n => if le_lt_dec k n then g_Var_b (S n) else g_Var_b n
  | g_Var_f d => if eq_var c d then g_Var_b k else g_Var_f d
  | g_Beta a b => g_Beta (closeC_tm c k a) (closeC_tm c k b)
  | g_Refl a => g_Refl (closeC_tm c k a)
  | g_Refl2 a b h => g_Refl2 (closeC_tm c k a) (closeC_tm c k b) (closeC_co c k h)
  | g_Sym h => g_Sym (closeC_co c k h)
  | g_Trans h1 h2 => g_Trans (closeC_co c k h1) (closeC_co c k h2)
  | g_PiCong rho h1 h2 => g_PiCong rho (closeC_co c k h1) (closeC_co c k h2)
  | g_AbsCong rho h1 h2 => g_AbsCong rho (closeC_co c k h1) (closeC_co c k h2)
  | g_AppCong h1 rho h2 => g_AppCong (closeC_co c k h1) rho (closeC_co c k h2)
  | g_PiFst h => g_PiFst (closeC_co c k h)
  | g_CPiFst h => g_CPiFst (closeC_co c k h)
  | g_IsoSnd h => g_IsoSnd (closeC_co c k h)
  | g_PiSnd h1 h2 => g_PiSnd (closeC_co c k h1) (closeC_co c k h2)
  | g_CPiCong h1 h3 => g_CPiCong (closeC_co c k h1) (closeC_co c (S k) h3)
  | g_CAbsCong h1 h3 h4 => g_CAbsCong (closeC_co c k h1) (closeC_co c (S k) h3) (closeC_co c k h4)
  | g_CAppCong h h1 h2 => g_CAppCong (closeC_co c k h) (closeC_co c k h1) (closeC_co c k h2)
  | g_CPiSnd h h1 h2 => g_CPiSnd (closeC_co c k h) (closeC_co c k h1) (closeC_co c k h2)
  | g_Cast h1 h2 => g_Cast (closeC_co c k h1) (closeC_co c k h2)
  | g_EqCong h1 A h2 => g_EqCong (closeC_co c k h1) (closeC_tm c k A) (closeC_co c k h2)
  | g_IsoConv phi1 phi2 h => g_IsoConv (closeC_constraint c k phi1) (closeC_constraint c k phi2) (closeC_co c k h)
  | g_Eta a => g_Eta (closeC_tm c k a)
  | g_Left h h' => g_Left (closeC_co c k h) (closeC_co c k h')
  | g_Right h h' => g_Right (closeC_co c k h) (closeC_co c k h')
  end
with closeC_constraint (c:atom) (k:nat) (phi:constraint) : constraint :=
  match phi with
  | Eq a b A => Eq (closeC_tm c k a) (closeC_tm c k b) (closeC_tm c k A)
  end.

(* ================================================================== *)
(* Erasable-shape predicate                                           *)
(* ================================================================== *)

Inductive Eok : tm -> Prop :=
| Eok_Star : Eok a_Star
| Eok_Bullet : Eok a_Bullet
| Eok_Var_b : forall n, Eok (a_Var_b n)
| Eok_Var_f : forall x, Eok (a_Var_f x)
| Eok_Fam : forall F, Eok (a_Fam F)
| Eok_Const : forall T, Eok (a_Const T)
| Eok_UAbs : forall rho b, Eok b -> Eok (a_UAbs rho b)
| Eok_App : forall a rho b, Eok a -> Eok b -> Eok (a_App a rho b)
| Eok_Pi : forall rho A B, Eok A -> Eok B -> Eok (a_Pi rho A B)
| Eok_CPi : forall phi B, EokConstraint phi -> Eok B -> Eok (a_CPi phi B)
| Eok_UCAbs : forall b, Eok b -> Eok (a_UCAbs b)
| Eok_CApp : forall a, Eok a -> Eok (a_CApp a g_Triv)
with EokConstraint : constraint -> Prop :=
| Eok_Eq : forall a b A, Eok a -> Eok b -> Eok A -> EokConstraint (Eq a b A).

Scheme Eok_ind' := Induction for Eok Sort Prop
with EokConstraint_ind' := Induction for EokConstraint Sort Prop.
Combined Scheme Eok_mutind from Eok_ind', EokConstraint_ind'.

Inductive EokCo : co -> Prop :=
| EokCo_Triv : EokCo g_Triv
| EokCo_Var_f : forall c, EokCo (g_Var_f c).

(* ================================================================== *)
(* Basic Eok facts                                                    *)
(* ================================================================== *)

Lemma Eok_erase : forall a, Eok (erase_tm a).
Proof.
  apply (tm_mutind
    (fun a => Eok (erase_tm a))
    (fun b => True)
    (fun g => True)
    (fun phi => EokConstraint (erase_constraint phi))).
  all: intros; try exact I; cbn [erase_tm erase_constraint].
  all: try (destruct rho; cbn [erase_tm]; eauto 20 using Eok, EokConstraint).
  all: eauto 20 using Eok, EokConstraint.
Qed.

Lemma EokConstraint_erase : forall phi, EokConstraint (erase_constraint phi).
Proof.
  intros [a b A]; cbn [erase_constraint].
  apply Eok_Eq; apply Eok_erase.
Qed.

Lemma Eok_open_tm_gen :
  (forall a (H:Eok a), forall k u, Eok u -> Eok (open_tm_wrt_tm_rec k u a)) /\
  (forall phi (H:EokConstraint phi), forall k u, Eok u ->
     EokConstraint (open_constraint_wrt_tm_rec k u phi)).
Proof.
  apply (Eok_mutind
    (fun a _ => forall k u, Eok u -> Eok (open_tm_wrt_tm_rec k u a))
    (fun phi _ => forall k u, Eok u -> EokConstraint (open_constraint_wrt_tm_rec k u phi))).
  all: intros.
  all: try (cbn [open_tm_wrt_tm_rec open_constraint_wrt_tm_rec]; eauto 30 using Eok, Eok_Eq).
  all: try (match goal with
            | n : nat, k : nat |- _ =>
              destruct (lt_eq_lt_dec n k) as [[?|?]|?]; cbn; eauto 30 using Eok
            end).
Qed.

Lemma Eok_open_tm : forall a u, Eok a -> Eok u -> Eok (open_tm_wrt_tm a u).
Proof. intros; exact (proj1 Eok_open_tm_gen a H 0 u H0). Qed.

Lemma Eok_open_co_var_gen :
  (forall a (H:Eok a), forall k c, Eok (open_tm_wrt_co_rec k (g_Var_f c) a)) /\
  (forall phi (H:EokConstraint phi), forall k c,
     EokConstraint (open_constraint_wrt_co_rec k (g_Var_f c) phi)).
Proof.
  apply (Eok_mutind
    (fun a _ => forall k c, Eok (open_tm_wrt_co_rec k (g_Var_f c) a))
    (fun phi _ => forall k c, EokConstraint (open_constraint_wrt_co_rec k (g_Var_f c) phi))).
  all: intros.
  all: try (cbn [open_tm_wrt_co_rec open_constraint_wrt_co_rec]; eauto 30 using Eok, Eok_Eq).
Qed.

Lemma Eok_open_co_var : forall a c, Eok a -> Eok (open_tm_wrt_co a (g_Var_f c)).
Proof. intros; exact (proj1 Eok_open_co_var_gen a H 0 c). Qed.

Lemma Eok_open_co_triv_gen :
  (forall a (H:Eok a), forall k, Eok (open_tm_wrt_co_rec k g_Triv a)) /\
  (forall phi (H:EokConstraint phi), forall k,
     EokConstraint (open_constraint_wrt_co_rec k g_Triv phi)).
Proof.
  apply (Eok_mutind
    (fun a _ => forall k, Eok (open_tm_wrt_co_rec k g_Triv a))
    (fun phi _ => forall k, EokConstraint (open_constraint_wrt_co_rec k g_Triv phi))).
  all: intros.
  all: try (cbn [open_tm_wrt_co_rec open_constraint_wrt_co_rec]; eauto 30 using Eok, Eok_Eq).
Qed.

Lemma Eok_open_co_triv : forall a, Eok a -> Eok (open_tm_wrt_co a g_Triv).
Proof. intros; exact (proj1 Eok_open_co_triv_gen a H 0). Qed.

Lemma Eok_open_tm_rec_inv_gen :
  (forall a, forall k x, Eok (open_tm_wrt_tm_rec k (a_Var_f x) a) -> Eok a) /\
  (forall b:brs, True) /\ (forall g:co, True) /\
  (forall phi, forall k x,
     EokConstraint (open_constraint_wrt_tm_rec k (a_Var_f x) phi) -> EokConstraint phi).
Proof.
  apply (tm_mutind
    (fun a => forall k x, Eok (open_tm_wrt_tm_rec k (a_Var_f x) a) -> Eok a)
    (fun b => True)
    (fun g => True)
    (fun phi => forall k x, EokConstraint (open_constraint_wrt_tm_rec k (a_Var_f x) phi) -> EokConstraint phi)).
  all: intros; try exact I.
  all: try (cbn [open_tm_wrt_tm_rec open_constraint_wrt_tm_rec] in *).
  all: try (match goal with
            | H : Eok (a_Var_b _) |- _ => exact (Eok_Var_b _)
            end).
  all: try (match goal with
            | H : Eok _ |- _ => inversion H; subst; eauto 30 using Eok, Eok_Eq
            | H : EokConstraint _ |- _ => inversion H; subst; eauto 30 using Eok, Eok_Eq
            end).
  all: try (match goal with
            | H : g_Triv = open_co_wrt_tm_rec _ _ ?g |- _ =>
              destruct g; cbn in H; try discriminate; eauto 30 using Eok, Eok_Eq
            end).
  all: eauto 30 using Eok, Eok_Eq.
Qed.

Lemma Eok_open_tm_inv : forall a x, Eok (open_tm_wrt_tm a (a_Var_f x)) -> Eok a.
Proof. intros; exact (proj1 Eok_open_tm_rec_inv_gen a 0 x H). Qed.

Lemma open_co_var_triv : forall g k c,
  open_co_wrt_co_rec k (g_Var_f c) g = g_Triv -> g = g_Triv.
Proof.
  intros g k c H.
  destruct g; cbn [open_co_wrt_co_rec] in H; try discriminate.
  - reflexivity.
  - destruct (lt_eq_lt_dec n k) as [[?|?]|?]; cbn in H; discriminate.
Qed.

Lemma Eok_open_co_rec_inv_gen :
  (forall a, forall k c, Eok (open_tm_wrt_co_rec k (g_Var_f c) a) -> Eok a) /\
  (forall b:brs, True) /\ (forall g:co, True) /\
  (forall phi, forall k c,
     EokConstraint (open_constraint_wrt_co_rec k (g_Var_f c) phi) -> EokConstraint phi).
Proof.
  apply (tm_mutind
    (fun a => forall k c, Eok (open_tm_wrt_co_rec k (g_Var_f c) a) -> Eok a)
    (fun b => True)
    (fun g => True)
    (fun phi => forall k c, EokConstraint (open_constraint_wrt_co_rec k (g_Var_f c) phi) -> EokConstraint phi)).
  all: intros; try exact I.
  all: try (cbn [open_tm_wrt_co_rec open_constraint_wrt_co_rec] in *).
  all: try (match goal with
            | H : Eok (a_Var_b _) |- _ => exact (Eok_Var_b _)
            | H : Eok (a_Var_f _) |- _ => exact (Eok_Var_f _)
            end).
  all: try (match goal with
            | H : Eok _ |- _ => inversion H; subst; eauto 30 using Eok, Eok_Eq
            | H : EokConstraint _ |- _ => inversion H; subst; eauto 30 using Eok, Eok_Eq
            end).
  all: try (match goal with
            | H : g_Triv = open_co_wrt_co_rec ?k (g_Var_f ?c) ?g |- Eok (a_CApp ?a ?g) =>
              pose proof (open_co_var_triv g k c (eq_sym H)) as E;
              subst g; eapply Eok_CApp; eauto 30 using Eok
            | H : open_co_wrt_co_rec ?k (g_Var_f ?c) ?g = g_Triv |- Eok (a_CApp ?a ?g) =>
              pose proof (open_co_var_triv g k c H) as E;
              subst g; eapply Eok_CApp; eauto 30 using Eok
            end).
  all: try (exfalso).
  all: try (destruct (lt_eq_lt_dec n k); cbn in *; try discriminate; eauto 30 using Eok, Eok_Eq).
  all: try (destruct (le_lt_dec k n); cbn in *; try discriminate; eauto 30 using Eok, Eok_Eq).
  all: eauto 30 using Eok, Eok_Eq.
Qed.

Lemma Eok_open_co_inv : forall a c, Eok (open_tm_wrt_co a (g_Var_f c)) -> Eok a.
Proof. intros; exact (proj1 Eok_open_co_rec_inv_gen a 0 c H). Qed.

Lemma EokConstraint_components : forall a b A,
  EokConstraint (Eq a b A) -> Eok a /\ Eok b /\ Eok A.
Proof. intros; inversion H; subst; auto. Qed.

Lemma Eok_closeT_gen :
  (forall a (H:Eok a), forall x k, Eok (closeT_tm x k a)) /\
  (forall phi (H:EokConstraint phi), forall x k,
     EokConstraint (closeT_constraint x k phi)).
Proof.
  apply (Eok_mutind
    (fun a _ => forall x k, Eok (closeT_tm x k a))
    (fun phi _ => forall x k, EokConstraint (closeT_constraint x k phi))).
  all: intros.
  all: try (cbn [closeT_tm closeT_constraint]; eauto 30 using Eok, Eok_Eq).
  all: try (match goal with
            | |- context [le_lt_dec ?k ?n] =>
              destruct (le_lt_dec k n); cbn; eauto 30 using Eok, Eok_Eq
            | |- context [eq_var ?x ?y] =>
              destruct (eq_var x y); cbn; eauto 30 using Eok, Eok_Eq
            end).
  all: eauto 30 using Eok, Eok_Eq.
Qed.

Lemma Eok_closeT_tm : forall a x k, Eok a -> Eok (closeT_tm x k a).
Proof. intros; exact (proj1 Eok_closeT_gen a H x k). Qed.

Lemma Eok_closeC_gen :
  (forall a (H:Eok a), forall c k, Eok (closeC_tm c k a)) /\
  (forall phi (H:EokConstraint phi), forall c k,
     EokConstraint (closeC_constraint c k phi)).
Proof.
  apply (Eok_mutind
    (fun a _ => forall c k, Eok (closeC_tm c k a))
    (fun phi _ => forall c k, EokConstraint (closeC_constraint c k phi))).
  all: intros.
  all: try (cbn [closeC_tm closeC_constraint]; eauto 30 using Eok, Eok_Eq).
  all: try (match goal with
            | |- context [le_lt_dec ?k ?n] =>
              destruct (le_lt_dec k n); cbn; eauto 30 using Eok, Eok_Eq
            | |- context [eq_var ?x ?y] =>
              destruct (eq_var x y); cbn; eauto 30 using Eok, Eok_Eq
            end).
  all: eauto 30 using Eok, Eok_Eq.
Qed.

Lemma Eok_closeC_tm : forall a c k, Eok a -> Eok (closeC_tm c k a).
Proof. intros; exact (proj1 Eok_closeC_gen a H c k). Qed.

(* ================================================================== *)
(* Open/close inverses                                                *)
(* ================================================================== *)

Lemma open_close_tm :
  (forall a k x, x `notin` fv_tm_tm_tm a ->
     open_tm_wrt_tm_rec k (a_Var_f x) (closeT_tm x k a) = a) /\
  (forall b k x, x `notin` fv_tm_tm_brs b ->
     open_brs_wrt_tm_rec k (a_Var_f x) (closeT_brs x k b) = b) /\
  (forall g k x, x `notin` fv_tm_tm_co g ->
     open_co_wrt_tm_rec k (a_Var_f x) (closeT_co x k g) = g) /\
  (forall phi k x, x `notin` fv_tm_tm_constraint phi ->
     open_constraint_wrt_tm_rec k (a_Var_f x) (closeT_constraint x k phi) = phi).
Proof.
  apply (tm_mutind
    (fun a => forall k x, x `notin` fv_tm_tm_tm a ->
       open_tm_wrt_tm_rec k (a_Var_f x) (closeT_tm x k a) = a)
    (fun b => forall k x, x `notin` fv_tm_tm_brs b ->
       open_brs_wrt_tm_rec k (a_Var_f x) (closeT_brs x k b) = b)
    (fun g => forall k x, x `notin` fv_tm_tm_co g ->
       open_co_wrt_tm_rec k (a_Var_f x) (closeT_co x k g) = g)
    (fun phi => forall k x, x `notin` fv_tm_tm_constraint phi ->
       open_constraint_wrt_tm_rec k (a_Var_f x) (closeT_constraint x k phi) = phi)).
  all: intros;
       cbn [fv_tm_tm_tm fv_tm_tm_brs fv_tm_tm_co fv_tm_tm_constraint] in *;
       repeat progress cbn [open_tm_wrt_tm_rec open_brs_wrt_tm_rec open_co_wrt_tm_rec
                            open_constraint_wrt_tm_rec
                            closeT_tm closeT_brs closeT_co closeT_constraint].
  all: try (match goal with
            | |- open_tm_wrt_tm_rec ?k (a_Var_f ?x)
                   (if le_lt_dec ?k ?n then a_Var_b (S ?n) else a_Var_b ?n) = a_Var_b ?n =>
              destruct (le_lt_dec k n) as [Hle|Hgt];
              [ cbn [open_tm_wrt_tm_rec];
                destruct (lt_eq_lt_dec (S n) k) as [[Hlt2|Heq2]|Hgt2];
                [ exfalso; lia
                | exfalso; lia
                | cbn [open_tm_wrt_tm_rec]; f_equal; lia ]
              | cbn [open_tm_wrt_tm_rec];
                destruct (lt_eq_lt_dec n k) as [[Hlt2|Heq2]|Hgt2];
                [ reflexivity
                | exfalso; lia
                | exfalso; lia ] ]
            end).
  all: try (match goal with
            | |- open_tm_wrt_tm_rec ?k (a_Var_f ?x)
                   (if eq_var ?x ?y then a_Var_b ?k else a_Var_f ?y) = a_Var_f ?y =>
              destruct (eq_var x y) eqn:E;
              [ apply eq_var_true in E; subst x;
                match type of H with
                | ?a `notin` {{?b}} => exfalso; exact (notin_singleton_1 b a H eq_refl)
                end
              | reflexivity ]
            end).
  all: try reflexivity.
  all: try (f_equal; eauto 12 using notin_union_1, notin_union_2, notin_union_3).
Qed.

Lemma open_close_co :
  (forall a k c, c `notin` cfv_tm a ->
     open_tm_wrt_co_rec k (g_Var_f c) (closeC_tm c k a) = a) /\
  (forall b k c, c `notin` cfv_brs b ->
     open_brs_wrt_co_rec k (g_Var_f c) (closeC_brs c k b) = b) /\
  (forall g k c, c `notin` cfv_co g ->
     open_co_wrt_co_rec k (g_Var_f c) (closeC_co c k g) = g) /\
  (forall phi k c, c `notin` cfv_constraint phi ->
     open_constraint_wrt_co_rec k (g_Var_f c) (closeC_constraint c k phi) = phi).
Proof.
  apply (tm_mutind
    (fun a => forall k c, c `notin` cfv_tm a ->
       open_tm_wrt_co_rec k (g_Var_f c) (closeC_tm c k a) = a)
    (fun b => forall k c, c `notin` cfv_brs b ->
       open_brs_wrt_co_rec k (g_Var_f c) (closeC_brs c k b) = b)
    (fun g => forall k c, c `notin` cfv_co g ->
       open_co_wrt_co_rec k (g_Var_f c) (closeC_co c k g) = g)
    (fun phi => forall k c, c `notin` cfv_constraint phi ->
       open_constraint_wrt_co_rec k (g_Var_f c) (closeC_constraint c k phi) = phi)).
  all: intros;
       cbn [cfv_tm cfv_brs cfv_co cfv_constraint] in *;
       repeat progress cbn [open_tm_wrt_co_rec open_brs_wrt_co_rec open_co_wrt_co_rec
                            open_constraint_wrt_co_rec
                            closeC_tm closeC_brs closeC_co closeC_constraint].
  all: try (match goal with
            | |- open_co_wrt_co_rec ?k (g_Var_f ?c)
                   (if le_lt_dec ?k ?n then g_Var_b (S ?n) else g_Var_b ?n) = g_Var_b ?n =>
              destruct (le_lt_dec k n) as [Hle|Hgt];
              [ cbn [open_co_wrt_co_rec];
                destruct (lt_eq_lt_dec (S n) k) as [[Hlt2|Heq2]|Hgt2];
                [ exfalso; lia
                | exfalso; lia
                | cbn [open_co_wrt_co_rec]; f_equal; lia ]
              | cbn [open_co_wrt_co_rec];
                destruct (lt_eq_lt_dec n k) as [[Hlt2|Heq2]|Hgt2];
                [ reflexivity
                | exfalso; lia
                | exfalso; lia ] ]
            end).
  all: try (match goal with
            | |- open_co_wrt_co_rec ?k (g_Var_f ?c)
                   (if eq_var ?c ?d then g_Var_b ?k else g_Var_f ?d) = g_Var_f ?d =>
              destruct (eq_var c d) eqn:E;
              [ apply eq_var_true in E; subst c;
                match type of H with
                | ?a `notin` {{?b}} => exfalso; exact (notin_singleton_1 b a H eq_refl)
                end
              | reflexivity ]
            end).
  all: try reflexivity.
  all: try (f_equal; eauto 12 using notin_union_1, notin_union_2, notin_union_3).
Qed.

(* ================================================================== *)
(* Generic lemmas for lc opening universalisation                     *)
(* ================================================================== *)

Lemma lc_open_tm_all_of_lc_one : forall L a,
  (exists x, x `notin` L /\ lc_tm (open_tm_wrt_tm a (a_Var_f x))) ->
  forall x, lc_tm (open_tm_wrt_tm a (a_Var_f x)).
Proof.
  intros L a [z [Hz Hlz]] x.
  exact (lc_open_tm_any a (a_Var_f z) (lc_a_Var_f z) Hlz x).
Qed.

Lemma lc_open_co_all_of_lc_one : forall L a,
  (exists c, c `notin` L /\ lc_tm (open_tm_wrt_co a (g_Var_f c))) ->
  forall c, lc_tm (open_tm_wrt_co a (g_Var_f c)).
Proof.
  intros L a [z [Hz Hlz]] c.
  exact (lc_open_tm_co_any a (g_Var_f z) (lc_g_Var_f z) Hlz (g_Var_f c) (lc_g_Var_f c)).
Qed.

Lemma lc_open_tm_all_of_cofinite : forall L a,
  (forall x, x `notin` L -> lc_tm (open_tm_wrt_tm a (a_Var_f x))) ->
  forall x, lc_tm (open_tm_wrt_tm a (a_Var_f x)).
Proof.
  intros L a H.
  apply (lc_open_tm_all_of_lc_one L a).
  destruct (atom_fresh L) as [z Hz].
  exists z; split; [exact Hz | apply H; exact Hz].
Qed.

Lemma lc_open_co_all_of_cofinite : forall L a,
  (forall c, c `notin` L -> lc_tm (open_tm_wrt_co a (g_Var_f c))) ->
  forall c, lc_tm (open_tm_wrt_co a (g_Var_f c)).
Proof.
  intros L a H.
  apply (lc_open_co_all_of_lc_one L a).
  destruct (atom_fresh L) as [z Hz].
  exists z; split; [exact Hz | apply H; exact Hz].
Qed.

Lemma lc_open_tm : forall (rho:relflag) (a' b':tm),
  lc_tm (a_UAbs rho a') -> lc_tm b' -> lc_tm (open_tm_wrt_tm a' b').
Proof.
  intros rho a' b' Ha Hb.
  exact (lc_open_body_uabs rho a' Ha b' Hb).
Qed.

Lemma lc_open_co : forall (a' : tm) (g : co),
  lc_tm (a_UCAbs a') -> lc_co g -> lc_tm (open_tm_wrt_co a' g).
Proof.
  intros a' g Ha Hg.
  exact (lc_open_body_ucabs a' Ha g Hg).
Qed.

Lemma lc_erase_FixDef : lc_tm (erase_tm FixDef).
Proof. apply (proj2 (lc_tm_iff (erase_tm FixDef))); split; vm_compute; auto with arith. Qed.

Lemma lc_erase_FixTy : lc_tm (erase_tm FixTy).
Proof. apply (proj2 (lc_tm_iff (erase_tm FixTy))); split; vm_compute; auto with arith. Qed.

Lemma toplevel_binds_lc : forall (F:tyfam) (a A:tm),
  binds F (Ax a A) toplevel -> lc_tm a.
Proof.
  intros F a A H.
  unfold toplevel, an_toplevel, erase_sig in H.
  simpl in H.
  destruct H as [Heq | Hnil].
  - inversion Heq; subst. apply lc_erase_FixDef.
  - contradiction.
Qed.

(* ================================================================== *)
(* Par and MultiPar preserve local closure                            *)
(* ================================================================== *)

Lemma Par_lc : forall G D a b, Par G D a b -> lc_tm a /\ lc_tm b.
Proof.
  apply (Par_ind (fun G D a b => lc_tm a /\ lc_tm b)).
  - intros G D a Hl. split; assumption.
  - intros G D a rho b a' b' Hpar1 IH1 Hpar2 IH2.
    split.
    + apply lc_a_App; [exact (proj1 IH1) | exact (proj1 IH2)].
    + apply (lc_open_tm rho a' b'); [exact (proj2 IH1) | exact (proj2 IH2)].
  - intros G D a rho b a' b' Hpar1 IH1 Hpar2 IH2.
    split; apply lc_a_App; [exact (proj1 IH1) | exact (proj1 IH2)
                           | exact (proj2 IH1) | exact (proj2 IH2)].
  - intros G D a a' Hpar IH.
    split.
    + apply lc_a_CApp; [exact (proj1 IH) | apply lc_g_Triv].
    + apply (lc_open_co a' g_Triv); [exact (proj2 IH) | apply lc_g_Triv].
  - intros G D a a' Hpar IH.
    split; apply lc_a_CApp; [exact (proj1 IH) | apply lc_g_Triv
                             | exact (proj2 IH) | apply lc_g_Triv].
  - intros L G D rho a a' Hpar IH.
    split.
    + apply lc_a_UAbs.
      apply (lc_open_tm_all_of_cofinite L a).
      intros x Hx. exact (proj1 (IH x Hx)).
    + apply lc_a_UAbs.
      apply (lc_open_tm_all_of_cofinite L a').
      intros x Hx. exact (proj2 (IH x Hx)).
  - intros L G D rho A B A' B' HparA IHA HparB IHB.
    split.
    + apply lc_a_Pi.
      * exact (proj1 IHA).
      * apply (lc_open_tm_all_of_cofinite L B).
        intros x Hx. exact (proj1 (IHB x Hx)).
    + apply lc_a_Pi.
      * exact (proj2 IHA).
      * apply (lc_open_tm_all_of_cofinite L B').
        intros x Hx. exact (proj2 (IHB x Hx)).
  - intros L G D a a' Hpar IH.
    split.
    + apply lc_a_UCAbs.
      apply (lc_open_co_all_of_cofinite L a).
      intros c Hc. exact (proj1 (IH c Hc)).
    + apply lc_a_UCAbs.
      apply (lc_open_co_all_of_cofinite L a').
      intros c Hc. exact (proj2 (IH c Hc)).
  - intros L G D A B A1 a A' B' A1' a' HparA IHA HparB IHB HparBody IHBody HparA1 IHA1.
    split.
    + apply lc_a_CPi.
      * apply lc_Eq; [exact (proj1 IHA) | exact (proj1 IHB) | exact (proj1 IHA1)].
      * apply (lc_open_co_all_of_cofinite L a).
        intros c Hc. exact (proj1 (IHBody c Hc)).
    + apply lc_a_CPi.
      * apply lc_Eq; [exact (proj2 IHA) | exact (proj2 IHB) | exact (proj2 IHA1)].
      * apply (lc_open_co_all_of_cofinite L a').
        intros c Hc. exact (proj2 (IHBody c Hc)).
  - intros G D F a A Hbinds.
    split.
    + apply lc_a_Fam.
    + exact (toplevel_binds_lc F a A Hbinds).
Qed.

Lemma Par_lc_MP : forall G D a b, MultiPar G D a b -> lc_tm a /\ lc_tm b.
Proof.
  apply (MultiPar_ind (fun G D a b => lc_tm a /\ lc_tm b)).
  - intros G D a Hl. split; assumption.
  - intros G D a a' b Hpar Hmp IH.
    pose proof (Par_lc _ _ _ _ Hpar) as [Hla Hlb].
    split; [exact Hla | exact (proj2 IH)].
Qed.

(* ================================================================== *)
(* Monotonicity in G and D                                           *)
(* ================================================================== *)

Lemma Par_mono : forall G D a b, Par G D a b -> forall G' D', Par G' D' a b.
Proof. intros G D a b H. induction H; intros G' D'; econstructor; eauto. Qed.

Lemma MultiPar_mono : forall G D a b, MultiPar G D a b -> forall G' D', MultiPar G' D' a b.
Proof.
  intros G D a b H. induction H as [G0 D0 a0 Hlc | G0 D0 a0 a' b0 Hpar Hmp IH];
    intros G' D'.
  - apply MP_Refl; assumption.
  - eapply MP_Step.
    + apply (Par_mono _ _ _ _ Hpar G' D').
    + apply IH.
Qed.

(* ================================================================== *)
(* Value implies local closure                                       *)
(* ================================================================== *)

Scheme Value_mut := Induction for Value Sort Prop
with CoercedValue_mut := Induction for CoercedValue Sort Prop.

Lemma Value_lc : forall a, Value a -> lc_tm a.
Proof.
  apply (Value_mut (fun a _ => lc_tm a) (fun a _ => lc_tm a)).
  - apply lc_a_Star.
  - intros rho A B lcA lcPi. exact lcPi.
  - intros phi B lcphi lcCPi. exact lcCPi.
  - intros A a lcA lcAbs. exact lcAbs.
  - intros a lcUAbs. exact lcUAbs.
  - intros L a H IH. destruct (atom_fresh L) as [x0 Hx0].
    apply lc_a_UAbs. intros x.
    apply (lc_open_tm_any a (a_Var_f x0)); [apply lc_a_Var_f | apply IH; exact Hx0].
  - intros L A a lcA H IH. destruct (atom_fresh L) as [x0 Hx0].
    apply lc_a_Abs; [exact lcA|]. intros x.
    apply (lc_open_tm_any a (a_Var_f x0)); [apply lc_a_Var_f | apply IH; exact Hx0].
  - intros phi a lcphi lcCAbs. exact lcCAbs.
  - intros a lcUCAbs. exact lcUCAbs.
  - intros a v IH. exact IH.
  - intros a g lcg v IH. apply lc_a_Conv; [exact IH|exact lcg].
Qed.

(* ================================================================== *)
(* Beta implies MultiPar                                             *)
(* ================================================================== *)

Lemma Beta_MultiPar : forall a b, Beta a b -> forall G D, MultiPar G D a b.
Proof.
  intros a b H. induction H; intros G D.
  - pose proof (Value_lc _ H0) as Hlc.
    eapply MP_Step.
    + eapply Par_Beta; [apply Par_Refl; exact Hlc | apply Par_Refl; exact H].
    + apply MP_Refl. exact (lc_open_body_uabs _ _ Hlc _ H).
  - eapply MP_Step.
    + eapply Par_CBeta. apply Par_Refl. exact H.
    + apply MP_Refl. exact (lc_open_body_ucabs _ H (g_Triv) (lc_g_Triv)).
  - eapply MP_Step.
    + eapply Par_Axiom; eassumption.
    + apply MP_Refl. exact (toplevel_binds_lc F a A H).
Qed.

(* ================================================================== *)
(* Shape inversion (source side)                                     *)
(* ================================================================== *)

Lemma Par_Conv_inv : forall G D a g b,
  Par G D (a_Conv a g) b -> b = a_Conv a g.
Proof. intros G D a g b H. inversion H; subst; reflexivity. Qed.

Lemma Par_Star_src_inv : forall G D b,
  Par G D a_Star b -> b = a_Star.
Proof. intros G D b H. inversion H; subst; reflexivity. Qed.

Lemma Par_UAbs_src_inv : forall G D rho a b,
  Par G D (a_UAbs rho a) b -> exists a', b = a_UAbs rho a'.
Proof. intros G D rho a b H. inversion H; subst; eauto. Qed.

Lemma Par_Pi_src_inv : forall G D rho A B b,
  Par G D (a_Pi rho A B) b -> exists A' B', b = a_Pi rho A' B'.
Proof. intros G D rho A B b H. inversion H; subst; eauto. Qed.

Lemma Par_CPi_src_inv : forall G D phi B b,
  Par G D (a_CPi phi B) b -> exists phi' B', b = a_CPi phi' B'.
Proof. intros G D phi B b H. inversion H; subst; eauto. Qed.

Lemma Par_CPi_Eq_src_inv : forall G D a b A B c,
  Par G D (a_CPi (Eq a b A) B) c ->
  exists a' b' A' B', c = a_CPi (Eq a' b' A') B'.
Proof. intros G D a b A B c H. inversion H; subst; eauto. Qed.

Lemma Par_UCAbs_src_inv : forall G D a b,
  Par G D (a_UCAbs a) b -> exists a', b = a_UCAbs a'.
Proof. intros G D a b H. inversion H; subst; eauto. Qed.

Lemma MultiPar_Star_src_inv : forall G D b,
  MultiPar G D a_Star b -> b = a_Star.
Proof.
  intros G D b H.
  assert (H' : (fun G D a b => a = a_Star -> b = a_Star) G D a_Star b).
  { refine (MultiPar_ind (fun G D a b => a = a_Star -> b = a_Star) _ _ G D a_Star b H).
    - intros G0 D0 x Hlc Ha. subst x. reflexivity.
    - intros G0 D0 x x' y Hpar Hmp IH Ha. subst x.
      pose proof (Par_Star_src_inv _ _ _ Hpar) as Hb. subst y.
      apply IH. reflexivity. }
  exact (H' eq_refl).
Qed.

Lemma MultiPar_UAbs_src_inv : forall G D rho a b,
  MultiPar G D (a_UAbs rho a) b -> exists a', b = a_UAbs rho a'.
Proof.
  intros G D rho a b H.
  assert (H' : (fun G D a b => forall rho a0, a = a_UAbs rho a0 ->
      exists a', b = a_UAbs rho a') G D (a_UAbs rho a) b).
  { refine (MultiPar_ind
      (fun G D a b => forall rho a0, a = a_UAbs rho a0 ->
         exists a', b = a_UAbs rho a') _ _ G D (a_UAbs rho a) b H).
    - intros G0 D0 x Hlc rho0 a0 Ha. subst x. eauto.
    - intros G0 D0 x x' y Hpar Hmp IH rho0 a0 Ha. subst x.
      destruct (Par_UAbs_src_inv _ _ _ _ _ Hpar) as [a'' Ha''].
      subst y. eapply IH. reflexivity. }
  exact (H' rho a eq_refl).
Qed.

Lemma MultiPar_Pi_src_inv : forall G D rho A B b,
  MultiPar G D (a_Pi rho A B) b -> exists A' B', b = a_Pi rho A' B'.
Proof.
  intros G D rho A B b H.
  assert (H' : (fun G D a b => forall rho A0 B0, a = a_Pi rho A0 B0 ->
      exists A' B', b = a_Pi rho A' B') G D (a_Pi rho A B) b).
  { refine (MultiPar_ind
      (fun G D a b => forall rho A0 B0, a = a_Pi rho A0 B0 ->
         exists A' B', b = a_Pi rho A' B') _ _ G D (a_Pi rho A B) b H).
    - intros G0 D0 x Hlc rho0 A0 B0 Ha. subst x. eauto.
    - intros G0 D0 x x' y Hpar Hmp IH rho0 A0 B0 Ha. subst x.
      destruct (Par_Pi_src_inv _ _ _ _ _ _ Hpar) as [A' [B' Hb]].
      subst y. eapply IH. reflexivity. }
  exact (H' rho A B eq_refl).
Qed.

Lemma MultiPar_CPi_src_inv : forall G D phi B b,
  MultiPar G D (a_CPi phi B) b -> exists phi' B', b = a_CPi phi' B'.
Proof.
  intros G D phi B b H.
  assert (H' : (fun G D a b => forall phi0 B0, a = a_CPi phi0 B0 ->
      exists phi' B', b = a_CPi phi' B') G D (a_CPi phi B) b).
  { refine (MultiPar_ind
      (fun G D a b => forall phi0 B0, a = a_CPi phi0 B0 ->
         exists phi' B', b = a_CPi phi' B') _ _ G D (a_CPi phi B) b H).
    - intros G0 D0 x Hlc phi0 B0 Ha. subst x. eauto.
    - intros G0 D0 x x' y Hpar Hmp IH phi0 B0 Ha. subst x.
      destruct (Par_CPi_src_inv _ _ _ _ _ Hpar) as [phi' [B' Hb]].
      subst y. eapply IH. reflexivity. }
  exact (H' phi B eq_refl).
Qed.

Lemma MultiPar_CPi_Eq_src_inv : forall G D a b A B c,
  MultiPar G D (a_CPi (Eq a b A) B) c ->
  exists a' b' A' B', c = a_CPi (Eq a' b' A') B'.
Proof.
  intros G D a b A B c H.
  assert (H' : (fun G D a0 b0 =>
    forall a1 b1 A0 B0, a0 = a_CPi (Eq a1 b1 A0) B0 ->
      exists a' b' A' B', b0 = a_CPi (Eq a' b' A') B')
    G D (a_CPi (Eq a b A) B) c).
  { refine (MultiPar_ind
      (fun G D a0 b0 =>
         forall a1 b1 A0 B0, a0 = a_CPi (Eq a1 b1 A0) B0 ->
           exists a' b' A' B', b0 = a_CPi (Eq a' b' A') B') _ _
      G D (a_CPi (Eq a b A) B) c H).
    - intros G0 D0 x Hlc a1 b1 A0 B0 Ha. subst x. eauto.
    - intros G0 D0 x x' y Hpar Hmp IH a1 b1 A0 B0 Ha. subst x.
      destruct (Par_CPi_Eq_src_inv _ _ _ _ _ _ _ Hpar)
        as [a' [b' [A' [B' Hb]]]].
      subst y. eapply IH. reflexivity. }
  exact (H' a b A B eq_refl).
Qed.

Lemma MultiPar_UCAbs_src_inv : forall G D a b,
  MultiPar G D (a_UCAbs a) b -> exists a', b = a_UCAbs a'.
Proof.
  intros G D a b H.
  assert (H' : (fun G D a b => forall a0, a = a_UCAbs a0 ->
      exists a', b = a_UCAbs a') G D (a_UCAbs a) b).
  { refine (MultiPar_ind
      (fun G D a b => forall a0, a = a_UCAbs a0 -> exists a', b = a_UCAbs a')
      _ _ G D (a_UCAbs a) b H).
    - intros G0 D0 x Hlc a0 Ha. subst x. eauto.
    - intros G0 D0 x x' y Hpar Hmp IH a0 Ha. subst x.
      destruct (Par_UCAbs_src_inv _ _ _ _ Hpar) as [a'' Ha''].
      subst y. eapply IH. reflexivity. }
  exact (H' a eq_refl).
Qed.

Lemma MultiPar_Conv_src_inv : forall G D a0 g b,
  MultiPar G D (a_Conv a0 g) b -> b = a_Conv a0 g.
Proof.
  intros G D a0 g b H.
  assert (H' : (fun G D a b =>
    forall a0 g, a = a_Conv a0 g -> b = a_Conv a0 g) G D (a_Conv a0 g) b).
  { refine (MultiPar_ind
      (fun G D a b =>
         forall a0 g, a = a_Conv a0 g -> b = a_Conv a0 g) _ _
      G D (a_Conv a0 g) b H).
    - intros G0 D0 x Hlc a1 g1 Ha. subst x. reflexivity.
    - intros G0 D0 x x' y Hpar Hmp IH a1 g1 Ha. subst x.
      pose proof (Par_Conv_inv _ _ _ _ _ Hpar) as Hb. subst y.
      apply IH. reflexivity. }
  exact (H' a0 g eq_refl).
Qed.

(* Erasure only ever produces the following head shapes. *)

Lemma erase_Abs_shape : forall rho A b,
  erase_tm (a_Abs rho A b) = a_UAbs rho (erase_tm b).
Proof. reflexivity. Qed.

Lemma erase_CAbs_shape : forall phi b,
  erase_tm (a_CAbs phi b) = a_UCAbs (erase_tm b).
Proof. reflexivity. Qed.

Lemma MultiPar_erase_Abs_inv : forall G D rho A b c,
  MultiPar G D (erase_tm (a_Abs rho A b)) c ->
  exists b', c = a_UAbs rho b'.
Proof.
  intros. rewrite erase_Abs_shape in H.
  exact (MultiPar_UAbs_src_inv _ _ _ _ _ H).
Qed.

Lemma MultiPar_erase_CAbs_inv : forall G D phi b c,
  MultiPar G D (erase_tm (a_CAbs phi b)) c ->
  exists b', c = a_UCAbs b'.
Proof.
  intros. rewrite erase_CAbs_shape in H.
  exact (MultiPar_UCAbs_src_inv _ _ _ _ H).
Qed.

(* ================================================================== *)
(* Counterexamples: unrestricted diamond/confluence are false.       *)
(* The only missing congruence in Par is the one for a_Conv.         *)
(* ================================================================== *)

Definition cex_f : tm := a_UAbs Rel (a_Conv (a_Var_b 0) g_Triv).
Definition cex_b : tm := a_App (a_UAbs Rel a_Star) Rel a_Star.
Definition cex_src : tm := a_App cex_f Rel cex_b.
Definition cex_left : tm := a_Conv a_Star g_Triv.
Definition cex_right : tm := a_Conv cex_b g_Triv.

Lemma lc_cex_f : lc_tm cex_f.
Proof.
  unfold cex_f. apply lc_a_UAbs. intros x.
  cbn [open_tm_wrt_tm]. apply lc_a_Conv.
  - apply lc_a_Var_f.
  - apply lc_g_Triv.
Qed.

Lemma lc_cex_b : lc_tm cex_b.
Proof.
  unfold cex_b. apply lc_a_App.
  - apply lc_a_UAbs. intros x. cbn [open_tm_wrt_tm]. apply lc_a_Star.
  - apply lc_a_Star.
Qed.

Lemma Par_cex_left : forall G D, Par G D cex_src cex_left.
Proof.
  intros. unfold cex_src, cex_left.
  refine (Par_Beta G D cex_f Rel cex_b (a_Conv (a_Var_b 0) g_Triv) a_Star _ _).
  - apply Par_Refl. exact lc_cex_f.
  - unfold cex_b.
    refine (Par_Beta G D (a_UAbs Rel a_Star) Rel a_Star a_Star a_Star _ _).
    + apply Par_Refl. apply lc_a_UAbs. intros x.
      cbn [open_tm_wrt_tm]. apply lc_a_Star.
    + apply Par_Refl. apply lc_a_Star.
Qed.

Lemma Par_cex_right : forall G D, Par G D cex_src cex_right.
Proof.
  intros. unfold cex_src, cex_right.
  refine (Par_Beta G D cex_f Rel cex_b (a_Conv (a_Var_b 0) g_Triv) cex_b _ _).
  - apply Par_Refl. exact lc_cex_f.
  - apply Par_Refl. exact lc_cex_b.
Qed.

Lemma Par_diamond_false :
  exists G D a b c,
    Par G D a b /\ Par G D a c /\
    (forall d, ~ (Par G D b d /\ Par G D c d)).
Proof.
  exists (@nil (atom*sort)), (empty:atoms), cex_src, cex_left, cex_right.
  split; [apply Par_cex_left | split; [apply Par_cex_right |]].
  intros d [Hbd Hcd].
  unfold cex_left in Hbd.
  pose proof (Par_Conv_inv _ _ _ _ _ Hbd) as Hd. subst d.
  unfold cex_right in Hcd.
  pose proof (Par_Conv_inv _ _ _ _ _ Hcd) as Heq.
  injection Heq as Hb.
  unfold cex_b in Hb. discriminate Hb.
Qed.

Lemma MultiPar_diamond_false :
  exists G D a b c,
    MultiPar G D a b /\ MultiPar G D a c /\
    (forall d, ~ (MultiPar G D b d /\ MultiPar G D c d)).
Proof.
  exists (@nil (atom*sort)), (empty:atoms), cex_src, cex_left, cex_right.
  split.
  - apply MP_Step with (b:=cex_left).
    + apply Par_cex_left.
    + apply MP_Refl. unfold cex_left. apply lc_a_Conv; [apply lc_a_Star | apply lc_g_Triv].
  - split.
    + apply MP_Step with (b:=cex_right).
      * apply Par_cex_right.
      * apply MP_Refl. unfold cex_right. apply lc_a_Conv; [exact lc_cex_b | apply lc_g_Triv].
    + intros d [Hbd Hcd].
      unfold cex_left in Hbd.
      pose proof (MultiPar_Conv_src_inv _ _ _ _ _ Hbd) as Hd. subst d.
      unfold cex_right in Hcd.
      pose proof (MultiPar_Conv_src_inv _ _ _ _ _ Hcd) as Heq.
      injection Heq as Hb.
      unfold cex_b in Hb. discriminate Hb.
Qed.

(* ================================================================== *)
(* Strongest true restricted diamond: terms on which Par only        *)
(* reifies (no beta/axiom redex and no congruence under a binder).   *)
(* ================================================================== *)

Inductive par_rigid : tm -> Prop :=
| pr_Star : par_rigid a_Star
| pr_Var_b : forall n, par_rigid (a_Var_b n)
| pr_Var_f : forall x, par_rigid (a_Var_f x)
| pr_Bullet : par_rigid a_Bullet
| pr_Const : forall T, par_rigid (a_Const T)
| pr_DataCon : forall K, par_rigid (a_DataCon K)
| pr_Abs : forall rho A b, par_rigid (a_Abs rho A b)
| pr_Conv : forall a g, par_rigid (a_Conv a g)
| pr_CAbs : forall phi b, par_rigid (a_CAbs phi b)
| pr_Case : forall a brs, par_rigid (a_Case a brs).

Lemma Par_rigid_inv : forall G D a b,
  par_rigid a -> Par G D a b -> b = a.
Proof.
  intros G D a b Hr Hp. induction Hr; inversion Hp; subst; reflexivity.
Qed.

Lemma MultiPar_rigid_inv : forall G D a b,
  par_rigid a -> MultiPar G D a b -> b = a.
Proof.
  intros G D a b Hr H.
  refine (MultiPar_ind (fun G D a b => par_rigid a -> b = a) _ _ G D a b H Hr).
  - intros G0 D0 x Hlc Hr0. reflexivity.
  - intros G0 D0 x x' y Hpar Hmp IH Hr0.
    pose proof (Par_rigid_inv _ _ _ _ Hr0 Hpar) as Hxy. subst y.
    apply IH. exact Hr0.
Qed.

Lemma Par_diamond_rigid : forall G D a b c,
  par_rigid a -> Par G D a b -> Par G D a c ->
  exists d, Par G D b d /\ Par G D c d.
Proof.
  intros G D a b c Hr H1 H2.
  pose proof (Par_rigid_inv _ _ _ _ Hr H1) as Hb.
  pose proof (Par_rigid_inv _ _ _ _ Hr H2) as Hc.
  subst b. subst c. exists a. split; assumption.
Qed.

Lemma MultiPar_diamond_rigid : forall G D a b c,
  par_rigid a -> MultiPar G D a b -> MultiPar G D a c ->
  exists d, MultiPar G D b d /\ MultiPar G D c d.
Proof.
  intros G D a b c Hr H1 H2.
  pose proof (MultiPar_rigid_inv _ _ _ _ Hr H1) as Hb.
  pose proof (MultiPar_rigid_inv _ _ _ _ Hr H2) as Hc.
  subst b. subst c. exists a. split; assumption.
Qed.

(* ================================================================== *)
(* The An_Assn case of Good joinability.                             *)
(* Good's second component directly supplies the required parallel   *)
(* reduct of the two erased endpoints.                               *)
(* ================================================================== *)

Lemma binds_erase_context : forall (G:context) (c:covar) (s:sort),
  binds c s G -> binds c (erase_sort s) (erase_context G).
Proof.
  intros G. induction G as [|[a s'] G IH]; intros c s H.
  - unfold binds in H. cbn in H. contradiction.
  - unfold erase_context in *. cbn [EnvImpl.map].
    unfold binds in *.
    simpl in H. destruct H as [Heq | Hin].
    + inversion Heq; subst. left. reflexivity.
    + right. apply IH. exact Hin.
Qed.

Lemma Good_Assn_join : forall G D c a b A,
  Good (erase_context G) D ->
  binds c (Co (Eq a b A)) G ->
  c `in` D ->
  exists C, Par (erase_context G) D (erase_tm a) C /\
            Par (erase_context G) D (erase_tm b) C.
Proof.
  intros G D c a b A [_ Hgood] Hb Hin.
  apply (Hgood c (erase_tm a) (erase_tm b) (erase_tm A)).
  - change (binds c (Co (Eq (erase_tm a) (erase_tm b) (erase_tm A))) (erase_context G)).
    exact (binds_erase_context G c (Co (Eq a b A)) Hb).
  - exact Hin.
Qed.

Lemma Good_Assn_MultiPar_join : forall G D c a b A,
  Good (erase_context G) D ->
  binds c (Co (Eq a b A)) G ->
  c `in` D ->
  exists C, MultiPar (erase_context G) D (erase_tm a) C /\
            MultiPar (erase_context G) D (erase_tm b) C.
Proof.
  intros G D c a b A Hg Hb Hin.
  destruct (Good_Assn_join G D c a b A Hg Hb Hin) as [C [HA HB]].
  exists C. split.
  - eapply MP_Step; [exact HA | apply MP_Refl; exact (proj2 (Par_lc _ _ _ _ HA))].
  - eapply MP_Step; [exact HB | apply MP_Refl; exact (proj2 (Par_lc _ _ _ _ HB))].
Qed.

(* ===== Sub ===== *)
Require Import Lia.
Require Import List.
Import ListNotations.

(* ================================================================== *)
(* Substituted sorts and contexts                                      *)
(* ================================================================== *)

Definition subTm_sort (x:tmvar) (u:tm) (s:sort) : sort :=
  match s with
  | Tm A => Tm (subst_tm_tm x u A)
  | Co p => Co (subst_tm_constraint x u p)
  end.

Definition subTm_ctx (x:tmvar) (u:tm) (G:context) : context :=
  map (fun q => (fst q, subTm_sort x u (snd q))) G.

Definition subCo_sort (c:covar) (g:co) (s:sort) : sort :=
  match s with
  | Tm A => Tm (subst_co_tm c g A)
  | Co p => Co (subst_co_constraint c g p)
  end.

Definition subCo_ctx (c:covar) (g:co) (G:context) : context :=
  map (fun q => (fst q, subCo_sort c g (snd q))) G.

(* ================================================================== *)
(* Generic context/list facts                                          *)
(* ================================================================== *)

Lemma subTm_ctx_app : forall x u G1 G2,
  subTm_ctx x u (G1 ++ G2) = subTm_ctx x u G1 ++ subTm_ctx x u G2.
Proof. intros. apply map_app. Qed.

Lemma subCo_ctx_app : forall c g G1 G2,
  subCo_ctx c g (G1 ++ G2) = subCo_ctx c g G1 ++ subCo_ctx c g G2.
Proof. intros. apply map_app. Qed.

Lemma dom_subTm_ctx : forall x u G, dom (subTm_ctx x u G) = dom G.
Proof.
  intros x u G. induction G as [|[y s] G IH]; cbn [subTm_ctx map dom].
  - reflexivity.
  - f_equal. exact IH.
Qed.

Lemma dom_subCo_ctx : forall c g G, dom (subCo_ctx c g G) = dom G.
Proof.
  intros c g G. induction G as [|[y s] G IH]; cbn [subCo_ctx map dom].
  - reflexivity.
  - f_equal. exact IH.
Qed.

Lemma binds_subTm_ctx : forall x u G (y:atom) s,
  binds y s G -> binds y (subTm_sort x u s) (subTm_ctx x u G).
Proof.
  intros. unfold binds in *. apply in_map with (f := fun q => (fst q, subTm_sort x u (snd q))) in H.
  cbn [fst snd] in H. exact H.
Qed.

Lemma binds_subCo_ctx : forall c g G (y:atom) s,
  binds y s G -> binds y (subCo_sort c g s) (subCo_ctx c g G).
Proof.
  intros. unfold binds in *. apply in_map with (f := fun q => (fst q, subCo_sort c g (snd q))) in H.
  cbn [fst snd] in H. exact H.
Qed.

Lemma ctx_sub_subTm_right : forall x u G1 G2,
  ctx_sub (subTm_ctx x u G2) (subTm_ctx x u G1 ++ subTm_ctx x u G2).
Proof. intros x u G1 G2 y s H. apply in_or_app. right. exact H. Qed.

Lemma ctx_sub_subCo_right : forall c g G1 G2,
  ctx_sub (subCo_ctx c g G2) (subCo_ctx c g G1 ++ subCo_ctx c g G2).
Proof. intros c g G1 G2 y s H. apply in_or_app. right. exact H. Qed.

Lemma ctx_sub_suffix : forall (G1:context) (x:atom) s G2,
  ctx_sub (G1 ++ G2) (G1 ++ (x,s) :: G2).
Proof.
  intros. intros y t H. apply in_app_iff in H. apply in_app_iff.
  destruct H as [H|H]; [left; exact H|right]. apply in_cons. exact H.
Qed.

Lemma in_dom_of_in : forall (A:Type) (l:list (atom*A)) (x:atom) (a:A),
  In (x,a) l -> x `in` dom l.
Proof. intros. apply binds_In with (a:=a). exact H. Qed.

Lemma in_remove_mid : forall (A:Type) (l1:list (atom*A)) x (a:A) l2 (c:atom) (t:A),
  In (c,t) (l1 ++ (x,a)::l2) -> c <> x -> In (c,t) (l1 ++ l2).
Proof.
  intros A l1 x a l2 c t H Hne.
  apply in_app_iff in H. destruct H as [H|H].
  - apply in_app_iff. left. exact H.
  - apply in_app_iff. right. simpl in H. destruct H as [Heq|H].
    + inversion Heq. subst. exfalso. apply Hne. reflexivity.
    + exact H.
Qed.

Lemma in_dom_remove_mid : forall (G1:context) (x:atom) s G2 (c:atom),
  c `in` dom (G1 ++ (x,s) :: G2) -> c <> x -> c `in` dom (G1 ++ G2).
Proof.
  intros. destruct (@in_dom_binds sort c (G1 ++ (x,s) :: G2) H) as [t Ht].
  apply in_dom_of_in with (a:=t). apply in_remove_mid with (x:=x) (a:=s); auto.
Qed.

Lemma uniq_cons_uniq : forall (x:atom) (a:sort) (E:context),
  uniq ((x,a)::E) -> uniq E.
Proof. intros. cbn in H. inversion H. assumption. Qed.

Lemma uniq_cons_notin : forall (x:atom) (a:sort) (E:context),
  uniq ((x,a)::E) -> x `notin` dom E.
Proof. intros. cbn in H. inversion H. assumption. Qed.

Lemma uniq_split : forall (G1:context) (x:atom) s G2,
  uniq (G1 ++ (x,s) :: G2) -> x `notin` dom G1 /\ x `notin` dom G2.
Proof.
  induction G1 as [|[y t] G1 IH]; intros x s G2 H.
  - cbn [app] in H. split.
    + apply notin_empty.
    + exact (uniq_cons_notin x s G2 H).
  - cbn [app] in H.
    pose proof (uniq_cons_notin y t (G1 ++ (x,s) :: G2) H) as Hy.
    pose proof (uniq_cons_uniq y t (G1 ++ (x,s) :: G2) H) as Htail.
    destruct (IH x s G2 Htail) as [H1 H2]. split; [|exact H2].
    intro Hx. apply AtomSetFacts.add_iff in Hx. destruct Hx as [Heq|Hin].
    + subst y. exfalso. apply Hy. apply in_dom_of_in with (a:=s).
      apply in_app_iff. right. simpl. left. reflexivity.
    + exact (H1 Hin).
Qed.

Lemma binds_split : forall (G1:context) (x:tmvar) (A0:tm) G2 (y:atom) A,
  x `notin` dom G1 -> x `notin` dom G2 ->
  binds y A (G1 ++ (x, Tm A0) :: nil ++ G2) ->
  (y = x /\ A = Tm A0) \/ (y <> x /\ binds y A (G1 ++ G2)).
Proof.
  intros G1 x A0 G2 y A Hx1 Hx2 H. unfold binds in *.
  apply in_app_iff in H. destruct H as [H|H].
  - right. split; [|apply in_app_iff; left; exact H].
    intro Heq. subst y. exfalso. apply Hx1. apply in_dom_of_in with (a:=A). exact H.
  - simpl in H. destruct H as [Heq|H].
    + left. inversion Heq. auto.
    + right. split; [|apply in_app_iff; right; exact H].
      intro Heq. subst y. exfalso. apply Hx2. apply in_dom_of_in with (a:=A). exact H.
Qed.

Lemma binds_split_co : forall (G1:context) (c:covar) (a b A:tm) G2 (y:atom) s,
  c `notin` dom G1 -> c `notin` dom G2 ->
  binds y s (G1 ++ (c, Co (Eq a b A)) :: nil ++ G2) ->
  (y = c /\ s = Co (Eq a b A)) \/ (y <> c /\ binds y s (G1 ++ G2)).
Proof.
  intros G1 c a b A G2 y s Hx1 Hx2 H. unfold binds in *.
  apply in_app_iff in H. destruct H as [H|H].
  - right. split; [|apply in_app_iff; left; exact H].
    intro Heq. subst y. exfalso. apply Hx1. apply in_dom_of_in with (a:=s). exact H.
  - simpl in H. destruct H as [Heq|H].
    + left. inversion Heq. auto.
    + right. split; [|apply in_app_iff; right; exact H].
      intro Heq. subst y. exfalso. apply Hx2. apply in_dom_of_in with (a:=s). exact H.
Qed.

(* ================================================================== *)
(* Auxiliary tactics / sorts                                          *)
(* ================================================================== *)

Ltac notin_split_all :=
  repeat match goal with
  | H : ~ AtomSetImpl.In ?x (AtomSetImpl.union ?s ?t) |- _ =>
      let H1 := fresh in let H2 := fresh in
      pose proof (notin_union_1 x s t H) as H1;
      pose proof (notin_union_2 x s t H) as H2;
      clear H
  end.

Definition fv_sort (s:sort) : vars :=
  match s with Tm A => fv_tm_tm_tm A | Co p => fv_tm_tm_constraint p end.

Definition fvx_sort (s:sort) : vars :=
  match s with Tm A => fvx_tm A | Co p => fvx_constraint p end.

Lemma in_dom_app : forall (G1 G2:context) (c:atom),
  c `in` dom (G1 ++ G2) <-> c `in` dom G1 \/ c `in` dom G2.
Proof.
  induction G1 as [|[y t] G1 IH]; intros G2 c; cbn [app dom].
  - split; intro H.
    + right. exact H.
    + destruct H as [H|H]; [exfalso; apply AtomSetFacts.empty_iff in H; exact H|exact H].
  - rewrite AtomSetFacts.add_iff.
    rewrite IH.
    rewrite AtomSetFacts.add_iff.
    tauto.
Qed.

(* ================================================================== *)
(* The two signatures                                                 *)
(* ================================================================== *)

Lemma an_toplevel_binds_ax : forall (F:atom) (a A:tm),
  binds F (Ax a A) an_toplevel -> a = FixDef /\ A = FixTy.
Proof.
  intros F a A H. unfold binds in H.
  unfold an_toplevel in H. cbn [singleton] in H.
  simpl in H. destruct H as [Heq|H]; [|contradiction].
  inversion Heq. auto.
Qed.

Lemma toplevel_binds_ax : forall (F:atom) (a A:tm),
  binds F (Ax a A) toplevel -> a = erase_tm FixDef /\ A = erase_tm FixTy.
Proof.
  intros F a A H. unfold binds in H.
  unfold toplevel, an_toplevel, erase_sig in H. cbn [map] in H.
  simpl in H. destruct H as [Heq|H]; [|contradiction].
  inversion Heq. auto.
Qed.

Lemma an_toplevel_ax_subst_tm : forall (F:atom) (a A:tm) x u,
  binds F (Ax a A) an_toplevel -> subst_tm_tm x u a = a /\ subst_tm_tm x u A = A.
Proof.
  intros F a A x u H. destruct (an_toplevel_binds_ax _ _ _ H) as [Ha HA].
  subst. cbn [subst_tm_tm]. split; reflexivity.
Qed.

Lemma an_toplevel_ax_subst_co : forall (F:atom) (a A:tm) c g,
  binds F (Ax a A) an_toplevel -> subst_co_tm c g a = a /\ subst_co_tm c g A = A.
Proof.
  intros F a A c g H. destruct (an_toplevel_binds_ax _ _ _ H) as [Ha HA].
  subst. cbn [subst_co_tm]. split; reflexivity.
Qed.

Lemma toplevel_ax_subst_tm : forall (F:atom) (a A:tm) x u,
  binds F (Ax a A) toplevel -> subst_tm_tm x u a = a.
Proof.
  intros F a A x u H. destruct (toplevel_binds_ax _ _ _ H) as [Ha HA].
  subst. cbn [subst_tm_tm erase_tm]. reflexivity.
Qed.

Lemma toplevel_ax_subst_co : forall (F:atom) (a A:tm) c g,
  binds F (Ax a A) toplevel -> subst_co_tm c g a = a.
Proof.
  intros F a A c g H. destruct (toplevel_binds_ax _ _ _ H) as [Ha HA].
  subst. cbn [subst_co_tm erase_tm]. reflexivity.
Qed.

(* ================================================================== *)
(* Erasure and substitution commutation                               *)
(* ================================================================== *)

Lemma erase_subst_tm_tm :
  (forall a x u, erase_tm (subst_tm_tm x u a) = subst_tm_tm x (erase_tm u) (erase_tm a)) /\
  (forall b x u, erase_brs (subst_tm_brs x u b) = subst_tm_brs x (erase_tm u) (erase_brs b)) /\
  (forall (g:co), True) /\
  (forall p x u, erase_constraint (subst_tm_constraint x u p) = subst_tm_constraint x (erase_tm u) (erase_constraint p)).
Proof.
  apply (tm_mutind
    (fun a => forall x u, erase_tm (subst_tm_tm x u a) = subst_tm_tm x (erase_tm u) (erase_tm a))
    (fun b => forall x u, erase_brs (subst_tm_brs x u b) = subst_tm_brs x (erase_tm u) (erase_brs b))
    (fun g => True)
    (fun p => forall x u, erase_constraint (subst_tm_constraint x u p) = subst_tm_constraint x (erase_tm u) (erase_constraint p))).
  all: try solve [intros; cbn [subst_tm_tm subst_tm_brs subst_tm_co subst_tm_constraint erase_tm erase_brs erase_constraint];
                  try reflexivity; try (f_equal; auto 20)].
  all: try solve [intros; cbn [subst_tm_tm subst_tm_co erase_tm];
                  try match goal with |- context [KeySetFacts.eq_dec ?a ?b] =>
                        destruct (KeySetFacts.eq_dec a b) as [e|e]; simpl
                  end;
                  try reflexivity; try (subst; rewrite subst_tm_var_eq); reflexivity].
  all: try solve [intros; cbn [subst_tm_tm subst_tm_co erase_tm];
                  try (match goal with r : relflag |- _ => destruct r; cbn [subst_tm_tm subst_tm_co erase_tm] end);
                  f_equal; eauto 10].
  all: try exact I.
Qed.

Lemma notin_subst_tm_tm :
  (forall a x u y, y `notin` fv_tm_tm_tm a -> y `notin` fv_tm_tm_tm u ->
      y `notin` fv_tm_tm_tm (subst_tm_tm x u a)) /\
  (forall b x u y, y `notin` fv_tm_tm_brs b -> y `notin` fv_tm_tm_tm u ->
      y `notin` fv_tm_tm_brs (subst_tm_brs x u b)) /\
  (forall g x u y, y `notin` fv_tm_tm_co g -> y `notin` fv_tm_tm_tm u ->
      y `notin` fv_tm_tm_co (subst_tm_co x u g)) /\
  (forall p x u y, y `notin` fv_tm_tm_constraint p -> y `notin` fv_tm_tm_tm u ->
      y `notin` fv_tm_tm_constraint (subst_tm_constraint x u p)).
Proof.
  apply (tm_mutind
    (fun a => forall x u y, y `notin` fv_tm_tm_tm a -> y `notin` fv_tm_tm_tm u ->
        y `notin` fv_tm_tm_tm (subst_tm_tm x u a))
    (fun b => forall x u y, y `notin` fv_tm_tm_brs b -> y `notin` fv_tm_tm_tm u ->
        y `notin` fv_tm_tm_brs (subst_tm_brs x u b))
    (fun g => forall x u y, y `notin` fv_tm_tm_co g -> y `notin` fv_tm_tm_tm u ->
        y `notin` fv_tm_tm_co (subst_tm_co x u g))
    (fun p => forall x u y, y `notin` fv_tm_tm_constraint p -> y `notin` fv_tm_tm_tm u ->
        y `notin` fv_tm_tm_constraint (subst_tm_constraint x u p))).
  all: try solve [intros; cbn [subst_tm_tm subst_tm_brs subst_tm_co subst_tm_constraint
                                 fv_tm_tm_tm fv_tm_tm_brs fv_tm_tm_co fv_tm_tm_constraint] in *;
                  try (apply AtomSetImpl.union_3); try (apply AtomSetImpl.union_2);
                  notin_destruct; auto;
                  try (apply AtomSetImpl.union_3); try (apply AtomSetImpl.union_2); auto].
  all: try solve [intros; cbn [subst_tm_tm];
                  match goal with |- context [KeySetFacts.eq_dec ?a ?b] =>
                    destruct (KeySetFacts.eq_dec a b) as [e|e]; simpl; auto end].
Qed.

Lemma erase_subst_co_tm :
  (forall a c g, erase_tm (subst_co_tm c g a) = erase_tm a) /\
  (forall b c g, erase_brs (subst_co_brs c g b) = erase_brs b) /\
  (forall (h:co), True) /\
  (forall p c g, erase_constraint (subst_co_constraint c g p) = erase_constraint p).
Proof.
  apply (tm_mutind
    (fun a => forall c g, erase_tm (subst_co_tm c g a) = erase_tm a)
    (fun b => forall c g, erase_brs (subst_co_brs c g b) = erase_brs b)
    (fun h => True)
    (fun p => forall c g, erase_constraint (subst_co_constraint c g p) = erase_constraint p)).
  all: try solve [intros; cbn [subst_co_tm subst_co_brs subst_co_co subst_co_constraint
                                 erase_tm erase_brs erase_constraint];
                  try reflexivity; try (f_equal; auto 20)].
  all: try solve [intros; cbn [subst_co_tm erase_tm];
                  try (match goal with r : relflag |- _ => destruct r; cbn [subst_co_tm erase_tm] end);
                  f_equal; eauto 10].
  all: try solve [intros; cbn [subst_co_tm erase_tm]; eauto 20].
  all: try exact I.
Qed.

(* ================================================================== *)
(* Substitution is the identity on objects avoiding the variable      *)
(* ================================================================== *)

Lemma subst_tm_tm_id_notin_all :
  (forall a x u, x `notin` fv_tm_tm_tm a -> subst_tm_tm x u a = a) /\
  (forall b x u, x `notin` fv_tm_tm_brs b -> subst_tm_brs x u b = b) /\
  (forall g x u, x `notin` fv_tm_tm_co g -> subst_tm_co x u g = g) /\
  (forall p x u, x `notin` fv_tm_tm_constraint p -> subst_tm_constraint x u p = p).
Proof.
  apply (tm_mutind
    (fun a => forall x u, x `notin` fv_tm_tm_tm a -> subst_tm_tm x u a = a)
    (fun b => forall x u, x `notin` fv_tm_tm_brs b -> subst_tm_brs x u b = b)
    (fun g => forall x u, x `notin` fv_tm_tm_co g -> subst_tm_co x u g = g)
    (fun p => forall x u, x `notin` fv_tm_tm_constraint p -> subst_tm_constraint x u p = p)).
  all: try solve [intros; cbn [subst_tm_tm subst_tm_brs subst_tm_co subst_tm_constraint
                                 fv_tm_tm_tm fv_tm_tm_brs fv_tm_tm_co fv_tm_tm_constraint] in *;
                  notin_split_all; try reflexivity; try (f_equal; eauto 20)].
  (* a_Var_f *)
  intros y x u H. cbn [subst_tm_tm fv_tm_tm_tm] in *.
  destruct (KeySetFacts.eq_dec y x) as [Heq|Hneq]; [|reflexivity].
  exfalso. apply (notin_singleton_1 y x H). exact Heq.
Qed.

Lemma subst_co_tm_id_fresh_all :
  (forall a c g, c `notin` fvx_tm a -> subst_co_tm c g a = a) /\
  (forall b c g, c `notin` fvx_brs b -> subst_co_brs c g b = b) /\
  (forall h c g, c `notin` fvx_co h -> subst_co_co c g h = h) /\
  (forall p c g, c `notin` fvx_constraint p -> subst_co_constraint c g p = p).
Proof.
  apply (tm_mutind
    (fun a => forall c g, c `notin` fvx_tm a -> subst_co_tm c g a = a)
    (fun b => forall c g, c `notin` fvx_brs b -> subst_co_brs c g b = b)
    (fun h => forall c g, c `notin` fvx_co h -> subst_co_co c g h = h)
    (fun p => forall c g, c `notin` fvx_constraint p -> subst_co_constraint c g p = p)).
  all: try solve [intros; cbn [subst_co_tm subst_co_brs subst_co_co subst_co_constraint
                                 fvx_tm fvx_brs fvx_co fvx_constraint] in *;
                  notin_split_all; try reflexivity; try (f_equal; eauto 20)].
  (* g_Var_f *)
  intros y c g H. cbn [subst_co_co fvx_co] in *.
  destruct (KeySetFacts.eq_dec y c) as [Heq|Hneq]; [|reflexivity].
  exfalso. apply H. apply AtomSetFacts.singleton_iff. exact Heq.
Qed.

Lemma subst_tm_sort_id : forall x u s,
  x `notin` fv_sort s -> subTm_sort x u s = s.
Proof.
  intros x u [A|p] H; cbn [fv_sort subTm_sort] in *.
  - f_equal. exact (proj1 subst_tm_tm_id_notin_all A x u H).
  - f_equal. exact (proj2 (proj2 (proj2 subst_tm_tm_id_notin_all)) p x u H).
Qed.

Lemma subst_co_sort_id : forall c g s,
  c `notin` fvx_sort s -> subCo_sort c g s = s.
Proof.
  intros c g [A|p] H; cbn [fvx_sort subCo_sort] in *.
  - f_equal. exact (proj1 subst_co_tm_id_fresh_all A c g H).
  - f_equal. exact (proj2 (proj2 (proj2 subst_co_tm_id_fresh_all)) p c g H).
Qed.

Lemma subTm_ctx_id : forall x u G,
  (forall y s, binds y s G -> x `notin` fv_sort s) -> subTm_ctx x u G = G.
Proof.
  intros x u G H. induction G as [|[y s] G IH].
  - reflexivity.
  - cbn [subTm_ctx map]. f_equal.
    + f_equal. apply subst_tm_sort_id. apply (H y s). simpl. left. reflexivity.
    + apply IH. intros z t Hzt. apply (H z t). simpl. right. exact Hzt.
Qed.

Lemma subCo_ctx_id : forall c g G,
  (forall y s, binds y s G -> c `notin` fvx_sort s) -> subCo_ctx c g G = G.
Proof.
  intros c g G H. induction G as [|[y s] G IH].
  - reflexivity.
  - cbn [subCo_ctx map]. f_equal.
    + f_equal. apply subst_co_sort_id. apply (H y s). simpl. left. reflexivity.
    + apply IH. intros z t Hzt. apply (H z t). simpl. right. exact Hzt.
Qed.

(* ================================================================== *)
(* Erasure commutes with opening                                      *)
(* ================================================================== *)

Lemma erase_open_tm_tm_all :
  (forall a k u, erase_tm (open_tm_wrt_tm_rec k u a) = open_tm_wrt_tm_rec k (erase_tm u) (erase_tm a)) /\
  (forall b k u, erase_brs (open_brs_wrt_tm_rec k u b) = open_brs_wrt_tm_rec k (erase_tm u) (erase_brs b)) /\
  (forall (g:co), True) /\
  (forall p k u, erase_constraint (open_constraint_wrt_tm_rec k u p) = open_constraint_wrt_tm_rec k (erase_tm u) (erase_constraint p)).
Proof.
  apply (tm_mutind
    (fun a => forall k u, erase_tm (open_tm_wrt_tm_rec k u a) = open_tm_wrt_tm_rec k (erase_tm u) (erase_tm a))
    (fun b => forall k u, erase_brs (open_brs_wrt_tm_rec k u b) = open_brs_wrt_tm_rec k (erase_tm u) (erase_brs b))
    (fun g => True)
    (fun p => forall k u, erase_constraint (open_constraint_wrt_tm_rec k u p) = open_constraint_wrt_tm_rec k (erase_tm u) (erase_constraint p))).
  all: try solve [intros; cbn [open_tm_wrt_tm_rec open_brs_wrt_tm_rec open_co_wrt_tm_rec
                                 open_constraint_wrt_tm_rec erase_tm erase_brs erase_constraint];
                  try reflexivity; try (f_equal; eauto 20)].
  all: try solve [intros; cbn [open_tm_wrt_tm_rec open_co_wrt_tm_rec erase_tm];
                  try (match goal with r : relflag |- _ => destruct r; cbn [erase_tm open_tm_wrt_tm_rec] end);
                  try (match goal with |- context [lt_eq_lt_dec ?a ?b] =>
                         destruct (lt_eq_lt_dec a b) as [[?|?]|?]; cbn [erase_tm] end);
                  try reflexivity; try (f_equal; eauto 20)].
  all: try exact I.
Qed.

Lemma erase_open_co_all :
  (forall a k g, erase_tm (open_tm_wrt_co_rec k g a) = erase_tm a) /\
  (forall b k g, erase_brs (open_brs_wrt_co_rec k g b) = erase_brs b) /\
  (forall (h:co), True) /\
  (forall p k g, erase_constraint (open_constraint_wrt_co_rec k g p) = erase_constraint p).
Proof.
  apply (tm_mutind
    (fun a => forall k g, erase_tm (open_tm_wrt_co_rec k g a) = erase_tm a)
    (fun b => forall k g, erase_brs (open_brs_wrt_co_rec k g b) = erase_brs b)
    (fun h => True)
    (fun p => forall k g, erase_constraint (open_constraint_wrt_co_rec k g p) = erase_constraint p)).
  all: try solve [intros; cbn [open_tm_wrt_co_rec open_brs_wrt_co_rec open_co_wrt_co_rec
                                 open_constraint_wrt_co_rec erase_tm erase_brs erase_constraint];
                  try reflexivity; try (f_equal; eauto 20)].
  - intros a IHA rho b IHb k g.
    destruct rho; cbn [erase_tm open_tm_wrt_co_rec]; f_equal; eauto 20.
  - intros a IHA g Hg k g0. cbn [erase_tm open_tm_wrt_co_rec open_co_wrt_co_rec].
    exact (IHA k g0).
  all: try exact I.
Qed.

Lemma erase_open_tm_var : forall a y,
  erase_tm (open_tm_wrt_tm a (a_Var_f y)) = open_tm_wrt_tm (erase_tm a) (a_Var_f y).
Proof.
  intros. exact (proj1 erase_open_tm_tm_all a 0 (a_Var_f y)).
Qed.

Lemma erase_open_co_tm : forall a g,
  erase_tm (open_tm_wrt_co a g) = erase_tm a.
Proof.
  intros. exact (proj1 erase_open_co_all a 0 g).
Qed.

Lemma erase_open_co_constraint : forall p g,
  erase_constraint (open_constraint_wrt_co_rec 0 g p) = erase_constraint p.
Proof.
  intros. exact (proj2 (proj2 (proj2 erase_open_co_all)) p 0 g).
Qed.

(* erased terms have no coercion bvars, so co-opening them is the identity *)
Lemma erase_co_closed_all :
  (forall a k g, open_tm_wrt_co_rec k g (erase_tm a) = erase_tm a) /\
  (forall b k g, open_brs_wrt_co_rec k g (erase_brs b) = erase_brs b) /\
  (forall (h:co), True) /\
  (forall p k g, open_constraint_wrt_co_rec k g (erase_constraint p) = erase_constraint p).
Proof.
  apply (tm_mutind
    (fun a => forall k g, open_tm_wrt_co_rec k g (erase_tm a) = erase_tm a)
    (fun b => forall k g, open_brs_wrt_co_rec k g (erase_brs b) = erase_brs b)
    (fun h => True)
    (fun p => forall k g, open_constraint_wrt_co_rec k g (erase_constraint p) = erase_constraint p)).
  all: try solve [intros; cbn [erase_tm erase_brs erase_constraint
                                 open_tm_wrt_co_rec open_brs_wrt_co_rec open_co_wrt_co_rec
                                 open_constraint_wrt_co_rec];
                  try reflexivity; try (f_equal; eauto 20)].
  all: try solve [intros; cbn [erase_tm open_tm_wrt_co_rec];
                  try (match goal with r : relflag |- _ => destruct r; cbn [erase_tm open_tm_wrt_co_rec] end);
                  try reflexivity; try (f_equal; eauto 20)].
  all: try exact I.
Qed.

Lemma erase_co_closed_tm : forall a k g,
  open_tm_wrt_co_rec k g (erase_tm a) = erase_tm a.
Proof. intros. exact (proj1 erase_co_closed_all a k g). Qed.

Lemma erase_co_closed_constraint : forall p k g,
  open_constraint_wrt_co_rec k g (erase_constraint p) = erase_constraint p.
Proof. intros. exact (proj2 (proj2 (proj2 erase_co_closed_all)) p k g). Qed.

Lemma open_co_erase : forall (a:tm) (g:co),
  open_tm_wrt_co (erase_tm a) g = erase_tm a.
Proof. intros. unfold open_tm_wrt_co. apply erase_co_closed_tm. Qed.

(* ================================================================== *)
(* Local closedness is preserved by erasure                           *)
(* ================================================================== *)

Lemma lc_erase_all :
  (forall a, lc_tm a -> lc_tm (erase_tm a)) /\
  (forall g, lc_co g -> True) /\
  (forall b, lc_brs b -> lc_brs (erase_brs b)) /\
  (forall p, lc_constraint p -> lc_constraint (erase_constraint p)).
Proof.
  apply (lc_mutind
    (fun a (l:lc_tm a) => lc_tm (erase_tm a))
    (fun g (l:lc_co g) => True)
    (fun b (l:lc_brs b) => lc_brs (erase_brs b))
    (fun p (l:lc_constraint p) => lc_constraint (erase_constraint p))).
  all: try solve [intros; cbn [erase_tm erase_brs erase_constraint];
                  try constructor; eauto 20].
  (* lc_a_Abs *)
  - intros rho A b lA IHA lbody IHb. cbn [erase_tm].
    apply lc_a_UAbs. intro y.
    specialize (IHb y). rewrite erase_open_tm_var in IHb. exact IHb.
  (* lc_a_UAbs *)
  - intros rho b lbody IHb. cbn [erase_tm].
    apply lc_a_UAbs. intro y.
    specialize (IHb y). rewrite erase_open_tm_var in IHb. exact IHb.
  (* lc_a_App *)
  - intros a rho b lA IHA lB IHB. cbn [erase_tm].
    destruct rho; cbn [erase_tm].
    + constructor; eauto.
    + apply lc_a_App; [exact IHA | constructor].
  (* lc_a_Pi *)
  - intros rho A B lA IHA lbody IHB. cbn [erase_tm].
    apply lc_a_Pi.
    + exact IHA.
    + intro y. specialize (IHB y). rewrite erase_open_tm_var in IHB. exact IHB.
  (* lc_a_CPi *)
  - intros phi B lphi IHP lbody IHB. cbn [erase_tm].
    apply lc_a_CPi.
    + exact IHP.
    + intro c. specialize (IHB c).
      rewrite erase_open_co_tm in IHB.
      rewrite (open_co_erase B (g_Var_f c)).
      exact IHB.
  (* lc_a_CAbs *)
  - intros phi b lphi IHP lbody IHb. cbn [erase_tm].
    apply lc_a_UCAbs. intro c. specialize (IHb c).
    rewrite erase_open_co_tm in IHb.
    rewrite (open_co_erase b (g_Var_f c)).
    exact IHb.
  (* lc_a_UCAbs *)
  - intros b lbody IHb. cbn [erase_tm].
    apply lc_a_UCAbs. intro c. specialize (IHb c).
    rewrite erase_open_co_tm in IHb.
    rewrite (open_co_erase b (g_Var_f c)).
    exact IHb.
  (* lc_a_CApp *)
  - intros a g lA IHA Hg Ht. cbn [erase_tm].
    apply lc_a_CApp; [exact IHA | constructor].
Qed.

(* ================================================================== *)
(* Commutation helpers at wrapper level                               *)
(* ================================================================== *)

Lemma subst_tm_tm_var_eq : forall x u,
  subst_tm_tm x u (a_Var_f x) = u.
Proof.
  intros. cbn [subst_tm_tm].
  destruct (KeySetFacts.eq_dec x x) as [e|n]; [reflexivity|exfalso; apply n; reflexivity].
Qed.

Lemma subst_tm_tm_var_neq : forall x y u,
  y <> x -> subst_tm_tm x u (a_Var_f y) = a_Var_f y.
Proof.
  intros. cbn [subst_tm_tm].
  destruct (KeySetFacts.eq_dec y x) as [e|n]; [exfalso; apply H; exact e|reflexivity].
Qed.

Lemma subst_co_co_var_eq : forall c g,
  subst_co_co c g (g_Var_f c) = g.
Proof.
  intros. cbn [subst_co_co].
  destruct (KeySetFacts.eq_dec c c) as [e|n]; [reflexivity|exfalso; apply n; reflexivity].
Qed.

Lemma subst_co_co_var_neq : forall c d g,
  d <> c -> subst_co_co c g (g_Var_f d) = g_Var_f d.
Proof.
  intros. cbn [subst_co_co].
  destruct (KeySetFacts.eq_dec d c) as [e|n]; [exfalso; apply H; exact e|reflexivity].
Qed.

Lemma subst_tm_open_tm_var : forall b x u y, lc_tm u ->
  subst_tm_tm x u (open_tm_wrt_tm b (a_Var_f y)) =
  open_tm_wrt_tm (subst_tm_tm x u b) (subst_tm_tm x u (a_Var_f y)).
Proof.
  intros. unfold open_tm_wrt_tm. apply (proj1 subst_tm_open_tm b x u y 0 H).
Qed.

Lemma subst_tm_open_tm_v : forall b x u v, lc_tm u ->
  subst_tm_tm x u (open_tm_wrt_tm b v) =
  open_tm_wrt_tm (subst_tm_tm x u b) (subst_tm_tm x u v).
Proof.
  intros. unfold open_tm_wrt_tm. apply (proj1 subst_tm_open_co_tm b x u v 0 H).
Qed.

Lemma subst_tm_open_tm_co_var : forall b x u c, lc_tm u ->
  subst_tm_tm x u (open_tm_wrt_co b (g_Var_f c)) =
  open_tm_wrt_co (subst_tm_tm x u b) (subst_tm_co x u (g_Var_f c)).
Proof.
  intros. unfold open_tm_wrt_co. apply (proj1 subst_tm_open_tm_co b x u (g_Var_f c) 0 H).
Qed.

Lemma subst_tm_open_tm_co_g : forall b x u g, lc_tm u ->
  subst_tm_tm x u (open_tm_wrt_co b g) =
  open_tm_wrt_co (subst_tm_tm x u b) (subst_tm_co x u g).
Proof.
  intros. unfold open_tm_wrt_co. apply (proj1 subst_tm_open_tm_co b x u g 0 H).
Qed.

Lemma subst_tm_open_co_wrt_tm_var : forall h x u y, lc_tm u ->
  subst_tm_co x u (open_co_wrt_tm h (a_Var_f y)) =
  open_co_wrt_tm (subst_tm_co x u h) (subst_tm_tm x u (a_Var_f y)).
Proof.
  intros. unfold open_co_wrt_tm. apply (proj1 (proj2 (proj2 subst_tm_open_tm)) h x u y 0 H).
Qed.

Lemma subst_tm_open_co_wrt_tm_v : forall h x u v, lc_tm u ->
  subst_tm_co x u (open_co_wrt_tm h v) =
  open_co_wrt_tm (subst_tm_co x u h) (subst_tm_tm x u v).
Proof.
  intros. unfold open_co_wrt_tm. apply (proj1 (proj2 (proj2 subst_tm_open_co_tm)) h x u v 0 H).
Qed.

Lemma subst_tm_open_co_co_var : forall h x u d, lc_tm u ->
  subst_tm_co x u (open_co_wrt_co h (g_Var_f d)) =
  open_co_wrt_co (subst_tm_co x u h) (subst_tm_co x u (g_Var_f d)).
Proof.
  intros. unfold open_co_wrt_co. apply (proj1 (proj2 (proj2 subst_tm_open_tm_co)) h x u (g_Var_f d) 0 H).
Qed.

Lemma subst_tm_open_co_co_g : forall h x u g, lc_tm u ->
  subst_tm_co x u (open_co_wrt_co h g) =
  open_co_wrt_co (subst_tm_co x u h) (subst_tm_co x u g).
Proof.
  intros. unfold open_co_wrt_co. apply (proj1 (proj2 (proj2 subst_tm_open_tm_co)) h x u g 0 H).
Qed.

Lemma subst_co_open_tm_var : forall a c g y, lc_co g ->
  subst_co_tm c g (open_tm_wrt_tm a (a_Var_f y)) =
  open_tm_wrt_tm (subst_co_tm c g a) (a_Var_f y).
Proof.
  intros. unfold open_tm_wrt_tm. rewrite (proj1 subst_co_open_tm a c g (a_Var_f y) 0 H).
  cbn [subst_co_tm]. reflexivity.
Qed.

Lemma subst_co_open_tm_v : forall a c g v, lc_co g ->
  subst_co_tm c g (open_tm_wrt_tm a v) =
  open_tm_wrt_tm (subst_co_tm c g a) (subst_co_tm c g v).
Proof.
  intros. unfold open_tm_wrt_tm. apply (proj1 subst_co_open_tm a c g v 0 H).
Qed.

Lemma subst_co_open_tm_co_var : forall a c g d, lc_co g ->
  subst_co_tm c g (open_tm_wrt_co a (g_Var_f d)) =
  open_tm_wrt_co (subst_co_tm c g a) (subst_co_co c g (g_Var_f d)).
Proof.
  intros. unfold open_tm_wrt_co. apply (proj1 subst_co_open_co a c g d 0 H).
Qed.

Lemma subst_co_open_tm_co_h : forall a c g h, lc_co g ->
  subst_co_tm c g (open_tm_wrt_co a h) =
  open_tm_wrt_co (subst_co_tm c g a) (subst_co_co c g h).
Proof.
  intros. unfold open_tm_wrt_co. apply (proj1 subst_co_open_tm_co a c g h 0 H).
Qed.

Lemma subst_co_open_co_tm_var : forall h c g y, lc_co g ->
  subst_co_co c g (open_co_wrt_tm h (a_Var_f y)) =
  open_co_wrt_tm (subst_co_co c g h) (a_Var_f y).
Proof.
  intros. unfold open_co_wrt_tm. rewrite (proj1 (proj2 (proj2 subst_co_open_tm)) h c g (a_Var_f y) 0 H).
  cbn [subst_co_tm]. reflexivity.
Qed.

Lemma subst_co_open_co_tm_v : forall h c g v, lc_co g ->
  subst_co_co c g (open_co_wrt_tm h v) =
  open_co_wrt_tm (subst_co_co c g h) (subst_co_tm c g v).
Proof.
  intros. unfold open_co_wrt_tm. apply (proj1 (proj2 (proj2 subst_co_open_tm)) h c g v 0 H).
Qed.

Lemma subst_co_open_co_co_var : forall h c g d, lc_co g ->
  subst_co_co c g (open_co_wrt_co h (g_Var_f d)) =
  open_co_wrt_co (subst_co_co c g h) (subst_co_co c g (g_Var_f d)).
Proof.
  intros. unfold open_co_wrt_co. apply (proj1 (proj2 (proj2 subst_co_open_co)) h c g d 0 H).
Qed.

Lemma subst_co_open_co_co_h : forall h c g h2, lc_co g ->
  subst_co_co c g (open_co_wrt_co h h2) =
  open_co_wrt_co (subst_co_co c g h) (subst_co_co c g h2).
Proof.
  intros. unfold open_co_wrt_co. apply (proj1 (proj2 (proj2 subst_co_open_tm_co)) h c g h2 0 H).
Qed.

(* ================================================================== *)
(* Local closedness is preserved by term substitution                 *)
(* ================================================================== *)

Lemma lc_subst_tm_all :
  (forall a, lc_tm a -> forall x u, lc_tm u -> lc_tm (subst_tm_tm x u a)) /\
  (forall g, lc_co g -> forall x u, lc_tm u -> lc_co (subst_tm_co x u g)) /\
  (forall b, lc_brs b -> forall x u, lc_tm u -> lc_brs (subst_tm_brs x u b)) /\
  (forall p, lc_constraint p -> forall x u, lc_tm u -> lc_constraint (subst_tm_constraint x u p)).
Proof.
  apply (lc_mutind
    (fun a (l:lc_tm a) => forall x u, lc_tm u -> lc_tm (subst_tm_tm x u a))
    (fun g (l:lc_co g) => forall x u, lc_tm u -> lc_co (subst_tm_co x u g))
    (fun b (l:lc_brs b) => forall x u, lc_tm u -> lc_brs (subst_tm_brs x u b))
    (fun p (l:lc_constraint p) => forall x u, lc_tm u -> lc_constraint (subst_tm_constraint x u p))).
  all: try solve [intros; cbn [subst_tm_tm subst_tm_brs subst_tm_co subst_tm_constraint];
                  try constructor; eauto 20].
  (* lc_a_Var_f *)
  - intros y x u Hu. cbn [subst_tm_tm].
    destruct (KeySetFacts.eq_dec y x) as [e|n].
    + subst y. exact Hu.
    + constructor.
  (* lc_a_Abs *)
  - intros rho A b lA IHA lbody IHb x u Hu. cbn [subst_tm_tm].
    apply lc_a_Abs.
    + apply IHA. exact Hu.
    + intro y. specialize (IHb y x u Hu).
      rewrite (subst_tm_open_tm_var b x u y Hu) in IHb.
      destruct (KeySetFacts.eq_dec y x) as [e|n].
      * subst y. rewrite subst_tm_tm_var_eq in IHb.
        eapply lc_open_tm_any; [exact Hu | exact IHb].
      * rewrite (subst_tm_tm_var_neq x y u n) in IHb. exact IHb.
  (* lc_a_UAbs *)
  - intros rho b lbody IHb x u Hu. cbn [subst_tm_tm].
    apply lc_a_UAbs. intro y. specialize (IHb y x u Hu).
    rewrite (subst_tm_open_tm_var b x u y Hu) in IHb.
    destruct (KeySetFacts.eq_dec y x) as [e|n].
    + subst y. rewrite subst_tm_tm_var_eq in IHb.
      eapply lc_open_tm_any; [exact Hu | exact IHb].
    + rewrite (subst_tm_tm_var_neq x y u n) in IHb. exact IHb.
  (* lc_a_Pi *)
  - intros rho A B lA IHA lbody IHB x u Hu. cbn [subst_tm_tm].
    apply lc_a_Pi.
    + apply IHA. exact Hu.
    + intro y. specialize (IHB y x u Hu).
      rewrite (subst_tm_open_tm_var B x u y Hu) in IHB.
      destruct (KeySetFacts.eq_dec y x) as [e|n].
      * subst y. rewrite subst_tm_tm_var_eq in IHB.
        eapply lc_open_tm_any; [exact Hu | exact IHB].
      * rewrite (subst_tm_tm_var_neq x y u n) in IHB. exact IHB.
  (* lc_a_CPi *)
  - intros phi B lphi IHP lbody IHB x u Hu. cbn [subst_tm_tm].
    apply lc_a_CPi.
    + apply IHP. exact Hu.
    + intro c. specialize (IHB c x u Hu).
      rewrite (subst_tm_open_tm_co_var B x u c Hu) in IHB.
      cbn [subst_tm_co] in IHB. exact IHB.
  (* lc_a_CAbs *)
  - intros phi b lphi IHP lbody IHb x u Hu. cbn [subst_tm_tm].
    apply lc_a_CAbs.
    + apply IHP. exact Hu.
    + intro c. specialize (IHb c x u Hu).
      rewrite (subst_tm_open_tm_co_var b x u c Hu) in IHb.
      cbn [subst_tm_co] in IHb. exact IHb.
  (* lc_a_UCAbs *)
  - intros b lbody IHb x u Hu. cbn [subst_tm_tm].
    apply lc_a_UCAbs. intro c. specialize (IHb c x u Hu).
    rewrite (subst_tm_open_tm_co_var b x u c Hu) in IHb.
    cbn [subst_tm_co] in IHb. exact IHb.
  (* lc_g_PiCong *)
  - intros rho g1 g2 l1 IH1 l2 IH2 x u Hu. cbn [subst_tm_co].
    apply lc_g_PiCong.
    + apply IH1. exact Hu.
    + intro y. specialize (IH2 y x u Hu).
      rewrite (subst_tm_open_co_wrt_tm_var g2 x u y Hu) in IH2.
      destruct (KeySetFacts.eq_dec y x) as [e|n].
      * subst y. rewrite subst_tm_tm_var_eq in IH2.
        eapply lc_open_co_tm_any; [exact Hu | exact IH2].
      * rewrite (subst_tm_tm_var_neq x y u n) in IH2. exact IH2.
  (* lc_g_AbsCong *)
  - intros rho g1 g2 l1 IH1 l2 IH2 x u Hu. cbn [subst_tm_co].
    apply lc_g_AbsCong.
    + apply IH1. exact Hu.
    + intro y. specialize (IH2 y x u Hu).
      rewrite (subst_tm_open_co_wrt_tm_var g2 x u y Hu) in IH2.
      destruct (KeySetFacts.eq_dec y x) as [e|n].
      * subst y. rewrite subst_tm_tm_var_eq in IH2.
        eapply lc_open_co_tm_any; [exact Hu | exact IH2].
      * rewrite (subst_tm_tm_var_neq x y u n) in IH2. exact IH2.
  (* lc_g_CPiCong *)
  - intros g1 g3 l1 IH1 l2 IH2 x u Hu. cbn [subst_tm_co].
    apply lc_g_CPiCong.
    + apply IH1. exact Hu.
    + intro c. specialize (IH2 c x u Hu).
      rewrite (subst_tm_open_co_co_var g3 x u c Hu) in IH2.
      cbn [subst_tm_co] in IH2. exact IH2.
  (* lc_g_CAbsCong *)
  - intros g1 g3 g4 l1 IH1 l2 IH2 l4 IH4 x u Hu. cbn [subst_tm_co].
    apply lc_g_CAbsCong.
    + apply IH1. exact Hu.
    + intro c. specialize (IH2 c x u Hu).
      rewrite (subst_tm_open_co_co_var g3 x u c Hu) in IH2.
      cbn [subst_tm_co] in IH2. exact IH2.
    + apply IH4. exact Hu.
Qed.

(* ================================================================== *)
(* Local closedness is preserved by coercion substitution             *)
(* ================================================================== *)

Lemma lc_subst_co_all :
  (forall a, lc_tm a -> forall c g, lc_co g -> lc_tm (subst_co_tm c g a)) /\
  (forall h, lc_co h -> forall c g, lc_co g -> lc_co (subst_co_co c g h)) /\
  (forall b, lc_brs b -> forall c g, lc_co g -> lc_brs (subst_co_brs c g b)) /\
  (forall p, lc_constraint p -> forall c g, lc_co g -> lc_constraint (subst_co_constraint c g p)).
Proof.
  apply (lc_mutind
    (fun a (l:lc_tm a) => forall c g, lc_co g -> lc_tm (subst_co_tm c g a))
    (fun h (l:lc_co h) => forall c g, lc_co g -> lc_co (subst_co_co c g h))
    (fun b (l:lc_brs b) => forall c g, lc_co g -> lc_brs (subst_co_brs c g b))
    (fun p (l:lc_constraint p) => forall c g, lc_co g -> lc_constraint (subst_co_constraint c g p))).
  all: try solve [intros; cbn [subst_co_tm subst_co_brs subst_co_co subst_co_constraint];
                  try constructor; eauto 20].
  (* lc_a_Abs *)
  - intros rho A b lA IHA lbody IHb c g Hg. cbn [subst_co_tm].
    apply lc_a_Abs.
    + apply IHA. exact Hg.
    + intro y. specialize (IHb y c g Hg).
      rewrite (subst_co_open_tm_var b c g y Hg) in IHb. exact IHb.
  (* lc_a_UAbs *)
  - intros rho b lbody IHb c g Hg. cbn [subst_co_tm].
    apply lc_a_UAbs. intro y. specialize (IHb y c g Hg).
    rewrite (subst_co_open_tm_var b c g y Hg) in IHb. exact IHb.
  (* lc_a_Pi *)
  - intros rho A B lA IHA lbody IHB c g Hg. cbn [subst_co_tm].
    apply lc_a_Pi.
    + apply IHA. exact Hg.
    + intro y. specialize (IHB y c g Hg).
      rewrite (subst_co_open_tm_var B c g y Hg) in IHB. exact IHB.
  (* lc_a_CPi *)
  - intros phi B lphi IHP lbody IHB c g Hg. cbn [subst_co_tm].
    apply lc_a_CPi.
    + apply IHP. exact Hg.
    + intro d. specialize (IHB d c g Hg).
      rewrite (subst_co_open_tm_co_var B c g d Hg) in IHB.
      destruct (KeySetFacts.eq_dec d c) as [e|n].
      * subst d. rewrite subst_co_co_var_eq in IHB.
        eapply lc_open_tm_co_any; [exact Hg | exact IHB | constructor].
      * rewrite (subst_co_co_var_neq c d g n) in IHB. exact IHB.
  (* lc_a_CAbs *)
  - intros phi b lphi IHP lbody IHb c g Hg. cbn [subst_co_tm].
    apply lc_a_CAbs.
    + apply IHP. exact Hg.
    + intro d. specialize (IHb d c g Hg).
      rewrite (subst_co_open_tm_co_var b c g d Hg) in IHb.
      destruct (KeySetFacts.eq_dec d c) as [e|n].
      * subst d. rewrite subst_co_co_var_eq in IHb.
        eapply lc_open_tm_co_any; [exact Hg | exact IHb | constructor].
      * rewrite (subst_co_co_var_neq c d g n) in IHb. exact IHb.
  (* lc_a_UCAbs *)
  - intros b lbody IHb c g Hg. cbn [subst_co_tm].
    apply lc_a_UCAbs. intro d. specialize (IHb d c g Hg).
    rewrite (subst_co_open_tm_co_var b c g d Hg) in IHb.
    destruct (KeySetFacts.eq_dec d c) as [e|n].
    + subst d. rewrite subst_co_co_var_eq in IHb.
      eapply lc_open_tm_co_any; [exact Hg | exact IHb | constructor].
    + rewrite (subst_co_co_var_neq c d g n) in IHb. exact IHb.
  (* lc_g_Var_f *)
  - intros d c g Hg. cbn [subst_co_co].
    destruct (KeySetFacts.eq_dec d c) as [e|n].
    + subst d. exact Hg.
    + constructor.
  (* lc_g_PiCong *)
  - intros rho g1 g2 l1 IH1 l2 IH2 c g Hg. cbn [subst_co_co].
    apply lc_g_PiCong.
    + apply IH1. exact Hg.
    + intro y. specialize (IH2 y c g Hg).
      rewrite (subst_co_open_co_tm_var g2 c g y Hg) in IH2. exact IH2.
  (* lc_g_AbsCong *)
  - intros rho g1 g2 l1 IH1 l2 IH2 c g Hg. cbn [subst_co_co].
    apply lc_g_AbsCong.
    + apply IH1. exact Hg.
    + intro y. specialize (IH2 y c g Hg).
      rewrite (subst_co_open_co_tm_var g2 c g y Hg) in IH2. exact IH2.
  (* lc_g_CPiCong *)
  - intros g1 g3 l1 IH1 l2 IH2 c g Hg. cbn [subst_co_co].
    apply lc_g_CPiCong.
    + apply IH1. exact Hg.
    + intro d. specialize (IH2 d c g Hg).
      rewrite (subst_co_open_co_co_var g3 c g d Hg) in IH2.
      destruct (KeySetFacts.eq_dec d c) as [e|n].
      * subst d. rewrite subst_co_co_var_eq in IH2.
        exact (lc_open_co_co_any (subst_co_co c g g3) g Hg IH2 (g_Var_f c) (lc_g_Var_f c)).
      * rewrite (subst_co_co_var_neq c d g n) in IH2. exact IH2.
  (* lc_g_CAbsCong *)
  - intros g1 g3 g4 l1 IH1 l2 IH2 l4 IH4 c g Hg. cbn [subst_co_co].
    apply lc_g_CAbsCong.
    + apply IH1. exact Hg.
    + intro d. specialize (IH2 d c g Hg).
      rewrite (subst_co_open_co_co_var g3 c g d Hg) in IH2.
      destruct (KeySetFacts.eq_dec d c) as [e|n].
      * subst d. rewrite subst_co_co_var_eq in IH2.
        exact (lc_open_co_co_any (subst_co_co c g g3) g Hg IH2 (g_Var_f c) (lc_g_Var_f c)).
      * rewrite (subst_co_co_var_neq c d g n) in IH2. exact IH2.
    + apply IH4. exact Hg.
Qed.

(* ================================================================== *)
(* Values and value types are closed under term substitution          *)
(* ================================================================== *)

Scheme Value_mut3 := Induction for Value Sort Prop
  with CoercedValue_mut3 := Induction for CoercedValue Sort Prop
  with value_type_mut3 := Induction for value_type Sort Prop.

Lemma Value_subst_tm : forall a, Value a ->
  forall x u, lc_tm u -> Value (subst_tm_tm x u a).
Proof.
  apply (Value_mut3
    (fun a _ => forall x u, lc_tm u -> Value (subst_tm_tm x u a))
    (fun a _ => forall x u, lc_tm u -> CoercedValue (subst_tm_tm x u a))
    (fun a _ => forall x u, lc_tm u -> value_type (subst_tm_tm x u a))).
  (* Value_Star *)
  - intros x u Hu. cbn [subst_tm_tm]. constructor.
  (* Value_Pi *)
  - intros rho A B lA lPi x u Hu. cbn [subst_tm_tm].
    apply Value_Pi.
    + apply (proj1 lc_subst_tm_all); [exact lA | exact Hu].
    + exact (proj1 lc_subst_tm_all (a_Pi rho A B) lPi x u Hu).
  (* Value_CPi *)
  - intros phi B lphi lCPi x u Hu. cbn [subst_tm_tm].
    apply Value_CPi.
    + apply (proj2 (proj2 (proj2 lc_subst_tm_all))); [exact lphi | exact Hu].
    + exact (proj1 lc_subst_tm_all (a_CPi phi B) lCPi x u Hu).
  (* Value_AbsRel *)
  - intros A a lA lAbs x u Hu. cbn [subst_tm_tm].
    apply Value_AbsRel.
    + apply (proj1 lc_subst_tm_all); [exact lA | exact Hu].
    + exact (proj1 lc_subst_tm_all (a_Abs Rel A a) lAbs x u Hu).
  (* Value_UAbsRel *)
  - intros a lAbs x u Hu. cbn [subst_tm_tm].
    apply Value_UAbsRel. exact (proj1 lc_subst_tm_all (a_UAbs Rel a) lAbs x u Hu).
  (* Value_UAbsIrrel *)
  - intros L a v IHv x u Hu. cbn [subst_tm_tm].
    apply Value_UAbsIrrel with (L := AtomSetImpl.union L (AtomSetImpl.singleton x)).
    intro y. intro Hy.
    assert (HL : y \notin L) by (apply (notin_union_1 _ _ _ Hy)).
    assert (Hne : y <> x) by (symmetry; apply (notin_singleton_1 _ _ (notin_union_2 _ _ _ Hy))).
    specialize (IHv y HL x u Hu).
    rewrite (subst_tm_open_tm_var a x u y Hu) in IHv.
    rewrite (subst_tm_tm_var_neq x y u Hne) in IHv. exact IHv.
  (* Value_AbsIrrel *)
  - intros L A a lA c IHc x u Hu. cbn [subst_tm_tm].
    apply Value_AbsIrrel with (L := AtomSetImpl.union L (AtomSetImpl.singleton x)).
    + apply (proj1 lc_subst_tm_all); [exact lA | exact Hu].
    + intro y. intro Hy.
      assert (HL : y \notin L) by (apply (notin_union_1 _ _ _ Hy)).
      assert (Hne : y <> x) by (symmetry; apply (notin_singleton_1 _ _ (notin_union_2 _ _ _ Hy))).
      specialize (IHc y HL x u Hu).
      rewrite (subst_tm_open_tm_var a x u y Hu) in IHc.
      rewrite (subst_tm_tm_var_neq x y u Hne) in IHc. exact IHc.
  (* Value_CAbs *)
  - intros phi a lphi lCAbs x u Hu. cbn [subst_tm_tm].
    apply Value_CAbs.
    + apply (proj2 (proj2 (proj2 lc_subst_tm_all))); [exact lphi | exact Hu].
    + exact (proj1 lc_subst_tm_all (a_CAbs phi a) lCAbs x u Hu).
  (* Value_UCAbs *)
  - intros a lUCAbs x u Hu. cbn [subst_tm_tm].
    apply Value_UCAbs. exact (proj1 lc_subst_tm_all (a_UCAbs a) lUCAbs x u Hu).
  (* CV *)
  - intros a v IHv x u Hu. cbn [subst_tm_tm].
    apply CV. apply IHv. exact Hu.
  (* CC *)
  - intros a g lg v IHv x u Hu. cbn [subst_tm_tm].
    apply CC.
    + apply (proj1 (proj2 lc_subst_tm_all)); [exact lg | exact Hu].
    + apply IHv. exact Hu.
  (* value_type_Star *)
  - intros x u Hu. cbn [subst_tm_tm]. apply value_type_Star.
  (* value_type_Pi *)
  - intros rho A B lA lPi x u Hu. cbn [subst_tm_tm].
    apply value_type_Pi.
    + apply (proj1 lc_subst_tm_all); [exact lA | exact Hu].
    + exact (proj1 lc_subst_tm_all (a_Pi rho A B) lPi x u Hu).
  (* value_type_CPi *)
  - intros phi B lphi lCPi x u Hu. cbn [subst_tm_tm].
    apply value_type_CPi.
    + apply (proj2 (proj2 (proj2 lc_subst_tm_all))); [exact lphi | exact Hu].
    + exact (proj1 lc_subst_tm_all (a_CPi phi B) lCPi x u Hu).
Qed.

Lemma CoercedValue_subst_tm : forall a, CoercedValue a ->
  forall x u, lc_tm u -> CoercedValue (subst_tm_tm x u a).
Proof.
  apply (CoercedValue_mut3
    (fun a _ => True)
    (fun a _ => forall x u, lc_tm u -> CoercedValue (subst_tm_tm x u a))
    (fun a _ => True)).
  all: try solve [intros; exact I].
  (* CV *)
  - intros a v IHv x u Hu. cbn [subst_tm_tm].
    apply CV. apply Value_subst_tm; [exact v | exact Hu].
  (* CC *)
  - intros a g lg v IHv x u Hu. cbn [subst_tm_tm].
    apply CC.
    + apply (proj1 (proj2 lc_subst_tm_all)); [exact lg | exact Hu].
    + apply Value_subst_tm; [exact v | exact Hu].
Qed.

Lemma value_type_subst_tm : forall a, value_type a ->
  forall x u, lc_tm u -> value_type (subst_tm_tm x u a).
Proof.
  apply (value_type_mut3
    (fun a _ => forall x u, lc_tm u -> value_type (subst_tm_tm x u a))).
  - intros x u Hu. cbn [subst_tm_tm]. apply value_type_Star.
  - intros rho A B lA lPi x u Hu. cbn [subst_tm_tm].
    apply value_type_Pi.
    + apply (proj1 lc_subst_tm_all); [exact lA | exact Hu].
    + exact (proj1 lc_subst_tm_all (a_Pi rho A B) lPi x u Hu).
  - intros phi B lphi lCPi x u Hu. cbn [subst_tm_tm].
    apply value_type_CPi.
    + apply (proj2 (proj2 (proj2 lc_subst_tm_all))); [exact lphi | exact Hu].
    + exact (proj1 lc_subst_tm_all (a_CPi phi B) lCPi x u Hu).
Qed.

Lemma Value_subst_co : forall a, Value a ->
  forall c g, lc_co g -> Value (subst_co_tm c g a).
Proof.
  apply (Value_mut3
    (fun a _ => forall c g, lc_co g -> Value (subst_co_tm c g a))
    (fun a _ => forall c g, lc_co g -> CoercedValue (subst_co_tm c g a))
    (fun a _ => forall c g, lc_co g -> value_type (subst_co_tm c g a))).
  (* Value_Star *)
  - intros c g Hg. cbn [subst_co_tm]. constructor.
  (* Value_Pi *)
  - intros rho A B lA lPi c g Hg. cbn [subst_co_tm].
    apply Value_Pi.
    + apply (proj1 lc_subst_co_all); [exact lA | exact Hg].
    + exact (proj1 lc_subst_co_all (a_Pi rho A B) lPi c g Hg).
  (* Value_CPi *)
  - intros phi B lphi lCPi c g Hg. cbn [subst_co_tm].
    apply Value_CPi.
    + apply (proj2 (proj2 (proj2 lc_subst_co_all))); [exact lphi | exact Hg].
    + exact (proj1 lc_subst_co_all (a_CPi phi B) lCPi c g Hg).
  (* Value_AbsRel *)
  - intros A a lA lAbs c g Hg. cbn [subst_co_tm].
    apply Value_AbsRel.
    + apply (proj1 lc_subst_co_all); [exact lA | exact Hg].
    + exact (proj1 lc_subst_co_all (a_Abs Rel A a) lAbs c g Hg).
  (* Value_UAbsRel *)
  - intros a lAbs c g Hg. cbn [subst_co_tm].
    apply Value_UAbsRel. exact (proj1 lc_subst_co_all (a_UAbs Rel a) lAbs c g Hg).
  (* Value_UAbsIrrel *)
  - intros L a v IHv c g Hg. cbn [subst_co_tm].
    apply Value_UAbsIrrel with (L := L).
    intro y. intro Hy.
    specialize (IHv y Hy c g Hg).
    rewrite (subst_co_open_tm_var a c g y Hg) in IHv. exact IHv.
  (* Value_AbsIrrel *)
  - intros L A a lA cc IHc c g Hg. cbn [subst_co_tm].
    apply Value_AbsIrrel with (L := L).
    + apply (proj1 lc_subst_co_all); [exact lA | exact Hg].
    + intro y. intro Hy.
      specialize (IHc y Hy c g Hg).
      rewrite (subst_co_open_tm_var a c g y Hg) in IHc. exact IHc.
  (* Value_CAbs *)
  - intros phi a lphi lCAbs c g Hg. cbn [subst_co_tm].
    apply Value_CAbs.
    + apply (proj2 (proj2 (proj2 lc_subst_co_all))); [exact lphi | exact Hg].
    + exact (proj1 lc_subst_co_all (a_CAbs phi a) lCAbs c g Hg).
  (* Value_UCAbs *)
  - intros a lUCAbs c g Hg. cbn [subst_co_tm].
    apply Value_UCAbs. exact (proj1 lc_subst_co_all (a_UCAbs a) lUCAbs c g Hg).
  (* CV *)
  - intros a v IHv c g Hg. cbn [subst_co_tm].
    apply CV. apply IHv. exact Hg.
  (* CC *)
  - intros a g0 lg v IHv c g Hg. cbn [subst_co_tm].
    apply CC.
    + apply (proj1 (proj2 lc_subst_co_all)); [exact lg | exact Hg].
    + apply IHv. exact Hg.
  (* value_type_Star *)
  - intros c g Hg. cbn [subst_co_tm]. apply value_type_Star.
  (* value_type_Pi *)
  - intros rho A B lA lPi c g Hg. cbn [subst_co_tm].
    apply value_type_Pi.
    + apply (proj1 lc_subst_co_all); [exact lA | exact Hg].
    + exact (proj1 lc_subst_co_all (a_Pi rho A B) lPi c g Hg).
  (* value_type_CPi *)
  - intros phi B lphi lCPi c g Hg. cbn [subst_co_tm].
    apply value_type_CPi.
    + apply (proj2 (proj2 (proj2 lc_subst_co_all))); [exact lphi | exact Hg].
    + exact (proj1 lc_subst_co_all (a_CPi phi B) lCPi c g Hg).
Qed.

Lemma CoercedValue_subst_co : forall a, CoercedValue a ->
  forall c g, lc_co g -> CoercedValue (subst_co_tm c g a).
Proof.
  apply (CoercedValue_mut3
    (fun a _ => True)
    (fun a _ => forall c g, lc_co g -> CoercedValue (subst_co_tm c g a))
    (fun a _ => True)).
  all: try solve [intros; exact I].
  (* CV *)
  - intros a v IHv c g Hg. cbn [subst_co_tm].
    apply CV. apply Value_subst_co; [exact v | exact Hg].
  (* CC *)
  - intros a g0 lg v IHv c g Hg. cbn [subst_co_tm].
    apply CC.
    + apply (proj1 (proj2 lc_subst_co_all)); [exact lg | exact Hg].
    + apply Value_subst_co; [exact v | exact Hg].
Qed.

Lemma value_type_subst_co : forall a, value_type a ->
  forall c g, lc_co g -> value_type (subst_co_tm c g a).
Proof.
  apply (value_type_mut3
    (fun a _ => forall c g, lc_co g -> value_type (subst_co_tm c g a))).
  - intros c g Hg. cbn [subst_co_tm]. apply value_type_Star.
  - intros rho A B lA lPi c g Hg. cbn [subst_co_tm].
    apply value_type_Pi.
    + apply (proj1 lc_subst_co_all); [exact lA | exact Hg].
    + exact (proj1 lc_subst_co_all (a_Pi rho A B) lPi c g Hg).
  - intros phi B lphi lCPi c g Hg. cbn [subst_co_tm].
    apply value_type_CPi.
    + apply (proj2 (proj2 (proj2 lc_subst_co_all))); [exact lphi | exact Hg].
    + exact (proj1 lc_subst_co_all (a_CPi phi B) lCPi c g Hg).
Qed.

(* ================================================================== *)
(* Beta is closed under substitution                                  *)
(* ================================================================== *)

Lemma Beta_subst_tm : forall a b, Beta a b ->
  forall x u, lc_tm u -> Beta (subst_tm_tm x u a) (subst_tm_tm x u b).
Proof.
  intros a b H. induction H as [rho v b lcb vval | a' lcUCAbs | F a A Hb].
  - intros x u Hu. cbn [subst_tm_tm].
    rewrite (subst_tm_open_tm_v v x u b Hu).
    apply Beta_AppAbs.
    + apply (proj1 lc_subst_tm_all); [exact lcb | exact Hu].
    + exact (Value_subst_tm (a_UAbs rho v) vval x u Hu).
  - intros x u Hu. cbn [subst_tm_tm].
    rewrite (subst_tm_open_tm_co_g a' x u g_Triv Hu).
    cbn [subst_tm_co].
    apply Beta_CAppCAbs.
    exact (proj1 lc_subst_tm_all (a_UCAbs a') lcUCAbs x u Hu).
  - intros x u Hu. cbn [subst_tm_tm].
    rewrite (toplevel_ax_subst_tm F a A x u Hb).
    apply (Beta_Axiom F a A Hb).
Qed.

Lemma Beta_subst_co : forall a b, Beta a b ->
  forall c g, lc_co g -> Beta (subst_co_tm c g a) (subst_co_tm c g b).
Proof.
  intros a b H. induction H as [rho v b lcb vval | a' lcUCAbs | F a A Hb].
  - intros c g Hg. cbn [subst_co_tm].
    rewrite (subst_co_open_tm_v v c g b Hg).
    apply Beta_AppAbs.
    + apply (proj1 lc_subst_co_all); [exact lcb | exact Hg].
    + exact (Value_subst_co (a_UAbs rho v) vval c g Hg).
  - intros c g Hg. cbn [subst_co_tm].
    rewrite (subst_co_open_tm_co_h a' c g g_Triv Hg).
    cbn [subst_co_co].
    apply Beta_CAppCAbs.
    exact (proj1 lc_subst_co_all (a_UCAbs a') lcUCAbs c g Hg).
  - intros c g Hg. cbn [subst_co_tm].
    rewrite (toplevel_ax_subst_co F a A c g Hb).
    apply (Beta_Axiom F a A Hb).
Qed.

(* ================================================================== *)
(* Helpers for the main substitution induction                        *)
(* ================================================================== *)

Lemma notin_union4 : forall (y:atom) (s1 s2 s3 s4:atoms),
  y `notin` AtomSetImpl.union s1 (AtomSetImpl.union s2 (AtomSetImpl.union s3 s4)) ->
  y `notin` s1 /\ y `notin` s2 /\ y `notin` s3 /\ y `notin` s4.
Proof.
  intros y s1 s2 s3 s4 H.
  assert (H1 : y `notin` s1) by (apply (notin_union_1 y s1 _ H)).
  assert (H2 : y `notin` AtomSetImpl.union s2 (AtomSetImpl.union s3 s4))
    by (apply (notin_union_2 y s1 _ H)).
  assert (H3 : y `notin` s2) by (apply (notin_union_1 y s2 _ H2)).
  assert (H4 : y `notin` AtomSetImpl.union s3 s4) by (apply (notin_union_2 y s2 _ H2)).
  assert (H5 : y `notin` s3) by (apply (notin_union_1 y s3 _ H4)).
  assert (H6 : y `notin` s4) by (apply (notin_union_2 y s3 _ H4)).
  auto.
Qed.

Lemma in_dom_subst_ctx : forall (G1:context) (X:atom) (s:sort) G2 u (c:atom),
  c `in` dom (G1 ++ (X,s) :: nil ++ G2) -> c <> X ->
  c `in` dom (subTm_ctx X u G1 ++ subTm_ctx X u G2).
Proof.
  intros G1 X s G2 u c H Hne.
  cbn [app] in H.
  assert (H' : c `in` dom (G1 ++ G2))
    by (apply (in_dom_remove_mid G1 X s G2 c); auto).
  rewrite <- subTm_ctx_app. rewrite dom_subTm_ctx. exact H'.
Qed.

Lemma notin_dom_subst_ctx : forall (G1:context) (X:atom) (s:sort) G2 u (y:atom),
  y `notin` dom (G1 ++ (X,s) :: nil ++ G2) ->
  y `notin` dom (subTm_ctx X u G1 ++ subTm_ctx X u G2).
Proof.
  intros G1 X s G2 u y H Hin.
  cbn [app] in H.
  assert (Hin' : y `in` dom (G1 ++ G2)).
  { rewrite <- subTm_ctx_app in Hin. rewrite dom_subTm_ctx in Hin. exact Hin. }
  apply H. destruct (@in_dom_binds sort y (G1++G2) Hin') as [t Ht].
  apply in_dom_of_in with (a:=t). apply in_app_iff in Ht.
  destruct Ht as [H1|H2]; apply in_app_iff.
  - left. exact H1.
  - right. apply in_cons. exact H2.
Qed.

Lemma erase_open_subst_tm_var : forall (b:tm) (X:tmvar) (u:tm) (y:tmvar),
  lc_tm u -> y <> X ->
  erase_tm (open_tm_wrt_tm (subst_tm_tm X u b) (a_Var_f y))
  = subst_tm_tm X (erase_tm u) (erase_tm (open_tm_wrt_tm b (a_Var_f y))).
Proof.
  intros b X u y Hu Hne.
  rewrite erase_open_tm_var.
  rewrite (proj1 erase_subst_tm_tm b X u).
  rewrite erase_open_tm_var.
  rewrite (subst_tm_open_tm_var (erase_tm b) X (erase_tm u) y (proj1 lc_erase_all u Hu)).
  f_equal.
  rewrite subst_tm_tm_var_neq; [reflexivity | exact Hne].
Qed.

Lemma annctx_uniq_split : forall (G:context) G1 X s G2,
  AnnCtx G -> G = G1 ++ (X,s) :: nil ++ G2 ->
  X `notin` dom G1 /\ X `notin` dom G2.
Proof.
  intros G G1 X s G2 Hctx Heq.
  pose proof (AnnCtx_uniq G Hctx) as Hu.
  rewrite Heq in Hu. cbn [app] in Hu.
  exact (uniq_split G1 X s G2 Hu).
Qed.

Lemma cons_ctx_decomp : forall (y:atom) (s:sort) G1 X A0 G2 G,
  G = G1 ++ (X, Tm A0) :: nil ++ G2 ->
  ((y,s) :: G) = ((y,s) :: G1) ++ (X, Tm A0) :: nil ++ G2.
Proof.
  intros y s G1 X A0 G2 G Heq. subst G.
  reflexivity.
Qed.

Lemma in_dom_subst_ctx' : forall (G:context) G1 X s G2 u c,
  G = G1 ++ (X,s) :: nil ++ G2 ->
  c `in` dom G -> c <> X ->
  c `in` dom (subTm_ctx X u G1 ++ subTm_ctx X u G2).
Proof.
  intros G G1 X s G2 u c Heq Hin Hne.
  rewrite Heq in Hin.
  apply (in_dom_subst_ctx G1 X s G2 u c Hin Hne).
Qed.

Lemma notin_dom_subst_ctx' : forall (G:context) G1 X s G2 u y,
  G = G1 ++ (X,s) :: nil ++ G2 ->
  y `notin` dom G ->
  y `notin` dom (subTm_ctx X u G1 ++ subTm_ctx X u G2).
Proof.
  intros G G1 X s G2 u y Heq Hy.
  rewrite Heq in Hy.
  apply (notin_dom_subst_ctx G1 X s G2 u y Hy).
Qed.

Lemma RhoCheck_irrel_inv : forall (x:tmvar) (A:tm),
  RhoCheck Irrel x A -> x `notin` fv_tm_tm_tm A.
Proof.
  intros x A H. inversion H. assumption.
Qed.

Lemma binds_split_any : forall (G1:context) (x:tmvar) (s0:sort) G2 (y:atom) s,
  x `notin` dom G1 -> x `notin` dom G2 ->
  binds y s (G1 ++ (x, s0) :: nil ++ G2) ->
  (y = x /\ s = s0) \/ (y <> x /\ binds y s (G1 ++ G2)).
Proof.
  intros G1 x s0 G2 y s Hx1 Hx2 H. unfold binds in *.
  apply in_app_iff in H. destruct H as [H|H].
  - right. split; [|apply in_app_iff; left; exact H].
    intro Heq. subst y. exfalso. apply Hx1. apply in_dom_of_in with (a:=s). exact H.
  - simpl in H. destruct H as [Heq|H].
    + left. inversion Heq. auto.
    + right. split; [|apply in_app_iff; right; exact H].
      intro Heq. subst y. exfalso. apply Hx2. apply in_dom_of_in with (a:=s). exact H.
Qed.

Lemma subst_tm_tm_conv_var_sym : forall (X:tmvar) (u:tm) (y:tmvar) (g:co),
  y <> X ->
  subst_tm_tm X u (a_Conv (a_Var_f y) (g_Sym g))
  = a_Conv (a_Var_f y) (g_Sym (subst_tm_co X u g)).
Proof.
  intros X u y g Hne.
  cbn [subst_tm_tm subst_tm_co].
  destruct (KeySetFacts.eq_dec y X) as [e|e].
  - exfalso. apply Hne. exact e.
  - reflexivity.
Qed.


Definition PT (G:context) (t T:tm) (H:AnnTyping G t T) : Prop :=
  forall (G1 G2:context) (X:tmvar) (A u:tm),
    G = G1 ++ (X, Tm A) :: nil ++ G2 ->
    AnnCtx G ->
    X `notin` fv_tm_tm_tm A ->
    lc_tm u ->
    AnnCtx (subTm_ctx X u G1 ++ subTm_ctx X u G2) ->
    (forall G', ctx_sub (subTm_ctx X u G2) G' -> AnnCtx G' -> AnnTyping G' u A) ->
    AnnTyping (subTm_ctx X u G1 ++ subTm_ctx X u G2)
              (subst_tm_tm X u t) (subst_tm_tm X u T).

Definition PW (G:context) (p:constraint) (H:AnnPropWff G p) : Prop :=
  forall (G1 G2:context) (X:tmvar) (A u:tm),
    G = G1 ++ (X, Tm A) :: nil ++ G2 ->
    AnnCtx G ->
    X `notin` fv_tm_tm_tm A ->
    lc_tm u ->
    AnnCtx (subTm_ctx X u G1 ++ subTm_ctx X u G2) ->
    (forall G', ctx_sub (subTm_ctx X u G2) G' -> AnnCtx G' -> AnnTyping G' u A) ->
    AnnPropWff (subTm_ctx X u G1 ++ subTm_ctx X u G2) (subst_tm_constraint X u p).

Definition PI (G:context) (D:available_props) (g:co) (p q:constraint) (H:AnnIso G D g p q) : Prop :=
  forall (G1 G2:context) (X:tmvar) (A u:tm),
    G = G1 ++ (X, Tm A) :: nil ++ G2 ->
    AnnCtx G ->
    X `notin` fv_tm_tm_tm A ->
    lc_tm u ->
    AnnCtx (subTm_ctx X u G1 ++ subTm_ctx X u G2) ->
    (forall G', ctx_sub (subTm_ctx X u G2) G' -> AnnCtx G' -> AnnTyping G' u A) ->
    forall D', (forall c, c `in` D -> c <> X -> c `in` D') ->
    AnnIso (subTm_ctx X u G1 ++ subTm_ctx X u G2) D'
           (subst_tm_co X u g) (subst_tm_constraint X u p) (subst_tm_constraint X u q).

Definition PE (G:context) (D:available_props) (g:co) (a b:tm) (H:AnnDefEq G D g a b) : Prop :=
  forall (G1 G2:context) (X:tmvar) (A u:tm),
    G = G1 ++ (X, Tm A) :: nil ++ G2 ->
    AnnCtx G ->
    X `notin` fv_tm_tm_tm A ->
    lc_tm u ->
    AnnCtx (subTm_ctx X u G1 ++ subTm_ctx X u G2) ->
    (forall G', ctx_sub (subTm_ctx X u G2) G' -> AnnCtx G' -> AnnTyping G' u A) ->
    forall D', (forall c, c `in` D -> c <> X -> c `in` D') ->
    AnnDefEq (subTm_ctx X u G1 ++ subTm_ctx X u G2) D'
             (subst_tm_co X u g) (subst_tm_tm X u a) (subst_tm_tm X u b).

Lemma Main_aux :
  (forall G t T (H:AnnTyping G t T), PT G t T H) /\
  (forall G p (H:AnnPropWff G p), PW G p H) /\
  (forall G D g p q (H:AnnIso G D g p q), PI G D g p q H) /\
  (forall G D g a b (H:AnnDefEq G D g a b), PE G D g a b H) /\
  (forall c, AnnCtx c -> True) /\
  (forall s, AnnSig s -> True).
Proof.
  apply (AnnTyping_comb PT PW PI PE (fun _ _ => True) (fun _ _ => True)).
  (* An_Star *)
  - intros G a IHa G1 G2 X A0 u0 Heq HctxG HX Hu HCtxSub HHyp.
    cbn [subst_tm_tm]. apply An_Star. exact HCtxSub.
  (* An_Var *)
  - intros G x A a IHa b G1 G2 X A0 u0 Heq HctxG HX Hu HCtxSub HHyp.
    destruct (annctx_uniq_split G G1 X (Tm A0) G2 HctxG Heq) as [HX1 HX2].
    rewrite Heq in b.
    destruct (binds_split G1 X A0 G2 x (Tm A) HX1 HX2 b) as [[Hxeq HAeq]|[Hne Hb]].
    + subst x. inversion HAeq. subst A.
      rewrite subst_tm_tm_var_eq.
      rewrite ((proj1 subst_tm_tm_id_notin_all) A0 X u0 HX).
      exact (HHyp (subTm_ctx X u0 G1 ++ subTm_ctx X u0 G2)
                  (ctx_sub_subTm_right X u0 G1 G2) HCtxSub).
    + rewrite (subst_tm_tm_var_neq X x u0 Hne).
      apply An_Var.
      * exact HCtxSub.
      * rewrite <- subTm_ctx_app.
        apply (binds_subTm_ctx X u0 (G1++G2) x (Tm A) Hb).
  (* An_Pi *)
  - intros L G rho A B a IHa a0 IHA0 G1 G2 X A0 u0 Heq HctxG HX Hu HCtxSub HHyp.
    apply An_Pi with (L := AtomSetImpl.union L (AtomSetImpl.union (dom G) (AtomSetImpl.union (AtomSetImpl.singleton X) (fv_tm_tm_tm (erase_tm u0))))).
    + intro y. intro Hy.
      destruct (notin_union4 y L (dom G) (AtomSetImpl.singleton X) (fv_tm_tm_tm (erase_tm u0)) Hy) as (HyL & HyDomG & HyX & HyFu).
      assert (Hne : y <> X) by (symmetry; exact (notin_singleton_1 X y HyX)).
      assert (HctxM : AnnCtx ((y, Tm A) :: G)) by exact (An_ConsTm G y A HctxG a0 HyDomG).
      assert (HctxSubM : AnnCtx ((y, Tm (subst_tm_tm X u0 A)) :: (subTm_ctx X u0 G1 ++ subTm_ctx X u0 G2)))
        by exact (An_ConsTm (subTm_ctx X u0 G1 ++ subTm_ctx X u0 G2) y (subst_tm_tm X u0 A) HCtxSub
                     (IHA0 G1 G2 X A0 u0 Heq HctxG HX Hu HCtxSub HHyp)
                     (notin_dom_subst_ctx' G G1 X (Tm A0) G2 u0 y Heq HyDomG)).
      assert (Hbody := IHa y HyL ((y, Tm A) :: G1) G2 X A0 u0
                        (cons_ctx_decomp y (Tm A) G1 X A0 G2 G Heq) HctxM HX Hu HctxSubM HHyp).
      rewrite (subst_tm_open_tm_var B X u0 y Hu) in Hbody.
      rewrite (subst_tm_tm_var_neq X y u0 Hne) in Hbody.
      exact Hbody.
    + exact (IHA0 G1 G2 X A0 u0 Heq HctxG HX Hu HCtxSub HHyp).
  (* An_Abs *)
  - intros L G rho A a B a0 IHA0 a1 IHa r G1 G2 X A0 u0 Heq HctxG HX Hu HCtxSub HHyp.
    apply An_Abs with (L := AtomSetImpl.union L (AtomSetImpl.union (dom G) (AtomSetImpl.union (AtomSetImpl.singleton X) (fv_tm_tm_tm (erase_tm u0))))).
    + exact (IHA0 G1 G2 X A0 u0 Heq HctxG HX Hu HCtxSub HHyp).
    + intro y. intro Hy.
      destruct (notin_union4 y L (dom G) (AtomSetImpl.singleton X) (fv_tm_tm_tm (erase_tm u0)) Hy) as (HyL & HyDomG & HyX & HyFu).
      assert (Hne : y <> X) by (symmetry; exact (notin_singleton_1 X y HyX)).
      assert (HctxM : AnnCtx ((y, Tm A) :: G)) by exact (An_ConsTm G y A HctxG a0 HyDomG).
      assert (HctxSubM : AnnCtx ((y, Tm (subst_tm_tm X u0 A)) :: (subTm_ctx X u0 G1 ++ subTm_ctx X u0 G2)))
        by exact (An_ConsTm (subTm_ctx X u0 G1 ++ subTm_ctx X u0 G2) y (subst_tm_tm X u0 A) HCtxSub
                     (IHA0 G1 G2 X A0 u0 Heq HctxG HX Hu HCtxSub HHyp)
                     (notin_dom_subst_ctx' G G1 X (Tm A0) G2 u0 y Heq HyDomG)).
      assert (Hbody := IHa y HyL ((y, Tm A) :: G1) G2 X A0 u0
                        (cons_ctx_decomp y (Tm A) G1 X A0 G2 G Heq) HctxM HX Hu HctxSubM HHyp).
      rewrite (subst_tm_open_tm_var a X u0 y Hu) in Hbody.
      rewrite (subst_tm_tm_var_neq X y u0 Hne) in Hbody.
      rewrite (subst_tm_open_tm_var B X u0 y Hu) in Hbody.
      rewrite (subst_tm_tm_var_neq X y u0 Hne) in Hbody.
      exact Hbody.
    + intro y. intro Hy.
      destruct (notin_union4 y L (dom G) (AtomSetImpl.singleton X) (fv_tm_tm_tm (erase_tm u0)) Hy) as (HyL & HyDomG & HyX & HyFu).
      assert (Hne : y <> X) by (symmetry; exact (notin_singleton_1 X y HyX)).
      destruct rho.
      * apply Rho_Rel. exact I.
      * apply Rho_IrrRel.
        fold subst_tm_tm.
        rewrite (erase_open_subst_tm_var a X u0 y Hu Hne).
        exact ((proj1 notin_subst_tm_tm) (erase_tm (open_tm_wrt_tm a (a_Var_f y))) X (erase_tm u0) y
                 (RhoCheck_irrel_inv y (erase_tm (open_tm_wrt_tm a (a_Var_f y))) (r y HyL)) HyFu).
  (* An_App *)
  - intros G b rho a B A a0 IHa a1 IHa1 G1 G2 X A0 u0 Heq HctxG HX Hu HCtxSub HHyp.
    cbn [subst_tm_tm].
    rewrite (subst_tm_open_tm_v B X u0 a Hu).
    apply An_App with (A := subst_tm_tm X u0 A).
    + exact (IHa G1 G2 X A0 u0 Heq HctxG HX Hu HCtxSub HHyp).
    + exact (IHa1 G1 G2 X A0 u0 Heq HctxG HX Hu HCtxSub HHyp).
  (* An_Conv *)
  - intros G a g B A a0 IHa a1 IHa1 a2 IHa2 G1 G2 X A0 u0 Heq HctxG HX Hu HCtxSub HHyp.
    cbn [subst_tm_tm].
    apply An_Conv with (A := subst_tm_tm X u0 A).
    + exact (IHa G1 G2 X A0 u0 Heq HctxG HX Hu HCtxSub HHyp).
    + exact (IHa1 G1 G2 X A0 u0 Heq HctxG HX Hu HCtxSub HHyp (dom (subTm_ctx X u0 G1 ++ subTm_ctx X u0 G2))
                   (fun c Hin Hne => in_dom_subst_ctx' G G1 X (Tm A0) G2 u0 c Heq Hin Hne)).
    + exact (IHa2 G1 G2 X A0 u0 Heq HctxG HX Hu HCtxSub HHyp).
  (* An_CPi *)
  - intros L G phi B a IHa a0 IHa0 G1 G2 X A0 u0 Heq HctxG HX Hu HCtxSub HHyp.
    apply An_CPi with (L := AtomSetImpl.union L (AtomSetImpl.union (dom G) (AtomSetImpl.union (AtomSetImpl.singleton X) (fv_tm_tm_tm (erase_tm u0))))).
    + exact (IHa G1 G2 X A0 u0 Heq HctxG HX Hu HCtxSub HHyp).
    + intro c. intro Hc.
      destruct (notin_union4 c L (dom G) (AtomSetImpl.singleton X) (fv_tm_tm_tm (erase_tm u0)) Hc) as (HcL & HcDomG & HcX & HcFu).
      assert (HctxM : AnnCtx ((c, Co phi) :: G)) by exact (An_ConsCo G c phi HctxG a HcDomG).
      assert (HctxSubM : AnnCtx ((c, Co (subst_tm_constraint X u0 phi)) :: (subTm_ctx X u0 G1 ++ subTm_ctx X u0 G2)))
        by exact (An_ConsCo (subTm_ctx X u0 G1 ++ subTm_ctx X u0 G2) c (subst_tm_constraint X u0 phi) HCtxSub
                     (IHa G1 G2 X A0 u0 Heq HctxG HX Hu HCtxSub HHyp)
                     (notin_dom_subst_ctx' G G1 X (Tm A0) G2 u0 c Heq HcDomG)).
      assert (Hbody := IHa0 c HcL ((c, Co phi) :: G1) G2 X A0 u0
                        (cons_ctx_decomp c (Co phi) G1 X A0 G2 G Heq) HctxM HX Hu HctxSubM HHyp).
      rewrite (subst_tm_open_tm_co_var B X u0 c Hu) in Hbody.
      cbn [subst_tm_co] in Hbody.
      exact Hbody.
  (* An_CAbs *)
  - intros L G phi a B a0 IHa a1 IHa1 G1 G2 X A0 u0 Heq HctxG HX Hu HCtxSub HHyp.
    apply An_CAbs with (L := AtomSetImpl.union L (AtomSetImpl.union (dom G) (AtomSetImpl.union (AtomSetImpl.singleton X) (fv_tm_tm_tm (erase_tm u0))))).
    + exact (IHa G1 G2 X A0 u0 Heq HctxG HX Hu HCtxSub HHyp).
    + intro c. intro Hc.
      destruct (notin_union4 c L (dom G) (AtomSetImpl.singleton X) (fv_tm_tm_tm (erase_tm u0)) Hc) as (HcL & HcDomG & HcX & HcFu).
      assert (HctxM : AnnCtx ((c, Co phi) :: G)) by exact (An_ConsCo G c phi HctxG a0 HcDomG).
      assert (HctxSubM : AnnCtx ((c, Co (subst_tm_constraint X u0 phi)) :: (subTm_ctx X u0 G1 ++ subTm_ctx X u0 G2)))
        by exact (An_ConsCo (subTm_ctx X u0 G1 ++ subTm_ctx X u0 G2) c (subst_tm_constraint X u0 phi) HCtxSub
                     (IHa G1 G2 X A0 u0 Heq HctxG HX Hu HCtxSub HHyp)
                     (notin_dom_subst_ctx' G G1 X (Tm A0) G2 u0 c Heq HcDomG)).
      assert (Hbody := IHa1 c HcL ((c, Co phi) :: G1) G2 X A0 u0
                        (cons_ctx_decomp c (Co phi) G1 X A0 G2 G Heq) HctxM HX Hu HctxSubM HHyp).
      rewrite (subst_tm_open_tm_co_var a X u0 c Hu) in Hbody.
      cbn [subst_tm_co] in Hbody.
      rewrite (subst_tm_open_tm_co_var B X u0 c Hu) in Hbody.
      cbn [subst_tm_co] in Hbody.
      exact Hbody.
  (* An_CApp *)
  - intros G a1 g B a b A1 a0 IHa a1' IHa1 G1 G2 X A0 u0 Heq HctxG HX Hu HCtxSub HHyp.
    cbn [subst_tm_tm].
    rewrite (subst_tm_open_tm_co_g B X u0 g Hu).
    apply An_CApp with (a := subst_tm_tm X u0 a) (b := subst_tm_tm X u0 b) (A1 := subst_tm_tm X u0 A1).
    + exact (IHa G1 G2 X A0 u0 Heq HctxG HX Hu HCtxSub HHyp).
    + exact (IHa1 G1 G2 X A0 u0 Heq HctxG HX Hu HCtxSub HHyp (dom (subTm_ctx X u0 G1 ++ subTm_ctx X u0 G2))
                   (fun c Hin Hne => in_dom_subst_ctx' G G1 X (Tm A0) G2 u0 c Heq Hin Hne)).
  (* An_Fam *)
  - intros G F A a a0 IHa b a1 IHa1 G1 G2 X A0 u0 Heq HctxG HX Hu HCtxSub HHyp.
    destruct (an_toplevel_ax_subst_tm F a A X u0 b) as [Ha HA].
    apply (An_Fam (subTm_ctx X u0 G1 ++ subTm_ctx X u0 G2) F (subst_tm_tm X u0 A) (subst_tm_tm X u0 a)).
    + exact HCtxSub.
    + rewrite Ha, HA. exact b.
    + rewrite HA. exact a1.

  (* An_Wff *)
  - intros G a b A B a0 IHa a1 IHa1 e G1 G2 X A0 u0 Heq HctxG HX Hu HCtxSub HHyp.
    cbn [subst_tm_constraint].
    apply An_Wff with (B := subst_tm_tm X u0 B).
    + exact (IHa G1 G2 X A0 u0 Heq HctxG HX Hu HCtxSub HHyp).
    + exact (IHa1 G1 G2 X A0 u0 Heq HctxG HX Hu HCtxSub HHyp).
    + rewrite ((proj1 erase_subst_tm_tm) A X u0).
      rewrite ((proj1 erase_subst_tm_tm) B X u0).
      rewrite e. reflexivity.
  (* An_PropCong *)
  - intros G D g1 A g2 A1 B1 A2 B2 a IHa a0 IHa0 a1 IHa1 a2 IHa2 G1 G2 X A0 u0 Heq HctxG HX Hu HCtxSub HHyp D' HDsub.
    cbn [subst_tm_constraint].
    apply An_PropCong.
    + exact (IHa G1 G2 X A0 u0 Heq HctxG HX Hu HCtxSub HHyp D' HDsub).
    + exact (IHa0 G1 G2 X A0 u0 Heq HctxG HX Hu HCtxSub HHyp D' HDsub).
    + exact (IHa1 G1 G2 X A0 u0 Heq HctxG HX Hu HCtxSub HHyp).
    + exact (IHa2 G1 G2 X A0 u0 Heq HctxG HX Hu HCtxSub HHyp).
  (* An_CPiFst *)
  - intros G D g phi1 phi2 A2 B2 a IHa G1 G2 X A0 u0 Heq HctxG HX Hu HCtxSub HHyp D' HDsub.
    cbn [subst_tm_co subst_tm_constraint].
    apply (An_CPiFst (subTm_ctx X u0 G1 ++ subTm_ctx X u0 G2) D' (subst_tm_co X u0 g) (subst_tm_constraint X u0 phi1) (subst_tm_constraint X u0 phi2) (subst_tm_tm X u0 A2) (subst_tm_tm X u0 B2)).
    exact (IHa G1 G2 X A0 u0 Heq HctxG HX Hu HCtxSub HHyp D' HDsub).
  (* An_IsoSym *)
  - intros G D g phi2 phi1 a IHa G1 G2 X A0 u0 Heq HctxG HX Hu HCtxSub HHyp D' HDsub.
    cbn [subst_tm_co subst_tm_constraint].
    apply An_IsoSym.
    exact (IHa G1 G2 X A0 u0 Heq HctxG HX Hu HCtxSub HHyp D' HDsub).
  (* An_IsoConv *)
  - intros G D a1 a2 A a1' a2' B g a IHa a0 IHa0 a3 IHa3 e e0 G1 G2 X A0 u0 Heq HctxG HX Hu HCtxSub HHyp D' HDsub.
    cbn [subst_tm_co subst_tm_constraint].
    apply An_IsoConv.
    + exact (IHa G1 G2 X A0 u0 Heq HctxG HX Hu HCtxSub HHyp D' HDsub).
    + exact (IHa0 G1 G2 X A0 u0 Heq HctxG HX Hu HCtxSub HHyp).
    + exact (IHa3 G1 G2 X A0 u0 Heq HctxG HX Hu HCtxSub HHyp).
    + rewrite ((proj1 erase_subst_tm_tm) a1 X u0).
      rewrite ((proj1 erase_subst_tm_tm) a1' X u0).
      rewrite e. reflexivity.
    + rewrite ((proj1 erase_subst_tm_tm) a2 X u0).
      rewrite ((proj1 erase_subst_tm_tm) a2' X u0).
      rewrite e0. reflexivity.


  (* An_Assn *)
  - intros G D c a b A a0 IHa Hb i G1 G2 X A0 u0 Heq HctxG HX Hu HCtxSub HHyp D' HDsub.
    destruct (annctx_uniq_split G G1 X (Tm A0) G2 HctxG Heq) as [HX1 HX2].
    rewrite Heq in Hb.
    destruct (binds_split_any G1 X (Tm A0) G2 c (Co (Eq a b A)) HX1 HX2 Hb) as [[Hceq Hseq]|[Hne Hb']].
    + subst c. discriminate Hseq.
    + cbn [subst_tm_co].
      apply (An_Assn (subTm_ctx X u0 G1 ++ subTm_ctx X u0 G2) D' c (subst_tm_tm X u0 a) (subst_tm_tm X u0 b) (subst_tm_tm X u0 A)).
      * exact HCtxSub.
      * rewrite <- subTm_ctx_app.
        apply (binds_subTm_ctx X u0 (G1++G2) c (Co (Eq a b A)) Hb').
      * exact (HDsub c i Hne).
  (* An_Refl *)
  - intros G D a A a0 IHa G1 G2 X A0 u0 Heq HctxG HX Hu HCtxSub HHyp D' HDsub.
    cbn [subst_tm_co subst_tm_tm].
    apply An_Refl with (A := subst_tm_tm X u0 A).
    exact (IHa G1 G2 X A0 u0 Heq HctxG HX Hu HCtxSub HHyp).
  (* An_EraseEq *)
  - intros G D a b g A B a0 IHa a1 IHa1 e a2 IHa2 G1 G2 X A0 u0 Heq HctxG HX Hu HCtxSub HHyp D' HDsub.
    cbn [subst_tm_co subst_tm_tm].
    apply An_EraseEq with (A := subst_tm_tm X u0 A) (B := subst_tm_tm X u0 B).
    + exact (IHa G1 G2 X A0 u0 Heq HctxG HX Hu HCtxSub HHyp).
    + exact (IHa1 G1 G2 X A0 u0 Heq HctxG HX Hu HCtxSub HHyp).
    + rewrite ((proj1 erase_subst_tm_tm) a X u0).
      rewrite ((proj1 erase_subst_tm_tm) b X u0).
      rewrite e. reflexivity.
    + exact (IHa2 G1 G2 X A0 u0 Heq HctxG HX Hu HCtxSub HHyp (dom (subTm_ctx X u0 G1 ++ subTm_ctx X u0 G2))
                   (fun c Hin Hne => in_dom_subst_ctx' G G1 X (Tm A0) G2 u0 c Heq Hin Hne)).
  (* An_Sym *)
  - intros G D g a b B A g1 a0 IHa0 a1 IHa1 a2 IHa2 a3 IHa3 G1 G2 X A0 u0 Heq HctxG HX Hu HCtxSub HHyp D' HDsub.
    cbn [subst_tm_co subst_tm_tm].
    apply An_Sym with (B := subst_tm_tm X u0 B) (A := subst_tm_tm X u0 A) (g1 := subst_tm_co X u0 g1).
    + exact (IHa0 G1 G2 X A0 u0 Heq HctxG HX Hu HCtxSub HHyp).
    + exact (IHa1 G1 G2 X A0 u0 Heq HctxG HX Hu HCtxSub HHyp).
    + exact (IHa2 G1 G2 X A0 u0 Heq HctxG HX Hu HCtxSub HHyp (dom (subTm_ctx X u0 G1 ++ subTm_ctx X u0 G2))
                   (fun c Hin Hne => in_dom_subst_ctx' G G1 X (Tm A0) G2 u0 c Heq Hin Hne)).
    + exact (IHa3 G1 G2 X A0 u0 Heq HctxG HX Hu HCtxSub HHyp D' HDsub).
  (* An_Trans *)
  - intros G D g1 g2 a b a1 A A1 g3 a0 IHa0 a2 IHa2 a3 IHa3 a4 IHa4 a5 IHa5 G1 G2 X A0 u0 Heq HctxG HX Hu HCtxSub HHyp D' HDsub.
    cbn [subst_tm_co subst_tm_tm].
    apply An_Trans with (a1 := subst_tm_tm X u0 a1) (A := subst_tm_tm X u0 A) (A1 := subst_tm_tm X u0 A1) (g3 := subst_tm_co X u0 g3).
    + exact (IHa0 G1 G2 X A0 u0 Heq HctxG HX Hu HCtxSub HHyp D' HDsub).
    + exact (IHa2 G1 G2 X A0 u0 Heq HctxG HX Hu HCtxSub HHyp D' HDsub).
    + exact (IHa3 G1 G2 X A0 u0 Heq HctxG HX Hu HCtxSub HHyp).
    + exact (IHa4 G1 G2 X A0 u0 Heq HctxG HX Hu HCtxSub HHyp).
    + exact (IHa5 G1 G2 X A0 u0 Heq HctxG HX Hu HCtxSub HHyp (dom (subTm_ctx X u0 G1 ++ subTm_ctx X u0 G2))
                   (fun c Hin Hne => in_dom_subst_ctx' G G1 X (Tm A0) G2 u0 c Heq Hin Hne)).


  (* An_Beta *)
  - intros G D a1 a2 B0 B1 a IHa a0 IHa0 e b G1 G2 X A0 u0 Heq HctxG HX Hu HCtxSub HHyp D' HDsub.
    cbn [subst_tm_co subst_tm_tm].
    apply An_Beta with (B0 := subst_tm_tm X u0 B0) (B1 := subst_tm_tm X u0 B1).
    + exact (IHa G1 G2 X A0 u0 Heq HctxG HX Hu HCtxSub HHyp).
    + exact (IHa0 G1 G2 X A0 u0 Heq HctxG HX Hu HCtxSub HHyp).
    + rewrite ((proj1 erase_subst_tm_tm) B0 X u0).
      rewrite ((proj1 erase_subst_tm_tm) B1 X u0).
      rewrite e. reflexivity.
    + rewrite ((proj1 erase_subst_tm_tm) a1 X u0).
      rewrite ((proj1 erase_subst_tm_tm) a2 X u0).
      exact (Beta_subst_tm (erase_tm a1) (erase_tm a2) b X (erase_tm u0) (proj1 lc_erase_all u0 Hu)).
  (* An_PiCong *)
  - intros L G D rho g1 g2 A1 B1 A2 B3 B2 a IHa a0 IHa0 e a1 IHa1 a2 IHa2 a3 IHa3 G1 G2 X A0 u0 Heq HctxG HX Hu HCtxSub HHyp D' HDsub.
    cbn [subst_tm_co subst_tm_tm].
    apply (An_PiCong (AtomSetImpl.union L (AtomSetImpl.union (dom G) (AtomSetImpl.union (AtomSetImpl.singleton X) (fv_tm_tm_tm (erase_tm u0)))))
              (subTm_ctx X u0 G1 ++ subTm_ctx X u0 G2) D' rho
              (subst_tm_co X u0 g1) (subst_tm_co X u0 g2)
              (subst_tm_tm X u0 A1) (subst_tm_tm X u0 B1)
              (subst_tm_tm X u0 A2) (subst_tm_tm X u0 B3) (subst_tm_tm X u0 B2)).
    + exact (IHa G1 G2 X A0 u0 Heq HctxG HX Hu HCtxSub HHyp D' HDsub).
    + intro y. intro Hy.
      destruct (notin_union4 y L (dom G) (AtomSetImpl.singleton X) (fv_tm_tm_tm (erase_tm u0)) Hy) as (HyL & HyDomG & HyX & HyFu).
      assert (Hne : y <> X) by (symmetry; exact (notin_singleton_1 X y HyX)).
      assert (HtyA1sub : AnnTyping (subTm_ctx X u0 G1 ++ subTm_ctx X u0 G2) (a_Pi rho (subst_tm_tm X u0 A1) (subst_tm_tm X u0 B1)) a_Star).
      { cbn [subst_tm_tm]. exact (IHa1 G1 G2 X A0 u0 Heq HctxG HX Hu HCtxSub HHyp). }
      assert (HctxM : AnnCtx ((y, Tm A1) :: G)) by exact (An_ConsTm G y A1 HctxG (AnnTyping_pi_dom G rho A1 B1 a1) HyDomG).
      assert (HctxSubM : AnnCtx ((y, Tm (subst_tm_tm X u0 A1)) :: (subTm_ctx X u0 G1 ++ subTm_ctx X u0 G2)))
        by exact (An_ConsTm (subTm_ctx X u0 G1 ++ subTm_ctx X u0 G2) y (subst_tm_tm X u0 A1) HCtxSub
                     (AnnTyping_pi_dom (subTm_ctx X u0 G1 ++ subTm_ctx X u0 G2) rho (subst_tm_tm X u0 A1) (subst_tm_tm X u0 B1) HtyA1sub)
                     (notin_dom_subst_ctx' G G1 X (Tm A0) G2 u0 y Heq HyDomG)).
      assert (Hbody := IHa0 y HyL ((y, Tm A1) :: G1) G2 X A0 u0
                        (cons_ctx_decomp y (Tm A1) G1 X A0 G2 G Heq) HctxM HX Hu HctxSubM HHyp D' HDsub).
      rewrite (subst_tm_open_co_wrt_tm_var g2 X u0 y Hu) in Hbody.
      rewrite (subst_tm_open_tm_var B1 X u0 y Hu) in Hbody.
      rewrite (subst_tm_open_tm_var B2 X u0 y Hu) in Hbody.
      rewrite (subst_tm_tm_var_neq X y u0 Hne) in Hbody.
      exact Hbody.
    + intro y. intro Hy.
      destruct (notin_union4 y L (dom G) (AtomSetImpl.singleton X) (fv_tm_tm_tm (erase_tm u0)) Hy) as (HyL & HyDomG & HyX & HyFu).
      assert (Hne : y <> X) by (symmetry; exact (notin_singleton_1 X y HyX)).
      assert (Hf := f_equal (subst_tm_tm X u0) (e y HyL)).
      rewrite (subst_tm_open_tm_var B3 X u0 y Hu) in Hf.
      rewrite (subst_tm_open_tm_v B2 X u0 (a_Conv (a_Var_f y) (g_Sym g1)) Hu) in Hf.
      rewrite (subst_tm_tm_conv_var_sym X u0 y g1 Hne) in Hf.
      rewrite (subst_tm_tm_var_neq X y u0 Hne) in Hf.
      exact Hf.
    + exact (IHa1 G1 G2 X A0 u0 Heq HctxG HX Hu HCtxSub HHyp).
    + exact (IHa2 G1 G2 X A0 u0 Heq HctxG HX Hu HCtxSub HHyp).
    + exact (IHa3 G1 G2 X A0 u0 Heq HctxG HX Hu HCtxSub HHyp).
  (* An_AbsCong *)
  - intros L G D rho g1 g2 A1 b1 A2 b3 b2 B a IHa a0 IHa0 e a1 IHa1 a2 IHa2 r1 r2 a3 IHa3 G1 G2 X A0 u0 Heq HctxG HX Hu HCtxSub HHyp D' HDsub.
    cbn [subst_tm_co subst_tm_tm].
    apply (An_AbsCong (AtomSetImpl.union L (AtomSetImpl.union (dom G) (AtomSetImpl.union (AtomSetImpl.singleton X) (fv_tm_tm_tm (erase_tm u0)))))
              (subTm_ctx X u0 G1 ++ subTm_ctx X u0 G2) D' rho
              (subst_tm_co X u0 g1) (subst_tm_co X u0 g2)
              (subst_tm_tm X u0 A1) (subst_tm_tm X u0 b1)
              (subst_tm_tm X u0 A2) (subst_tm_tm X u0 b3) (subst_tm_tm X u0 b2) (subst_tm_tm X u0 B)).
    + exact (IHa G1 G2 X A0 u0 Heq HctxG HX Hu HCtxSub HHyp D' HDsub).
    + intro y. intro Hy.
      destruct (notin_union4 y L (dom G) (AtomSetImpl.singleton X) (fv_tm_tm_tm (erase_tm u0)) Hy) as (HyL & HyDomG & HyX & HyFu).
      assert (Hne : y <> X) by (symmetry; exact (notin_singleton_1 X y HyX)).
      assert (HctxM : AnnCtx ((y, Tm A1) :: G)) by exact (An_ConsTm G y A1 HctxG a1 HyDomG).
      assert (HctxSubM : AnnCtx ((y, Tm (subst_tm_tm X u0 A1)) :: (subTm_ctx X u0 G1 ++ subTm_ctx X u0 G2)))
        by exact (An_ConsTm (subTm_ctx X u0 G1 ++ subTm_ctx X u0 G2) y (subst_tm_tm X u0 A1) HCtxSub
                     (IHa1 G1 G2 X A0 u0 Heq HctxG HX Hu HCtxSub HHyp)
                     (notin_dom_subst_ctx' G G1 X (Tm A0) G2 u0 y Heq HyDomG)).
      assert (Hbody := IHa0 y HyL ((y, Tm A1) :: G1) G2 X A0 u0
                        (cons_ctx_decomp y (Tm A1) G1 X A0 G2 G Heq) HctxM HX Hu HctxSubM HHyp D' HDsub).
      rewrite (subst_tm_open_co_wrt_tm_var g2 X u0 y Hu) in Hbody.
      rewrite (subst_tm_open_tm_var b1 X u0 y Hu) in Hbody.
      rewrite (subst_tm_open_tm_var b2 X u0 y Hu) in Hbody.
      rewrite (subst_tm_tm_var_neq X y u0 Hne) in Hbody.
      exact Hbody.
    + intro y. intro Hy.
      destruct (notin_union4 y L (dom G) (AtomSetImpl.singleton X) (fv_tm_tm_tm (erase_tm u0)) Hy) as (HyL & HyDomG & HyX & HyFu).
      assert (Hne : y <> X) by (symmetry; exact (notin_singleton_1 X y HyX)).
      assert (Hf := f_equal (subst_tm_tm X u0) (e y HyL)).
      rewrite (subst_tm_open_tm_var b3 X u0 y Hu) in Hf.
      rewrite (subst_tm_open_tm_v b2 X u0 (a_Conv (a_Var_f y) (g_Sym g1)) Hu) in Hf.
      rewrite (subst_tm_tm_conv_var_sym X u0 y g1 Hne) in Hf.
      rewrite (subst_tm_tm_var_neq X y u0 Hne) in Hf.
      exact Hf.
    + exact (IHa1 G1 G2 X A0 u0 Heq HctxG HX Hu HCtxSub HHyp).
    + exact (IHa2 G1 G2 X A0 u0 Heq HctxG HX Hu HCtxSub HHyp).
    + intro y. intro Hy.
      destruct (notin_union4 y L (dom G) (AtomSetImpl.singleton X) (fv_tm_tm_tm (erase_tm u0)) Hy) as (HyL & HyDomG & HyX & HyFu).
      assert (Hne : y <> X) by (symmetry; exact (notin_singleton_1 X y HyX)).
      destruct rho.
      * apply Rho_Rel. exact I.
      * apply Rho_IrrRel.
        fold subst_tm_tm.
        rewrite (erase_open_subst_tm_var b1 X u0 y Hu Hne).
        exact ((proj1 notin_subst_tm_tm) (erase_tm (open_tm_wrt_tm b1 (a_Var_f y))) X (erase_tm u0) y
                 (RhoCheck_irrel_inv y (erase_tm (open_tm_wrt_tm b1 (a_Var_f y))) (r1 y HyL)) HyFu).
    + intro y. intro Hy.
      destruct (notin_union4 y L (dom G) (AtomSetImpl.singleton X) (fv_tm_tm_tm (erase_tm u0)) Hy) as (HyL & HyDomG & HyX & HyFu).
      assert (Hne : y <> X) by (symmetry; exact (notin_singleton_1 X y HyX)).
      destruct rho.
      * apply Rho_Rel. exact I.
      * apply Rho_IrrRel.
        fold subst_tm_tm.
        rewrite (erase_open_subst_tm_var b3 X u0 y Hu Hne).
        exact ((proj1 notin_subst_tm_tm) (erase_tm (open_tm_wrt_tm b3 (a_Var_f y))) X (erase_tm u0) y
                 (RhoCheck_irrel_inv y (erase_tm (open_tm_wrt_tm b3 (a_Var_f y))) (r2 y HyL)) HyFu).
    + exact (IHa3 G1 G2 X A0 u0 Heq HctxG HX Hu HCtxSub HHyp).
  (* An_AppCong *)
  - intros G D g1 rho g2 a1 a2 b1 b2 A B g3 a IHa a0 IHa0 a1' IHa1 a2' IHa2 a3 IHa3 G1 G2 X A0 u0 Heq HctxG HX Hu HCtxSub HHyp D' HDsub.
    cbn [subst_tm_co subst_tm_tm].
    apply (An_AppCong (subTm_ctx X u0 G1 ++ subTm_ctx X u0 G2) D'
              (subst_tm_co X u0 g1) rho (subst_tm_co X u0 g2)
              (subst_tm_tm X u0 a1) (subst_tm_tm X u0 a2)
              (subst_tm_tm X u0 b1) (subst_tm_tm X u0 b2)
              (subst_tm_tm X u0 A) (subst_tm_tm X u0 B) (subst_tm_co X u0 g3)).
    + exact (IHa G1 G2 X A0 u0 Heq HctxG HX Hu HCtxSub HHyp D' HDsub).
    + exact (IHa0 G1 G2 X A0 u0 Heq HctxG HX Hu HCtxSub HHyp D' HDsub).
    + exact (IHa1 G1 G2 X A0 u0 Heq HctxG HX Hu HCtxSub HHyp).
    + exact (IHa2 G1 G2 X A0 u0 Heq HctxG HX Hu HCtxSub HHyp).
    + exact (IHa3 G1 G2 X A0 u0 Heq HctxG HX Hu HCtxSub HHyp (dom (subTm_ctx X u0 G1 ++ subTm_ctx X u0 G2))
                   (fun c Hin Hne => in_dom_subst_ctx' G G1 X (Tm A0) G2 u0 c Heq Hin Hne)).
  (* An_PiFst *)
  - intros G D g A1 A2 rho B1 B2 a IHa G1 G2 X A0 u0 Heq HctxG HX Hu HCtxSub HHyp D' HDsub.
    cbn [subst_tm_co subst_tm_tm].
    apply An_PiFst with (rho := rho) (B1 := subst_tm_tm X u0 B1) (B2 := subst_tm_tm X u0 B2).
    exact (IHa G1 G2 X A0 u0 Heq HctxG HX Hu HCtxSub HHyp D' HDsub).


  (* An_PiSnd *)
  - intros G D g1 g2 B1 a1 B2 a2 rho A1 A2 a IHa a0 IHa0 a1' IHa1 a2' IHa2 G1 G2 X A0 u0 Heq HctxG HX Hu HCtxSub HHyp D' HDsub.
    cbn [subst_tm_co subst_tm_tm].
    rewrite (subst_tm_open_tm_v B1 X u0 a1 Hu).
    rewrite (subst_tm_open_tm_v B2 X u0 a2 Hu).
    apply (An_PiSnd (subTm_ctx X u0 G1 ++ subTm_ctx X u0 G2) D'
              (subst_tm_co X u0 g1) (subst_tm_co X u0 g2)
              (subst_tm_tm X u0 B1) (subst_tm_tm X u0 a1)
              (subst_tm_tm X u0 B2) (subst_tm_tm X u0 a2) rho
              (subst_tm_tm X u0 A1) (subst_tm_tm X u0 A2)).
    + exact (IHa G1 G2 X A0 u0 Heq HctxG HX Hu HCtxSub HHyp D' HDsub).
    + exact (IHa0 G1 G2 X A0 u0 Heq HctxG HX Hu HCtxSub HHyp D' HDsub).
    + exact (IHa1 G1 G2 X A0 u0 Heq HctxG HX Hu HCtxSub HHyp).
    + exact (IHa2 G1 G2 X A0 u0 Heq HctxG HX Hu HCtxSub HHyp).
  (* An_CPiCong *)
  - intros L G D g1 g3 phi1 B1 phi2 B3 B2 a IHa a0 IHa0 e a1 IHa1 a2 IHa2 a3 IHa3 G1 G2 X A0 u0 Heq HctxG HX Hu HCtxSub HHyp D' HDsub.
    cbn [subst_tm_co subst_tm_constraint subst_tm_tm].
    apply (An_CPiCong (AtomSetImpl.union L (AtomSetImpl.union (dom G) (AtomSetImpl.union (AtomSetImpl.singleton X) (fv_tm_tm_tm (erase_tm u0)))))
              (subTm_ctx X u0 G1 ++ subTm_ctx X u0 G2) D'
              (subst_tm_co X u0 g1) (subst_tm_co X u0 g3)
              (subst_tm_constraint X u0 phi1) (subst_tm_tm X u0 B1)
              (subst_tm_constraint X u0 phi2) (subst_tm_tm X u0 B3) (subst_tm_tm X u0 B2)).
    + exact (IHa G1 G2 X A0 u0 Heq HctxG HX Hu HCtxSub HHyp D' HDsub).
    + intro c. intro Hc.
      destruct (notin_union4 c L (dom G) (AtomSetImpl.singleton X) (fv_tm_tm_tm (erase_tm u0)) Hc) as (HcL & HcDomG & HcX & HcFu).
      assert (Hty1 : AnnTyping (subTm_ctx X u0 G1 ++ subTm_ctx X u0 G2) (a_CPi (subst_tm_constraint X u0 phi1) (subst_tm_tm X u0 B1)) a_Star).
      { cbn [subst_tm_tm]. exact (IHa1 G1 G2 X A0 u0 Heq HctxG HX Hu HCtxSub HHyp). }
      assert (HctxM : AnnCtx ((c, Co phi1) :: G)) by exact (An_ConsCo G c phi1 HctxG (AnnTyping_cpi_wff G phi1 B1 a1) HcDomG).
      assert (HctxSubM : AnnCtx ((c, Co (subst_tm_constraint X u0 phi1)) :: (subTm_ctx X u0 G1 ++ subTm_ctx X u0 G2)))
        by exact (An_ConsCo (subTm_ctx X u0 G1 ++ subTm_ctx X u0 G2) c (subst_tm_constraint X u0 phi1) HCtxSub
                     (AnnTyping_cpi_wff (subTm_ctx X u0 G1 ++ subTm_ctx X u0 G2) (subst_tm_constraint X u0 phi1) (subst_tm_tm X u0 B1) Hty1)
                     (notin_dom_subst_ctx' G G1 X (Tm A0) G2 u0 c Heq HcDomG)).
      assert (Hbody := IHa0 c HcL ((c, Co phi1) :: G1) G2 X A0 u0
                        (cons_ctx_decomp c (Co phi1) G1 X A0 G2 G Heq) HctxM HX Hu HctxSubM HHyp D' HDsub).
      rewrite (subst_tm_open_co_co_var g3 X u0 c Hu) in Hbody.
      rewrite (subst_tm_open_tm_co_var B1 X u0 c Hu) in Hbody.
      rewrite (subst_tm_open_tm_co_var B2 X u0 c Hu) in Hbody.
      exact Hbody.
    + intro c. intro Hc.
      destruct (notin_union4 c L (dom G) (AtomSetImpl.singleton X) (fv_tm_tm_tm (erase_tm u0)) Hc) as (HcL & HcDomG & HcX & HcFu).
      assert (Hf := f_equal (subst_tm_tm X u0) (e c HcL)).
      rewrite (subst_tm_open_tm_co_var B3 X u0 c Hu) in Hf.
      rewrite (subst_tm_open_tm_co_g B2 X u0 (g_Cast (g_Var_f c) (g_Sym g1)) Hu) in Hf.
      cbn [subst_tm_co] in Hf.
      exact Hf.
    + exact (IHa1 G1 G2 X A0 u0 Heq HctxG HX Hu HCtxSub HHyp).
    + exact (IHa2 G1 G2 X A0 u0 Heq HctxG HX Hu HCtxSub HHyp).
    + exact (IHa3 G1 G2 X A0 u0 Heq HctxG HX Hu HCtxSub HHyp).
  (* An_CAbsCong *)
  - intros L G D g1 g3 g4 phi1 a1 phi2 a3 a2 B1 B B2 a IHa a0 IHa0 e p1 IHp1 p2 IHp2 p3 IHp3 p4 IHp4 G1 G2 X A0 u0 Heq HctxG HX Hu HCtxSub HHyp D' HDsub.
    cbn [subst_tm_co subst_tm_constraint subst_tm_tm].
    apply (An_CAbsCong (AtomSetImpl.union L (AtomSetImpl.union (dom G) (AtomSetImpl.union (AtomSetImpl.singleton X) (fv_tm_tm_tm (erase_tm u0)))))
              (subTm_ctx X u0 G1 ++ subTm_ctx X u0 G2) D'
              (subst_tm_co X u0 g1) (subst_tm_co X u0 g3) (subst_tm_co X u0 g4)
              (subst_tm_constraint X u0 phi1) (subst_tm_tm X u0 a1)
              (subst_tm_constraint X u0 phi2) (subst_tm_tm X u0 a3) (subst_tm_tm X u0 a2)
              (subst_tm_tm X u0 B1) (subst_tm_tm X u0 B) (subst_tm_tm X u0 B2)).
    + exact (IHa G1 G2 X A0 u0 Heq HctxG HX Hu HCtxSub HHyp D' HDsub).
    + intro c. intro Hc.
      destruct (notin_union4 c L (dom G) (AtomSetImpl.singleton X) (fv_tm_tm_tm (erase_tm u0)) Hc) as (HcL & HcDomG & HcX & HcFu).
      assert (Hty1 : AnnTyping (subTm_ctx X u0 G1 ++ subTm_ctx X u0 G2) (a_CAbs (subst_tm_constraint X u0 phi1) (subst_tm_tm X u0 a1)) (a_CPi (subst_tm_constraint X u0 phi1) (subst_tm_tm X u0 B1))).
      { cbn [subst_tm_tm]. exact (IHp1 G1 G2 X A0 u0 Heq HctxG HX Hu HCtxSub HHyp). }
      assert (HctxM : AnnCtx ((c, Co phi1) :: G)) by exact (An_ConsCo G c phi1 HctxG (AnnTyping_cabs_wff G phi1 a1 (a_CPi phi1 B1) p1) HcDomG).
      assert (HctxSubM : AnnCtx ((c, Co (subst_tm_constraint X u0 phi1)) :: (subTm_ctx X u0 G1 ++ subTm_ctx X u0 G2)))
        by exact (An_ConsCo (subTm_ctx X u0 G1 ++ subTm_ctx X u0 G2) c (subst_tm_constraint X u0 phi1) HCtxSub
                     (AnnTyping_cabs_wff (subTm_ctx X u0 G1 ++ subTm_ctx X u0 G2) (subst_tm_constraint X u0 phi1) (subst_tm_tm X u0 a1) (a_CPi (subst_tm_constraint X u0 phi1) (subst_tm_tm X u0 B1)) Hty1)
                     (notin_dom_subst_ctx' G G1 X (Tm A0) G2 u0 c Heq HcDomG)).
      assert (Hbody := IHa0 c HcL ((c, Co phi1) :: G1) G2 X A0 u0
                        (cons_ctx_decomp c (Co phi1) G1 X A0 G2 G Heq) HctxM HX Hu HctxSubM HHyp D' HDsub).
      rewrite (subst_tm_open_co_co_var g3 X u0 c Hu) in Hbody.
      rewrite (subst_tm_open_tm_co_var a1 X u0 c Hu) in Hbody.
      rewrite (subst_tm_open_tm_co_var a2 X u0 c Hu) in Hbody.
      exact Hbody.
    + intro c. intro Hc.
      destruct (notin_union4 c L (dom G) (AtomSetImpl.singleton X) (fv_tm_tm_tm (erase_tm u0)) Hc) as (HcL & HcDomG & HcX & HcFu).
      assert (Hf := f_equal (subst_tm_tm X u0) (e c HcL)).
      rewrite (subst_tm_open_tm_co_var a3 X u0 c Hu) in Hf.
      rewrite (subst_tm_open_tm_co_g a2 X u0 (g_Cast (g_Var_f c) (g_Sym g1)) Hu) in Hf.
      cbn [subst_tm_co] in Hf.
      exact Hf.
    + exact (IHp1 G1 G2 X A0 u0 Heq HctxG HX Hu HCtxSub HHyp).
    + exact (IHp2 G1 G2 X A0 u0 Heq HctxG HX Hu HCtxSub HHyp).
    + exact (IHp3 G1 G2 X A0 u0 Heq HctxG HX Hu HCtxSub HHyp).
    + exact (IHp4 G1 G2 X A0 u0 Heq HctxG HX Hu HCtxSub HHyp (dom (subTm_ctx X u0 G1 ++ subTm_ctx X u0 G2))
                   (fun c Hin Hne => in_dom_subst_ctx' G G1 X (Tm A0) G2 u0 c Heq Hin Hne)).
  (* An_CAppCong *)
  - intros G D g1 g2 g3 a1 b1 a2 b2 a3 b3 A B g4 a IHa a0 IHa0 a1' IHa1 a2' IHa2 a3' IHa3 a4 IHa4 G1 G2 X A0 u0 Heq HctxG HX Hu HCtxSub HHyp D' HDsub.
    cbn [subst_tm_co subst_tm_tm].
    apply (An_CAppCong (subTm_ctx X u0 G1 ++ subTm_ctx X u0 G2) D'
              (subst_tm_co X u0 g1) (subst_tm_co X u0 g2) (subst_tm_co X u0 g3)
              (subst_tm_tm X u0 a1) (subst_tm_tm X u0 b1)
              (subst_tm_tm X u0 a2) (subst_tm_tm X u0 b2)
              (subst_tm_tm X u0 a3) (subst_tm_tm X u0 b3)
              (subst_tm_tm X u0 A) (subst_tm_tm X u0 B) (subst_tm_co X u0 g4)).
    + exact (IHa G1 G2 X A0 u0 Heq HctxG HX Hu HCtxSub HHyp D' HDsub).
    + exact (IHa0 G1 G2 X A0 u0 Heq HctxG HX Hu HCtxSub HHyp (dom (subTm_ctx X u0 G1 ++ subTm_ctx X u0 G2))
                   (fun c Hin Hne => in_dom_subst_ctx' G G1 X (Tm A0) G2 u0 c Heq Hin Hne)).
    + exact (IHa1 G1 G2 X A0 u0 Heq HctxG HX Hu HCtxSub HHyp (dom (subTm_ctx X u0 G1 ++ subTm_ctx X u0 G2))
                   (fun c Hin Hne => in_dom_subst_ctx' G G1 X (Tm A0) G2 u0 c Heq Hin Hne)).
    + exact (IHa2 G1 G2 X A0 u0 Heq HctxG HX Hu HCtxSub HHyp).
    + exact (IHa3 G1 G2 X A0 u0 Heq HctxG HX Hu HCtxSub HHyp).
    + exact (IHa4 G1 G2 X A0 u0 Heq HctxG HX Hu HCtxSub HHyp (dom (subTm_ctx X u0 G1 ++ subTm_ctx X u0 G2))
                   (fun c Hin Hne => in_dom_subst_ctx' G G1 X (Tm A0) G2 u0 c Heq Hin Hne)).
  (* An_CPiSnd *)
  - intros G D g1 g2 g3 B1 B2 a a' A b b' B a0 IHa0 a1 IHa1 a2 IHa2 G1 G2 X A0 u0 Heq HctxG HX Hu HCtxSub HHyp D' HDsub.
    cbn [subst_tm_co subst_tm_tm].
    rewrite (subst_tm_open_tm_co_g B1 X u0 g2 Hu).
    rewrite (subst_tm_open_tm_co_g B2 X u0 g3 Hu).
    apply (An_CPiSnd (subTm_ctx X u0 G1 ++ subTm_ctx X u0 G2) D'
              (subst_tm_co X u0 g1) (subst_tm_co X u0 g2) (subst_tm_co X u0 g3)
              (subst_tm_tm X u0 B1) (subst_tm_tm X u0 B2)
              (subst_tm_tm X u0 a) (subst_tm_tm X u0 a') (subst_tm_tm X u0 A)
              (subst_tm_tm X u0 b) (subst_tm_tm X u0 b') (subst_tm_tm X u0 B)).
    + exact (IHa0 G1 G2 X A0 u0 Heq HctxG HX Hu HCtxSub HHyp D' HDsub).
    + exact (IHa1 G1 G2 X A0 u0 Heq HctxG HX Hu HCtxSub HHyp (dom (subTm_ctx X u0 G1 ++ subTm_ctx X u0 G2))
                   (fun c Hin Hne => in_dom_subst_ctx' G G1 X (Tm A0) G2 u0 c Heq Hin Hne)).
    + exact (IHa2 G1 G2 X A0 u0 Heq HctxG HX Hu HCtxSub HHyp (dom (subTm_ctx X u0 G1 ++ subTm_ctx X u0 G2))
                   (fun c Hin Hne => in_dom_subst_ctx' G G1 X (Tm A0) G2 u0 c Heq Hin Hne)).


  (* An_Cast *)
  - intros G D g1 g2 b b' a a' A B a0 IHa0 a1 IHa1 G1 G2 X A0 u0 Heq HctxG HX Hu HCtxSub HHyp D' HDsub.
    cbn [subst_tm_co subst_tm_tm].
    apply (An_Cast (subTm_ctx X u0 G1 ++ subTm_ctx X u0 G2) D'
              (subst_tm_co X u0 g1) (subst_tm_co X u0 g2)
              (subst_tm_tm X u0 b) (subst_tm_tm X u0 b')
              (subst_tm_tm X u0 a) (subst_tm_tm X u0 a')
              (subst_tm_tm X u0 A) (subst_tm_tm X u0 B)).
    + exact (IHa0 G1 G2 X A0 u0 Heq HctxG HX Hu HCtxSub HHyp D' HDsub).
    + exact (IHa1 G1 G2 X A0 u0 Heq HctxG HX Hu HCtxSub HHyp D' HDsub).
  (* An_IsoSnd *)
  - intros G D g A B a a' b b' a0 IHa G1 G2 X A0 u0 Heq HctxG HX Hu HCtxSub HHyp D' HDsub.
    cbn [subst_tm_co subst_tm_tm].
    apply (An_IsoSnd (subTm_ctx X u0 G1 ++ subTm_ctx X u0 G2) D'
              (subst_tm_co X u0 g) (subst_tm_tm X u0 A) (subst_tm_tm X u0 B)
              (subst_tm_tm X u0 a) (subst_tm_tm X u0 a')
              (subst_tm_tm X u0 b) (subst_tm_tm X u0 b')).
    exact (IHa G1 G2 X A0 u0 Heq HctxG HX Hu HCtxSub HHyp D' HDsub).
  (* An_Empty *)
  - intros. exact I.
  (* An_ConsTm *)
  - intros. exact I.
  (* An_ConsCo *)
  - intros. exact I.
  (* An_Sig_Empty *)
  - intros. exact I.
  (* An_Sig_Cons *)
  - intros. exact I.
Qed.



(* ================================================================== *)
(* Main term-substitution theorem (suffix-context form)               *)
(* ================================================================== *)

Lemma AnnTyping_subst_tm_all :
  (forall G t T (H:AnnTyping G t T), forall G1 G2 x A u,
    G = G1 ++ (x, Tm A) :: nil ++ G2 ->
    x `notin` fv_tm_tm_tm A ->
    lc_tm u ->
    AnnCtx (subTm_ctx x u G1 ++ subTm_ctx x u G2) ->
    (forall G', ctx_sub (subTm_ctx x u G2) G' -> AnnCtx G' -> AnnTyping G' u A) ->
    AnnTyping (subTm_ctx x u G1 ++ subTm_ctx x u G2)
              (subst_tm_tm x u t) (subst_tm_tm x u T)) /\
  (forall G p (H:AnnPropWff G p), forall G1 G2 x A u,
    G = G1 ++ (x, Tm A) :: nil ++ G2 ->
    x `notin` fv_tm_tm_tm A ->
    lc_tm u ->
    AnnCtx (subTm_ctx x u G1 ++ subTm_ctx x u G2) ->
    (forall G', ctx_sub (subTm_ctx x u G2) G' -> AnnCtx G' -> AnnTyping G' u A) ->
    AnnPropWff (subTm_ctx x u G1 ++ subTm_ctx x u G2) (subst_tm_constraint x u p)) /\
  (forall G D g p q (H:AnnIso G D g p q), forall G1 G2 x A u,
    G = G1 ++ (x, Tm A) :: nil ++ G2 ->
    x `notin` fv_tm_tm_tm A ->
    lc_tm u ->
    AnnCtx (subTm_ctx x u G1 ++ subTm_ctx x u G2) ->
    (forall G', ctx_sub (subTm_ctx x u G2) G' -> AnnCtx G' -> AnnTyping G' u A) ->
    forall D', (forall c, c `in` D -> c <> x -> c `in` D') ->
    AnnIso (subTm_ctx x u G1 ++ subTm_ctx x u G2) D'
           (subst_tm_co x u g) (subst_tm_constraint x u p) (subst_tm_constraint x u q)) /\
  (forall G D g a b (H:AnnDefEq G D g a b), forall G1 G2 x A u,
    G = G1 ++ (x, Tm A) :: nil ++ G2 ->
    x `notin` fv_tm_tm_tm A ->
    lc_tm u ->
    AnnCtx (subTm_ctx x u G1 ++ subTm_ctx x u G2) ->
    (forall G', ctx_sub (subTm_ctx x u G2) G' -> AnnCtx G' -> AnnTyping G' u A) ->
    forall D', (forall c, c `in` D -> c <> x -> c `in` D') ->
    AnnDefEq (subTm_ctx x u G1 ++ subTm_ctx x u G2) D'
             (subst_tm_co x u g) (subst_tm_tm x u a) (subst_tm_tm x u b)).
Proof.
  destruct Main_aux as [H1 [H2 [H3 [H4 _]]]].
  repeat split.
  - intros G t T H G1 G2 x A u Heq HX Hu HCtxSub HHyp.
    exact (H1 G t T H G1 G2 x A u Heq (AnnTyping_AnnCtx G t T H) HX Hu HCtxSub HHyp).
  - intros G p H G1 G2 x A u Heq HX Hu HCtxSub HHyp.
    exact (H2 G p H G1 G2 x A u Heq (AnnPropWff_AnnCtx G p H) HX Hu HCtxSub HHyp).
  - intros G D g p q H G1 G2 x A u Heq HX Hu HCtxSub HHyp D' HDsub.
    exact (H3 G D g p q H G1 G2 x A u Heq (AnnIso_AnnCtx G D g p q H) HX Hu HCtxSub HHyp D' HDsub).
  - intros G D g a b H G1 G2 x A u Heq HX Hu HCtxSub HHyp D' HDsub.
    exact (H4 G D g a b H G1 G2 x A u Heq (AnnDefEq_AnnCtx G D g a b H) HX Hu HCtxSub HHyp D' HDsub).
Qed.
(* Helpers for coercion-variable substitution *)
Lemma notin_union3 : forall (y:atom) (s1 s2 s3:atoms),
  y `notin` AtomSetImpl.union s1 (AtomSetImpl.union s2 s3) ->
  y `notin` s1 /\ y `notin` s2 /\ y `notin` s3.
Proof.
  intros y s1 s2 s3 H.
  assert (H1 : y `notin` s1) by (apply (notin_union_1 y s1 _ H)).
  assert (H23 : y `notin` AtomSetImpl.union s2 s3)
    by (apply (notin_union_2 y s1 _ H)).
  split; [exact H1|]. split.
  - exact (notin_union_1 y s2 s3 H23).
  - exact (notin_union_2 y s2 s3 H23).
Qed.

Lemma cons_ctx_decomp_co : forall (a:atom) (s:sort) (G1:context) (C:covar) (Phi:constraint) (G2 G:context),
  G = G1 ++ (C, Co Phi) :: nil ++ G2 ->
  ((a,s) :: G) = ((a,s) :: G1) ++ (C, Co Phi) :: nil ++ G2.
Proof.
  intros a s G1 C Phi G2 G Heq. subst G. reflexivity.
Qed.

Lemma in_dom_subCo_ctx : forall (G1:context) (C:covar) (s:sort) G2 g (c:atom),
  c `in` dom (G1 ++ (C,s) :: nil ++ G2) -> c <> C ->
  c `in` dom (subCo_ctx C g G1 ++ subCo_ctx C g G2).
Proof.
  intros G1 C s G2 g c H Hne.
  cbn [app] in H.
  assert (H' : c `in` dom (G1 ++ G2))
    by (apply (in_dom_remove_mid G1 C s G2 c); auto).
  rewrite <- subCo_ctx_app. rewrite dom_subCo_ctx. exact H'.
Qed.

Lemma notin_dom_subCo_ctx : forall (G1:context) (C:covar) (s:sort) G2 g (y:atom),
  y `notin` dom (G1 ++ (C,s) :: nil ++ G2) ->
  y `notin` dom (subCo_ctx C g G1 ++ subCo_ctx C g G2).
Proof.
  intros G1 C s G2 g y H Hin.
  cbn [app] in H.
  assert (Hin' : y `in` dom (G1 ++ G2)).
  { rewrite <- subCo_ctx_app in Hin. rewrite dom_subCo_ctx in Hin. exact Hin. }
  apply H. destruct (@in_dom_binds sort y (G1++G2) Hin') as [t Ht].
  apply in_dom_of_in with (a:=t). apply in_app_iff in Ht.
  destruct Ht as [H1|H2]; apply in_app_iff.
  - left. exact H1.
  - right. apply in_cons. exact H2.
Qed.

Lemma in_dom_subCo_ctx' : forall (G:context) G1 (C:covar) s G2 g c,
  G = G1 ++ (C,s) :: nil ++ G2 ->
  c `in` dom G -> c <> C ->
  c `in` dom (subCo_ctx C g G1 ++ subCo_ctx C g G2).
Proof.
  intros G G1 C s G2 g c Heq Hin Hne.
  rewrite Heq in Hin.
  apply (in_dom_subCo_ctx G1 C s G2 g c Hin Hne).
Qed.

Lemma notin_dom_subCo_ctx' : forall (G:context) G1 (C:covar) s G2 g y,
  G = G1 ++ (C,s) :: nil ++ G2 ->
  y `notin` dom G ->
  y `notin` dom (subCo_ctx C g G1 ++ subCo_ctx C g G2).
Proof.
  intros G G1 C s G2 g y Heq Hy.
  rewrite Heq in Hy.
  apply (notin_dom_subCo_ctx G1 C s G2 g y Hy).
Qed.

Lemma subst_co_tm_conv_var_sym : forall (C:covar) (GSub:co) (y:tmvar) (g:co),
  y <> C ->
  subst_co_tm C GSub (a_Conv (a_Var_f y) (g_Sym g))
  = a_Conv (a_Var_f y) (g_Sym (subst_co_co C GSub g)).
Proof.
  intros C GSub y g Hne.
  cbn [subst_co_tm subst_co_co].
  destruct (KeySetFacts.eq_dec y C) as [e|e].
  - exfalso. apply Hne. exact e.
  - reflexivity.
Qed.

Lemma subst_co_co_cast_var_sym : forall (C:covar) (GSub:co) (c:covar) (g:co),
  c <> C ->
  subst_co_co C GSub (g_Cast (g_Var_f c) (g_Sym g))
  = g_Cast (g_Var_f c) (g_Sym (subst_co_co C GSub g)).
Proof.
  intros C GSub c g Hne.
  cbn [subst_co_co].
  destruct (KeySetFacts.eq_dec c C) as [e|e].
  - exfalso. apply Hne. exact e.
  - reflexivity.
Qed.


Lemma erase_open_subst_co_tm_var : forall (b:tm) (C:covar) (GSub:co) (y:tmvar),
  lc_co GSub ->
  erase_tm (open_tm_wrt_tm (subst_co_tm C GSub b) (a_Var_f y))
  = erase_tm (open_tm_wrt_tm b (a_Var_f y)).
Proof.
  intros b C GSub y HG.
  rewrite <- (subst_co_open_tm_var b C GSub y HG).
  rewrite (proj1 erase_subst_co_tm). reflexivity.
Qed.

Definition CoRemovedHyp (C:covar) (G2:context) (Phi:constraint) (GSub:co) : Prop :=
  forall (G':context) (D':available_props) (a b A:tm), Phi = Eq a b A ->
    ctx_sub (subCo_ctx C GSub G2) G' -> AnnCtx G' ->
    AnnDefEq G' D' GSub a b.

Definition QT (G:context) (t T:tm) (H:AnnTyping G t T) : Prop :=
  forall (G1 G2:context) (C:covar) (Phi:constraint) (GSub:co),
    G = G1 ++ (C, Co Phi) :: nil ++ G2 ->
    AnnCtx G ->
    C `notin` fvx_constraint Phi ->
    lc_co GSub ->
    AnnCtx (subCo_ctx C GSub G1 ++ subCo_ctx C GSub G2) ->
    CoRemovedHyp C G2 Phi GSub ->
    AnnTyping (subCo_ctx C GSub G1 ++ subCo_ctx C GSub G2)
              (subst_co_tm C GSub t) (subst_co_tm C GSub T).

Definition QW (G:context) (p:constraint) (H:AnnPropWff G p) : Prop :=
  forall (G1 G2:context) (C:covar) (Phi:constraint) (GSub:co),
    G = G1 ++ (C, Co Phi) :: nil ++ G2 ->
    AnnCtx G ->
    C `notin` fvx_constraint Phi ->
    lc_co GSub ->
    AnnCtx (subCo_ctx C GSub G1 ++ subCo_ctx C GSub G2) ->
    CoRemovedHyp C G2 Phi GSub ->
    AnnPropWff (subCo_ctx C GSub G1 ++ subCo_ctx C GSub G2) (subst_co_constraint C GSub p).

Definition QI (G:context) (D:available_props) (g:co) (p q:constraint) (H:AnnIso G D g p q) : Prop :=
  forall (G1 G2:context) (C:covar) (Phi:constraint) (GSub:co),
    G = G1 ++ (C, Co Phi) :: nil ++ G2 ->
    AnnCtx G ->
    C `notin` fvx_constraint Phi ->
    lc_co GSub ->
    AnnCtx (subCo_ctx C GSub G1 ++ subCo_ctx C GSub G2) ->
    CoRemovedHyp C G2 Phi GSub ->
    forall D', (forall d, d `in` D -> d <> C -> d `in` D') ->
    AnnIso (subCo_ctx C GSub G1 ++ subCo_ctx C GSub G2) D'
           (subst_co_co C GSub g) (subst_co_constraint C GSub p) (subst_co_constraint C GSub q).

Definition QE (G:context) (D:available_props) (g:co) (a b:tm) (H:AnnDefEq G D g a b) : Prop :=
  forall (G1 G2:context) (C:covar) (Phi:constraint) (GSub:co),
    G = G1 ++ (C, Co Phi) :: nil ++ G2 ->
    AnnCtx G ->
    C `notin` fvx_constraint Phi ->
    lc_co GSub ->
    AnnCtx (subCo_ctx C GSub G1 ++ subCo_ctx C GSub G2) ->
    CoRemovedHyp C G2 Phi GSub ->
    forall D', (forall d, d `in` D -> d <> C -> d `in` D') ->
    AnnDefEq (subCo_ctx C GSub G1 ++ subCo_ctx C GSub G2) D'
             (subst_co_co C GSub g) (subst_co_tm C GSub a) (subst_co_tm C GSub b).

Lemma Main_co_aux :
  (forall G t T (H:AnnTyping G t T), QT G t T H) /\
  (forall G p (H:AnnPropWff G p), QW G p H) /\
  (forall G D g p q (H:AnnIso G D g p q), QI G D g p q H) /\
  (forall G D g a b (H:AnnDefEq G D g a b), QE G D g a b H) /\
  (forall G, AnnCtx G -> True) /\
  (forall S, AnnSig S -> True).
Proof.
  apply (AnnTyping_comb QT QW QI QE (fun _ _ => True) (fun _ _ => True)).
  (* An_Star *)
  - intros G a IHa G1 G2 C Phi GSub Heq HctxG HPhi HG HCtxSub HHyp.
    cbn [subst_co_tm]. apply An_Star. exact HCtxSub.
  (* An_Var *)
  - intros G x A a IHa b G1 G2 C Phi GSub Heq HctxG HPhi HG HCtxSub HHyp.
    destruct (annctx_uniq_split G G1 C (Co Phi) G2 HctxG Heq) as [HX1 HX2].
    rewrite Heq in b.
    destruct (binds_split_any G1 C (Co Phi) G2 x (Tm A) HX1 HX2 b) as [[Hxeq HAeq]|[Hne Hb]].
    + subst x. discriminate HAeq.
    + apply An_Var.
      * exact HCtxSub.
      * rewrite <- subCo_ctx_app.
        apply (binds_subCo_ctx C GSub (G1++G2) x (Tm A) Hb).
  (* An_Pi *)
  - intros L G rho A B a IHa a0 IHA0 G1 G2 C Phi GSub Heq HctxG HPhi HG HCtxSub HHyp.
    apply An_Pi with (L := AtomSetImpl.union L (AtomSetImpl.union (dom G) (AtomSetImpl.singleton C))).
    + intro y. intro Hy.
      destruct (notin_union3 y L (dom G) (AtomSetImpl.singleton C) Hy) as (HyL & HyDomG & HyX).
      assert (Hne : y <> C) by (symmetry; exact (notin_singleton_1 C y HyX)).
      assert (HctxM : AnnCtx ((y, Tm A) :: G)) by exact (An_ConsTm G y A HctxG a0 HyDomG).
      assert (HctxSubM : AnnCtx ((y, Tm (subst_co_tm C GSub A)) :: (subCo_ctx C GSub G1 ++ subCo_ctx C GSub G2)))
        by exact (An_ConsTm (subCo_ctx C GSub G1 ++ subCo_ctx C GSub G2) y (subst_co_tm C GSub A) HCtxSub
                     (IHA0 G1 G2 C Phi GSub Heq HctxG HPhi HG HCtxSub HHyp)
                     (notin_dom_subCo_ctx' G G1 C (Co Phi) G2 GSub y Heq HyDomG)).
      assert (Hbody := IHa y HyL ((y, Tm A) :: G1) G2 C Phi GSub
                        (cons_ctx_decomp_co y (Tm A) G1 C Phi G2 G Heq) HctxM HPhi HG HctxSubM HHyp).
      rewrite (subst_co_open_tm_var B C GSub y HG) in Hbody.
      exact Hbody.
    + exact (IHA0 G1 G2 C Phi GSub Heq HctxG HPhi HG HCtxSub HHyp).
  (* An_Abs *)
  - intros L G rho A a B a0 IHA0 a1 IHa r G1 G2 C Phi GSub Heq HctxG HPhi HG HCtxSub HHyp.
    apply An_Abs with (L := AtomSetImpl.union L (AtomSetImpl.union (dom G) (AtomSetImpl.singleton C))).
    + exact (IHA0 G1 G2 C Phi GSub Heq HctxG HPhi HG HCtxSub HHyp).
    + intro y. intro Hy.
      destruct (notin_union3 y L (dom G) (AtomSetImpl.singleton C) Hy) as (HyL & HyDomG & HyX).
      assert (Hne : y <> C) by (symmetry; exact (notin_singleton_1 C y HyX)).
      assert (HctxM : AnnCtx ((y, Tm A) :: G)) by exact (An_ConsTm G y A HctxG a0 HyDomG).
      assert (HctxSubM : AnnCtx ((y, Tm (subst_co_tm C GSub A)) :: (subCo_ctx C GSub G1 ++ subCo_ctx C GSub G2)))
        by exact (An_ConsTm (subCo_ctx C GSub G1 ++ subCo_ctx C GSub G2) y (subst_co_tm C GSub A) HCtxSub
                     (IHA0 G1 G2 C Phi GSub Heq HctxG HPhi HG HCtxSub HHyp)
                     (notin_dom_subCo_ctx' G G1 C (Co Phi) G2 GSub y Heq HyDomG)).
      assert (Hbody := IHa y HyL ((y, Tm A) :: G1) G2 C Phi GSub
                        (cons_ctx_decomp_co y (Tm A) G1 C Phi G2 G Heq) HctxM HPhi HG HctxSubM HHyp).
      rewrite (subst_co_open_tm_var a C GSub y HG) in Hbody.
      rewrite (subst_co_open_tm_var B C GSub y HG) in Hbody.
      exact Hbody.
    + intro y. intro Hy.
      destruct (notin_union3 y L (dom G) (AtomSetImpl.singleton C) Hy) as (HyL & HyDomG & HyX).
      assert (Hne : y <> C) by (symmetry; exact (notin_singleton_1 C y HyX)).
      destruct rho.
      * apply Rho_Rel. exact I.
      * apply Rho_IrrRel.
        fold subst_co_tm.
        rewrite (erase_open_subst_co_tm_var a C GSub y HG).
        exact (RhoCheck_irrel_inv y (erase_tm (open_tm_wrt_tm a (a_Var_f y))) (r y HyL)).
  (* An_App *)
  - intros G b rho a B A a0 IHa a1 IHa1 G1 G2 C Phi GSub Heq HctxG HPhi HG HCtxSub HHyp.
    cbn [subst_co_tm].
    rewrite (subst_co_open_tm_v B C GSub a HG).
    apply An_App with (A := subst_co_tm C GSub A).
    + exact (IHa G1 G2 C Phi GSub Heq HctxG HPhi HG HCtxSub HHyp).
    + exact (IHa1 G1 G2 C Phi GSub Heq HctxG HPhi HG HCtxSub HHyp).
  (* An_Conv *)
  - intros G a g B A a0 IHa a1 IHa1 a2 IHa2 G1 G2 C Phi GSub Heq HctxG HPhi HG HCtxSub HHyp.
    cbn [subst_co_tm].
    apply An_Conv with (A := subst_co_tm C GSub A).
    + exact (IHa G1 G2 C Phi GSub Heq HctxG HPhi HG HCtxSub HHyp).
    + exact (IHa1 G1 G2 C Phi GSub Heq HctxG HPhi HG HCtxSub HHyp (dom (subCo_ctx C GSub G1 ++ subCo_ctx C GSub G2))
                   (fun c Hin Hne => in_dom_subCo_ctx' G G1 C (Co Phi) G2 GSub c Heq Hin Hne)).
    + exact (IHa2 G1 G2 C Phi GSub Heq HctxG HPhi HG HCtxSub HHyp).
  (* An_CPi *)
  - intros L G phi B a IHa a0 IHa0 G1 G2 C Phi GSub Heq HctxG HPhi HG HCtxSub HHyp.
    apply An_CPi with (L := AtomSetImpl.union L (AtomSetImpl.union (dom G) (AtomSetImpl.singleton C))).
    + exact (IHa G1 G2 C Phi GSub Heq HctxG HPhi HG HCtxSub HHyp).
    + intro c. intro Hc.
      destruct (notin_union3 c L (dom G) (AtomSetImpl.singleton C) Hc) as (HcL & HcDomG & HcX).
      assert (Hcne : c <> C) by (symmetry; exact (notin_singleton_1 C c HcX)).
      assert (HctxM : AnnCtx ((c, Co phi) :: G)) by exact (An_ConsCo G c phi HctxG a HcDomG).
      assert (HctxSubM : AnnCtx ((c, Co (subst_co_constraint C GSub phi)) :: (subCo_ctx C GSub G1 ++ subCo_ctx C GSub G2)))
        by exact (An_ConsCo (subCo_ctx C GSub G1 ++ subCo_ctx C GSub G2) c (subst_co_constraint C GSub phi) HCtxSub
                     (IHa G1 G2 C Phi GSub Heq HctxG HPhi HG HCtxSub HHyp)
                     (notin_dom_subCo_ctx' G G1 C (Co Phi) G2 GSub c Heq HcDomG)).
      assert (Hbody := IHa0 c HcL ((c, Co phi) :: G1) G2 C Phi GSub
                        (cons_ctx_decomp_co c (Co phi) G1 C Phi G2 G Heq) HctxM HPhi HG HctxSubM HHyp).
      rewrite (subst_co_open_tm_co_var B C GSub c HG) in Hbody.
      rewrite (subst_co_co_var_neq C c GSub Hcne) in Hbody.
      exact Hbody.
  (* An_CAbs *)
  - intros L G phi a B a0 IHa a1 IHa1 G1 G2 C Phi GSub Heq HctxG HPhi HG HCtxSub HHyp.
    apply An_CAbs with (L := AtomSetImpl.union L (AtomSetImpl.union (dom G) (AtomSetImpl.singleton C))).
    + exact (IHa G1 G2 C Phi GSub Heq HctxG HPhi HG HCtxSub HHyp).
    + intro c. intro Hc.
      destruct (notin_union3 c L (dom G) (AtomSetImpl.singleton C) Hc) as (HcL & HcDomG & HcX).
      assert (Hcne : c <> C) by (symmetry; exact (notin_singleton_1 C c HcX)).
      assert (HctxM : AnnCtx ((c, Co phi) :: G)) by exact (An_ConsCo G c phi HctxG a0 HcDomG).
      assert (HctxSubM : AnnCtx ((c, Co (subst_co_constraint C GSub phi)) :: (subCo_ctx C GSub G1 ++ subCo_ctx C GSub G2)))
        by exact (An_ConsCo (subCo_ctx C GSub G1 ++ subCo_ctx C GSub G2) c (subst_co_constraint C GSub phi) HCtxSub
                     (IHa G1 G2 C Phi GSub Heq HctxG HPhi HG HCtxSub HHyp)
                     (notin_dom_subCo_ctx' G G1 C (Co Phi) G2 GSub c Heq HcDomG)).
      assert (Hbody := IHa1 c HcL ((c, Co phi) :: G1) G2 C Phi GSub
                        (cons_ctx_decomp_co c (Co phi) G1 C Phi G2 G Heq) HctxM HPhi HG HctxSubM HHyp).
      rewrite (subst_co_open_tm_co_var a C GSub c HG) in Hbody.
      rewrite (subst_co_co_var_neq C c GSub Hcne) in Hbody.
      rewrite (subst_co_open_tm_co_var B C GSub c HG) in Hbody.
      rewrite (subst_co_co_var_neq C c GSub Hcne) in Hbody.
      exact Hbody.
  (* An_CApp *)
  - intros G a1 g B a b A1 a0 IHa a1' IHa1 G1 G2 C Phi GSub Heq HctxG HPhi HG HCtxSub HHyp.
    cbn [subst_co_tm].
    rewrite (subst_co_open_tm_co_h B C GSub g HG).
    apply An_CApp with (a := subst_co_tm C GSub a) (b := subst_co_tm C GSub b) (A1 := subst_co_tm C GSub A1).
    + exact (IHa G1 G2 C Phi GSub Heq HctxG HPhi HG HCtxSub HHyp).
    + exact (IHa1 G1 G2 C Phi GSub Heq HctxG HPhi HG HCtxSub HHyp (dom (subCo_ctx C GSub G1 ++ subCo_ctx C GSub G2))
                   (fun c Hin Hne => in_dom_subCo_ctx' G G1 C (Co Phi) G2 GSub c Heq Hin Hne)).
  (* An_Fam *)
  - intros G F A a a0 IHa b a1 IHa1 G1 G2 C Phi GSub Heq HctxG HPhi HG HCtxSub HHyp.
    destruct (an_toplevel_ax_subst_co F a A C GSub b) as [Ha HA].
    apply (An_Fam (subCo_ctx C GSub G1 ++ subCo_ctx C GSub G2) F (subst_co_tm C GSub A) (subst_co_tm C GSub a)).
    + exact HCtxSub.
    + rewrite Ha, HA. exact b.
    + rewrite HA. exact a1.

  (* An_Wff *)
  - intros G a b A B a0 IHa a1 IHa1 e G1 G2 C Phi GSub Heq HctxG HPhi HG HCtxSub HHyp.
    cbn [subst_co_constraint].
    apply An_Wff with (B := subst_co_tm C GSub B).
    + exact (IHa G1 G2 C Phi GSub Heq HctxG HPhi HG HCtxSub HHyp).
    + exact (IHa1 G1 G2 C Phi GSub Heq HctxG HPhi HG HCtxSub HHyp).
    + rewrite ((proj1 erase_subst_co_tm) A C GSub).
      rewrite ((proj1 erase_subst_co_tm) B C GSub).
      rewrite e. reflexivity.
  (* An_PropCong *)
  - intros G D g1 A g2 A1 B1 A2 B2 a IHa a0 IHa0 a1 IHa1 a2 IHa2 G1 G2 C Phi GSub Heq HctxG HPhi HG HCtxSub HHyp D' HDsub.
    cbn [subst_co_constraint].
    apply An_PropCong.
    + exact (IHa G1 G2 C Phi GSub Heq HctxG HPhi HG HCtxSub HHyp D' HDsub).
    + exact (IHa0 G1 G2 C Phi GSub Heq HctxG HPhi HG HCtxSub HHyp D' HDsub).
    + exact (IHa1 G1 G2 C Phi GSub Heq HctxG HPhi HG HCtxSub HHyp).
    + exact (IHa2 G1 G2 C Phi GSub Heq HctxG HPhi HG HCtxSub HHyp).
  (* An_CPiFst *)
  - intros G D g phi1 phi2 A2 B2 a IHa G1 G2 C Phi GSub Heq HctxG HPhi HG HCtxSub HHyp D' HDsub.
    cbn [subst_co_co subst_co_constraint].
    apply (An_CPiFst (subCo_ctx C GSub G1 ++ subCo_ctx C GSub G2) D' (subst_co_co C GSub g) (subst_co_constraint C GSub phi1) (subst_co_constraint C GSub phi2) (subst_co_tm C GSub A2) (subst_co_tm C GSub B2)).
    exact (IHa G1 G2 C Phi GSub Heq HctxG HPhi HG HCtxSub HHyp D' HDsub).
  (* An_IsoSym *)
  - intros G D g phi2 phi1 a IHa G1 G2 C Phi GSub Heq HctxG HPhi HG HCtxSub HHyp D' HDsub.
    cbn [subst_co_co subst_co_constraint].
    apply An_IsoSym.
    exact (IHa G1 G2 C Phi GSub Heq HctxG HPhi HG HCtxSub HHyp D' HDsub).
  (* An_IsoConv *)
  - intros G D a1 a2 A a1' a2' B g a IHa a0 IHa0 a3 IHa3 e e0 G1 G2 C Phi GSub Heq HctxG HPhi HG HCtxSub HHyp D' HDsub.
    cbn [subst_co_co subst_co_constraint].
    apply An_IsoConv.
    + exact (IHa G1 G2 C Phi GSub Heq HctxG HPhi HG HCtxSub HHyp D' HDsub).
    + exact (IHa0 G1 G2 C Phi GSub Heq HctxG HPhi HG HCtxSub HHyp).
    + exact (IHa3 G1 G2 C Phi GSub Heq HctxG HPhi HG HCtxSub HHyp).
    + rewrite ((proj1 erase_subst_co_tm) a1 C GSub).
      rewrite ((proj1 erase_subst_co_tm) a1' C GSub).
      rewrite e. reflexivity.
    + rewrite ((proj1 erase_subst_co_tm) a2 C GSub).
      rewrite ((proj1 erase_subst_co_tm) a2' C GSub).
      rewrite e0. reflexivity.


  (* An_Assn *)
  - intros G D d a b A a0 IHa Hb i G1 G2 C Phi GSub Heq HctxG HPhi HG HCtxSub HHyp D' HDsub.
    destruct (annctx_uniq_split G G1 C (Co Phi) G2 HctxG Heq) as [HX1 HX2].
    rewrite Heq in Hb.
    destruct (binds_split_any G1 C (Co Phi) G2 d (Co (Eq a b A)) HX1 HX2 Hb) as [[Hdeq Hseq]|[Hne Hb']].
    + subst d. injection Hseq as Hphi.
      assert (HPhiEq : Phi = Eq a b A) by (symmetry; exact Hphi).
      assert (HsubstA : subst_co_tm C GSub a = a).
      { apply (proj1 subst_co_tm_id_fresh_all).
        rewrite HPhiEq in HPhi. cbn [fvx_constraint] in HPhi. notin_split_all. assumption. }
      assert (HsubstB : subst_co_tm C GSub b = b).
      { apply (proj1 subst_co_tm_id_fresh_all).
        rewrite HPhiEq in HPhi. cbn [fvx_constraint] in HPhi. notin_split_all. assumption. }
      rewrite subst_co_co_var_eq.
      rewrite HsubstA, HsubstB.
      exact (HHyp (subCo_ctx C GSub G1 ++ subCo_ctx C GSub G2) D' a b A HPhiEq
                  (ctx_sub_subCo_right C GSub G1 G2) HCtxSub).
    + rewrite (subst_co_co_var_neq C d GSub Hne).
      apply (An_Assn (subCo_ctx C GSub G1 ++ subCo_ctx C GSub G2) D' d (subst_co_tm C GSub a) (subst_co_tm C GSub b) (subst_co_tm C GSub A)).
      * exact HCtxSub.
      * rewrite <- subCo_ctx_app.
        apply (binds_subCo_ctx C GSub (G1++G2) d (Co (Eq a b A)) Hb').
      * exact (HDsub d i Hne).
  (* An_Refl *)
  - intros G D a A a0 IHa G1 G2 C Phi GSub Heq HctxG HPhi HG HCtxSub HHyp D' HDsub.
    cbn [subst_co_co subst_co_tm].
    apply An_Refl with (A := subst_co_tm C GSub A).
    exact (IHa G1 G2 C Phi GSub Heq HctxG HPhi HG HCtxSub HHyp).
  (* An_EraseEq *)
  - intros G D a b g A B a0 IHa a1 IHa1 e a2 IHa2 G1 G2 C Phi GSub Heq HctxG HPhi HG HCtxSub HHyp D' HDsub.
    cbn [subst_co_co subst_co_tm].
    apply An_EraseEq with (A := subst_co_tm C GSub A) (B := subst_co_tm C GSub B).
    + exact (IHa G1 G2 C Phi GSub Heq HctxG HPhi HG HCtxSub HHyp).
    + exact (IHa1 G1 G2 C Phi GSub Heq HctxG HPhi HG HCtxSub HHyp).
    + rewrite ((proj1 erase_subst_co_tm) a C GSub).
      rewrite ((proj1 erase_subst_co_tm) b C GSub).
      rewrite e. reflexivity.
    + exact (IHa2 G1 G2 C Phi GSub Heq HctxG HPhi HG HCtxSub HHyp (dom (subCo_ctx C GSub G1 ++ subCo_ctx C GSub G2))
                   (fun c Hin Hne => in_dom_subCo_ctx' G G1 C (Co Phi) G2 GSub c Heq Hin Hne)).
  (* An_Sym *)
  - intros G D g a b B A g1 a0 IHa0 a1 IHa1 a2 IHa2 a3 IHa3 G1 G2 C Phi GSub Heq HctxG HPhi HG HCtxSub HHyp D' HDsub.
    cbn [subst_co_co subst_co_tm].
    apply An_Sym with (B := subst_co_tm C GSub B) (A := subst_co_tm C GSub A) (g1 := subst_co_co C GSub g1).
    + exact (IHa0 G1 G2 C Phi GSub Heq HctxG HPhi HG HCtxSub HHyp).
    + exact (IHa1 G1 G2 C Phi GSub Heq HctxG HPhi HG HCtxSub HHyp).
    + exact (IHa2 G1 G2 C Phi GSub Heq HctxG HPhi HG HCtxSub HHyp (dom (subCo_ctx C GSub G1 ++ subCo_ctx C GSub G2))
                   (fun c Hin Hne => in_dom_subCo_ctx' G G1 C (Co Phi) G2 GSub c Heq Hin Hne)).
    + exact (IHa3 G1 G2 C Phi GSub Heq HctxG HPhi HG HCtxSub HHyp D' HDsub).
  (* An_Trans *)
  - intros G D g1 g2 a b a1 A A1 g3 a0 IHa0 a2 IHa2 a3 IHa3 a4 IHa4 a5 IHa5 G1 G2 C Phi GSub Heq HctxG HPhi HG HCtxSub HHyp D' HDsub.
    cbn [subst_co_co subst_co_tm].
    apply An_Trans with (a1 := subst_co_tm C GSub a1) (A := subst_co_tm C GSub A) (A1 := subst_co_tm C GSub A1) (g3 := subst_co_co C GSub g3).
    + exact (IHa0 G1 G2 C Phi GSub Heq HctxG HPhi HG HCtxSub HHyp D' HDsub).
    + exact (IHa2 G1 G2 C Phi GSub Heq HctxG HPhi HG HCtxSub HHyp D' HDsub).
    + exact (IHa3 G1 G2 C Phi GSub Heq HctxG HPhi HG HCtxSub HHyp).
    + exact (IHa4 G1 G2 C Phi GSub Heq HctxG HPhi HG HCtxSub HHyp).
    + exact (IHa5 G1 G2 C Phi GSub Heq HctxG HPhi HG HCtxSub HHyp (dom (subCo_ctx C GSub G1 ++ subCo_ctx C GSub G2))
                   (fun c Hin Hne => in_dom_subCo_ctx' G G1 C (Co Phi) G2 GSub c Heq Hin Hne)).


  (* An_Beta *)
  - intros G D a1 a2 B0 B1 a IHa a0 IHa0 e b G1 G2 C Phi GSub Heq HctxG HPhi HG HCtxSub HHyp D' HDsub.
    cbn [subst_co_co subst_co_tm].
    apply An_Beta with (B0 := subst_co_tm C GSub B0) (B1 := subst_co_tm C GSub B1).
    + exact (IHa G1 G2 C Phi GSub Heq HctxG HPhi HG HCtxSub HHyp).
    + exact (IHa0 G1 G2 C Phi GSub Heq HctxG HPhi HG HCtxSub HHyp).
    + rewrite ((proj1 erase_subst_co_tm) B0 C GSub).
      rewrite ((proj1 erase_subst_co_tm) B1 C GSub).
      rewrite e. reflexivity.
    + rewrite ((proj1 erase_subst_co_tm) a1 C GSub).
      rewrite ((proj1 erase_subst_co_tm) a2 C GSub).
      exact b.
  (* An_PiCong *)
  - intros L G D rho g1 g2 A1 B1 A2 B3 B2 a IHa a0 IHa0 e a1 IHa1 a2 IHa2 a3 IHa3 G1 G2 C Phi GSub Heq HctxG HPhi HG HCtxSub HHyp D' HDsub.
    cbn [subst_co_co subst_co_tm].
    apply (An_PiCong (AtomSetImpl.union L (AtomSetImpl.union (dom G) (AtomSetImpl.singleton C)))
              (subCo_ctx C GSub G1 ++ subCo_ctx C GSub G2) D' rho
              (subst_co_co C GSub g1) (subst_co_co C GSub g2)
              (subst_co_tm C GSub A1) (subst_co_tm C GSub B1)
              (subst_co_tm C GSub A2) (subst_co_tm C GSub B3) (subst_co_tm C GSub B2)).
    + exact (IHa G1 G2 C Phi GSub Heq HctxG HPhi HG HCtxSub HHyp D' HDsub).
    + intro y. intro Hy.
      destruct (notin_union3 y L (dom G) (AtomSetImpl.singleton C) Hy) as (HyL & HyDomG & HyX).
      assert (Hne : y <> C) by (symmetry; exact (notin_singleton_1 C y HyX)).
      assert (HtyA1sub : AnnTyping (subCo_ctx C GSub G1 ++ subCo_ctx C GSub G2) (a_Pi rho (subst_co_tm C GSub A1) (subst_co_tm C GSub B1)) a_Star).
      { cbn [subst_co_tm]. exact (IHa1 G1 G2 C Phi GSub Heq HctxG HPhi HG HCtxSub HHyp). }
      assert (HctxM : AnnCtx ((y, Tm A1) :: G)) by exact (An_ConsTm G y A1 HctxG (AnnTyping_pi_dom G rho A1 B1 a1) HyDomG).
      assert (HctxSubM : AnnCtx ((y, Tm (subst_co_tm C GSub A1)) :: (subCo_ctx C GSub G1 ++ subCo_ctx C GSub G2)))
        by exact (An_ConsTm (subCo_ctx C GSub G1 ++ subCo_ctx C GSub G2) y (subst_co_tm C GSub A1) HCtxSub
                     (AnnTyping_pi_dom (subCo_ctx C GSub G1 ++ subCo_ctx C GSub G2) rho (subst_co_tm C GSub A1) (subst_co_tm C GSub B1) HtyA1sub)
                     (notin_dom_subCo_ctx' G G1 C (Co Phi) G2 GSub y Heq HyDomG)).
      assert (Hbody := IHa0 y HyL ((y, Tm A1) :: G1) G2 C Phi GSub
                        (cons_ctx_decomp_co y (Tm A1) G1 C Phi G2 G Heq) HctxM HPhi HG HctxSubM HHyp D' HDsub).
      rewrite (subst_co_open_co_tm_var g2 C GSub y HG) in Hbody.
      rewrite (subst_co_open_tm_var B1 C GSub y HG) in Hbody.
      rewrite (subst_co_open_tm_var B2 C GSub y HG) in Hbody.
      exact Hbody.
    + intro y. intro Hy.
      destruct (notin_union3 y L (dom G) (AtomSetImpl.singleton C) Hy) as (HyL & HyDomG & HyX).
      assert (Hne : y <> C) by (symmetry; exact (notin_singleton_1 C y HyX)).
      assert (Hf := f_equal (subst_co_tm C GSub) (e y HyL)).
      rewrite (subst_co_open_tm_var B3 C GSub y HG) in Hf.
      rewrite (subst_co_open_tm_v B2 C GSub (a_Conv (a_Var_f y) (g_Sym g1)) HG) in Hf.
      rewrite (subst_co_tm_conv_var_sym C GSub y g1 Hne) in Hf.
      exact Hf.
    + exact (IHa1 G1 G2 C Phi GSub Heq HctxG HPhi HG HCtxSub HHyp).
    + exact (IHa2 G1 G2 C Phi GSub Heq HctxG HPhi HG HCtxSub HHyp).
    + exact (IHa3 G1 G2 C Phi GSub Heq HctxG HPhi HG HCtxSub HHyp).
  (* An_AbsCong *)
  - intros L G D rho g1 g2 A1 b1 A2 b3 b2 B a IHa a0 IHa0 e a1 IHa1 a2 IHa2 r1 r2 a3 IHa3 G1 G2 C Phi GSub Heq HctxG HPhi HG HCtxSub HHyp D' HDsub.
    cbn [subst_co_co subst_co_tm].
    apply (An_AbsCong (AtomSetImpl.union L (AtomSetImpl.union (dom G) (AtomSetImpl.singleton C)))
              (subCo_ctx C GSub G1 ++ subCo_ctx C GSub G2) D' rho
              (subst_co_co C GSub g1) (subst_co_co C GSub g2)
              (subst_co_tm C GSub A1) (subst_co_tm C GSub b1)
              (subst_co_tm C GSub A2) (subst_co_tm C GSub b3) (subst_co_tm C GSub b2) (subst_co_tm C GSub B)).
    + exact (IHa G1 G2 C Phi GSub Heq HctxG HPhi HG HCtxSub HHyp D' HDsub).
    + intro y. intro Hy.
      destruct (notin_union3 y L (dom G) (AtomSetImpl.singleton C) Hy) as (HyL & HyDomG & HyX).
      assert (Hne : y <> C) by (symmetry; exact (notin_singleton_1 C y HyX)).
      assert (HctxM : AnnCtx ((y, Tm A1) :: G)) by exact (An_ConsTm G y A1 HctxG a1 HyDomG).
      assert (HctxSubM : AnnCtx ((y, Tm (subst_co_tm C GSub A1)) :: (subCo_ctx C GSub G1 ++ subCo_ctx C GSub G2)))
        by exact (An_ConsTm (subCo_ctx C GSub G1 ++ subCo_ctx C GSub G2) y (subst_co_tm C GSub A1) HCtxSub
                     (IHa1 G1 G2 C Phi GSub Heq HctxG HPhi HG HCtxSub HHyp)
                     (notin_dom_subCo_ctx' G G1 C (Co Phi) G2 GSub y Heq HyDomG)).
      assert (Hbody := IHa0 y HyL ((y, Tm A1) :: G1) G2 C Phi GSub
                        (cons_ctx_decomp_co y (Tm A1) G1 C Phi G2 G Heq) HctxM HPhi HG HctxSubM HHyp D' HDsub).
      rewrite (subst_co_open_co_tm_var g2 C GSub y HG) in Hbody.
      rewrite (subst_co_open_tm_var b1 C GSub y HG) in Hbody.
      rewrite (subst_co_open_tm_var b2 C GSub y HG) in Hbody.
      exact Hbody.
    + intro y. intro Hy.
      destruct (notin_union3 y L (dom G) (AtomSetImpl.singleton C) Hy) as (HyL & HyDomG & HyX).
      assert (Hne : y <> C) by (symmetry; exact (notin_singleton_1 C y HyX)).
      assert (Hf := f_equal (subst_co_tm C GSub) (e y HyL)).
      rewrite (subst_co_open_tm_var b3 C GSub y HG) in Hf.
      rewrite (subst_co_open_tm_v b2 C GSub (a_Conv (a_Var_f y) (g_Sym g1)) HG) in Hf.
      rewrite (subst_co_tm_conv_var_sym C GSub y g1 Hne) in Hf.
      exact Hf.
    + exact (IHa1 G1 G2 C Phi GSub Heq HctxG HPhi HG HCtxSub HHyp).
    + exact (IHa2 G1 G2 C Phi GSub Heq HctxG HPhi HG HCtxSub HHyp).
    + intro y. intro Hy.
      destruct (notin_union3 y L (dom G) (AtomSetImpl.singleton C) Hy) as (HyL & HyDomG & HyX).
      assert (Hne : y <> C) by (symmetry; exact (notin_singleton_1 C y HyX)).
      destruct rho.
      * apply Rho_Rel. exact I.
      * apply Rho_IrrRel.
        rewrite (erase_open_subst_co_tm_var b1 C GSub y HG).
        exact (RhoCheck_irrel_inv y (erase_tm (open_tm_wrt_tm b1 (a_Var_f y))) (r1 y HyL)).
    + intro y. intro Hy.
      destruct (notin_union3 y L (dom G) (AtomSetImpl.singleton C) Hy) as (HyL & HyDomG & HyX).
      assert (Hne : y <> C) by (symmetry; exact (notin_singleton_1 C y HyX)).
      destruct rho.
      * apply Rho_Rel. exact I.
      * apply Rho_IrrRel.
        rewrite (erase_open_subst_co_tm_var b3 C GSub y HG).
        exact (RhoCheck_irrel_inv y (erase_tm (open_tm_wrt_tm b3 (a_Var_f y))) (r2 y HyL)).
    + exact (IHa3 G1 G2 C Phi GSub Heq HctxG HPhi HG HCtxSub HHyp).
  (* An_AppCong *)
  - intros G D g1 rho g2 a1 a2 b1 b2 A B g3 a IHa a0 IHa0 a1' IHa1 a2' IHa2 a3 IHa3 G1 G2 C Phi GSub Heq HctxG HPhi HG HCtxSub HHyp D' HDsub.
    cbn [subst_co_co subst_co_tm].
    apply (An_AppCong (subCo_ctx C GSub G1 ++ subCo_ctx C GSub G2) D'
              (subst_co_co C GSub g1) rho (subst_co_co C GSub g2)
              (subst_co_tm C GSub a1) (subst_co_tm C GSub a2)
              (subst_co_tm C GSub b1) (subst_co_tm C GSub b2)
              (subst_co_tm C GSub A) (subst_co_tm C GSub B) (subst_co_co C GSub g3)).
    + exact (IHa G1 G2 C Phi GSub Heq HctxG HPhi HG HCtxSub HHyp D' HDsub).
    + exact (IHa0 G1 G2 C Phi GSub Heq HctxG HPhi HG HCtxSub HHyp D' HDsub).
    + exact (IHa1 G1 G2 C Phi GSub Heq HctxG HPhi HG HCtxSub HHyp).
    + exact (IHa2 G1 G2 C Phi GSub Heq HctxG HPhi HG HCtxSub HHyp).
    + exact (IHa3 G1 G2 C Phi GSub Heq HctxG HPhi HG HCtxSub HHyp (dom (subCo_ctx C GSub G1 ++ subCo_ctx C GSub G2))
                   (fun c Hin Hne => in_dom_subCo_ctx' G G1 C (Co Phi) G2 GSub c Heq Hin Hne)).
  (* An_PiFst *)
  - intros G D g A1 A2 rho B1 B2 a IHa G1 G2 C Phi GSub Heq HctxG HPhi HG HCtxSub HHyp D' HDsub.
    cbn [subst_co_co subst_co_tm].
    apply An_PiFst with (rho := rho) (B1 := subst_co_tm C GSub B1) (B2 := subst_co_tm C GSub B2).
    exact (IHa G1 G2 C Phi GSub Heq HctxG HPhi HG HCtxSub HHyp D' HDsub).


  (* An_PiSnd *)
  - intros G D g1 g2 B1 a1 B2 a2 rho A1 A2 a IHa a0 IHa0 a1' IHa1 a2' IHa2 G1 G2 C Phi GSub Heq HctxG HPhi HG HCtxSub HHyp D' HDsub.
    cbn [subst_co_co subst_co_tm].
    rewrite (subst_co_open_tm_v B1 C GSub a1 HG).
    rewrite (subst_co_open_tm_v B2 C GSub a2 HG).
    apply (An_PiSnd (subCo_ctx C GSub G1 ++ subCo_ctx C GSub G2) D'
              (subst_co_co C GSub g1) (subst_co_co C GSub g2)
              (subst_co_tm C GSub B1) (subst_co_tm C GSub a1)
              (subst_co_tm C GSub B2) (subst_co_tm C GSub a2) rho
              (subst_co_tm C GSub A1) (subst_co_tm C GSub A2)).
    + exact (IHa G1 G2 C Phi GSub Heq HctxG HPhi HG HCtxSub HHyp D' HDsub).
    + exact (IHa0 G1 G2 C Phi GSub Heq HctxG HPhi HG HCtxSub HHyp D' HDsub).
    + exact (IHa1 G1 G2 C Phi GSub Heq HctxG HPhi HG HCtxSub HHyp).
    + exact (IHa2 G1 G2 C Phi GSub Heq HctxG HPhi HG HCtxSub HHyp).
  (* An_CPiCong *)
  - intros L G D g1 g3 phi1 B1 phi2 B3 B2 a IHa a0 IHa0 e a1 IHa1 a2 IHa2 a3 IHa3 G1 G2 C Phi GSub Heq HctxG HPhi HG HCtxSub HHyp D' HDsub.
    cbn [subst_co_co subst_co_constraint subst_co_tm].
    apply (An_CPiCong (AtomSetImpl.union L (AtomSetImpl.union (dom G) (AtomSetImpl.singleton C)))
              (subCo_ctx C GSub G1 ++ subCo_ctx C GSub G2) D'
              (subst_co_co C GSub g1) (subst_co_co C GSub g3)
              (subst_co_constraint C GSub phi1) (subst_co_tm C GSub B1)
              (subst_co_constraint C GSub phi2) (subst_co_tm C GSub B3) (subst_co_tm C GSub B2)).
    + exact (IHa G1 G2 C Phi GSub Heq HctxG HPhi HG HCtxSub HHyp D' HDsub).
    + intro c. intro Hc.
      destruct (notin_union3 c L (dom G) (AtomSetImpl.singleton C) Hc) as (HcL & HcDomG & HcX).
      assert (Hcne : c <> C) by (symmetry; exact (notin_singleton_1 C c HcX)).
      assert (Hty1 : AnnTyping (subCo_ctx C GSub G1 ++ subCo_ctx C GSub G2) (a_CPi (subst_co_constraint C GSub phi1) (subst_co_tm C GSub B1)) a_Star).
      { cbn [subst_co_tm]. exact (IHa1 G1 G2 C Phi GSub Heq HctxG HPhi HG HCtxSub HHyp). }
      assert (HctxM : AnnCtx ((c, Co phi1) :: G)) by exact (An_ConsCo G c phi1 HctxG (AnnTyping_cpi_wff G phi1 B1 a1) HcDomG).
      assert (HctxSubM : AnnCtx ((c, Co (subst_co_constraint C GSub phi1)) :: (subCo_ctx C GSub G1 ++ subCo_ctx C GSub G2)))
        by exact (An_ConsCo (subCo_ctx C GSub G1 ++ subCo_ctx C GSub G2) c (subst_co_constraint C GSub phi1) HCtxSub
                     (AnnTyping_cpi_wff (subCo_ctx C GSub G1 ++ subCo_ctx C GSub G2) (subst_co_constraint C GSub phi1) (subst_co_tm C GSub B1) Hty1)
                     (notin_dom_subCo_ctx' G G1 C (Co Phi) G2 GSub c Heq HcDomG)).
      assert (Hbody := IHa0 c HcL ((c, Co phi1) :: G1) G2 C Phi GSub
                        (cons_ctx_decomp_co c (Co phi1) G1 C Phi G2 G Heq) HctxM HPhi HG HctxSubM HHyp D' HDsub).
      rewrite (subst_co_open_co_co_var g3 C GSub c HG) in Hbody.
      rewrite (subst_co_co_var_neq C c GSub Hcne) in Hbody.
      rewrite (subst_co_open_tm_co_var B1 C GSub c HG) in Hbody.
      rewrite (subst_co_open_tm_co_var B2 C GSub c HG) in Hbody.
      rewrite (subst_co_co_var_neq C c GSub Hcne) in Hbody.
      exact Hbody.
    + intro c. intro Hc.
      destruct (notin_union3 c L (dom G) (AtomSetImpl.singleton C) Hc) as (HcL & HcDomG & HcX).
      assert (Hcne : c <> C) by (symmetry; exact (notin_singleton_1 C c HcX)).
      assert (Hf := f_equal (subst_co_tm C GSub) (e c HcL)).
      rewrite (subst_co_open_tm_co_var B3 C GSub c HG) in Hf.
      rewrite (subst_co_open_tm_co_h B2 C GSub (g_Cast (g_Var_f c) (g_Sym g1)) HG) in Hf.
      rewrite (subst_co_co_var_neq C c GSub Hcne) in Hf.
      rewrite (subst_co_co_cast_var_sym C GSub c g1 Hcne) in Hf.
      exact Hf.
    + exact (IHa1 G1 G2 C Phi GSub Heq HctxG HPhi HG HCtxSub HHyp).
    + exact (IHa2 G1 G2 C Phi GSub Heq HctxG HPhi HG HCtxSub HHyp).
    + exact (IHa3 G1 G2 C Phi GSub Heq HctxG HPhi HG HCtxSub HHyp).
  (* An_CAbsCong *)
  - intros L G D g1 g3 g4 phi1 a1 phi2 a3 a2 B1 B B2 a IHa a0 IHa0 e p1 IHp1 p2 IHp2 p3 IHp3 p4 IHp4 G1 G2 C Phi GSub Heq HctxG HPhi HG HCtxSub HHyp D' HDsub.
    cbn [subst_co_co subst_co_constraint subst_co_tm].
    apply (An_CAbsCong (AtomSetImpl.union L (AtomSetImpl.union (dom G) (AtomSetImpl.singleton C)))
              (subCo_ctx C GSub G1 ++ subCo_ctx C GSub G2) D'
              (subst_co_co C GSub g1) (subst_co_co C GSub g3) (subst_co_co C GSub g4)
              (subst_co_constraint C GSub phi1) (subst_co_tm C GSub a1)
              (subst_co_constraint C GSub phi2) (subst_co_tm C GSub a3) (subst_co_tm C GSub a2)
              (subst_co_tm C GSub B1) (subst_co_tm C GSub B) (subst_co_tm C GSub B2)).
    + exact (IHa G1 G2 C Phi GSub Heq HctxG HPhi HG HCtxSub HHyp D' HDsub).
    + intro c. intro Hc.
      destruct (notin_union3 c L (dom G) (AtomSetImpl.singleton C) Hc) as (HcL & HcDomG & HcX).
      assert (Hcne : c <> C) by (symmetry; exact (notin_singleton_1 C c HcX)).
      assert (Hty1 : AnnTyping (subCo_ctx C GSub G1 ++ subCo_ctx C GSub G2) (a_CAbs (subst_co_constraint C GSub phi1) (subst_co_tm C GSub a1)) (a_CPi (subst_co_constraint C GSub phi1) (subst_co_tm C GSub B1))).
      { cbn [subst_co_tm]. exact (IHp1 G1 G2 C Phi GSub Heq HctxG HPhi HG HCtxSub HHyp). }
      assert (HctxM : AnnCtx ((c, Co phi1) :: G)) by exact (An_ConsCo G c phi1 HctxG (AnnTyping_cabs_wff G phi1 a1 (a_CPi phi1 B1) p1) HcDomG).
      assert (HctxSubM : AnnCtx ((c, Co (subst_co_constraint C GSub phi1)) :: (subCo_ctx C GSub G1 ++ subCo_ctx C GSub G2)))
        by exact (An_ConsCo (subCo_ctx C GSub G1 ++ subCo_ctx C GSub G2) c (subst_co_constraint C GSub phi1) HCtxSub
                     (AnnTyping_cabs_wff (subCo_ctx C GSub G1 ++ subCo_ctx C GSub G2) (subst_co_constraint C GSub phi1) (subst_co_tm C GSub a1) (a_CPi (subst_co_constraint C GSub phi1) (subst_co_tm C GSub B1)) Hty1)
                     (notin_dom_subCo_ctx' G G1 C (Co Phi) G2 GSub c Heq HcDomG)).
      assert (Hbody := IHa0 c HcL ((c, Co phi1) :: G1) G2 C Phi GSub
                        (cons_ctx_decomp_co c (Co phi1) G1 C Phi G2 G Heq) HctxM HPhi HG HctxSubM HHyp D' HDsub).
      rewrite (subst_co_open_co_co_var g3 C GSub c HG) in Hbody.
      rewrite (subst_co_co_var_neq C c GSub Hcne) in Hbody.
      rewrite (subst_co_open_tm_co_var a1 C GSub c HG) in Hbody.
      rewrite (subst_co_open_tm_co_var a2 C GSub c HG) in Hbody.
      rewrite (subst_co_co_var_neq C c GSub Hcne) in Hbody.
      exact Hbody.
    + intro c. intro Hc.
      destruct (notin_union3 c L (dom G) (AtomSetImpl.singleton C) Hc) as (HcL & HcDomG & HcX).
      assert (Hcne : c <> C) by (symmetry; exact (notin_singleton_1 C c HcX)).
      assert (Hf := f_equal (subst_co_tm C GSub) (e c HcL)).
      rewrite (subst_co_open_tm_co_var a3 C GSub c HG) in Hf.
      rewrite (subst_co_open_tm_co_h a2 C GSub (g_Cast (g_Var_f c) (g_Sym g1)) HG) in Hf.
      rewrite (subst_co_co_var_neq C c GSub Hcne) in Hf.
      rewrite (subst_co_co_cast_var_sym C GSub c g1 Hcne) in Hf.
      exact Hf.
    + exact (IHp1 G1 G2 C Phi GSub Heq HctxG HPhi HG HCtxSub HHyp).
    + exact (IHp2 G1 G2 C Phi GSub Heq HctxG HPhi HG HCtxSub HHyp).
    + exact (IHp3 G1 G2 C Phi GSub Heq HctxG HPhi HG HCtxSub HHyp).
    + exact (IHp4 G1 G2 C Phi GSub Heq HctxG HPhi HG HCtxSub HHyp (dom (subCo_ctx C GSub G1 ++ subCo_ctx C GSub G2))
                   (fun c Hin Hne => in_dom_subCo_ctx' G G1 C (Co Phi) G2 GSub c Heq Hin Hne)).
  (* An_CAppCong *)
  - intros G D g1 g2 g3 a1 b1 a2 b2 a3 b3 A B g4 a IHa a0 IHa0 a1' IHa1 a2' IHa2 a3' IHa3 a4 IHa4 G1 G2 C Phi GSub Heq HctxG HPhi HG HCtxSub HHyp D' HDsub.
    cbn [subst_co_co subst_co_tm].
    apply (An_CAppCong (subCo_ctx C GSub G1 ++ subCo_ctx C GSub G2) D'
              (subst_co_co C GSub g1) (subst_co_co C GSub g2) (subst_co_co C GSub g3)
              (subst_co_tm C GSub a1) (subst_co_tm C GSub b1)
              (subst_co_tm C GSub a2) (subst_co_tm C GSub b2)
              (subst_co_tm C GSub a3) (subst_co_tm C GSub b3)
              (subst_co_tm C GSub A) (subst_co_tm C GSub B) (subst_co_co C GSub g4)).
    + exact (IHa G1 G2 C Phi GSub Heq HctxG HPhi HG HCtxSub HHyp D' HDsub).
    + exact (IHa0 G1 G2 C Phi GSub Heq HctxG HPhi HG HCtxSub HHyp (dom (subCo_ctx C GSub G1 ++ subCo_ctx C GSub G2))
                   (fun c Hin Hne => in_dom_subCo_ctx' G G1 C (Co Phi) G2 GSub c Heq Hin Hne)).
    + exact (IHa1 G1 G2 C Phi GSub Heq HctxG HPhi HG HCtxSub HHyp (dom (subCo_ctx C GSub G1 ++ subCo_ctx C GSub G2))
                   (fun c Hin Hne => in_dom_subCo_ctx' G G1 C (Co Phi) G2 GSub c Heq Hin Hne)).
    + exact (IHa2 G1 G2 C Phi GSub Heq HctxG HPhi HG HCtxSub HHyp).
    + exact (IHa3 G1 G2 C Phi GSub Heq HctxG HPhi HG HCtxSub HHyp).
    + exact (IHa4 G1 G2 C Phi GSub Heq HctxG HPhi HG HCtxSub HHyp (dom (subCo_ctx C GSub G1 ++ subCo_ctx C GSub G2))
                   (fun c Hin Hne => in_dom_subCo_ctx' G G1 C (Co Phi) G2 GSub c Heq Hin Hne)).
  (* An_CPiSnd *)
  - intros G D g1 g2 g3 B1 B2 a a' A b b' B a0 IHa0 a1 IHa1 a2 IHa2 G1 G2 C Phi GSub Heq HctxG HPhi HG HCtxSub HHyp D' HDsub.
    cbn [subst_co_co subst_co_tm].
    rewrite (subst_co_open_tm_co_h B1 C GSub g2 HG).
    rewrite (subst_co_open_tm_co_h B2 C GSub g3 HG).
    apply (An_CPiSnd (subCo_ctx C GSub G1 ++ subCo_ctx C GSub G2) D'
              (subst_co_co C GSub g1) (subst_co_co C GSub g2) (subst_co_co C GSub g3)
              (subst_co_tm C GSub B1) (subst_co_tm C GSub B2)
              (subst_co_tm C GSub a) (subst_co_tm C GSub a') (subst_co_tm C GSub A)
              (subst_co_tm C GSub b) (subst_co_tm C GSub b') (subst_co_tm C GSub B)).
    + exact (IHa0 G1 G2 C Phi GSub Heq HctxG HPhi HG HCtxSub HHyp D' HDsub).
    + exact (IHa1 G1 G2 C Phi GSub Heq HctxG HPhi HG HCtxSub HHyp (dom (subCo_ctx C GSub G1 ++ subCo_ctx C GSub G2))
                   (fun c Hin Hne => in_dom_subCo_ctx' G G1 C (Co Phi) G2 GSub c Heq Hin Hne)).
    + exact (IHa2 G1 G2 C Phi GSub Heq HctxG HPhi HG HCtxSub HHyp (dom (subCo_ctx C GSub G1 ++ subCo_ctx C GSub G2))
                   (fun c Hin Hne => in_dom_subCo_ctx' G G1 C (Co Phi) G2 GSub c Heq Hin Hne)).


  (* An_Cast *)
  - intros G D g1 g2 b b' a a' A B a0 IHa0 a1 IHa1 G1 G2 C Phi GSub Heq HctxG HPhi HG HCtxSub HHyp D' HDsub.
    cbn [subst_co_co subst_co_tm].
    apply (An_Cast (subCo_ctx C GSub G1 ++ subCo_ctx C GSub G2) D'
              (subst_co_co C GSub g1) (subst_co_co C GSub g2)
              (subst_co_tm C GSub b) (subst_co_tm C GSub b')
              (subst_co_tm C GSub a) (subst_co_tm C GSub a')
              (subst_co_tm C GSub A) (subst_co_tm C GSub B)).
    + exact (IHa0 G1 G2 C Phi GSub Heq HctxG HPhi HG HCtxSub HHyp D' HDsub).
    + exact (IHa1 G1 G2 C Phi GSub Heq HctxG HPhi HG HCtxSub HHyp D' HDsub).
  (* An_IsoSnd *)
  - intros G D g A B a a' b b' a0 IHa G1 G2 C Phi GSub Heq HctxG HPhi HG HCtxSub HHyp D' HDsub.
    cbn [subst_co_co subst_co_tm].
    apply (An_IsoSnd (subCo_ctx C GSub G1 ++ subCo_ctx C GSub G2) D'
              (subst_co_co C GSub g) (subst_co_tm C GSub A) (subst_co_tm C GSub B)
              (subst_co_tm C GSub a) (subst_co_tm C GSub a')
              (subst_co_tm C GSub b) (subst_co_tm C GSub b')).
    exact (IHa G1 G2 C Phi GSub Heq HctxG HPhi HG HCtxSub HHyp D' HDsub).
  (* An_Empty *)
  - intros. exact I.
  (* An_ConsTm *)
  - intros. exact I.
  (* An_ConsCo *)
  - intros. exact I.
  (* An_Sig_Empty *)
  - intros. exact I.
  (* An_Sig_Cons *)
  - intros. exact I.
Qed.

Lemma AnnTyping_subst_co_all :
  (forall G t T (H:AnnTyping G t T), forall G1 G2 C Phi GSub,
    G = G1 ++ (C, Co Phi) :: nil ++ G2 ->
    C `notin` fvx_constraint Phi ->
    lc_co GSub ->
    AnnCtx (subCo_ctx C GSub G1 ++ subCo_ctx C GSub G2) ->
    CoRemovedHyp C G2 Phi GSub ->
    AnnTyping (subCo_ctx C GSub G1 ++ subCo_ctx C GSub G2)
              (subst_co_tm C GSub t) (subst_co_tm C GSub T)) /\
  (forall G p (H:AnnPropWff G p), forall G1 G2 C Phi GSub,
    G = G1 ++ (C, Co Phi) :: nil ++ G2 ->
    C `notin` fvx_constraint Phi ->
    lc_co GSub ->
    AnnCtx (subCo_ctx C GSub G1 ++ subCo_ctx C GSub G2) ->
    CoRemovedHyp C G2 Phi GSub ->
    AnnPropWff (subCo_ctx C GSub G1 ++ subCo_ctx C GSub G2)
               (subst_co_constraint C GSub p)) /\
  (forall G D g p q (H:AnnIso G D g p q), forall G1 G2 C Phi GSub,
    G = G1 ++ (C, Co Phi) :: nil ++ G2 ->
    C `notin` fvx_constraint Phi ->
    lc_co GSub ->
    AnnCtx (subCo_ctx C GSub G1 ++ subCo_ctx C GSub G2) ->
    CoRemovedHyp C G2 Phi GSub ->
    forall D', (forall d, d `in` D -> d <> C -> d `in` D') ->
    AnnIso (subCo_ctx C GSub G1 ++ subCo_ctx C GSub G2) D'
           (subst_co_co C GSub g) (subst_co_constraint C GSub p) (subst_co_constraint C GSub q)) /\
  (forall G D g a b (H:AnnDefEq G D g a b), forall G1 G2 C Phi GSub,
    G = G1 ++ (C, Co Phi) :: nil ++ G2 ->
    C `notin` fvx_constraint Phi ->
    lc_co GSub ->
    AnnCtx (subCo_ctx C GSub G1 ++ subCo_ctx C GSub G2) ->
    CoRemovedHyp C G2 Phi GSub ->
    forall D', (forall d, d `in` D -> d <> C -> d `in` D') ->
    AnnDefEq (subCo_ctx C GSub G1 ++ subCo_ctx C GSub G2) D'
             (subst_co_co C GSub g) (subst_co_tm C GSub a) (subst_co_tm C GSub b)).
Proof.
  destruct Main_co_aux as [H1 [H2 [H3 [H4 _]]]].
  repeat split.
  - intros G t T H G1 G2 C Phi GSub Heq HPhi HG HCtxSub HHyp.
    exact (H1 G t T H G1 G2 C Phi GSub Heq (AnnTyping_AnnCtx G t T H) HPhi HG HCtxSub HHyp).
  - intros G p H G1 G2 C Phi GSub Heq HPhi HG HCtxSub HHyp.
    exact (H2 G p H G1 G2 C Phi GSub Heq (AnnPropWff_AnnCtx G p H) HPhi HG HCtxSub HHyp).
  - intros G D g p q H G1 G2 C Phi GSub Heq HPhi HG HCtxSub HHyp D' HDsub.
    exact (H3 G D g p q H G1 G2 C Phi GSub Heq (AnnIso_AnnCtx G D g p q H) HPhi HG HCtxSub HHyp D' HDsub).
  - intros G D g a b H G1 G2 C Phi GSub Heq HPhi HG HCtxSub HHyp D' HDsub.
    exact (H4 G D g a b H G1 G2 C Phi GSub Heq (AnnDefEq_AnnCtx G D g a b H) HPhi HG HCtxSub HHyp D' HDsub).
Qed.

(* Dom-only removed-binding hypothesis for the typing/PropWff theorem. *)
Definition CoRemovedHypDom (C:covar) (G2:context) (Phi:constraint) (GSub:co) : Prop :=
  forall (G':context) (a b A:tm), Phi = Eq a b A ->
    ctx_sub (subCo_ctx C GSub G2) G' -> AnnCtx G' ->
    AnnDefEq G' (dom G') GSub a b.

Lemma ctx_sub_cons_r : forall (G G':context) (x:atom) s,
  ctx_sub G G' -> ctx_sub G ((x,s)::G').
Proof.
  intros G G' x s H y t Hb.
  apply binds_cons_iff. right. apply H. exact Hb.
Qed.

Definition QTd (G:context) (t T:tm) (H:AnnTyping G t T) : Prop :=
  forall (G1 G2:context) (C:covar) (Phi:constraint) (GSub:co),
    G = G1 ++ (C, Co Phi) :: nil ++ G2 ->
    AnnCtx G ->
    C `notin` fvx_constraint Phi ->
    lc_co GSub ->
    AnnCtx (subCo_ctx C GSub G1 ++ subCo_ctx C GSub G2) ->
    CoRemovedHypDom C G2 Phi GSub ->
    AnnTyping (subCo_ctx C GSub G1 ++ subCo_ctx C GSub G2)
              (subst_co_tm C GSub t) (subst_co_tm C GSub T).

Definition QWd (G:context) (p:constraint) (H:AnnPropWff G p) : Prop :=
  forall (G1 G2:context) (C:covar) (Phi:constraint) (GSub:co),
    G = G1 ++ (C, Co Phi) :: nil ++ G2 ->
    AnnCtx G ->
    C `notin` fvx_constraint Phi ->
    lc_co GSub ->
    AnnCtx (subCo_ctx C GSub G1 ++ subCo_ctx C GSub G2) ->
    CoRemovedHypDom C G2 Phi GSub ->
    AnnPropWff (subCo_ctx C GSub G1 ++ subCo_ctx C GSub G2) (subst_co_constraint C GSub p).

Definition QId (G:context) (D:available_props) (g:co) (p q:constraint) (H:AnnIso G D g p q) : Prop :=
  forall (G1 G2:context) (C:covar) (Phi:constraint) (GSub:co),
    G = G1 ++ (C, Co Phi) :: nil ++ G2 ->
    AnnCtx G ->
    C `notin` fvx_constraint Phi ->
    lc_co GSub ->
    AnnCtx (subCo_ctx C GSub G1 ++ subCo_ctx C GSub G2) ->
    CoRemovedHypDom C G2 Phi GSub ->
    forall (S0:context) (D0:available_props),
    D0 = dom S0 ->
    ctx_sub S0 (subCo_ctx C GSub G1 ++ subCo_ctx C GSub G2) ->
    AnnCtx S0 ->
    ctx_sub (subCo_ctx C GSub G2) S0 ->
    (forall d, d `in` D -> d <> C -> d `in` D0) ->
    AnnIso (subCo_ctx C GSub G1 ++ subCo_ctx C GSub G2) D0
           (subst_co_co C GSub g) (subst_co_constraint C GSub p) (subst_co_constraint C GSub q).

Definition QEd (G:context) (D:available_props) (g:co) (a b:tm) (H:AnnDefEq G D g a b) : Prop :=
  forall (G1 G2:context) (C:covar) (Phi:constraint) (GSub:co),
    G = G1 ++ (C, Co Phi) :: nil ++ G2 ->
    AnnCtx G ->
    C `notin` fvx_constraint Phi ->
    lc_co GSub ->
    AnnCtx (subCo_ctx C GSub G1 ++ subCo_ctx C GSub G2) ->
    CoRemovedHypDom C G2 Phi GSub ->
    forall (S0:context) (D0:available_props),
    D0 = dom S0 ->
    ctx_sub S0 (subCo_ctx C GSub G1 ++ subCo_ctx C GSub G2) ->
    AnnCtx S0 ->
    ctx_sub (subCo_ctx C GSub G2) S0 ->
    (forall d, d `in` D -> d <> C -> d `in` D0) ->
    AnnDefEq (subCo_ctx C GSub G1 ++ subCo_ctx C GSub G2) D0
             (subst_co_co C GSub g) (subst_co_tm C GSub a) (subst_co_tm C GSub b).

Lemma Main_co_dom_aux :
  (forall G t T (H:AnnTyping G t T), QTd G t T H) /\
  (forall G p (H:AnnPropWff G p), QWd G p H) /\
  (forall G D g p q (H:AnnIso G D g p q), QId G D g p q H) /\
  (forall G D g a b (H:AnnDefEq G D g a b), QEd G D g a b H) /\
  (forall G, AnnCtx G -> True) /\
  (forall S, AnnSig S -> True).
Proof.
  apply (AnnTyping_comb QTd QWd QId QEd (fun _ _ => True) (fun _ _ => True)).
  (* An_Star *)
  - intros G a IHa G1 G2 C Phi GSub Heq HctxG HPhi HG HCtxSub HHyp.
    cbn [subst_co_tm]. apply An_Star. exact HCtxSub.
  (* An_Var *)
  - intros G x A a IHa b G1 G2 C Phi GSub Heq HctxG HPhi HG HCtxSub HHyp.
    destruct (annctx_uniq_split G G1 C (Co Phi) G2 HctxG Heq) as [HX1 HX2].
    rewrite Heq in b.
    destruct (binds_split_any G1 C (Co Phi) G2 x (Tm A) HX1 HX2 b) as [[Hxeq HAeq]|[Hne Hb]].
    + subst x. discriminate HAeq.
    + apply An_Var.
      * exact HCtxSub.
      * rewrite <- subCo_ctx_app.
        apply (binds_subCo_ctx C GSub (G1++G2) x (Tm A) Hb).
  (* An_Pi *)
  - intros L G rho A B a IHa a0 IHA0 G1 G2 C Phi GSub Heq HctxG HPhi HG HCtxSub HHyp.
    apply An_Pi with (L := AtomSetImpl.union L (AtomSetImpl.union (dom G) (AtomSetImpl.singleton C))).
    + intro y. intro Hy.
      destruct (notin_union3 y L (dom G) (AtomSetImpl.singleton C) Hy) as (HyL & HyDomG & HyX).
      assert (Hne : y <> C) by (symmetry; exact (notin_singleton_1 C y HyX)).
      assert (HctxM : AnnCtx ((y, Tm A) :: G)) by exact (An_ConsTm G y A HctxG a0 HyDomG).
      assert (HctxSubM : AnnCtx ((y, Tm (subst_co_tm C GSub A)) :: (subCo_ctx C GSub G1 ++ subCo_ctx C GSub G2)))
        by exact (An_ConsTm (subCo_ctx C GSub G1 ++ subCo_ctx C GSub G2) y (subst_co_tm C GSub A) HCtxSub
                     (IHA0 G1 G2 C Phi GSub Heq HctxG HPhi HG HCtxSub HHyp)
                     (notin_dom_subCo_ctx' G G1 C (Co Phi) G2 GSub y Heq HyDomG)).
      assert (Hbody := IHa y HyL ((y, Tm A) :: G1) G2 C Phi GSub
                        (cons_ctx_decomp_co y (Tm A) G1 C Phi G2 G Heq) HctxM HPhi HG HctxSubM HHyp).
      rewrite (subst_co_open_tm_var B C GSub y HG) in Hbody.
      exact Hbody.
    + exact (IHA0 G1 G2 C Phi GSub Heq HctxG HPhi HG HCtxSub HHyp).
  (* An_Abs *)
  - intros L G rho A a B a0 IHA0 a1 IHa r G1 G2 C Phi GSub Heq HctxG HPhi HG HCtxSub HHyp.
    apply An_Abs with (L := AtomSetImpl.union L (AtomSetImpl.union (dom G) (AtomSetImpl.singleton C))).
    + exact (IHA0 G1 G2 C Phi GSub Heq HctxG HPhi HG HCtxSub HHyp).
    + intro y. intro Hy.
      destruct (notin_union3 y L (dom G) (AtomSetImpl.singleton C) Hy) as (HyL & HyDomG & HyX).
      assert (Hne : y <> C) by (symmetry; exact (notin_singleton_1 C y HyX)).
      assert (HctxM : AnnCtx ((y, Tm A) :: G)) by exact (An_ConsTm G y A HctxG a0 HyDomG).
      assert (HctxSubM : AnnCtx ((y, Tm (subst_co_tm C GSub A)) :: (subCo_ctx C GSub G1 ++ subCo_ctx C GSub G2)))
        by exact (An_ConsTm (subCo_ctx C GSub G1 ++ subCo_ctx C GSub G2) y (subst_co_tm C GSub A) HCtxSub
                     (IHA0 G1 G2 C Phi GSub Heq HctxG HPhi HG HCtxSub HHyp)
                     (notin_dom_subCo_ctx' G G1 C (Co Phi) G2 GSub y Heq HyDomG)).
      assert (Hbody := IHa y HyL ((y, Tm A) :: G1) G2 C Phi GSub
                        (cons_ctx_decomp_co y (Tm A) G1 C Phi G2 G Heq) HctxM HPhi HG HctxSubM HHyp).
      rewrite (subst_co_open_tm_var a C GSub y HG) in Hbody.
      rewrite (subst_co_open_tm_var B C GSub y HG) in Hbody.
      exact Hbody.
    + intro y. intro Hy.
      destruct (notin_union3 y L (dom G) (AtomSetImpl.singleton C) Hy) as (HyL & HyDomG & HyX).
      assert (Hne : y <> C) by (symmetry; exact (notin_singleton_1 C y HyX)).
      destruct rho.
      * apply Rho_Rel. exact I.
      * apply Rho_IrrRel.
        fold subst_co_tm.
        rewrite (erase_open_subst_co_tm_var a C GSub y HG).
        exact (RhoCheck_irrel_inv y (erase_tm (open_tm_wrt_tm a (a_Var_f y))) (r y HyL)).
  (* An_App *)
  - intros G b rho a B A a0 IHa a1 IHa1 G1 G2 C Phi GSub Heq HctxG HPhi HG HCtxSub HHyp.
    cbn [subst_co_tm].
    rewrite (subst_co_open_tm_v B C GSub a HG).
    apply An_App with (A := subst_co_tm C GSub A).
    + exact (IHa G1 G2 C Phi GSub Heq HctxG HPhi HG HCtxSub HHyp).
    + exact (IHa1 G1 G2 C Phi GSub Heq HctxG HPhi HG HCtxSub HHyp).
  (* An_Conv *)
  - intros G a g B A a0 IHa a1 IHa1 a2 IHa2 G1 G2 C Phi GSub Heq HctxG HPhi HG HCtxSub HHyp.
    cbn [subst_co_tm].
    apply An_Conv with (A := subst_co_tm C GSub A).
    + exact (IHa G1 G2 C Phi GSub Heq HctxG HPhi HG HCtxSub HHyp).
    + exact (IHa1 G1 G2 C Phi GSub Heq HctxG HPhi HG HCtxSub HHyp (subCo_ctx C GSub G1 ++ subCo_ctx C GSub G2) (dom (subCo_ctx C GSub G1 ++ subCo_ctx C GSub G2))
                   eq_refl (ctx_sub_refl (subCo_ctx C GSub G1 ++ subCo_ctx C GSub G2)) HCtxSub
                   (ctx_sub_subCo_right C GSub G1 G2)
                   (fun c Hin Hne => in_dom_subCo_ctx' G G1 C (Co Phi) G2 GSub c Heq Hin Hne)).
    + exact (IHa2 G1 G2 C Phi GSub Heq HctxG HPhi HG HCtxSub HHyp).
  (* An_CPi *)
  - intros L G phi B a IHa a0 IHa0 G1 G2 C Phi GSub Heq HctxG HPhi HG HCtxSub HHyp.
    apply An_CPi with (L := AtomSetImpl.union L (AtomSetImpl.union (dom G) (AtomSetImpl.singleton C))).
    + exact (IHa G1 G2 C Phi GSub Heq HctxG HPhi HG HCtxSub HHyp).
    + intro c. intro Hc.
      destruct (notin_union3 c L (dom G) (AtomSetImpl.singleton C) Hc) as (HcL & HcDomG & HcX).
      assert (Hcne : c <> C) by (symmetry; exact (notin_singleton_1 C c HcX)).
      assert (HctxM : AnnCtx ((c, Co phi) :: G)) by exact (An_ConsCo G c phi HctxG a HcDomG).
      assert (HctxSubM : AnnCtx ((c, Co (subst_co_constraint C GSub phi)) :: (subCo_ctx C GSub G1 ++ subCo_ctx C GSub G2)))
        by exact (An_ConsCo (subCo_ctx C GSub G1 ++ subCo_ctx C GSub G2) c (subst_co_constraint C GSub phi) HCtxSub
                     (IHa G1 G2 C Phi GSub Heq HctxG HPhi HG HCtxSub HHyp)
                     (notin_dom_subCo_ctx' G G1 C (Co Phi) G2 GSub c Heq HcDomG)).
      assert (Hbody := IHa0 c HcL ((c, Co phi) :: G1) G2 C Phi GSub
                        (cons_ctx_decomp_co c (Co phi) G1 C Phi G2 G Heq) HctxM HPhi HG HctxSubM HHyp).
      rewrite (subst_co_open_tm_co_var B C GSub c HG) in Hbody.
      rewrite (subst_co_co_var_neq C c GSub Hcne) in Hbody.
      exact Hbody.
  (* An_CAbs *)
  - intros L G phi a B a0 IHa a1 IHa1 G1 G2 C Phi GSub Heq HctxG HPhi HG HCtxSub HHyp.
    apply An_CAbs with (L := AtomSetImpl.union L (AtomSetImpl.union (dom G) (AtomSetImpl.singleton C))).
    + exact (IHa G1 G2 C Phi GSub Heq HctxG HPhi HG HCtxSub HHyp).
    + intro c. intro Hc.
      destruct (notin_union3 c L (dom G) (AtomSetImpl.singleton C) Hc) as (HcL & HcDomG & HcX).
      assert (Hcne : c <> C) by (symmetry; exact (notin_singleton_1 C c HcX)).
      assert (HctxM : AnnCtx ((c, Co phi) :: G)) by exact (An_ConsCo G c phi HctxG a0 HcDomG).
      assert (HctxSubM : AnnCtx ((c, Co (subst_co_constraint C GSub phi)) :: (subCo_ctx C GSub G1 ++ subCo_ctx C GSub G2)))
        by exact (An_ConsCo (subCo_ctx C GSub G1 ++ subCo_ctx C GSub G2) c (subst_co_constraint C GSub phi) HCtxSub
                     (IHa G1 G2 C Phi GSub Heq HctxG HPhi HG HCtxSub HHyp)
                     (notin_dom_subCo_ctx' G G1 C (Co Phi) G2 GSub c Heq HcDomG)).
      assert (Hbody := IHa1 c HcL ((c, Co phi) :: G1) G2 C Phi GSub
                        (cons_ctx_decomp_co c (Co phi) G1 C Phi G2 G Heq) HctxM HPhi HG HctxSubM HHyp).
      rewrite (subst_co_open_tm_co_var a C GSub c HG) in Hbody.
      rewrite (subst_co_co_var_neq C c GSub Hcne) in Hbody.
      rewrite (subst_co_open_tm_co_var B C GSub c HG) in Hbody.
      rewrite (subst_co_co_var_neq C c GSub Hcne) in Hbody.
      exact Hbody.
  (* An_CApp *)
  - intros G a1 g B a b A1 a0 IHa a1' IHa1 G1 G2 C Phi GSub Heq HctxG HPhi HG HCtxSub HHyp.
    cbn [subst_co_tm].
    rewrite (subst_co_open_tm_co_h B C GSub g HG).
    apply An_CApp with (a := subst_co_tm C GSub a) (b := subst_co_tm C GSub b) (A1 := subst_co_tm C GSub A1).
    + exact (IHa G1 G2 C Phi GSub Heq HctxG HPhi HG HCtxSub HHyp).
    + exact (IHa1 G1 G2 C Phi GSub Heq HctxG HPhi HG HCtxSub HHyp (subCo_ctx C GSub G1 ++ subCo_ctx C GSub G2) (dom (subCo_ctx C GSub G1 ++ subCo_ctx C GSub G2))
                   eq_refl (ctx_sub_refl (subCo_ctx C GSub G1 ++ subCo_ctx C GSub G2)) HCtxSub
                   (ctx_sub_subCo_right C GSub G1 G2)
                   (fun c Hin Hne => in_dom_subCo_ctx' G G1 C (Co Phi) G2 GSub c Heq Hin Hne)).
  (* An_Fam *)
  - intros G F A a a0 IHa b a1 IHa1 G1 G2 C Phi GSub Heq HctxG HPhi HG HCtxSub HHyp.
    destruct (an_toplevel_ax_subst_co F a A C GSub b) as [Ha HA].
    apply (An_Fam (subCo_ctx C GSub G1 ++ subCo_ctx C GSub G2) F (subst_co_tm C GSub A) (subst_co_tm C GSub a)).
    + exact HCtxSub.
    + rewrite Ha, HA. exact b.
    + rewrite HA. exact a1.

  (* An_Wff *)
  - intros G a b A B a0 IHa a1 IHa1 e G1 G2 C Phi GSub Heq HctxG HPhi HG HCtxSub HHyp.
    cbn [subst_co_constraint].
    apply An_Wff with (B := subst_co_tm C GSub B).
    + exact (IHa G1 G2 C Phi GSub Heq HctxG HPhi HG HCtxSub HHyp).
    + exact (IHa1 G1 G2 C Phi GSub Heq HctxG HPhi HG HCtxSub HHyp).
    + rewrite ((proj1 erase_subst_co_tm) A C GSub).
      rewrite ((proj1 erase_subst_co_tm) B C GSub).
      rewrite e. reflexivity.
  (* An_PropCong *)
  - intros G D g1 A g2 A1 B1 A2 B2 a IHa a0 IHa0 a1 IHa1 a2 IHa2 G1 G2 C Phi GSub Heq HctxG HPhi HG HCtxSub HHyp S0 D0 HD0 HsubS0S HctxS0 HsubG2S0 HDsub.
    cbn [subst_co_constraint].
    apply An_PropCong.
    + exact (IHa G1 G2 C Phi GSub Heq HctxG HPhi HG HCtxSub HHyp S0 D0 HD0 HsubS0S HctxS0 HsubG2S0 HDsub).
    + exact (IHa0 G1 G2 C Phi GSub Heq HctxG HPhi HG HCtxSub HHyp S0 D0 HD0 HsubS0S HctxS0 HsubG2S0 HDsub).
    + exact (IHa1 G1 G2 C Phi GSub Heq HctxG HPhi HG HCtxSub HHyp).
    + exact (IHa2 G1 G2 C Phi GSub Heq HctxG HPhi HG HCtxSub HHyp).
  (* An_CPiFst *)
  - intros G D g phi1 phi2 A2 B2 a IHa G1 G2 C Phi GSub Heq HctxG HPhi HG HCtxSub HHyp S0 D0 HD0 HsubS0S HctxS0 HsubG2S0 HDsub.
    cbn [subst_co_co subst_co_constraint].
    apply (An_CPiFst (subCo_ctx C GSub G1 ++ subCo_ctx C GSub G2) D0 (subst_co_co C GSub g) (subst_co_constraint C GSub phi1) (subst_co_constraint C GSub phi2) (subst_co_tm C GSub A2) (subst_co_tm C GSub B2)).
    exact (IHa G1 G2 C Phi GSub Heq HctxG HPhi HG HCtxSub HHyp S0 D0 HD0 HsubS0S HctxS0 HsubG2S0 HDsub).
  (* An_IsoSym *)
  - intros G D g phi2 phi1 a IHa G1 G2 C Phi GSub Heq HctxG HPhi HG HCtxSub HHyp S0 D0 HD0 HsubS0S HctxS0 HsubG2S0 HDsub.
    cbn [subst_co_co subst_co_constraint].
    apply An_IsoSym.
    exact (IHa G1 G2 C Phi GSub Heq HctxG HPhi HG HCtxSub HHyp S0 D0 HD0 HsubS0S HctxS0 HsubG2S0 HDsub).
  (* An_IsoConv *)
  - intros G D a1 a2 A a1' a2' B g a IHa a0 IHa0 a3 IHa3 e e0 G1 G2 C Phi GSub Heq HctxG HPhi HG HCtxSub HHyp S0 D0 HD0 HsubS0S HctxS0 HsubG2S0 HDsub.
    cbn [subst_co_co subst_co_constraint].
    apply An_IsoConv.
    + exact (IHa G1 G2 C Phi GSub Heq HctxG HPhi HG HCtxSub HHyp S0 D0 HD0 HsubS0S HctxS0 HsubG2S0 HDsub).
    + exact (IHa0 G1 G2 C Phi GSub Heq HctxG HPhi HG HCtxSub HHyp).
    + exact (IHa3 G1 G2 C Phi GSub Heq HctxG HPhi HG HCtxSub HHyp).
    + rewrite ((proj1 erase_subst_co_tm) a1 C GSub).
      rewrite ((proj1 erase_subst_co_tm) a1' C GSub).
      rewrite e. reflexivity.
    + rewrite ((proj1 erase_subst_co_tm) a2 C GSub).
      rewrite ((proj1 erase_subst_co_tm) a2' C GSub).
      rewrite e0. reflexivity.


  (* An_Assn *)
  - intros G D d a b A a0 IHa Hb i G1 G2 C Phi GSub Heq HctxG HPhi HG HCtxSub HHyp S0 D0 HD0 HsubS0S HctxS0 HsubG2S0 HDsub.
    destruct (annctx_uniq_split G G1 C (Co Phi) G2 HctxG Heq) as [HX1 HX2].
    rewrite Heq in Hb.
    destruct (binds_split_any G1 C (Co Phi) G2 d (Co (Eq a b A)) HX1 HX2 Hb) as [[Hdeq Hseq]|[Hne Hb']].
    + subst d. injection Hseq as Hphi.
      assert (HPhiEq : Phi = Eq a b A) by (symmetry; exact Hphi).
      assert (HsubstA : subst_co_tm C GSub a = a).
      { apply (proj1 subst_co_tm_id_fresh_all).
        rewrite HPhiEq in HPhi. cbn [fvx_constraint] in HPhi. notin_split_all. assumption. }
      assert (HsubstB : subst_co_tm C GSub b = b).
      { apply (proj1 subst_co_tm_id_fresh_all).
        rewrite HPhiEq in HPhi. cbn [fvx_constraint] in HPhi. notin_split_all. assumption. }
      rewrite subst_co_co_var_eq.
      rewrite HsubstA, HsubstB.
      assert (Hdf0 : AnnDefEq S0 (dom S0) GSub a b).
      { exact (HHyp S0 a b A HPhiEq HsubG2S0 HctxS0). }
      rewrite <- HD0 in Hdf0.
      exact (AnnDefEq_weaken S0 D0 GSub a b Hdf0
               (subCo_ctx C GSub G1 ++ subCo_ctx C GSub G2) HsubS0S HCtxSub).
    + rewrite (subst_co_co_var_neq C d GSub Hne).
      apply (An_Assn (subCo_ctx C GSub G1 ++ subCo_ctx C GSub G2) D0 d (subst_co_tm C GSub a) (subst_co_tm C GSub b) (subst_co_tm C GSub A)).
      * exact HCtxSub.
      * rewrite <- subCo_ctx_app.
        apply (binds_subCo_ctx C GSub (G1++G2) d (Co (Eq a b A)) Hb').
      * exact (HDsub d i Hne).
  (* An_Refl *)
  - intros G D a A a0 IHa G1 G2 C Phi GSub Heq HctxG HPhi HG HCtxSub HHyp S0 D0 HD0 HsubS0S HctxS0 HsubG2S0 HDsub.
    cbn [subst_co_co subst_co_tm].
    apply An_Refl with (A := subst_co_tm C GSub A).
    exact (IHa G1 G2 C Phi GSub Heq HctxG HPhi HG HCtxSub HHyp).
  (* An_EraseEq *)
  - intros G D a b g A B a0 IHa a1 IHa1 e a2 IHa2 G1 G2 C Phi GSub Heq HctxG HPhi HG HCtxSub HHyp S0 D0 HD0 HsubS0S HctxS0 HsubG2S0 HDsub.
    cbn [subst_co_co subst_co_tm].
    apply An_EraseEq with (A := subst_co_tm C GSub A) (B := subst_co_tm C GSub B).
    + exact (IHa G1 G2 C Phi GSub Heq HctxG HPhi HG HCtxSub HHyp).
    + exact (IHa1 G1 G2 C Phi GSub Heq HctxG HPhi HG HCtxSub HHyp).
    + rewrite ((proj1 erase_subst_co_tm) a C GSub).
      rewrite ((proj1 erase_subst_co_tm) b C GSub).
      rewrite e. reflexivity.
    + exact (IHa2 G1 G2 C Phi GSub Heq HctxG HPhi HG HCtxSub HHyp (subCo_ctx C GSub G1 ++ subCo_ctx C GSub G2) (dom (subCo_ctx C GSub G1 ++ subCo_ctx C GSub G2))
                   eq_refl (ctx_sub_refl (subCo_ctx C GSub G1 ++ subCo_ctx C GSub G2)) HCtxSub
                   (ctx_sub_subCo_right C GSub G1 G2)
                   (fun c Hin Hne => in_dom_subCo_ctx' G G1 C (Co Phi) G2 GSub c Heq Hin Hne)).
  (* An_Sym *)
  - intros G D g a b B A g1 a0 IHa0 a1 IHa1 a2 IHa2 a3 IHa3 G1 G2 C Phi GSub Heq HctxG HPhi HG HCtxSub HHyp S0 D0 HD0 HsubS0S HctxS0 HsubG2S0 HDsub.
    cbn [subst_co_co subst_co_tm].
    apply An_Sym with (B := subst_co_tm C GSub B) (A := subst_co_tm C GSub A) (g1 := subst_co_co C GSub g1).
    + exact (IHa0 G1 G2 C Phi GSub Heq HctxG HPhi HG HCtxSub HHyp).
    + exact (IHa1 G1 G2 C Phi GSub Heq HctxG HPhi HG HCtxSub HHyp).
    + exact (IHa2 G1 G2 C Phi GSub Heq HctxG HPhi HG HCtxSub HHyp (subCo_ctx C GSub G1 ++ subCo_ctx C GSub G2) (dom (subCo_ctx C GSub G1 ++ subCo_ctx C GSub G2))
                   eq_refl (ctx_sub_refl (subCo_ctx C GSub G1 ++ subCo_ctx C GSub G2)) HCtxSub
                   (ctx_sub_subCo_right C GSub G1 G2)
                   (fun c Hin Hne => in_dom_subCo_ctx' G G1 C (Co Phi) G2 GSub c Heq Hin Hne)).
    + exact (IHa3 G1 G2 C Phi GSub Heq HctxG HPhi HG HCtxSub HHyp S0 D0 HD0 HsubS0S HctxS0 HsubG2S0 HDsub).
  (* An_Trans *)
  - intros G D g1 g2 a b a1 A A1 g3 a0 IHa0 a2 IHa2 a3 IHa3 a4 IHa4 a5 IHa5 G1 G2 C Phi GSub Heq HctxG HPhi HG HCtxSub HHyp S0 D0 HD0 HsubS0S HctxS0 HsubG2S0 HDsub.
    cbn [subst_co_co subst_co_tm].
    apply An_Trans with (a1 := subst_co_tm C GSub a1) (A := subst_co_tm C GSub A) (A1 := subst_co_tm C GSub A1) (g3 := subst_co_co C GSub g3).
    + exact (IHa0 G1 G2 C Phi GSub Heq HctxG HPhi HG HCtxSub HHyp S0 D0 HD0 HsubS0S HctxS0 HsubG2S0 HDsub).
    + exact (IHa2 G1 G2 C Phi GSub Heq HctxG HPhi HG HCtxSub HHyp S0 D0 HD0 HsubS0S HctxS0 HsubG2S0 HDsub).
    + exact (IHa3 G1 G2 C Phi GSub Heq HctxG HPhi HG HCtxSub HHyp).
    + exact (IHa4 G1 G2 C Phi GSub Heq HctxG HPhi HG HCtxSub HHyp).
    + exact (IHa5 G1 G2 C Phi GSub Heq HctxG HPhi HG HCtxSub HHyp (subCo_ctx C GSub G1 ++ subCo_ctx C GSub G2) (dom (subCo_ctx C GSub G1 ++ subCo_ctx C GSub G2))
                   eq_refl (ctx_sub_refl (subCo_ctx C GSub G1 ++ subCo_ctx C GSub G2)) HCtxSub
                   (ctx_sub_subCo_right C GSub G1 G2)
                   (fun c Hin Hne => in_dom_subCo_ctx' G G1 C (Co Phi) G2 GSub c Heq Hin Hne)).


  (* An_Beta *)
  - intros G D a1 a2 B0 B1 a IHa a0 IHa0 e b G1 G2 C Phi GSub Heq HctxG HPhi HG HCtxSub HHyp S0 D0 HD0 HsubS0S HctxS0 HsubG2S0 HDsub.
    cbn [subst_co_co subst_co_tm].
    apply An_Beta with (B0 := subst_co_tm C GSub B0) (B1 := subst_co_tm C GSub B1).
    + exact (IHa G1 G2 C Phi GSub Heq HctxG HPhi HG HCtxSub HHyp).
    + exact (IHa0 G1 G2 C Phi GSub Heq HctxG HPhi HG HCtxSub HHyp).
    + rewrite ((proj1 erase_subst_co_tm) B0 C GSub).
      rewrite ((proj1 erase_subst_co_tm) B1 C GSub).
      rewrite e. reflexivity.
    + rewrite ((proj1 erase_subst_co_tm) a1 C GSub).
      rewrite ((proj1 erase_subst_co_tm) a2 C GSub).
      exact b.
  (* An_PiCong *)
  - intros L G D rho g1 g2 A1 B1 A2 B3 B2 a IHa a0 IHa0 e a1 IHa1 a2 IHa2 a3 IHa3 G1 G2 C Phi GSub Heq HctxG HPhi HG HCtxSub HHyp S0 D0 HD0 HsubS0S HctxS0 HsubG2S0 HDsub.
    cbn [subst_co_co subst_co_tm].
    apply (An_PiCong (AtomSetImpl.union L (AtomSetImpl.union (dom G) (AtomSetImpl.singleton C)))
              (subCo_ctx C GSub G1 ++ subCo_ctx C GSub G2) D0 rho
              (subst_co_co C GSub g1) (subst_co_co C GSub g2)
              (subst_co_tm C GSub A1) (subst_co_tm C GSub B1)
              (subst_co_tm C GSub A2) (subst_co_tm C GSub B3) (subst_co_tm C GSub B2)).
    + exact (IHa G1 G2 C Phi GSub Heq HctxG HPhi HG HCtxSub HHyp S0 D0 HD0 HsubS0S HctxS0 HsubG2S0 HDsub).
    + intro y. intro Hy.
      destruct (notin_union3 y L (dom G) (AtomSetImpl.singleton C) Hy) as (HyL & HyDomG & HyX).
      assert (Hne : y <> C) by (symmetry; exact (notin_singleton_1 C y HyX)).
      assert (HtyA1sub : AnnTyping (subCo_ctx C GSub G1 ++ subCo_ctx C GSub G2) (a_Pi rho (subst_co_tm C GSub A1) (subst_co_tm C GSub B1)) a_Star).
      { cbn [subst_co_tm]. exact (IHa1 G1 G2 C Phi GSub Heq HctxG HPhi HG HCtxSub HHyp). }
      assert (HctxM : AnnCtx ((y, Tm A1) :: G)) by exact (An_ConsTm G y A1 HctxG (AnnTyping_pi_dom G rho A1 B1 a1) HyDomG).
      assert (HctxSubM : AnnCtx ((y, Tm (subst_co_tm C GSub A1)) :: (subCo_ctx C GSub G1 ++ subCo_ctx C GSub G2)))
        by exact (An_ConsTm (subCo_ctx C GSub G1 ++ subCo_ctx C GSub G2) y (subst_co_tm C GSub A1) HCtxSub
                     (AnnTyping_pi_dom (subCo_ctx C GSub G1 ++ subCo_ctx C GSub G2) rho (subst_co_tm C GSub A1) (subst_co_tm C GSub B1) HtyA1sub)
                     (notin_dom_subCo_ctx' G G1 C (Co Phi) G2 GSub y Heq HyDomG)).
      assert (Hbody := IHa0 y HyL ((y, Tm A1) :: G1) G2 C Phi GSub
                        (cons_ctx_decomp_co y (Tm A1) G1 C Phi G2 G Heq) HctxM HPhi HG HctxSubM HHyp S0 D0 HD0
                        (ctx_sub_cons_r S0 (subCo_ctx C GSub G1 ++ subCo_ctx C GSub G2) y (Tm (subst_co_tm C GSub A1)) HsubS0S)
                        HctxS0 HsubG2S0 HDsub).
      rewrite (subst_co_open_co_tm_var g2 C GSub y HG) in Hbody.
      rewrite (subst_co_open_tm_var B1 C GSub y HG) in Hbody.
      rewrite (subst_co_open_tm_var B2 C GSub y HG) in Hbody.
      exact Hbody.
    + intro y. intro Hy.
      destruct (notin_union3 y L (dom G) (AtomSetImpl.singleton C) Hy) as (HyL & HyDomG & HyX).
      assert (Hne : y <> C) by (symmetry; exact (notin_singleton_1 C y HyX)).
      assert (Hf := f_equal (subst_co_tm C GSub) (e y HyL)).
      rewrite (subst_co_open_tm_var B3 C GSub y HG) in Hf.
      rewrite (subst_co_open_tm_v B2 C GSub (a_Conv (a_Var_f y) (g_Sym g1)) HG) in Hf.
      rewrite (subst_co_tm_conv_var_sym C GSub y g1 Hne) in Hf.
      exact Hf.
    + exact (IHa1 G1 G2 C Phi GSub Heq HctxG HPhi HG HCtxSub HHyp).
    + exact (IHa2 G1 G2 C Phi GSub Heq HctxG HPhi HG HCtxSub HHyp).
    + exact (IHa3 G1 G2 C Phi GSub Heq HctxG HPhi HG HCtxSub HHyp).
  (* An_AbsCong *)
  - intros L G D rho g1 g2 A1 b1 A2 b3 b2 B a IHa a0 IHa0 e a1 IHa1 a2 IHa2 r1 r2 a3 IHa3 G1 G2 C Phi GSub Heq HctxG HPhi HG HCtxSub HHyp S0 D0 HD0 HsubS0S HctxS0 HsubG2S0 HDsub.
    cbn [subst_co_co subst_co_tm].
    apply (An_AbsCong (AtomSetImpl.union L (AtomSetImpl.union (dom G) (AtomSetImpl.singleton C)))
              (subCo_ctx C GSub G1 ++ subCo_ctx C GSub G2) D0 rho
              (subst_co_co C GSub g1) (subst_co_co C GSub g2)
              (subst_co_tm C GSub A1) (subst_co_tm C GSub b1)
              (subst_co_tm C GSub A2) (subst_co_tm C GSub b3) (subst_co_tm C GSub b2) (subst_co_tm C GSub B)).
    + exact (IHa G1 G2 C Phi GSub Heq HctxG HPhi HG HCtxSub HHyp S0 D0 HD0 HsubS0S HctxS0 HsubG2S0 HDsub).
    + intro y. intro Hy.
      destruct (notin_union3 y L (dom G) (AtomSetImpl.singleton C) Hy) as (HyL & HyDomG & HyX).
      assert (Hne : y <> C) by (symmetry; exact (notin_singleton_1 C y HyX)).
      assert (HctxM : AnnCtx ((y, Tm A1) :: G)) by exact (An_ConsTm G y A1 HctxG a1 HyDomG).
      assert (HctxSubM : AnnCtx ((y, Tm (subst_co_tm C GSub A1)) :: (subCo_ctx C GSub G1 ++ subCo_ctx C GSub G2)))
        by exact (An_ConsTm (subCo_ctx C GSub G1 ++ subCo_ctx C GSub G2) y (subst_co_tm C GSub A1) HCtxSub
                     (IHa1 G1 G2 C Phi GSub Heq HctxG HPhi HG HCtxSub HHyp)
                     (notin_dom_subCo_ctx' G G1 C (Co Phi) G2 GSub y Heq HyDomG)).
      assert (Hbody := IHa0 y HyL ((y, Tm A1) :: G1) G2 C Phi GSub
                        (cons_ctx_decomp_co y (Tm A1) G1 C Phi G2 G Heq) HctxM HPhi HG HctxSubM HHyp S0 D0 HD0
                        (ctx_sub_cons_r S0 (subCo_ctx C GSub G1 ++ subCo_ctx C GSub G2) y (Tm (subst_co_tm C GSub A1)) HsubS0S)
                        HctxS0 HsubG2S0 HDsub).
      rewrite (subst_co_open_co_tm_var g2 C GSub y HG) in Hbody.
      rewrite (subst_co_open_tm_var b1 C GSub y HG) in Hbody.
      rewrite (subst_co_open_tm_var b2 C GSub y HG) in Hbody.
      exact Hbody.
    + intro y. intro Hy.
      destruct (notin_union3 y L (dom G) (AtomSetImpl.singleton C) Hy) as (HyL & HyDomG & HyX).
      assert (Hne : y <> C) by (symmetry; exact (notin_singleton_1 C y HyX)).
      assert (Hf := f_equal (subst_co_tm C GSub) (e y HyL)).
      rewrite (subst_co_open_tm_var b3 C GSub y HG) in Hf.
      rewrite (subst_co_open_tm_v b2 C GSub (a_Conv (a_Var_f y) (g_Sym g1)) HG) in Hf.
      rewrite (subst_co_tm_conv_var_sym C GSub y g1 Hne) in Hf.
      exact Hf.
    + exact (IHa1 G1 G2 C Phi GSub Heq HctxG HPhi HG HCtxSub HHyp).
    + exact (IHa2 G1 G2 C Phi GSub Heq HctxG HPhi HG HCtxSub HHyp).
    + intro y. intro Hy.
      destruct (notin_union3 y L (dom G) (AtomSetImpl.singleton C) Hy) as (HyL & HyDomG & HyX).
      assert (Hne : y <> C) by (symmetry; exact (notin_singleton_1 C y HyX)).
      destruct rho.
      * apply Rho_Rel. exact I.
      * apply Rho_IrrRel.
        rewrite (erase_open_subst_co_tm_var b1 C GSub y HG).
        exact (RhoCheck_irrel_inv y (erase_tm (open_tm_wrt_tm b1 (a_Var_f y))) (r1 y HyL)).
    + intro y. intro Hy.
      destruct (notin_union3 y L (dom G) (AtomSetImpl.singleton C) Hy) as (HyL & HyDomG & HyX).
      assert (Hne : y <> C) by (symmetry; exact (notin_singleton_1 C y HyX)).
      destruct rho.
      * apply Rho_Rel. exact I.
      * apply Rho_IrrRel.
        rewrite (erase_open_subst_co_tm_var b3 C GSub y HG).
        exact (RhoCheck_irrel_inv y (erase_tm (open_tm_wrt_tm b3 (a_Var_f y))) (r2 y HyL)).
    + exact (IHa3 G1 G2 C Phi GSub Heq HctxG HPhi HG HCtxSub HHyp).
  (* An_AppCong *)
  - intros G D g1 rho g2 a1 a2 b1 b2 A B g3 a IHa a0 IHa0 a1' IHa1 a2' IHa2 a3 IHa3 G1 G2 C Phi GSub Heq HctxG HPhi HG HCtxSub HHyp S0 D0 HD0 HsubS0S HctxS0 HsubG2S0 HDsub.
    cbn [subst_co_co subst_co_tm].
    apply (An_AppCong (subCo_ctx C GSub G1 ++ subCo_ctx C GSub G2) D0
              (subst_co_co C GSub g1) rho (subst_co_co C GSub g2)
              (subst_co_tm C GSub a1) (subst_co_tm C GSub a2)
              (subst_co_tm C GSub b1) (subst_co_tm C GSub b2)
              (subst_co_tm C GSub A) (subst_co_tm C GSub B) (subst_co_co C GSub g3)).
    + exact (IHa G1 G2 C Phi GSub Heq HctxG HPhi HG HCtxSub HHyp S0 D0 HD0 HsubS0S HctxS0 HsubG2S0 HDsub).
    + exact (IHa0 G1 G2 C Phi GSub Heq HctxG HPhi HG HCtxSub HHyp S0 D0 HD0 HsubS0S HctxS0 HsubG2S0 HDsub).
    + exact (IHa1 G1 G2 C Phi GSub Heq HctxG HPhi HG HCtxSub HHyp).
    + exact (IHa2 G1 G2 C Phi GSub Heq HctxG HPhi HG HCtxSub HHyp).
    + exact (IHa3 G1 G2 C Phi GSub Heq HctxG HPhi HG HCtxSub HHyp (subCo_ctx C GSub G1 ++ subCo_ctx C GSub G2) (dom (subCo_ctx C GSub G1 ++ subCo_ctx C GSub G2))
                   eq_refl (ctx_sub_refl (subCo_ctx C GSub G1 ++ subCo_ctx C GSub G2)) HCtxSub
                   (ctx_sub_subCo_right C GSub G1 G2)
                   (fun c Hin Hne => in_dom_subCo_ctx' G G1 C (Co Phi) G2 GSub c Heq Hin Hne)).
  (* An_PiFst *)
  - intros G D g A1 A2 rho B1 B2 a IHa G1 G2 C Phi GSub Heq HctxG HPhi HG HCtxSub HHyp S0 D0 HD0 HsubS0S HctxS0 HsubG2S0 HDsub.
    cbn [subst_co_co subst_co_tm].
    apply An_PiFst with (rho := rho) (B1 := subst_co_tm C GSub B1) (B2 := subst_co_tm C GSub B2).
    exact (IHa G1 G2 C Phi GSub Heq HctxG HPhi HG HCtxSub HHyp S0 D0 HD0 HsubS0S HctxS0 HsubG2S0 HDsub).


  (* An_PiSnd *)
  - intros G D g1 g2 B1 a1 B2 a2 rho A1 A2 a IHa a0 IHa0 a1' IHa1 a2' IHa2 G1 G2 C Phi GSub Heq HctxG HPhi HG HCtxSub HHyp S0 D0 HD0 HsubS0S HctxS0 HsubG2S0 HDsub.
    cbn [subst_co_co subst_co_tm].
    rewrite (subst_co_open_tm_v B1 C GSub a1 HG).
    rewrite (subst_co_open_tm_v B2 C GSub a2 HG).
    apply (An_PiSnd (subCo_ctx C GSub G1 ++ subCo_ctx C GSub G2) D0
              (subst_co_co C GSub g1) (subst_co_co C GSub g2)
              (subst_co_tm C GSub B1) (subst_co_tm C GSub a1)
              (subst_co_tm C GSub B2) (subst_co_tm C GSub a2) rho
              (subst_co_tm C GSub A1) (subst_co_tm C GSub A2)).
    + exact (IHa G1 G2 C Phi GSub Heq HctxG HPhi HG HCtxSub HHyp S0 D0 HD0 HsubS0S HctxS0 HsubG2S0 HDsub).
    + exact (IHa0 G1 G2 C Phi GSub Heq HctxG HPhi HG HCtxSub HHyp S0 D0 HD0 HsubS0S HctxS0 HsubG2S0 HDsub).
    + exact (IHa1 G1 G2 C Phi GSub Heq HctxG HPhi HG HCtxSub HHyp).
    + exact (IHa2 G1 G2 C Phi GSub Heq HctxG HPhi HG HCtxSub HHyp).
  (* An_CPiCong *)
  - intros L G D g1 g3 phi1 B1 phi2 B3 B2 a IHa a0 IHa0 e a1 IHa1 a2 IHa2 a3 IHa3 G1 G2 C Phi GSub Heq HctxG HPhi HG HCtxSub HHyp S0 D0 HD0 HsubS0S HctxS0 HsubG2S0 HDsub.
    cbn [subst_co_co subst_co_constraint subst_co_tm].
    apply (An_CPiCong (AtomSetImpl.union L (AtomSetImpl.union (dom G) (AtomSetImpl.singleton C)))
              (subCo_ctx C GSub G1 ++ subCo_ctx C GSub G2) D0
              (subst_co_co C GSub g1) (subst_co_co C GSub g3)
              (subst_co_constraint C GSub phi1) (subst_co_tm C GSub B1)
              (subst_co_constraint C GSub phi2) (subst_co_tm C GSub B3) (subst_co_tm C GSub B2)).
    + exact (IHa G1 G2 C Phi GSub Heq HctxG HPhi HG HCtxSub HHyp S0 D0 HD0 HsubS0S HctxS0 HsubG2S0 HDsub).
    + intro c. intro Hc.
      destruct (notin_union3 c L (dom G) (AtomSetImpl.singleton C) Hc) as (HcL & HcDomG & HcX).
      assert (Hcne : c <> C) by (symmetry; exact (notin_singleton_1 C c HcX)).
      assert (Hty1 : AnnTyping (subCo_ctx C GSub G1 ++ subCo_ctx C GSub G2) (a_CPi (subst_co_constraint C GSub phi1) (subst_co_tm C GSub B1)) a_Star).
      { cbn [subst_co_tm]. exact (IHa1 G1 G2 C Phi GSub Heq HctxG HPhi HG HCtxSub HHyp). }
      assert (HctxM : AnnCtx ((c, Co phi1) :: G)) by exact (An_ConsCo G c phi1 HctxG (AnnTyping_cpi_wff G phi1 B1 a1) HcDomG).
      assert (HctxSubM : AnnCtx ((c, Co (subst_co_constraint C GSub phi1)) :: (subCo_ctx C GSub G1 ++ subCo_ctx C GSub G2)))
        by exact (An_ConsCo (subCo_ctx C GSub G1 ++ subCo_ctx C GSub G2) c (subst_co_constraint C GSub phi1) HCtxSub
                     (AnnTyping_cpi_wff (subCo_ctx C GSub G1 ++ subCo_ctx C GSub G2) (subst_co_constraint C GSub phi1) (subst_co_tm C GSub B1) Hty1)
                     (notin_dom_subCo_ctx' G G1 C (Co Phi) G2 GSub c Heq HcDomG)).
      assert (Hbody := IHa0 c HcL ((c, Co phi1) :: G1) G2 C Phi GSub
                        (cons_ctx_decomp_co c (Co phi1) G1 C Phi G2 G Heq) HctxM HPhi HG HctxSubM HHyp S0 D0 HD0
                        (ctx_sub_cons_r S0 (subCo_ctx C GSub G1 ++ subCo_ctx C GSub G2) c (Co (subst_co_constraint C GSub phi1)) HsubS0S)
                        HctxS0 HsubG2S0 HDsub).
      rewrite (subst_co_open_co_co_var g3 C GSub c HG) in Hbody.
      rewrite (subst_co_co_var_neq C c GSub Hcne) in Hbody.
      rewrite (subst_co_open_tm_co_var B1 C GSub c HG) in Hbody.
      rewrite (subst_co_open_tm_co_var B2 C GSub c HG) in Hbody.
      rewrite (subst_co_co_var_neq C c GSub Hcne) in Hbody.
      exact Hbody.
    + intro c. intro Hc.
      destruct (notin_union3 c L (dom G) (AtomSetImpl.singleton C) Hc) as (HcL & HcDomG & HcX).
      assert (Hcne : c <> C) by (symmetry; exact (notin_singleton_1 C c HcX)).
      assert (Hf := f_equal (subst_co_tm C GSub) (e c HcL)).
      rewrite (subst_co_open_tm_co_var B3 C GSub c HG) in Hf.
      rewrite (subst_co_open_tm_co_h B2 C GSub (g_Cast (g_Var_f c) (g_Sym g1)) HG) in Hf.
      rewrite (subst_co_co_var_neq C c GSub Hcne) in Hf.
      rewrite (subst_co_co_cast_var_sym C GSub c g1 Hcne) in Hf.
      exact Hf.
    + exact (IHa1 G1 G2 C Phi GSub Heq HctxG HPhi HG HCtxSub HHyp).
    + exact (IHa2 G1 G2 C Phi GSub Heq HctxG HPhi HG HCtxSub HHyp).
    + exact (IHa3 G1 G2 C Phi GSub Heq HctxG HPhi HG HCtxSub HHyp).
  (* An_CAbsCong *)
  - intros L G D g1 g3 g4 phi1 a1 phi2 a3 a2 B1 B B2 a IHa a0 IHa0 e p1 IHp1 p2 IHp2 p3 IHp3 p4 IHp4 G1 G2 C Phi GSub Heq HctxG HPhi HG HCtxSub HHyp S0 D0 HD0 HsubS0S HctxS0 HsubG2S0 HDsub.
    cbn [subst_co_co subst_co_constraint subst_co_tm].
    apply (An_CAbsCong (AtomSetImpl.union L (AtomSetImpl.union (dom G) (AtomSetImpl.singleton C)))
              (subCo_ctx C GSub G1 ++ subCo_ctx C GSub G2) D0
              (subst_co_co C GSub g1) (subst_co_co C GSub g3) (subst_co_co C GSub g4)
              (subst_co_constraint C GSub phi1) (subst_co_tm C GSub a1)
              (subst_co_constraint C GSub phi2) (subst_co_tm C GSub a3) (subst_co_tm C GSub a2)
              (subst_co_tm C GSub B1) (subst_co_tm C GSub B) (subst_co_tm C GSub B2)).
    + exact (IHa G1 G2 C Phi GSub Heq HctxG HPhi HG HCtxSub HHyp S0 D0 HD0 HsubS0S HctxS0 HsubG2S0 HDsub).
    + intro c. intro Hc.
      destruct (notin_union3 c L (dom G) (AtomSetImpl.singleton C) Hc) as (HcL & HcDomG & HcX).
      assert (Hcne : c <> C) by (symmetry; exact (notin_singleton_1 C c HcX)).
      assert (Hty1 : AnnTyping (subCo_ctx C GSub G1 ++ subCo_ctx C GSub G2) (a_CAbs (subst_co_constraint C GSub phi1) (subst_co_tm C GSub a1)) (a_CPi (subst_co_constraint C GSub phi1) (subst_co_tm C GSub B1))).
      { cbn [subst_co_tm]. exact (IHp1 G1 G2 C Phi GSub Heq HctxG HPhi HG HCtxSub HHyp). }
      assert (HctxM : AnnCtx ((c, Co phi1) :: G)) by exact (An_ConsCo G c phi1 HctxG (AnnTyping_cabs_wff G phi1 a1 (a_CPi phi1 B1) p1) HcDomG).
      assert (HctxSubM : AnnCtx ((c, Co (subst_co_constraint C GSub phi1)) :: (subCo_ctx C GSub G1 ++ subCo_ctx C GSub G2)))
        by exact (An_ConsCo (subCo_ctx C GSub G1 ++ subCo_ctx C GSub G2) c (subst_co_constraint C GSub phi1) HCtxSub
                     (AnnTyping_cabs_wff (subCo_ctx C GSub G1 ++ subCo_ctx C GSub G2) (subst_co_constraint C GSub phi1) (subst_co_tm C GSub a1) (a_CPi (subst_co_constraint C GSub phi1) (subst_co_tm C GSub B1)) Hty1)
                     (notin_dom_subCo_ctx' G G1 C (Co Phi) G2 GSub c Heq HcDomG)).
      assert (Hbody := IHa0 c HcL ((c, Co phi1) :: G1) G2 C Phi GSub
                        (cons_ctx_decomp_co c (Co phi1) G1 C Phi G2 G Heq) HctxM HPhi HG HctxSubM HHyp S0 D0 HD0
                        (ctx_sub_cons_r S0 (subCo_ctx C GSub G1 ++ subCo_ctx C GSub G2) c (Co (subst_co_constraint C GSub phi1)) HsubS0S)
                        HctxS0 HsubG2S0 HDsub).
      rewrite (subst_co_open_co_co_var g3 C GSub c HG) in Hbody.
      rewrite (subst_co_co_var_neq C c GSub Hcne) in Hbody.
      rewrite (subst_co_open_tm_co_var a1 C GSub c HG) in Hbody.
      rewrite (subst_co_open_tm_co_var a2 C GSub c HG) in Hbody.
      rewrite (subst_co_co_var_neq C c GSub Hcne) in Hbody.
      exact Hbody.
    + intro c. intro Hc.
      destruct (notin_union3 c L (dom G) (AtomSetImpl.singleton C) Hc) as (HcL & HcDomG & HcX).
      assert (Hcne : c <> C) by (symmetry; exact (notin_singleton_1 C c HcX)).
      assert (Hf := f_equal (subst_co_tm C GSub) (e c HcL)).
      rewrite (subst_co_open_tm_co_var a3 C GSub c HG) in Hf.
      rewrite (subst_co_open_tm_co_h a2 C GSub (g_Cast (g_Var_f c) (g_Sym g1)) HG) in Hf.
      rewrite (subst_co_co_var_neq C c GSub Hcne) in Hf.
      rewrite (subst_co_co_cast_var_sym C GSub c g1 Hcne) in Hf.
      exact Hf.
    + exact (IHp1 G1 G2 C Phi GSub Heq HctxG HPhi HG HCtxSub HHyp).
    + exact (IHp2 G1 G2 C Phi GSub Heq HctxG HPhi HG HCtxSub HHyp).
    + exact (IHp3 G1 G2 C Phi GSub Heq HctxG HPhi HG HCtxSub HHyp).
    + exact (IHp4 G1 G2 C Phi GSub Heq HctxG HPhi HG HCtxSub HHyp (subCo_ctx C GSub G1 ++ subCo_ctx C GSub G2) (dom (subCo_ctx C GSub G1 ++ subCo_ctx C GSub G2))
                   eq_refl (ctx_sub_refl (subCo_ctx C GSub G1 ++ subCo_ctx C GSub G2)) HCtxSub
                   (ctx_sub_subCo_right C GSub G1 G2)
                   (fun c Hin Hne => in_dom_subCo_ctx' G G1 C (Co Phi) G2 GSub c Heq Hin Hne)).
  (* An_CAppCong *)
  - intros G D g1 g2 g3 a1 b1 a2 b2 a3 b3 A B g4 a IHa a0 IHa0 a1' IHa1 a2' IHa2 a3' IHa3 a4 IHa4 G1 G2 C Phi GSub Heq HctxG HPhi HG HCtxSub HHyp S0 D0 HD0 HsubS0S HctxS0 HsubG2S0 HDsub.
    cbn [subst_co_co subst_co_tm].
    apply (An_CAppCong (subCo_ctx C GSub G1 ++ subCo_ctx C GSub G2) D0
              (subst_co_co C GSub g1) (subst_co_co C GSub g2) (subst_co_co C GSub g3)
              (subst_co_tm C GSub a1) (subst_co_tm C GSub b1)
              (subst_co_tm C GSub a2) (subst_co_tm C GSub b2)
              (subst_co_tm C GSub a3) (subst_co_tm C GSub b3)
              (subst_co_tm C GSub A) (subst_co_tm C GSub B) (subst_co_co C GSub g4)).
    + exact (IHa G1 G2 C Phi GSub Heq HctxG HPhi HG HCtxSub HHyp S0 D0 HD0 HsubS0S HctxS0 HsubG2S0 HDsub).
    + exact (IHa0 G1 G2 C Phi GSub Heq HctxG HPhi HG HCtxSub HHyp (subCo_ctx C GSub G1 ++ subCo_ctx C GSub G2) (dom (subCo_ctx C GSub G1 ++ subCo_ctx C GSub G2))
                   eq_refl (ctx_sub_refl (subCo_ctx C GSub G1 ++ subCo_ctx C GSub G2)) HCtxSub
                   (ctx_sub_subCo_right C GSub G1 G2)
                   (fun c Hin Hne => in_dom_subCo_ctx' G G1 C (Co Phi) G2 GSub c Heq Hin Hne)).
    + exact (IHa1 G1 G2 C Phi GSub Heq HctxG HPhi HG HCtxSub HHyp (subCo_ctx C GSub G1 ++ subCo_ctx C GSub G2) (dom (subCo_ctx C GSub G1 ++ subCo_ctx C GSub G2))
                   eq_refl (ctx_sub_refl (subCo_ctx C GSub G1 ++ subCo_ctx C GSub G2)) HCtxSub
                   (ctx_sub_subCo_right C GSub G1 G2)
                   (fun c Hin Hne => in_dom_subCo_ctx' G G1 C (Co Phi) G2 GSub c Heq Hin Hne)).
    + exact (IHa2 G1 G2 C Phi GSub Heq HctxG HPhi HG HCtxSub HHyp).
    + exact (IHa3 G1 G2 C Phi GSub Heq HctxG HPhi HG HCtxSub HHyp).
    + exact (IHa4 G1 G2 C Phi GSub Heq HctxG HPhi HG HCtxSub HHyp (subCo_ctx C GSub G1 ++ subCo_ctx C GSub G2) (dom (subCo_ctx C GSub G1 ++ subCo_ctx C GSub G2))
                   eq_refl (ctx_sub_refl (subCo_ctx C GSub G1 ++ subCo_ctx C GSub G2)) HCtxSub
                   (ctx_sub_subCo_right C GSub G1 G2)
                   (fun c Hin Hne => in_dom_subCo_ctx' G G1 C (Co Phi) G2 GSub c Heq Hin Hne)).
  (* An_CPiSnd *)
  - intros G D g1 g2 g3 B1 B2 a a' A b b' B a0 IHa0 a1 IHa1 a2 IHa2 G1 G2 C Phi GSub Heq HctxG HPhi HG HCtxSub HHyp S0 D0 HD0 HsubS0S HctxS0 HsubG2S0 HDsub.
    cbn [subst_co_co subst_co_tm].
    rewrite (subst_co_open_tm_co_h B1 C GSub g2 HG).
    rewrite (subst_co_open_tm_co_h B2 C GSub g3 HG).
    apply (An_CPiSnd (subCo_ctx C GSub G1 ++ subCo_ctx C GSub G2) D0
              (subst_co_co C GSub g1) (subst_co_co C GSub g2) (subst_co_co C GSub g3)
              (subst_co_tm C GSub B1) (subst_co_tm C GSub B2)
              (subst_co_tm C GSub a) (subst_co_tm C GSub a') (subst_co_tm C GSub A)
              (subst_co_tm C GSub b) (subst_co_tm C GSub b') (subst_co_tm C GSub B)).
    + exact (IHa0 G1 G2 C Phi GSub Heq HctxG HPhi HG HCtxSub HHyp S0 D0 HD0 HsubS0S HctxS0 HsubG2S0 HDsub).
    + exact (IHa1 G1 G2 C Phi GSub Heq HctxG HPhi HG HCtxSub HHyp (subCo_ctx C GSub G1 ++ subCo_ctx C GSub G2) (dom (subCo_ctx C GSub G1 ++ subCo_ctx C GSub G2))
                   eq_refl (ctx_sub_refl (subCo_ctx C GSub G1 ++ subCo_ctx C GSub G2)) HCtxSub
                   (ctx_sub_subCo_right C GSub G1 G2)
                   (fun c Hin Hne => in_dom_subCo_ctx' G G1 C (Co Phi) G2 GSub c Heq Hin Hne)).
    + exact (IHa2 G1 G2 C Phi GSub Heq HctxG HPhi HG HCtxSub HHyp (subCo_ctx C GSub G1 ++ subCo_ctx C GSub G2) (dom (subCo_ctx C GSub G1 ++ subCo_ctx C GSub G2))
                   eq_refl (ctx_sub_refl (subCo_ctx C GSub G1 ++ subCo_ctx C GSub G2)) HCtxSub
                   (ctx_sub_subCo_right C GSub G1 G2)
                   (fun c Hin Hne => in_dom_subCo_ctx' G G1 C (Co Phi) G2 GSub c Heq Hin Hne)).


  (* An_Cast *)
  - intros G D g1 g2 b b' a a' A B a0 IHa0 a1 IHa1 G1 G2 C Phi GSub Heq HctxG HPhi HG HCtxSub HHyp S0 D0 HD0 HsubS0S HctxS0 HsubG2S0 HDsub.
    cbn [subst_co_co subst_co_tm].
    apply (An_Cast (subCo_ctx C GSub G1 ++ subCo_ctx C GSub G2) D0
              (subst_co_co C GSub g1) (subst_co_co C GSub g2)
              (subst_co_tm C GSub b) (subst_co_tm C GSub b')
              (subst_co_tm C GSub a) (subst_co_tm C GSub a')
              (subst_co_tm C GSub A) (subst_co_tm C GSub B)).
    + exact (IHa0 G1 G2 C Phi GSub Heq HctxG HPhi HG HCtxSub HHyp S0 D0 HD0 HsubS0S HctxS0 HsubG2S0 HDsub).
    + exact (IHa1 G1 G2 C Phi GSub Heq HctxG HPhi HG HCtxSub HHyp S0 D0 HD0 HsubS0S HctxS0 HsubG2S0 HDsub).
  (* An_IsoSnd *)
  - intros G D g A B a a' b b' a0 IHa G1 G2 C Phi GSub Heq HctxG HPhi HG HCtxSub HHyp S0 D0 HD0 HsubS0S HctxS0 HsubG2S0 HDsub.
    cbn [subst_co_co subst_co_tm].
    apply (An_IsoSnd (subCo_ctx C GSub G1 ++ subCo_ctx C GSub G2) D0
              (subst_co_co C GSub g) (subst_co_tm C GSub A) (subst_co_tm C GSub B)
              (subst_co_tm C GSub a) (subst_co_tm C GSub a')
              (subst_co_tm C GSub b) (subst_co_tm C GSub b')).
    exact (IHa G1 G2 C Phi GSub Heq HctxG HPhi HG HCtxSub HHyp S0 D0 HD0 HsubS0S HctxS0 HsubG2S0 HDsub).
  (* An_Empty *)
  - intros. exact I.
  (* An_ConsTm *)
  - intros. exact I.
  (* An_ConsCo *)
  - intros. exact I.
  (* An_Sig_Empty *)
  - intros. exact I.
  (* An_Sig_Cons *)
  - intros. exact I.
Qed.

Lemma AnnTyping_subst_co_dom :
  (forall G t T (H:AnnTyping G t T), forall G1 G2 C Phi GSub,
    G = G1 ++ (C, Co Phi) :: nil ++ G2 ->
    C `notin` fvx_constraint Phi ->
    lc_co GSub ->
    AnnCtx (subCo_ctx C GSub G1 ++ subCo_ctx C GSub G2) ->
    CoRemovedHypDom C G2 Phi GSub ->
    AnnTyping (subCo_ctx C GSub G1 ++ subCo_ctx C GSub G2)
              (subst_co_tm C GSub t) (subst_co_tm C GSub T)) /\
  (forall G p (H:AnnPropWff G p), forall G1 G2 C Phi GSub,
    G = G1 ++ (C, Co Phi) :: nil ++ G2 ->
    C `notin` fvx_constraint Phi ->
    lc_co GSub ->
    AnnCtx (subCo_ctx C GSub G1 ++ subCo_ctx C GSub G2) ->
    CoRemovedHypDom C G2 Phi GSub ->
    AnnPropWff (subCo_ctx C GSub G1 ++ subCo_ctx C GSub G2)
               (subst_co_constraint C GSub p)).
Proof.
  destruct Main_co_dom_aux as [H1 [H2 _]].
  split.
  - intros G t T H G1 G2 C Phi GSub Heq HPhi HG HCtxSub HHyp.
    exact (H1 G t T H G1 G2 C Phi GSub Heq (AnnTyping_AnnCtx G t T H) HPhi HG HCtxSub HHyp).
  - intros G p H G1 G2 C Phi GSub Heq HPhi HG HCtxSub HHyp.
    exact (H2 G p H G1 G2 C Phi GSub Heq (AnnPropWff_AnnCtx G p H) HPhi HG HCtxSub HHyp).
Qed.

(* ===== PresDev ===== *)
From Stdlib Require Import List.
From Stdlib Require Import Lia.
Import ListNotations.

(* ============ inversion lemmas for AnnTyping ============ *)
Lemma AnnTyping_Conv_inv : forall (G:context) (a:tm) (g:co) (B:tm),
  AnnTyping G (a_Conv a g) B ->
  exists A, AnnTyping G a A /\ AnnDefEq G (dom G) g A B /\
            AnnTyping G B a_Star.
Proof. intros G a g B H. inversion H; subst; eauto. Qed.

Lemma AnnTyping_App_inv : forall (G:context) (b:tm) (rho:relflag) (a:tm) (T:tm),
  AnnTyping G (a_App b rho a) T ->
  exists A B, T = open_tm_wrt_tm B a /\
              AnnTyping G b (a_Pi rho A B) /\ AnnTyping G a A.
Proof. intros G b rho a T H. inversion H; subst; eauto. Qed.

Lemma AnnTyping_CApp_inv : forall (G:context) (b:tm) (g:co) (T:tm),
  AnnTyping G (a_CApp b g) T ->
  exists B a0 b0 A0, T = open_tm_wrt_co B g /\
    AnnTyping G b (a_CPi (Eq a0 b0 A0) B) /\ AnnDefEq G (dom G) g a0 b0.
Proof.
  intros G b g T H. inversion H; subst.
  eexists _, _, _, _. split; [reflexivity|]. split; eassumption.
Qed.

Lemma AnnTyping_Pi_inv : forall (G:context) (rho:relflag) (A B:tm),
  AnnTyping G (a_Pi rho A B) a_Star ->
  exists L, (forall x, x `notin` L ->
               AnnTyping ((x ~ Tm A) ++ G) (open_tm_wrt_tm B (a_Var_f x)) a_Star) /\
            AnnTyping G A a_Star.
Proof. intros G rho A B H. inversion H; subst; eauto. Qed.

Lemma AnnTyping_Abs_inv : forall (G:context) (rho:relflag) (A a B:tm),
  AnnTyping G (a_Abs rho A a) (a_Pi rho A B) ->
  exists L, AnnTyping G A a_Star /\
    (forall x, x `notin` L ->
       AnnTyping ((x ~ Tm A) ++ G) (open_tm_wrt_tm a (a_Var_f x))
                 (open_tm_wrt_tm B (a_Var_f x))) /\
    (forall x, x `notin` L ->
       RhoCheck rho x (erase_tm (open_tm_wrt_tm a (a_Var_f x)))).
Proof. intros G rho A a B H. inversion H; subst; eauto. Qed.

Lemma AnnTyping_CPi_inv : forall (G:context) (phi:constraint) (B:tm),
  AnnTyping G (a_CPi phi B) a_Star ->
  exists L, AnnPropWff G phi /\
    (forall c, c `notin` L ->
       AnnTyping ((c ~ Co phi) ++ G) (open_tm_wrt_co B (g_Var_f c)) a_Star).
Proof. intros G phi B H. inversion H; subst; eauto. Qed.

Lemma AnnTyping_CAbs_inv : forall (G:context) (phi:constraint) (a B:tm),
  AnnTyping G (a_CAbs phi a) (a_CPi phi B) ->
  exists L, AnnPropWff G phi /\
    (forall c, c `notin` L ->
       AnnTyping ((c ~ Co phi) ++ G) (open_tm_wrt_co a (g_Var_f c))
                 (open_tm_wrt_co B (g_Var_f c))).
Proof. intros G phi a B H. inversion H; subst; eauto. Qed.

(* ============ shape of typed values ============ *)
Lemma Value_AnnTyping_shape : forall (G:context) (a A:tm),
  Value a -> AnnTyping G a A ->
  (a = a_Star /\ A = a_Star) \/
  (exists (rho:relflag) (A' b:tm), a = a_Pi rho A' b /\ A = a_Star) \/
  (exists (phi:constraint) (b:tm), a = a_CPi phi b /\ A = a_Star) \/
  (exists (A1 b:tm), a = a_Abs Rel A1 b /\ exists B, A = a_Pi Rel A1 B) \/
  (exists (A1 b:tm), a = a_Abs Irrel A1 b /\ exists B, A = a_Pi Irrel A1 B) \/
  (exists (phi:constraint) (b:tm), a = a_CAbs phi b /\ exists B, A = a_CPi phi B).
Proof.
  intros G a A Hv Hty.
  destruct Hv as
    [|rho A0 B0 HlcA HlcPi|phi B0 Hlcp HlcCPi
     |A0 b HlcA HlcAbs|b HlcUAbs
     |L b Hbody|L A0 b HlcA Hbody
     |phi b Hlcp HlcCAbs|b HlcUCAbs].
  - left. inversion Hty; subst; auto.
  - right. left. exists rho, A0, B0. inversion Hty; subst; auto.
  - right. right. left. exists phi, B0. inversion Hty; subst; auto.
  - right. right. right. left.
    exists A0, b. split; [reflexivity|]. inversion Hty; subst. eauto.
  - inversion Hty.
  - inversion Hty.
  - right. right. right. right. left.
    exists A0, b. split; [reflexivity|]. inversion Hty; subst. eauto.
  - right. right. right. right. right.
    exists phi, b. split; [reflexivity|]. inversion Hty; subst. eauto.
  - inversion Hty.
Qed.

Lemma Value_typing_Pi : forall (G:context) (v:tm) (rho:relflag) (A B:tm),
  Value v -> AnnTyping G v (a_Pi rho A B) ->
  exists A0 b, v = a_Abs rho A0 b.
Proof.
  intros G v rho A B Hv Hty.
  pose proof (Value_AnnTyping_shape G v (a_Pi rho A B) Hv Hty) as Hsh.
  destruct Hsh as [Hsh | Hsh].
  - destruct Hsh as [Heq Hstar]. subst v. discriminate Hstar.
  - destruct Hsh as [Hsh | Hsh].
    + destruct Hsh as [rho0 [A0 [B0 [Heq Hstar]]]]. subst v. discriminate Hstar.
    + destruct Hsh as [Hsh | Hsh].
      * destruct Hsh as [phi [B0 [Heq Hstar]]]. subst v. discriminate Hstar.
      * destruct Hsh as [Hsh | Hsh].
        -- destruct Hsh as [A0 [b0 [Heq HB]]]. subst v.
           destruct HB as [B0 Hty0]. inversion Hty0; subst. eauto.
        -- destruct Hsh as [Hsh | Hsh].
           ++ destruct Hsh as [A0 [b0 [Heq HB]]]. subst v.
              destruct HB as [B0 Hty0]. inversion Hty0; subst. eauto.
           ++ destruct Hsh as [phi [b0 [Heq HB]]]. subst v.
              destruct HB as [B0 Hty0]. discriminate Hty0.
Qed.

Lemma Value_typing_CPi : forall (G:context) (v:tm) (phi:constraint) (B:tm),
  Value v -> AnnTyping G v (a_CPi phi B) ->
  exists phi0 b B0, v = a_CAbs phi0 b /\ phi0 = phi /\ B0 = B.
Proof.
  intros G v phi B Hv Hty.
  pose proof (Value_AnnTyping_shape G v (a_CPi phi B) Hv Hty) as Hsh.
  destruct Hsh as [Hsh | Hsh].
  - destruct Hsh as [Heq Hstar]. subst v. discriminate Hstar.
  - destruct Hsh as [Hsh | Hsh].
    + destruct Hsh as [rho0 [A0 [B0 [Heq Hstar]]]]. subst v. discriminate Hstar.
    + destruct Hsh as [Hsh | Hsh].
      * destruct Hsh as [phi0 [B0 [Heq Hstar]]]. subst v. discriminate Hstar.
      * destruct Hsh as [Hsh | Hsh].
        -- destruct Hsh as [A0 [b0 [Heq HB]]]. subst v.
           destruct HB as [B0 Hty0]. discriminate Hty0.
        -- destruct Hsh as [Hsh | Hsh].
           ++ destruct Hsh as [A0 [b0 [Heq HB]]]. subst v.
              destruct HB as [B0 Hty0]. discriminate Hty0.
           ++ destruct Hsh as [phi0 [b0 [Heq HB]]]. subst v.
              destruct HB as [B0 Hty0]. inversion Hty0; subst.
              exists phi0, b0, B0. repeat split; reflexivity.
Qed.

Lemma Value_typing_CPi_Eq : forall (G:context) (v:tm) (a b A B:tm),
  Value v -> AnnTyping G v (a_CPi (Eq a b A) B) ->
  exists b0, v = a_CAbs (Eq a b A) b0.
Proof.
  intros G v a b A B Hv Hty.
  destruct (Value_typing_CPi G v (Eq a b A) B Hv Hty)
    as [phi0 [b0 [B0 [Heq [Hphi HB]]]]]. subst phi0. subst B0.
  exists b0. exact Heq.
Qed.

(* ============ fvx is the same as fv_tm_tm_tm on erased terms ============ *)
Lemma fvx_eq_fv_erase :
  (forall a, fvx_tm (erase_tm a) = fv_tm_tm_tm (erase_tm a)) /\
  (forall b:brs, True) /\
  (forall g:co, True) /\
  (forall phi:constraint, fvx_constraint (erase_constraint phi) =
               fv_tm_tm_constraint (erase_constraint phi)).
Proof.
  apply (tm_mutind
    (fun a => fvx_tm (erase_tm a) = fv_tm_tm_tm (erase_tm a))
    (fun (b:brs) => True)
    (fun (g:co) => True)
    (fun (phi:constraint) => fvx_constraint (erase_constraint phi) =
                fv_tm_tm_constraint (erase_constraint phi)));
  intros; try exact I; try destruct rho;
  cbn [erase_tm erase_brs erase_constraint
       fvx_tm fvx_constraint fvx_co fv_tm_tm_tm fv_tm_tm_constraint fv_tm_tm_co];
  try reflexivity; try (repeat f_equal; try assumption).
Qed.

Lemma fvx_eq_fv_erase_tm : forall a,
  fvx_tm (erase_tm a) = fv_tm_tm_tm (erase_tm a).
Proof. exact (proj1 fvx_eq_fv_erase). Qed.

Lemma fv_tm_tm_open_subset_erased : forall a x,
  AtomSetImpl.Subset
    (fv_tm_tm_tm (open_tm_wrt_tm (erase_tm a) (a_Var_f x)))
    (fv_tm_tm_tm (erase_tm a) \u {{x}}).
Proof.
  intros a x.
  pose proof (fv_open_tm_subset_tm (erase_tm a) 0 (a_Var_f x)) as H.
  assert (Hopen : open_tm_wrt_tm_rec 0 (a_Var_f x) (erase_tm a) =
                  erase_tm (open_tm_wrt_tm_rec 0 (a_Var_f x) a)).
  { symmetry. apply (proj1 erase_open_tm_tm_all). }
  rewrite Hopen in H.
  rewrite fvx_eq_fv_erase_tm in H.
  rewrite fvx_eq_fv_erase_tm in H.
  cbn [fvx_tm] in H.
  change (AtomSetImpl.Subset
    (fv_tm_tm_tm (open_tm_wrt_tm_rec 0 (a_Var_f x) (erase_tm a)))
    (fv_tm_tm_tm (erase_tm a) \u {{x}})).
  rewrite Hopen.
  exact H.
Qed.

(* Opening with a free variable keeps every old free variable (any level). *)
Lemma fv_tm_tm_open_self_all :
  (forall a k x, AtomSetImpl.Subset (fv_tm_tm_tm a)
                 (fv_tm_tm_tm (open_tm_wrt_tm_rec k (a_Var_f x) a))) /\
  (forall b k x, AtomSetImpl.Subset (fv_tm_tm_brs b)
                 (fv_tm_tm_brs (open_brs_wrt_tm_rec k (a_Var_f x) b))) /\
  (forall g k x, AtomSetImpl.Subset (fv_tm_tm_co g)
                 (fv_tm_tm_co (open_co_wrt_tm_rec k (a_Var_f x) g))) /\
  (forall p k x, AtomSetImpl.Subset (fv_tm_tm_constraint p)
                 (fv_tm_tm_constraint (open_constraint_wrt_tm_rec k (a_Var_f x) p))).
Proof.
  apply (tm_mutind
    (fun a => forall k x, AtomSetImpl.Subset (fv_tm_tm_tm a)
                 (fv_tm_tm_tm (open_tm_wrt_tm_rec k (a_Var_f x) a)))
    (fun b => forall k x, AtomSetImpl.Subset (fv_tm_tm_brs b)
                 (fv_tm_tm_brs (open_brs_wrt_tm_rec k (a_Var_f x) b)))
    (fun g => forall k x, AtomSetImpl.Subset (fv_tm_tm_co g)
                 (fv_tm_tm_co (open_co_wrt_tm_rec k (a_Var_f x) g)))
    (fun p => forall k x, AtomSetImpl.Subset (fv_tm_tm_constraint p)
                 (fv_tm_tm_constraint (open_constraint_wrt_tm_rec k (a_Var_f x) p)))).
  all: intros; cbn [open_tm_wrt_tm open_tm_wrt_tm_rec open_brs_wrt_tm_rec
                       open_co_wrt_tm open_co_wrt_tm_rec
                       open_constraint_wrt_tm_rec fv_tm_tm_tm fv_tm_tm_brs
                       fv_tm_tm_co fv_tm_tm_constraint] in *.
  all: try (repeat match goal with
             H : forall (k0:nat) (x0:tmvar), AtomSetImpl.Subset _ _ |- _ =>
             let H1 := fresh in let H2 := fresh in
             pose proof (H k x) as H1; pose proof (H (S k) x) as H2; clear H end).
  all: try (repeat match goal with
             H : AtomSetImpl.Subset _ _ |- _ =>
             unfold AtomSetImpl.Subset in H end).
  all: try (unfold AtomSetImpl.Subset; intros y Hy;
            repeat match goal with
              H : forall a : atom, a `in` _ -> a `in` _ |- _ =>
              specialize (H y)
            end;
            repeat match goal with
              H : y `in` AtomSetImpl.union ?s ?t |- _ =>
              let H' := fresh in destruct (AtomSetImpl.union_1 H) as [H'|H'];
              clear H
            end;
            eauto 20 using AtomSetImpl.union_2, AtomSetImpl.union_3).
  all: try fsetdec.
  all: try reflexivity.
Qed.

Lemma fv_tm_tm_open_self : forall a x,
  AtomSetImpl.Subset (fv_tm_tm_tm a)
                     (fv_tm_tm_tm (open_tm_wrt_tm a (a_Var_f x))).
Proof. intros. exact (proj1 fv_tm_tm_open_self_all a 0 x). Qed.

(* Opening introduces at most the opener's free variables. *)
Lemma fv_open_tm_subset_all :
  (forall a k u, AtomSetImpl.Subset (fv_tm_tm_tm (open_tm_wrt_tm_rec k u a))
                 (AtomSetImpl.union (fv_tm_tm_tm a) (fv_tm_tm_tm u))) /\
  (forall b k u, AtomSetImpl.Subset (fv_tm_tm_brs (open_brs_wrt_tm_rec k u b))
                 (AtomSetImpl.union (fv_tm_tm_brs b) (fv_tm_tm_tm u))) /\
  (forall g k u, AtomSetImpl.Subset (fv_tm_tm_co (open_co_wrt_tm_rec k u g))
                 (AtomSetImpl.union (fv_tm_tm_co g) (fv_tm_tm_tm u))) /\
  (forall p k u, AtomSetImpl.Subset (fv_tm_tm_constraint (open_constraint_wrt_tm_rec k u p))
                 (AtomSetImpl.union (fv_tm_tm_constraint p) (fv_tm_tm_tm u))).
Proof.
  apply (tm_mutind
    (fun a => forall k u, AtomSetImpl.Subset (fv_tm_tm_tm (open_tm_wrt_tm_rec k u a))
                 (AtomSetImpl.union (fv_tm_tm_tm a) (fv_tm_tm_tm u)))
    (fun b => forall k u, AtomSetImpl.Subset (fv_tm_tm_brs (open_brs_wrt_tm_rec k u b))
                 (AtomSetImpl.union (fv_tm_tm_brs b) (fv_tm_tm_tm u)))
    (fun g => forall k u, AtomSetImpl.Subset (fv_tm_tm_co (open_co_wrt_tm_rec k u g))
                 (AtomSetImpl.union (fv_tm_tm_co g) (fv_tm_tm_tm u)))
    (fun p => forall k u, AtomSetImpl.Subset (fv_tm_tm_constraint (open_constraint_wrt_tm_rec k u p))
                 (AtomSetImpl.union (fv_tm_tm_constraint p) (fv_tm_tm_tm u)))).
  all: intros; cbn [open_tm_wrt_tm open_tm_wrt_tm_rec open_brs_wrt_tm_rec
                       open_co_wrt_tm open_co_wrt_tm_rec
                       open_constraint_wrt_tm_rec fv_tm_tm_tm fv_tm_tm_brs
                       fv_tm_tm_co fv_tm_tm_constraint] in *.
  all: try (repeat match goal with
             H : context [lt_eq_lt_dec ?n ?k] |- _ =>
             destruct (lt_eq_lt_dec n k) as [[?|?]|?] end).
  all: try (repeat match goal with
             |- context [lt_eq_lt_dec ?n ?k] =>
             destruct (lt_eq_lt_dec n k) as [[?|?]|?] end).
  all: try (cbn [fv_tm_tm_tm fv_tm_tm_brs fv_tm_tm_co fv_tm_tm_constraint] in *).
  all: try (repeat match goal with
             H : forall (k0:nat) (u0:tm), AtomSetImpl.Subset _ _ |- _ =>
             let H1 := fresh in let H2 := fresh in
             pose proof (H k u) as H1; pose proof (H (S k) u) as H2; clear H end).
  all: try (repeat match goal with
             H : AtomSetImpl.Subset _ _ |- _ =>
             unfold AtomSetImpl.Subset in H end).
  all: try (unfold AtomSetImpl.Subset; intros y Hy;
            repeat match goal with
              H : forall a : atom, a `in` _ -> a `in` _ |- _ =>
              specialize (H y)
            end;
            repeat match goal with
              H : y `in` AtomSetImpl.union ?s ?t |- _ =>
              let H' := fresh in destruct (AtomSetImpl.union_1 H) as [H'|H'];
              clear H
            end;
            eauto 30 using AtomSetImpl.union_2, AtomSetImpl.union_3).
  all: try (unfold AtomSetImpl.Subset; intros; fsetdec).
Qed.

Lemma fv_open_tm_subset_pd : forall a u,
  AtomSetImpl.Subset (fv_tm_tm_tm (open_tm_wrt_tm a u))
                     (AtomSetImpl.union (fv_tm_tm_tm a) (fv_tm_tm_tm u)).
Proof. intros. exact (proj1 fv_open_tm_subset_all a 0 u). Qed.

Lemma notin_fv_open_self_tm : forall a k x,
  x `notin` fv_tm_tm_tm (open_tm_wrt_tm_rec k (a_Var_f x) a) -> x `notin` fv_tm_tm_tm a.
Proof.
  intros a k x H. intro Hin. apply H.
  unfold AtomSetImpl.Subset in *.
  exact ((proj1 fv_tm_tm_open_self_all a k x x) Hin).
Qed.

Lemma notin_fv_open_self_brs : forall b k x,
  x `notin` fv_tm_tm_brs (open_brs_wrt_tm_rec k (a_Var_f x) b) -> x `notin` fv_tm_tm_brs b.
Proof.
  intros b k x H. intro Hin. apply H.
  unfold AtomSetImpl.Subset in *.
  exact ((proj1 (proj2 fv_tm_tm_open_self_all) b k x x) Hin).
Qed.

Lemma notin_fv_open_self_co : forall g k x,
  x `notin` fv_tm_tm_co (open_co_wrt_tm_rec k (a_Var_f x) g) -> x `notin` fv_tm_tm_co g.
Proof.
  intros g k x H. intro Hin. apply H.
  unfold AtomSetImpl.Subset in *.
  exact ((proj1 (proj2 (proj2 fv_tm_tm_open_self_all)) g k x x) Hin).
Qed.

Lemma notin_fv_open_self_constraint : forall p k x,
  x `notin` fv_tm_tm_constraint (open_constraint_wrt_tm_rec k (a_Var_f x) p) ->
  x `notin` fv_tm_tm_constraint p.
Proof.
  intros p k x H. intro Hin. apply H.
  unfold AtomSetImpl.Subset in *.
  exact ((proj2 (proj2 (proj2 fv_tm_tm_open_self_all)) p k x x) Hin).
Qed.


Lemma subset_empty_l : forall s, AtomSetImpl.Subset AtomSetImpl.empty s.
Proof. intros s z Hz. apply AtomSetImpl.empty_1 in Hz. contradiction. Qed.

Lemma subset_refl_set : forall s, AtomSetImpl.Subset s s.
Proof. intros s z Hz; exact Hz. Qed.

Lemma subset_union_both : forall s1 s2 t1 t2,
  AtomSetImpl.Subset s1 t1 -> AtomSetImpl.Subset s2 t2 ->
  AtomSetImpl.Subset (AtomSetImpl.union s1 s2) (AtomSetImpl.union t1 t2).
Proof.
  intros s1 s2 t1 t2 H1 H2 z Hz.
  apply AtomSetImpl.union_1 in Hz. destruct Hz as [Hz|Hz].
  - apply AtomSetImpl.union_2. unfold AtomSetImpl.Subset in H1. apply H1. exact Hz.
  - apply AtomSetImpl.union_3. unfold AtomSetImpl.Subset in H2. apply H2. exact Hz.
Qed.

Lemma subset_union_l : forall s1 t1 s2,
  AtomSetImpl.Subset s1 t1 ->
  AtomSetImpl.Subset (AtomSetImpl.union s1 s2) (AtomSetImpl.union t1 s2).
Proof. intros. apply subset_union_both; [assumption|apply subset_refl_set]. Qed.

Lemma subset_union_r : forall s1 t1 s2,
  AtomSetImpl.Subset s1 t1 ->
  AtomSetImpl.Subset (AtomSetImpl.union s2 s1) (AtomSetImpl.union s2 t1).
Proof. intros. apply subset_union_both; [apply subset_refl_set|assumption]. Qed.

(* If opening at level [k] with a fresh name introduces no free occurrence
   of that name, then opening with any term introduces no new free names. *)
Lemma fv_open_subset_of_rho_all :
  (forall a k y u, y `notin` fv_tm_tm_tm a ->
     y `notin` fv_tm_tm_tm (open_tm_wrt_tm_rec k (a_Var_f y) a) ->
     AtomSetImpl.Subset (fv_tm_tm_tm (open_tm_wrt_tm_rec k u a)) (fv_tm_tm_tm a)) /\
  (forall b k y u, y `notin` fv_tm_tm_brs b ->
     y `notin` fv_tm_tm_brs (open_brs_wrt_tm_rec k (a_Var_f y) b) ->
     AtomSetImpl.Subset (fv_tm_tm_brs (open_brs_wrt_tm_rec k u b)) (fv_tm_tm_brs b)) /\
  (forall g k y u, y `notin` fv_tm_tm_co g ->
     y `notin` fv_tm_tm_co (open_co_wrt_tm_rec k (a_Var_f y) g) ->
     AtomSetImpl.Subset (fv_tm_tm_co (open_co_wrt_tm_rec k u g)) (fv_tm_tm_co g)) /\
  (forall p k y u, y `notin` fv_tm_tm_constraint p ->
     y `notin` fv_tm_tm_constraint (open_constraint_wrt_tm_rec k (a_Var_f y) p) ->
     AtomSetImpl.Subset (fv_tm_tm_constraint (open_constraint_wrt_tm_rec k u p))
                        (fv_tm_tm_constraint p)).
Proof.
  apply (tm_mutind
    (fun a => forall k y u, y `notin` fv_tm_tm_tm a ->
       y `notin` fv_tm_tm_tm (open_tm_wrt_tm_rec k (a_Var_f y) a) ->
       AtomSetImpl.Subset (fv_tm_tm_tm (open_tm_wrt_tm_rec k u a)) (fv_tm_tm_tm a))
    (fun b => forall k y u, y `notin` fv_tm_tm_brs b ->
       y `notin` fv_tm_tm_brs (open_brs_wrt_tm_rec k (a_Var_f y) b) ->
       AtomSetImpl.Subset (fv_tm_tm_brs (open_brs_wrt_tm_rec k u b)) (fv_tm_tm_brs b))
    (fun g => forall k y u, y `notin` fv_tm_tm_co g ->
       y `notin` fv_tm_tm_co (open_co_wrt_tm_rec k (a_Var_f y) g) ->
       AtomSetImpl.Subset (fv_tm_tm_co (open_co_wrt_tm_rec k u g)) (fv_tm_tm_co g))
    (fun p => forall k y u, y `notin` fv_tm_tm_constraint p ->
       y `notin` fv_tm_tm_constraint (open_constraint_wrt_tm_rec k (a_Var_f y) p) ->
       AtomSetImpl.Subset (fv_tm_tm_constraint (open_constraint_wrt_tm_rec k u p))
                          (fv_tm_tm_constraint p))).
  all: intros; cbn [open_tm_wrt_tm_rec open_brs_wrt_tm_rec
                       open_co_wrt_tm_rec open_constraint_wrt_tm_rec
                       fv_tm_tm_tm fv_tm_tm_brs fv_tm_tm_co fv_tm_tm_constraint] in *.
  all: try (repeat match goal with
             |- context [lt_eq_lt_dec ?a ?b] =>
             destruct (lt_eq_lt_dec a b) as [[?|?]|?] end).
  all: try (repeat match goal with
             H : context [lt_eq_lt_dec ?a ?b] |- _ =>
             destruct (lt_eq_lt_dec a b) as [[?|?]|?] end).
  all: try (cbn [fv_tm_tm_tm fv_tm_tm_brs fv_tm_tm_co fv_tm_tm_constraint] in *).
  all: try notin_split_all.
  all: try (exfalso; fsetdec).
  all: try (eauto 25 using subset_union_both, subset_union_l, subset_union_r,
              subset_empty_l, subset_refl_set,
              notin_fv_open_self_tm, notin_fv_open_self_brs,
              notin_fv_open_self_co, notin_fv_open_self_constraint).
  all: try (unfold AtomSetImpl.Subset; intros; fsetdec).
Qed.

Lemma fv_open_subset_of_rho_tm : forall a y u,
  y `notin` fv_tm_tm_tm a ->
  y `notin` fv_tm_tm_tm (open_tm_wrt_tm a (a_Var_f y)) ->
  AtomSetImpl.Subset (fv_tm_tm_tm (open_tm_wrt_tm a u)) (fv_tm_tm_tm a).
Proof. intros. exact (proj1 fv_open_subset_of_rho_all a 0 y u H H0). Qed.

Lemma notin_empty : forall (x:atom), x `notin` AtomSetImpl.empty.
Proof. intros x H. apply AtomSetImpl.empty_1 in H. contradiction. Qed.

Lemma notin_union_intro : forall (x:atom) (s t:vars),
  x `notin` s -> x `notin` t -> x `notin` AtomSetImpl.union s t.
Proof.
  intros x s t Hs Ht Hin.
  apply AtomSetImpl.union_1 in Hin. destruct Hin as [Hin|Hin].
  - apply Hs. exact Hin.
  - apply Ht. exact Hin.
Qed.

Lemma fv_erase_FixDef_empty : forall x, x `notin` fv_tm_tm_tm (erase_tm FixDef).
Proof.
  intros x. unfold FixDef. cbn [erase_tm fv_tm_tm_tm]. fsetdec.
Qed.

(* Head reduction preserves avoidance of a name in the erasure, provided
   the source term is well typed. *)
Lemma head_reduction_erase_fv_subset :
  forall G a a', head_reduction G a a' ->
  forall T, AnnTyping G a T ->
  forall x, x `notin` fv_tm_tm_tm (erase_tm a) ->
            x `notin` fv_tm_tm_tm (erase_tm a').
Proof.
  intros G a a' Hred. induction Hred; intros T Hty x Hx.
  (* An_AppLeft *)
  - destruct (AnnTyping_App_inv G a rho b T Hty) as (A0 & B0 & HT & Hfun & Harg).
    cbn [erase_tm fv_tm_tm_tm] in Hx.
    destruct rho; cbn [erase_tm fv_tm_tm_tm] in Hx.
    + apply notin_union_elim in Hx. destruct Hx as [Ha Hb].
      cbn [erase_tm fv_tm_tm_tm].
      apply notin_union_intro.
      * exact (IHHred (a_Pi Rel A0 B0) Hfun x Ha).
      * exact Hb.
    + apply notin_union_elim in Hx. destruct Hx as [Ha _].
      cbn [erase_tm fv_tm_tm_tm].
      apply notin_union_intro.
      * exact (IHHred (a_Pi Irrel A0 B0) Hfun x Ha).
      * apply notin_empty.
  (* An_AppAbs *)
  - destruct (AnnTyping_App_inv G (a_Abs rho A w) rho a T Hty)
      as (A0 & B0 & HT & Hfun & Harg).
    destruct rho.
    + (* Rel *)
      cbn [erase_tm fv_tm_tm_tm] in Hx.
      apply notin_union_elim in Hx. destruct Hx as [Hw Ha].
      unfold open_tm_wrt_tm.
      rewrite (proj1 erase_open_tm_tm_all w 0 a).
      fold (open_tm_wrt_tm (erase_tm w) (erase_tm a)).
      intro Hin.
      apply fv_open_tm_subset_pd in Hin.
      exact (notin_union_intro x _ _ Hw Ha Hin).
    + (* Irrel *)
      cbn [erase_tm fv_tm_tm_tm] in Hx.
      assert (HA0 : A0 = A) by (inversion Hfun; reflexivity).
      subst A0.
      destruct (AnnTyping_Abs_inv G Irrel A w B0 Hfun)
        as (L0 & HtyA0 & Hbody & Hrho).
      set (S0 := AtomSetImpl.union L0 (fv_tm_tm_tm (erase_tm w))).
      destruct (atom_fresh S0) as [y Hy].
      apply notin_union_elim in Hy. destruct Hy as [HyL0 HyFw].
      unfold open_tm_wrt_tm.
      rewrite (proj1 erase_open_tm_tm_all w 0 a).
      fold (open_tm_wrt_tm (erase_tm w) (erase_tm a)).
      assert (HyOpen : y `notin` fv_tm_tm_tm (open_tm_wrt_tm (erase_tm w) (a_Var_f y))).
      { rewrite <- erase_open_tm_var. exact (RhoCheck_irrel_inv y _ (Hrho y HyL0)). }
      pose proof (fv_open_subset_of_rho_tm (erase_tm w) y (erase_tm a) HyFw HyOpen) as Hsub.
      apply notin_union_elim in Hx. destruct Hx as [Hxw _].
      intro Hin. apply Hsub in Hin. exact (Hxw Hin).
  (* An_CAppLeft *)
  - destruct (AnnTyping_CApp_inv G a g T Hty) as (B0 & a0 & b0 & A0 & HT & Hfun & Hdef).
    cbn [erase_tm fv_tm_tm_tm] in Hx.
    apply notin_union_elim in Hx. destruct Hx as [Hxa Hxg].
    cbn [erase_tm fv_tm_tm_tm].
    exact (notin_union_intro x _ _
             (IHHred (a_CPi (Eq a0 b0 A0) B0) Hfun x Hxa) Hxg).
  (* An_CAppCAbs *)
  - cbn [erase_tm fv_tm_tm_tm] in Hx.
    apply notin_union_elim in Hx. destruct Hx as [Hxb _].
    rewrite erase_open_co_tm.
    cbn [erase_tm fv_tm_tm_tm].
    exact Hxb.
  (* An_AbsTerm *)
  - inversion Hty; subst.
    rename H1 into IHAbs.
    rename H8 into Hbody.
    rename H9 into Hrho.
    cbn [erase_tm fv_tm_tm_tm] in Hx.
    cbn [erase_tm fv_tm_tm_tm].
    set (S0 := AtomSetImpl.union L
                 (AtomSetImpl.union L0
                    (AtomSetImpl.union (fv_tm_tm_tm (erase_tm b))
                       (AtomSetImpl.union (fv_tm_tm_tm (erase_tm b'))
                          (AtomSetImpl.singleton x))))).
    destruct (atom_fresh S0) as [y Hy].
    apply notin_union_elim in Hy. destruct Hy as [HyL HyRest].
    apply notin_union_elim in HyRest. destruct HyRest as [HyL0 HyRest].
    apply notin_union_elim in HyRest. destruct HyRest as [Hyb HyRest].
    apply notin_union_elim in HyRest. destruct HyRest as [Hyb' Hyx].
    assert (HyOpenB : x `notin` fv_tm_tm_tm (erase_tm (open_tm_wrt_tm b (a_Var_f y)))).
    { rewrite erase_open_tm_var.
      change (x `notin` fv_tm_tm_tm (open_tm_wrt_tm (erase_tm b) (a_Var_f y))).
      intro Hin. apply fv_open_tm_subset_pd in Hin.
      apply AtomSetImpl.union_1 in Hin. destruct Hin as [Hinb|Hinb].
      - exact (Hx Hinb).
      - apply AtomSetFacts.singleton_iff in Hinb.
        exact (Hyx (AtomSetImpl.singleton_2 (eq_sym Hinb))). }
    pose proof (IHAbs y HyL (open_tm_wrt_tm B (a_Var_f y))
                  (Hbody y HyL0) x HyOpenB) as Hnot.
    rewrite erase_open_tm_var in Hnot.
    intro Hin. apply Hnot.
    change (x `in` fv_tm_tm_tm (open_tm_wrt_tm (erase_tm b') (a_Var_f y))).
    apply (proj1 fv_tm_tm_open_self_all (erase_tm b') 0 y). exact Hin.
  (* An_Axiom *)
  - inversion Hty; subst.
    destruct (an_toplevel_binds_ax F a A H) as [Ha HA]. subst a.
    cbn [erase_tm fv_tm_tm_tm] in Hx.
    cbn [erase_tm fv_tm_tm_tm].
    apply fv_erase_FixDef_empty.
  (* An_ConvTerm *)
  - destruct (AnnTyping_Conv_inv G a g T Hty) as (A0 & Ha & Hdef & Hstar).
    cbn [erase_tm fv_tm_tm_tm] in Hx.
    cbn [erase_tm fv_tm_tm_tm].
    exact (IHHred A0 Ha x Hx).
  (* An_Combine *)
  - cbn [erase_tm fv_tm_tm_tm] in Hx.
    cbn [erase_tm fv_tm_tm_tm].
    exact Hx.
  (* An_Push *)
  - subst b'. cbn [erase_tm fv_tm_tm_tm] in Hx.
    destruct rho; cbn [erase_tm fv_tm_tm_tm] in *.
    + apply notin_union_elim in Hx. destruct Hx as [Hv Hb].
      cbn [erase_tm fv_tm_tm_tm].
      exact (notin_union_intro x _ _ Hv Hb).
    + apply notin_union_elim in Hx. destruct Hx as [Hv _].
      cbn [erase_tm fv_tm_tm_tm].
      exact (notin_union_intro x _ _ Hv (notin_empty x)).
  (* An_CPush *)
  - subst g1'. subst g'. cbn [erase_tm fv_tm_tm_tm] in *.
    cbn [erase_tm fv_tm_tm_tm]. exact Hx.
Qed.

(* ===== WfDev ===== *)
From Stdlib Require Import List.
Import ListNotations.

(* ============ fresh-name sets for contexts ============ *)

Fixpoint fv_context_w (G:context) : vars :=
  match G with
  | nil => {}
  | (y,s) :: G' => AtomSetImpl.union (fv_sort s) (fv_context_w G')
  end.

Lemma notin_fv_context_w : forall G x,
  x `notin` fv_context_w G ->
  forall y s, binds y s G -> x `notin` fv_sort s.
Proof.
  intros G. induction G as [|[y s] G IH]; intros x H z t Hb.
  - unfold binds in Hb. cbn in Hb. contradiction.
  - cbn [fv_context_w] in H. apply notin_union_elim in H. destruct H as [Hs HG].
    unfold binds in Hb. cbn [binds] in Hb. destruct Hb as [Heq|Hin].
    + inversion Heq. subst. exact Hs.
    + apply (IH x HG z t Hin).
Qed.

Fixpoint fvx_context_w (G:context) : vars :=
  match G with
  | nil => {}
  | (y,s) :: G' => AtomSetImpl.union (fvx_sort s) (fvx_context_w G')
  end.

Lemma notin_fvx_context_w : forall G x,
  x `notin` fvx_context_w G ->
  forall y s, binds y s G -> x `notin` fvx_sort s.
Proof.
  intros G. induction G as [|[y s] G IH]; intros x H z t Hb.
  - unfold binds in Hb. cbn in Hb. contradiction.
  - cbn [fvx_context_w] in H. apply notin_union_elim in H. destruct H as [Hs HG].
    unfold binds in Hb. cbn [binds] in Hb. destruct Hb as [Heq|Hin].
    + inversion Heq. subst. exact Hs.
    + apply (IH x HG z t Hin).
Qed.

(* ============ well-formed contexts bind well-typed sorts ============ *)

Lemma ctx_sub_cons_l_w : forall G x s, ctx_sub G ((x,s)::G).
Proof.
  intros G x s y t Hb. apply binds_cons_iff. right. exact Hb.
Qed.

Scheme AnnCtx_ind_simple := Induction for AnnCtx Sort Prop.

Lemma AnnCtx_binds_wf_all_w : forall G, AnnCtx G ->
  ((forall x A, binds x (Tm A) G -> AnnTyping G A a_Star) /\
   (forall c phi, binds c (Co phi) G -> AnnPropWff G phi)).
Proof.
  apply (AnnCtx_ind_simple (fun G _ =>
    ((forall x A, binds x (Tm A) G -> AnnTyping G A a_Star) /\
     (forall c phi, binds c (Co phi) G -> AnnPropWff G phi)))).
  - split.
    + intros y B Hb. inversion Hb.
    + intros d p Hd. inversion Hd.
  - intros G x A Hctx IH HA Hnin. destruct IH as [IHtm IHco]. split.
    + intros y B Hb. apply binds_cons_iff in Hb. destruct Hb as [[Heq Hs]|Hb].
      * inversion Heq; subst. inversion Hs; subst.
        apply (AnnTyping_weaken G A a_Star HA ((x, Tm A) :: G)).
        -- apply ctx_sub_cons_l_w.
        -- apply An_ConsTm; assumption.
      * apply (AnnTyping_weaken G B a_Star (IHtm y B Hb) ((x, Tm A) :: G)).
        -- apply ctx_sub_cons_l_w.
        -- apply An_ConsTm; assumption.
    + intros d p Hd. apply binds_cons_iff in Hd. destruct Hd as [[Heq Hs]|Hd].
      * inversion Heq; subst. inversion Hs.
      * apply (AnnPropWff_weaken G p (IHco d p Hd) ((x, Tm A) :: G)).
        -- apply ctx_sub_cons_l_w.
        -- apply An_ConsTm; assumption.
  - intros G c phi Hctx IH Hphi Hnin. destruct IH as [IHtm IHco]. split.
    + intros y B Hb. apply binds_cons_iff in Hb. destruct Hb as [[Heq Hs]|Hb].
      * inversion Heq; subst. inversion Hs.
      * apply (AnnTyping_weaken G B a_Star (IHtm y B Hb) ((c, Co phi) :: G)).
        -- apply ctx_sub_cons_l_w.
        -- apply An_ConsCo; assumption.
    + intros d p Hd. apply binds_cons_iff in Hd. destruct Hd as [[Heq Hs]|Hd].
      * inversion Heq; subst. inversion Hs; subst.
        apply (AnnPropWff_weaken G phi Hphi ((c, Co phi) :: G)).
        -- apply ctx_sub_cons_l_w.
        -- apply An_ConsCo; assumption.
      * apply (AnnPropWff_weaken G p (IHco d p Hd) ((c, Co phi) :: G)).
        -- apply ctx_sub_cons_l_w.
        -- apply An_ConsCo; assumption.
Qed.

Definition AnnCtx_binds_Tm_typing_w : forall G x A,
  AnnCtx G -> binds x (Tm A) G -> AnnTyping G A a_Star :=
  fun G x A Hctx Hb => proj1 (AnnCtx_binds_wf_all_w G Hctx) x A Hb.

Definition AnnCtx_binds_Co_wff_w : forall G c phi,
  AnnCtx G -> binds c (Co phi) G -> AnnPropWff G phi :=
  fun G c phi Hctx Hb => proj2 (AnnCtx_binds_wf_all_w G Hctx) c phi Hb.

(* ============ well-typedness of types ============ *)

Lemma AnnTyping_open_body_star_w : forall G rho A B a,
  AnnTyping G (a_Pi rho A B) a_Star ->
  AnnTyping G a A ->
  AnnTyping G (open_tm_wrt_tm B a) a_Star.
Proof.
  intros G rho A B a Hpi Ha.
  destruct (AnnTyping_Pi_inv G rho A B Hpi) as (L & Hbody & Hdom).
  pose proof (AnnTyping_AnnCtx G (a_Pi rho A B) a_Star Hpi) as HctxG.
  pose proof (proj1 (AnnTyping_wf G a A Ha)) as Hlca.
  set (S := AtomSetImpl.union L
              (AtomSetImpl.union (fv_context_w G)
                 (AtomSetImpl.union (fv_tm_tm_tm A)
                    (AtomSetImpl.union (fv_tm_tm_tm B) (fv_tm_tm_tm a))))).
  destruct (atom_fresh S) as [x HxS].
  apply notin_union_elim in HxS. destruct HxS as [HxL HxS].
  apply notin_union_elim in HxS. destruct HxS as [Hxctx HxS].
  apply notin_union_elim in HxS. destruct HxS as [HxA HxS].
  apply notin_union_elim in HxS. destruct HxS as [HxB Hxa].
  assert (Hsubctx : subTm_ctx x a G = G).
  { apply subTm_ctx_id. intros y s Hb. apply (notin_fv_context_w G x Hxctx y s Hb). }
  assert (HctxSub : AnnCtx (subTm_ctx x a nil ++ subTm_ctx x a G)).
  { change (AnnCtx (subTm_ctx x a G)). rewrite Hsubctx. exact HctxG. }
  assert (Hhyp : forall G', ctx_sub (subTm_ctx x a G) G' ->
                           AnnCtx G' -> AnnTyping G' a A).
  { intros G' Hsub Hctx'. rewrite Hsubctx in Hsub.
    exact (AnnTyping_weaken G a A Ha G' Hsub Hctx'). }
  pose proof (proj1 AnnTyping_subst_tm_all
    ((x ~ Tm A) ++ G) (open_tm_wrt_tm B (a_Var_f x)) a_Star
    (Hbody x HxL) nil G x A a eq_refl HxA Hlca HctxSub Hhyp) as Hres.
  change (AnnTyping (subTm_ctx x a G)
            (subst_tm_tm x a (open_tm_wrt_tm B (a_Var_f x))) a_Star) in Hres.
  rewrite Hsubctx in Hres.
  rewrite (subst_tm_open_tm_var B x a x Hlca) in Hres.
  rewrite subst_tm_tm_var_eq in Hres.
  rewrite ((proj1 subst_tm_tm_id_notin_all) B x a HxB) in Hres.
  exact Hres.
Qed.

Lemma AnnTyping_capp_body_star_w : forall G g B a0 b0 A1,
  AnnTyping G (a_CPi (Eq a0 b0 A1) B) a_Star ->
  AnnDefEq G (dom G) g a0 b0 ->
  AnnTyping G (open_tm_wrt_co B g) a_Star.
Proof.
  intros G g B a0 b0 A1 Hpi Hdef.
  destruct (AnnTyping_CPi_inv G (Eq a0 b0 A1) B Hpi) as (L & Hwff & Hbody).
  pose proof (AnnTyping_AnnCtx G (a_CPi (Eq a0 b0 A1) B) a_Star Hpi) as HctxG.
  pose proof (proj1 (AnnDefEq_wf G (dom G) g a0 b0 Hdef)) as Hlcg.
  set (S := AtomSetImpl.union L
              (AtomSetImpl.union (fvx_constraint (Eq a0 b0 A1))
                 (AtomSetImpl.union (fvx_tm B) (fvx_context_w G)))).
  destruct (atom_fresh S) as [c HcS].
  apply notin_union_elim in HcS. destruct HcS as [HcL HcS].
  apply notin_union_elim in HcS. destruct HcS as [HcPhi HcS].
  apply notin_union_elim in HcS. destruct HcS as [HcB Hcctx].
  assert (HsubCtxId : subCo_ctx c g G = G).
  { apply subCo_ctx_id. intros y s Hb. apply (notin_fvx_context_w G c Hcctx y s Hb). }
  assert (HctxSub : AnnCtx (subCo_ctx c g nil ++ subCo_ctx c g G)).
  { change (AnnCtx (subCo_ctx c g G)). rewrite HsubCtxId. exact HctxG. }
  assert (HHyp : CoRemovedHypDom c G (Eq a0 b0 A1) g).
  { intros G' a b' A Heq HsubG' HctxG'.
    injection Heq as Ha Hb HA. subst a. subst b'. subst A.
    rewrite HsubCtxId in HsubG'.
    pose proof (AnnDefEq_weaken G (dom G) g a0 b0 Hdef G' HsubG' HctxG') as Hw.
    exact (AnnDefEq_Dmono G' (dom G) (dom G') g a0 b0
             (dom_sub G G' HsubG') Hw). }
  pose proof (proj1 AnnTyping_subst_co_dom
    ((c ~ Co (Eq a0 b0 A1)) ++ G)
    (open_tm_wrt_co B (g_Var_f c)) a_Star
    (Hbody c HcL) nil G c (Eq a0 b0 A1) g eq_refl HcPhi Hlcg HctxSub HHyp) as Hres.
  change (AnnTyping (subCo_ctx c g G)
            (subst_co_tm c g (open_tm_wrt_co B (g_Var_f c))) a_Star) in Hres.
  rewrite HsubCtxId in Hres.
  rewrite (subst_co_open_tm_co_h B c g (g_Var_f c) Hlcg) in Hres.
  rewrite subst_co_co_var_eq in Hres.
  rewrite ((proj1 subst_co_tm_id_fresh_all) B c g HcB) in Hres.
  exact Hres.
Qed.

Lemma AnnTyping_type_wf_w : forall G t T, AnnTyping G t T -> AnnTyping G T a_Star.
Proof.
  apply (AnnTyping_comb
    (fun G t T _ => AnnTyping G T a_Star)
    (fun _ _ _ => True)
    (fun _ _ _ _ _ _ => True)
    (fun _ _ _ _ _ _ => True)
    (fun _ _ => True)
    (fun _ _ => True)).
  all: try (intros; exact I).
  - intros G Hctx IHctx. exact (An_Star G Hctx).
  - intros G x A Hctx IHctx Hb. exact (AnnCtx_binds_Tm_typing_w G x A Hctx Hb).
  - intros L G rho A B body IHbody A0 IH0.
    exact (An_Star G (AnnTyping_AnnCtx G A a_Star A0)).
  - intros L G rho A a B A0 IH0 body IHbody r.
    apply (An_Pi L G rho A B).
    + intros x Hx. apply IHbody; exact Hx.
    + exact A0.
  - intros G b rho a B A Hfun IHfun Harg IHarg.
    exact (AnnTyping_open_body_star_w G rho A B a IHfun Harg).
  - intros G a g B A Hsrc IHsrc Hdef IHdef Hstar IHstar.
    exact Hstar.
  - intros L G phi B Hwff IHwff body IHbody.
    exact (An_Star G (AnnPropWff_AnnCtx G phi Hwff)).
  - intros L G phi a B Hwff IHwff body IHbody.
    apply (An_CPi L G phi B Hwff).
    intros c Hc. apply IHbody; exact Hc.
  - intros G a1 g B a b A1 Hfun IHfun Hdef IHdef.
    exact (AnnTyping_capp_body_star_w G g B a b A1 IHfun Hdef).
  - intros G F A a Hctx IHctx Hb HtyA IHA.
    exact (AnnTyping_weaken nil A a_Star HtyA G (ctx_sub_nil G) Hctx).
Qed.

(* ===== PresDev2 ===== *)
From Stdlib Require Import List.
Import ListNotations.

Fixpoint fv_context (G:context) : vars :=
  match G with
  | nil => {}
  | (y,s) :: G' => AtomSetImpl.union (fv_sort s) (fv_context G')
  end.

Lemma notin_fv_context : forall G x,
  x `notin` fv_context G ->
  forall y s, binds y s G -> x `notin` fv_sort s.
Proof.
  intros G. induction G as [|[y s] G IH]; intros x H z t Hb.
  - unfold binds in Hb. cbn in Hb. contradiction.
  - cbn [fv_context] in H. apply notin_union_elim in H. destruct H as [Hs HG].
    unfold binds in Hb. cbn [binds] in Hb. destruct Hb as [Heq|Hin].
    + inversion Heq. subst. exact Hs.
    + apply (IH x HG z t Hin).
Qed.

Fixpoint fvx_context (G:context) : vars :=
  match G with
  | nil => {}
  | (y,s) :: G' => AtomSetImpl.union (fvx_sort s) (fvx_context G')
  end.

Lemma notin_fvx_context : forall G x,
  x `notin` fvx_context G ->
  forall y s, binds y s G -> x `notin` fvx_sort s.
Proof.
  intros G. induction G as [|[y s] G IH]; intros x H z t Hb.
  - unfold binds in Hb. cbn in Hb. contradiction.
  - cbn [fvx_context] in H. apply notin_union_elim in H. destruct H as [Hs HG].
    unfold binds in Hb. cbn [binds] in Hb. destruct Hb as [Heq|Hin].
    + inversion Heq. subst. exact Hs.
    + apply (IH x HG z t Hin).
Qed.

Theorem preservation : forall G a A, AnnTyping G a A -> forall a', head_reduction G a a' -> AnnTyping G a' A.
Proof.
  intros G a0 T Hty a' Hred.
  revert T Hty.
  induction Hred; intros T Hty.
  (* An_AppLeft *)
  - destruct (AnnTyping_App_inv G a rho b T Hty) as (A0 & B0 & HT & Hfun & Harg).
    subst T.
    apply (An_App G a' rho b B0 A0).
    + exact (IHHred (a_Pi rho A0 B0) Hfun).
    + exact Harg.
  (* An_AppAbs *)
  - destruct (AnnTyping_App_inv G (a_Abs rho A w) rho a T Hty)
      as (A0 & B0 & HT & Hfun & Harg).
    subst T.
    assert (HA0 : A0 = A) by (inversion Hfun; reflexivity).
    subst A0.
    destruct (AnnTyping_Abs_inv G rho A w B0 Hfun)
      as (L0 & HtyA & Hbody & Hrho).
    pose proof (AnnTyping_AnnCtx G (a_App (a_Abs rho A w) rho a)
                  (open_tm_wrt_tm B0 a) Hty) as HctxG.
    set (S := AtomSetImpl.union (fv_context G)
                (AtomSetImpl.union (fv_tm_tm_tm A)
                   (AtomSetImpl.union (fv_tm_tm_tm a)
                      (AtomSetImpl.union (fv_tm_tm_tm w)
                         (AtomSetImpl.union (fv_tm_tm_tm B0) L0))))).
    destruct (atom_fresh S) as [x HxS].
    apply notin_union_elim in HxS. destruct HxS as [Hxctx HxS].
    apply notin_union_elim in HxS. destruct HxS as [HxA HxS].
    apply notin_union_elim in HxS. destruct HxS as [Hxa HxS].
    apply notin_union_elim in HxS. destruct HxS as [Hxw HxS].
    apply notin_union_elim in HxS. destruct HxS as [HxB HxL0].
    assert (Hsubctx : subTm_ctx x a G = G).
    { apply subTm_ctx_id. intros y s Hb. apply (notin_fv_context G x Hxctx y s Hb). }
    assert (HctxSub : AnnCtx (subTm_ctx x a nil ++ subTm_ctx x a G)).
    { change (AnnCtx (subTm_ctx x a G)). rewrite Hsubctx. exact HctxG. }
    assert (Hhyp : forall G', ctx_sub (subTm_ctx x a G) G' ->
                             AnnCtx G' -> AnnTyping G' a A).
    { intros G' Hsub Hctx'. rewrite Hsubctx in Hsub.
      exact (AnnTyping_weaken G a A Harg G' Hsub Hctx'). }
    pose proof (proj1 AnnTyping_subst_tm_all
      ((x ~ Tm A) ++ G) (open_tm_wrt_tm w (a_Var_f x))
      (open_tm_wrt_tm B0 (a_Var_f x)) (Hbody x HxL0)
      nil G x A a eq_refl HxA H HctxSub Hhyp) as Hres.
    change (AnnTyping (subTm_ctx x a G)
        (subst_tm_tm x a (open_tm_wrt_tm w (a_Var_f x)))
        (subst_tm_tm x a (open_tm_wrt_tm B0 (a_Var_f x)))) in Hres.
    rewrite Hsubctx in Hres.
    rewrite (subst_tm_open_tm_var w x a x H) in Hres.
    rewrite (subst_tm_open_tm_var B0 x a x H) in Hres.
    rewrite ((proj1 subst_tm_tm_id_notin_all) w x a Hxw) in Hres.
    rewrite ((proj1 subst_tm_tm_id_notin_all) B0 x a HxB) in Hres.
    rewrite subst_tm_tm_var_eq in Hres.
    exact Hres.
  (* An_CAppLeft *)
  - destruct (AnnTyping_CApp_inv G a g T Hty) as (B0 & a0 & b0 & A0 & HT & Hfun & Hdef).
    subst T.
    apply (An_CApp G a' g B0 a0 b0 A0).
    + exact (IHHred (a_CPi (Eq a0 b0 A0) B0) Hfun).
    + exact Hdef.
  (* An_CAppCAbs *)
  - destruct (AnnTyping_CApp_inv G (a_CAbs phi b) g T Hty)
      as (B0 & a0 & b0 & A1 & HT & Hfun & Hdef).
    subst T.
    assert (HphiEq : phi = Eq a0 b0 A1) by (inversion Hfun; reflexivity).
    subst phi.
    destruct (AnnTyping_CAbs_inv G (Eq a0 b0 A1) b B0 Hfun)
      as (L & Hwff & Hbody).
    pose proof (AnnTyping_AnnCtx G (a_CApp (a_CAbs (Eq a0 b0 A1) b) g)
                  (open_tm_wrt_co B0 g) Hty) as HctxG.
    set (S := AtomSetImpl.union L
                (AtomSetImpl.union (fvx_constraint (Eq a0 b0 A1))
                   (AtomSetImpl.union (fvx_tm b)
                      (AtomSetImpl.union (fvx_tm B0) (fvx_context G))))).
    destruct (atom_fresh S) as [c HcS].
    apply notin_union_elim in HcS. destruct HcS as [HcL HcS].
    apply notin_union_elim in HcS. destruct HcS as [HcPhi HcS].
    apply notin_union_elim in HcS. destruct HcS as [Hcb HcS].
    apply notin_union_elim in HcS. destruct HcS as [HcB Hcctx].
    assert (HsubCtxId : subCo_ctx c g G = G).
    { apply subCo_ctx_id. intros y s Hb. apply (notin_fvx_context G c Hcctx y s Hb). }
    assert (HctxSub : AnnCtx (subCo_ctx c g nil ++ subCo_ctx c g G)).
    { change (AnnCtx (subCo_ctx c g G)). rewrite HsubCtxId. exact HctxG. }
    assert (HHyp : CoRemovedHypDom c G (Eq a0 b0 A1) g).
    { intros G' a b' A Heq HsubG' HctxG'.
      injection Heq as Ha Hb HA. subst a. subst b'. subst A.
      rewrite HsubCtxId in HsubG'.
      pose proof (AnnDefEq_weaken G (dom G) g a0 b0 Hdef G' HsubG' HctxG') as Hw.
      exact (AnnDefEq_Dmono G' (dom G) (dom G') g a0 b0
               (dom_sub G G' HsubG') Hw). }
    pose proof (proj1 AnnTyping_subst_co_dom
      ((c ~ Co (Eq a0 b0 A1)) ++ G)
      (open_tm_wrt_co b (g_Var_f c))
      (open_tm_wrt_co B0 (g_Var_f c))
      (Hbody c HcL)
      nil G c (Eq a0 b0 A1) g eq_refl HcPhi H1 HctxSub HHyp) as Hres.
    change (AnnTyping (subCo_ctx c g G)
              (subst_co_tm c g (open_tm_wrt_co b (g_Var_f c)))
              (subst_co_tm c g (open_tm_wrt_co B0 (g_Var_f c)))) in Hres.
    rewrite HsubCtxId in Hres.
    rewrite (subst_co_open_tm_co_h b c g (g_Var_f c) H1) in Hres.
    rewrite (subst_co_open_tm_co_h B0 c g (g_Var_f c) H1) in Hres.
    rewrite subst_co_co_var_eq in Hres.
    rewrite ((proj1 subst_co_tm_id_fresh_all) b c g Hcb) in Hres.
    rewrite ((proj1 subst_co_tm_id_fresh_all) B0 c g HcB) in Hres.
    exact Hres.
  (* An_AbsTerm *)
  - inversion Hty; subst.
    rename H1 into IHAbs.
    rename H8 into Hbody.
    rename H9 into Hrho.
    apply (An_Abs (AtomSetImpl.union L L0) G Irrel A b' B).
    + exact H6.
    + intros y Hy. apply notin_union_elim in Hy. destruct Hy as [HyL HyL0].
      exact (IHAbs y HyL (open_tm_wrt_tm B (a_Var_f y)) (Hbody y HyL0)).
    + intros y Hy. apply notin_union_elim in Hy. destruct Hy as [HyL HyL0].
      apply Rho_IrrRel.
      apply (head_reduction_erase_fv_subset ((y ~ Tm A) ++ G)
               (open_tm_wrt_tm b (a_Var_f y)) (open_tm_wrt_tm b' (a_Var_f y))
               (H0 y HyL) (open_tm_wrt_tm B (a_Var_f y)) (Hbody y HyL0) y).
      apply RhoCheck_irrel_inv. exact (Hrho y HyL0).
  (* An_Axiom *)
  - inversion Hty; subst.
    destruct (an_toplevel_binds_ax F a A H) as [Ha HA]. subst a.
    destruct (an_toplevel_binds_ax F a0 T H2) as [Ha0 HT]. subst a0. subst T.
    exact (AnnTyping_weaken nil FixDef FixTy AnnTyping_nil_FixDef G
             (ctx_sub_nil G) H1).
  (* An_ConvTerm *)
  - destruct (AnnTyping_Conv_inv G a g T Hty) as (A0 & Ha & Hdef & Hstar).
    apply (An_Conv G a' g T A0).
    + exact (IHHred A0 Ha).
    + exact Hdef.
    + exact Hstar.
  (* An_Combine *)
  - destruct (AnnTyping_Conv_inv G (a_Conv v g1) g2 T Hty)
      as (A0 & Hinner & Hdef2 & HstarT).
    destruct (AnnTyping_Conv_inv G v g1 A0 Hinner)
      as (A1 & Hv & Hdef1 & HstarA0).
    assert (HstarA1 : AnnTyping G A1 a_Star)
      by exact (AnnTyping_type_wf_w G v A1 Hv).
    pose proof (AnnTyping_AnnCtx G v A1 Hv) as HctxG.
    assert (Hrefl : AnnDefEq G (dom G) (g_Refl a_Star) a_Star a_Star)
      by exact (An_Refl G (dom G) a_Star a_Star (An_Star G HctxG)).
    assert (Htrans : AnnDefEq G (dom G) (g_Trans g1 g2) A1 T)
      by exact (An_Trans G (dom G) g1 g2 A1 T A0 a_Star a_Star
                  (g_Refl a_Star) Hdef1 Hdef2 HstarA1 HstarA0 Hrefl).
    apply (An_Conv G v (g_Trans g1 g2) T A1 Hv Htrans HstarT).
  (* An_Push *)
  - rename H into Hval.
    rename H0 into HdefR.
    rename H1 into Hb'eq.
    rename H2 into Hg'eq.
    destruct (AnnTyping_App_inv G (a_Conv v g) rho b T Hty)
      as (A & B & HT & Hfun & Harg).
    subst T.
    destruct (AnnTyping_Conv_inv G v g (a_Pi rho A B) Hfun)
      as (A0 & Hv & Hdef & HstarPi).
    pose proof (AnnDefEq_det G (dom G) g A0 (a_Pi rho A B)
                  (a_Pi rho A1 B1) (a_Pi rho A2 B2) Hdef HdefR)
      as [HA0 HPi].
    subst A0.
    injection HPi as HA HB. subst A. subst B.
    assert (HstarLeftPi : AnnTyping G (a_Pi rho A1 B1) a_Star)
      by exact (AnnTyping_type_wf_w G v (a_Pi rho A1 B1) Hv).
    assert (HstarA1 : AnnTyping G A1 a_Star)
      by exact (AnnTyping_pi_dom G rho A1 B1 HstarLeftPi).
    assert (HstarA2 : AnnTyping G A2 a_Star)
      by exact (AnnTyping_pi_dom G rho A2 B2 HstarPi).
    pose proof (AnnTyping_AnnCtx G v (a_Pi rho A1 B1) Hv) as HctxG.
    assert (HreflStar : AnnDefEq G (dom G) (g_Refl a_Star) a_Star a_Star)
      by exact (An_Refl G (dom G) a_Star a_Star (An_Star G HctxG)).
    assert (HpiFst : AnnDefEq G (dom G) (g_PiFst g) A1 A2)
      by exact (An_PiFst G (dom G) g A1 A2 rho B1 B2 HdefR).
    assert (HdefSym : AnnDefEq G (dom G) (g_Sym (g_PiFst g)) A2 A1)
      by exact (An_Sym G (dom G) (g_PiFst g) A2 A1 a_Star a_Star
                  (g_Refl a_Star) HstarA1 HstarA2 HreflStar HpiFst).
    assert (Hbstar : AnnTyping G (a_Conv b (g_Sym (g_PiFst g))) A1)
      by exact (An_Conv G b (g_Sym (g_PiFst g)) A1 A2 Harg HdefSym HstarA1).
    subst b'. subst g'.
    set (bstar := a_Conv b (g_Sym (g_PiFst g))) in *.
    set (gstar := g_PiSnd g (g_Refl2 bstar b (g_PiFst g))) in *.
    assert (Hrefl2 : AnnDefEq G (dom G) (g_Refl2 bstar b (g_PiFst g)) bstar b).
    { apply (An_EraseEq G (dom G) bstar b (g_PiFst g) A1 A2).
      - exact Hbstar.
      - exact Harg.
      - unfold bstar. cbn [erase_tm]. reflexivity.
      - exact HpiFst. }
    assert (HpiSnd : AnnDefEq G (dom G) gstar
              (open_tm_wrt_tm B1 bstar) (open_tm_wrt_tm B2 b)).
    { unfold gstar.
      exact (An_PiSnd G (dom G) g (g_Refl2 bstar b (g_PiFst g))
               B1 bstar B2 b rho A1 A2 HdefR Hrefl2 Hbstar Harg). }
    assert (Happ : AnnTyping G (a_App v rho bstar) (open_tm_wrt_tm B1 bstar))
      by exact (An_App G v rho bstar B1 A1 Hv Hbstar).
    assert (HstarTarget : AnnTyping G (open_tm_wrt_tm B2 b) a_Star)
      by exact (AnnTyping_open_body_star_w G rho A2 B2 b HstarPi Harg).
    exact (An_Conv G (a_App v rho bstar) gstar
             (open_tm_wrt_tm B2 b) (open_tm_wrt_tm B1 bstar)
             Happ HpiSnd HstarTarget).
  (* An_CPush *)
  - rename H into Hval.
    rename H0 into HdefR.
    rename H1 into Hg1'eq.
    rename H2 into Hg'eq.
    destruct (AnnTyping_CApp_inv G (a_Conv v g) g1 T Hty)
      as (B & a & b & A & HT & Hfun & HdefArg).
    subst T.
    destruct (AnnTyping_Conv_inv G v g (a_CPi (Eq a b A) B) Hfun)
      as (A0 & Hv & Hdef & HstarRight).
    pose proof (AnnDefEq_det G (dom G) g A0 (a_CPi (Eq a b A) B)
                  (a_CPi phi1 A1) (a_CPi phi2 A2) Hdef HdefR)
      as [HA0 HPi].
    subst A0.
    destruct phi1 as [p q P].
    destruct phi2 as [a2 b2 A2c].
    injection HPi as Ha2 Hb2 HA2c HB. subst a2. subst b2. subst A2c. subst B.
    subst g1'. subst g'.
    set (g1star := g_Cast g1 (g_Sym (g_CPiFst g))) in *.
    set (gstar := g_CPiSnd g g1star g1) in *.
    assert (HpiFstG : AnnIso G (dom G) (g_CPiFst g)
              (Eq p q P) (Eq a b A))
      by exact (An_CPiFst G (dom G) g (Eq p q P) (Eq a b A) A1 A2 HdefR).
    assert (HpiFstSym : AnnIso G (dom G) (g_Sym (g_CPiFst g))
              (Eq a b A) (Eq p q P))
      by exact (An_IsoSym G (dom G) (g_CPiFst g) (Eq a b A) (Eq p q P) HpiFstG).
    assert (HdefG1' : AnnDefEq G (dom G) g1star p q)
      by exact (An_Cast G (dom G) g1 (g_Sym (g_CPiFst g)) p q a b A P
                  HdefArg HpiFstSym).
    assert (Hcapp : AnnTyping G (a_CApp v g1star) (open_tm_wrt_co A1 g1star))
      by exact (An_CApp G v g1star A1 p q P Hv HdefG1').
    assert (HpiSnd : AnnDefEq G (dom G) gstar
              (open_tm_wrt_co A1 g1star) (open_tm_wrt_co A2 g1)).
    { unfold gstar.
      exact (An_CPiSnd G (dom G) g g1star g1 A1 A2 p q P a b A
               HdefR HdefG1' HdefArg). }
    assert (HstarTarget : AnnTyping G (open_tm_wrt_co A2 g1) a_Star)
      by exact (AnnTyping_capp_body_star_w G g1 A2 a b A HstarRight HdefArg).
    exact (An_Conv G (a_CApp v g1star) gstar
             (open_tm_wrt_co A2 g1) (open_tm_wrt_co A1 g1star)
             Hcapp HpiSnd HstarTarget).
Qed.

(* ===== ProgressPrep ===== *)
Require Import Lia.
Require Import List.
Import ListNotations.



Lemma CoercedValue_lc : forall a, CoercedValue a -> lc_tm a.
Proof.
  intros a H. induction H.
  - apply Value_lc; assumption.
  - apply lc_a_Conv; [apply Value_lc; assumption|assumption].
Qed.


(* Erasure commutes with term-opening (copy of agentD Base). *)
Ltac erase_tm_auto :=
  first
  [ match goal with
    | |- erase_tm (open_tm_wrt_tm_rec ?k ?u ?x) =
         open_tm_wrt_tm_rec ?k (erase_tm ?u) (erase_tm ?x) =>
        match goal with H : forall k0 u0,
          erase_tm (open_tm_wrt_tm_rec k0 u0 ?x) =
          open_tm_wrt_tm_rec k0 (erase_tm u0) (erase_tm ?x) |- _ =>
          exact (H k u) end
    | |- erase_brs (open_brs_wrt_tm_rec ?k ?u ?x) =
         open_brs_wrt_tm_rec ?k (erase_tm ?u) (erase_brs ?x) =>
        match goal with H : forall k0 u0,
          erase_brs (open_brs_wrt_tm_rec k0 u0 ?x) =
          open_brs_wrt_tm_rec k0 (erase_tm u0) (erase_brs ?x) |- _ =>
          exact (H k u) end
    | |- erase_constraint (open_constraint_wrt_tm_rec ?k ?u ?x) =
         open_constraint_wrt_tm_rec ?k (erase_tm ?u) (erase_constraint ?x) =>
        match goal with H : forall k0 u0,
          erase_constraint (open_constraint_wrt_tm_rec k0 u0 ?x) =
          open_constraint_wrt_tm_rec k0 (erase_tm u0) (erase_constraint ?x) |- _ =>
          exact (H k u) end
    end
  | reflexivity
  | (match goal with |- context [lt_eq_lt_dec ?a ?b] =>
       destruct (lt_eq_lt_dec a b) as [[Hlt|Heq]|Hgt];
       cbn [erase_tm]; reflexivity end)
  | (f_equal; erase_tm_auto) ].

Lemma erase_open_tm :
  (forall a, forall k u,
     erase_tm (open_tm_wrt_tm_rec k u a) =
     open_tm_wrt_tm_rec k (erase_tm u) (erase_tm a)) /\
  (forall b, forall k u,
     erase_brs (open_brs_wrt_tm_rec k u b) =
     open_brs_wrt_tm_rec k (erase_tm u) (erase_brs b)) /\
  (forall g : co, True) /\
  (forall phi, forall k u,
     erase_constraint (open_constraint_wrt_tm_rec k u phi) =
     open_constraint_wrt_tm_rec k (erase_tm u) (erase_constraint phi)).
Proof.
  apply (tm_mutind
    (fun a => forall k u,
       erase_tm (open_tm_wrt_tm_rec k u a) =
       open_tm_wrt_tm_rec k (erase_tm u) (erase_tm a))
    (fun b => forall k u,
       erase_brs (open_brs_wrt_tm_rec k u b) =
       open_brs_wrt_tm_rec k (erase_tm u) (erase_brs b))
    (fun g => True)
    (fun phi => forall k u,
       erase_constraint (open_constraint_wrt_tm_rec k u phi) =
       open_constraint_wrt_tm_rec k (erase_tm u) (erase_constraint phi))).
  all: try exact I.
  all: intros.
  all: try (match goal with |- context [a_App _ ?r _] => destruct r end).
  all: cbn [erase_tm erase_brs erase_constraint
           open_tm_wrt_tm_rec open_brs_wrt_tm_rec
           open_co_wrt_tm_rec open_constraint_wrt_tm_rec].
  all: try erase_tm_auto.
Qed.

Lemma erase_open_tm_tm : forall a k u,
  erase_tm (open_tm_wrt_tm_rec k u a) =
  open_tm_wrt_tm_rec k (erase_tm u) (erase_tm a).
Proof. intros; exact (proj1 erase_open_tm a k u). Qed.
Definition erase_open_tm_v : forall a u,
  erase_tm (open_tm_wrt_tm a u) =
  open_tm_wrt_tm (erase_tm a) (erase_tm u) :=
  fun a u => erase_open_tm_tm a 0 u.

(* Erasure is invariant under coercion-opening. *)
Ltac solve_erase_co :=
  first
  [ reflexivity
  | match goal with
    | |- erase_tm (open_tm_wrt_co_rec ?k ?g ?x) = erase_tm ?x =>
        match goal with H : forall k0 g0, erase_tm (open_tm_wrt_co_rec k0 g0 ?x) = erase_tm ?x |- _ =>
          exact (H k g) end
    | |- erase_brs (open_brs_wrt_co_rec ?k ?g ?x) = erase_brs ?x =>
        match goal with H : forall k0 g0, erase_brs (open_brs_wrt_co_rec k0 g0 ?x) = erase_brs ?x |- _ =>
          exact (H k g) end
    | |- erase_constraint (open_constraint_wrt_co_rec ?k ?g ?x) = erase_constraint ?x =>
        match goal with H : forall k0 g0, erase_constraint (open_constraint_wrt_co_rec k0 g0 ?x) = erase_constraint ?x |- _ =>
          exact (H k g) end
    end ].

Ltac erase_co_auto :=
  first
  [ solve_erase_co
  | reflexivity
  | (f_equal; erase_co_auto) ].

Lemma erase_open_co :
  (forall a, forall k g,
     erase_tm (open_tm_wrt_co_rec k g a) = erase_tm a) /\
  (forall b, forall k g,
     erase_brs (open_brs_wrt_co_rec k g b) = erase_brs b) /\
  (forall g : co, True) /\
  (forall phi, forall k g,
     erase_constraint (open_constraint_wrt_co_rec k g phi) = erase_constraint phi).
Proof.
  apply (tm_mutind
    (fun a => forall k g, erase_tm (open_tm_wrt_co_rec k g a) = erase_tm a)
    (fun b => forall k g, erase_brs (open_brs_wrt_co_rec k g b) = erase_brs b)
    (fun g => True)
    (fun phi => forall k g,
       erase_constraint (open_constraint_wrt_co_rec k g phi) = erase_constraint phi)).
  all: try exact I.
  all: intros.
  all: try (match goal with |- context [a_App _ ?r _] => destruct r end).
  all: cbn [erase_tm erase_brs erase_constraint
           open_tm_wrt_co_rec open_brs_wrt_co_rec
           open_co_wrt_co_rec open_constraint_wrt_co_rec].
  all: try erase_co_auto.
Qed.

Lemma erase_open_co_tm_pp : forall a k g,
  erase_tm (open_tm_wrt_co_rec k g a) = erase_tm a.
Proof. intros; exact (proj1 erase_open_co a k g). Qed.

(* Local closedness of erasures under coercion-opening. *)
Lemma lc_open_co_tm_pp : forall a k g, lc_tm a ->
  lc_tm (open_tm_wrt_co_rec k g a).
Proof.
  intros. rewrite (proj1 clc_closed_open_co a 0 (lc_clc_tm a H) k (le_0_n k) g).
  exact H.
Qed.

Lemma lc_erase :
  (forall a (l:lc_tm a), lc_tm (erase_tm a)) /\
  (forall g (l:lc_co g), True) /\
  (forall b (l:lc_brs b), lc_brs (erase_brs b)) /\
  (forall phi (l:lc_constraint phi), lc_constraint (erase_constraint phi)).
Proof.
  apply (lc_mutind
    (fun a _ => lc_tm (erase_tm a))
    (fun g _ => True)
    (fun b _ => lc_brs (erase_brs b))
    (fun phi _ => lc_constraint (erase_constraint phi))).
  all: try exact I.
  all: intros.
  all: try (match goal with |- context [a_App _ ?r _] => destruct r end).
  all: cbn [erase_tm erase_brs erase_constraint] in *.
  all: try constructor.
  all: try assumption.
  all: try (intro x;
    match goal with
    | |- lc_tm (open_tm_wrt_tm (erase_tm ?b) (a_Var_f ?x)) =>
        match goal with
        | H : forall y, lc_tm (erase_tm (open_tm_wrt_tm ?b (a_Var_f y))) |- _ =>
            specialize (H x); unfold open_tm_wrt_tm in H;
            rewrite erase_open_tm_tm in H;
            cbn [erase_tm] in H; exact H
        end
    end).
  all: try (intro c;
    match goal with
    | |- lc_tm (open_tm_wrt_co (erase_tm ?B) (g_Var_f ?c)) =>
        match goal with
        | H : forall d, lc_tm (erase_tm (open_tm_wrt_co ?B (g_Var_f d))) |- _ =>
            specialize (H c); unfold open_tm_wrt_co in H;
            rewrite erase_open_co_tm_pp in H;
            exact (lc_open_co_tm_pp (erase_tm B) 0 (g_Var_f c) H)
        end
    end).
  all: try constructor.
Qed.

Definition lc_erase_tm : forall a, lc_tm a -> lc_tm (erase_tm a) :=
  fun a H => proj1 lc_erase a H.

(* Every locally-closed term erases to an erased term. *)
Lemma erased_tm_erase_lc :
  (forall a, lc_tm a -> erased_tm (erase_tm a)) /\
  (forall g:co, lc_co g -> True) /\
  (forall b:brs, lc_brs b -> True) /\
  (forall p:constraint, lc_constraint p ->
     match p with
     | Eq a b A => erased_tm (erase_tm a) /\ erased_tm (erase_tm b) /\ erased_tm (erase_tm A)
     end).
Proof.
  apply (lc_mutind
    (fun a _ => erased_tm (erase_tm a))
    (fun g _ => True)
    (fun b _ => True)
    (fun p _ => (match p with
                | Eq a b A => erased_tm (erase_tm a) /\ erased_tm (erase_tm b) /\ erased_tm (erase_tm A)
                end))).
  - apply erased_a_Star.
  - apply erased_a_Var.
  - intros rho A b HlA IHA Hbody IHb. cbn [erase_tm].
    apply erased_a_Abs with (L:=empty). intros x Hx.
    change (erased_tm (open_tm_wrt_tm_rec 0 (erase_tm (a_Var_f x)) (erase_tm b))).
    rewrite <- erase_open_tm_tm. apply IHb.
  - intros rho b Hbody IHb. cbn [erase_tm].
    apply erased_a_Abs with (L:=empty). intros x Hx.
    change (erased_tm (open_tm_wrt_tm_rec 0 (erase_tm (a_Var_f x)) (erase_tm b))).
    rewrite <- erase_open_tm_tm. apply IHb.
  - intros a rho b Hla IHa Hlb IHb. destruct rho; cbn [erase_tm].
    + apply erased_a_App; assumption.
    + apply erased_a_App; [exact IHa | apply erased_a_Bullet].
  - apply erased_a_Fam.
  - apply erased_a_Const.
  - intros rho A B HlA IHA Hbody IHB. cbn [erase_tm].
    apply erased_a_Pi with (L:=empty); [exact IHA |]. intros x Hx.
    change (erased_tm (open_tm_wrt_tm_rec 0 (erase_tm (a_Var_f x)) (erase_tm B))).
    rewrite <- erase_open_tm_tm. apply IHB.
  - intros a g Hla IHa Hlg IHg. cbn [erase_tm]. exact IHa.
  - intros phi B Hphi Iphi Hbody IHB. destruct phi as [a b A]; cbn [erase_constraint erase_tm].
    apply erased_a_CPi with (L:=empty).
    + exact (proj1 Iphi).
    + exact (proj1 (proj2 Iphi)).
    + exact (proj2 (proj2 Iphi)).
    + intros c Hc.
      assert (HlcB : lc_tm (erase_tm B)).
      { specialize (Hbody c). unfold open_tm_wrt_co in Hbody.
        pose proof (lc_erase_tm (open_tm_wrt_co_rec 0 (g_Var_f c) B) Hbody) as Hx.
        rewrite erase_open_co_tm_pp in Hx. exact Hx. }
      change (erased_tm (open_tm_wrt_co_rec 0 (g_Var_f c) (erase_tm B))).
      rewrite (open_tm_co_closed (erase_tm B) 0 (g_Var_f c) HlcB).
      specialize (IHB c). unfold open_tm_wrt_co in IHB.
      rewrite erase_open_co_tm_pp in IHB. exact IHB.
  - intros phi b Hphi Iphi Hbody IHb. cbn [erase_tm].
    apply erased_a_CAbs with (L:=empty). intros c Hc.
    assert (HlcB : lc_tm (erase_tm b)).
    { specialize (Hbody c). unfold open_tm_wrt_co in Hbody.
      pose proof (lc_erase_tm (open_tm_wrt_co_rec 0 (g_Var_f c) b) Hbody) as Hx.
      rewrite erase_open_co_tm_pp in Hx. exact Hx. }
    change (erased_tm (open_tm_wrt_co_rec 0 (g_Var_f c) (erase_tm b))).
    rewrite (open_tm_co_closed (erase_tm b) 0 (g_Var_f c) HlcB).
    specialize (IHb c). unfold open_tm_wrt_co in IHb.
    rewrite erase_open_co_tm_pp in IHb. exact IHb.
  - intros b Hbody IHb. cbn [erase_tm].
    apply erased_a_CAbs with (L:=empty). intros c Hc.
    assert (HlcB : lc_tm (erase_tm b)).
    { specialize (Hbody c). unfold open_tm_wrt_co in Hbody.
      pose proof (lc_erase_tm (open_tm_wrt_co_rec 0 (g_Var_f c) b) Hbody) as Hx.
      rewrite erase_open_co_tm_pp in Hx. exact Hx. }
    change (erased_tm (open_tm_wrt_co_rec 0 (g_Var_f c) (erase_tm b))).
    rewrite (open_tm_co_closed (erase_tm b) 0 (g_Var_f c) HlcB).
    specialize (IHb c). unfold open_tm_wrt_co in IHb.
    rewrite erase_open_co_tm_pp in IHb. exact IHb.
  - intros a g Hla IHa Hlg IHg. cbn [erase_tm].
    apply erased_a_CApp. exact IHa.
  - apply erased_a_Bullet.
  - intros K. cbn [erase_tm]. apply erased_a_Star.
  - intros a brs5 Hla IHa Hlb IHb. cbn [erase_tm]. apply erased_a_Star.
  - intros; exact I.
  - intros; exact I.
  - intros; exact I.
  - intros; exact I.
  - intros; exact I.
  - intros; exact I.
  - intros; exact I.
  - intros; exact I.
  - intros; exact I.
  - intros; exact I.
  - intros; exact I.
  - intros; exact I.
  - intros; exact I.
  - intros; exact I.
  - intros; exact I.
  - intros; exact I.
  - intros; exact I.
  - intros; exact I.
  - intros; exact I.
  - intros; exact I.
  - intros; exact I.
  - intros; exact I.
  - intros; exact I.
  - intros; exact I.
  - intros; exact I.
  - intros; exact I.
  - intros a b A Hla IHa Hlb IHb HlA IHA. cbn [erase_constraint]. auto.
Qed.
Definition erased_tm_erase : forall a, lc_tm a -> erased_tm (erase_tm a) :=
  fun a H => proj1 erased_tm_erase_lc a H.

(* On erasures the level-aware and ordinary free-variable functions agree:
   erasure removes every free coercion variable. *)


Lemma erased_context_cons : forall x s G,
  erased_context ((x,s)::G) <-> erased_sort s /\ erased_context G.
Proof.
  intros. unfold erased_context. split.
  - intro H. split.
    + exact (Forall_inv H).
    + exact (Forall_inv_tail H).
  - intros [H1 H2]. apply Forall_cons; assumption.
Qed.

Lemma Good_extend_Tm : forall G D x A,
  Good G D -> x `notin` dom G -> lc_tm A ->
  Good ((x, Tm (erase_tm A)) :: G) (add x D).
Proof.
  intros G D x A Hgood Hx Hlc. destruct Hgood as [Hec Hjoin]. split.
  - unfold erased_context in *.
    apply Forall_cons.
    + apply erased_Tm. apply erased_tm_erase. exact Hlc.
    + exact Hec.
  - intros c1 A1 B1 T1 Hb Hin.
    apply binds_cons_iff in Hb.
    destruct Hb as [[Heq Hsat]|HbG].
    + inversion Hsat.
    + apply AtomSetFacts.add_iff in Hin.
      destruct Hin as [Hcx|HinD].
      * subst c1. exfalso. apply Hx.
        exact (@binds_In sort x (Co (Eq A1 B1 T1)) G HbG).
      * destruct (Hjoin c1 A1 B1 T1 HbG HinD) as [C [HC1 HC2]].
        exists C. split; eapply Par_mono; eassumption.
Qed.

Lemma AnnGood_extend_Tm : forall G D x A,
  AnnGood G D -> x `notin` dom G -> lc_tm A ->
  AnnGood (x ~ Tm A ++ G) (add x D).
Proof.
  intros G D x A HG Hx Hlc. unfold AnnGood in *.
  change (Good ((x, Tm (erase_tm A)) :: erase_context G) (add x D)).
  apply Good_extend_Tm.
  - exact HG.
  - intro Hin. apply Hx. pose proof (@dom_map sort sort erase_sort G) as Hdom.
    exact (proj1 (Hdom x) Hin).
  - exact Hlc.
Qed.

(* Extension of irrelevance through an irrelevant abstraction binder. *)
Lemma irrelevant_open_AbsIrrel : forall G D x A a,
  irrelevant G D (a_Abs Irrel A a) ->
  x `notin` dom G ->
  lc_tm A ->
  RhoCheck Irrel x (erase_tm (open_tm_wrt_tm a (a_Var_f x))) ->
  irrelevant (x ~ Tm A ++ G) (add x D) (open_tm_wrt_tm a (a_Var_f x)).
Proof.
  intros G D x A a [Hfv Hgood] Hx HlcA Hrho. split.
  - intros y B Hyb.
    apply binds_cons_iff in Hyb.
    destruct Hyb as [[Heq Hsat]|HyG].
    + subst y. inversion Hrho. assumption.
    + assert (HyG' : binds y (Tm B) G) by exact HyG.
      assert (Hnota : y `notin` fv_tm_tm_tm (erase_tm a)).
      { apply Hfv with (A:=B). exact HyG'. }
      assert (Hyx : y <> x).
      { intro Hyx. subst y. apply Hx. exact (@binds_In sort x (Tm B) G HyG'). }
      eapply notin_subset.
      * rewrite erase_open_tm_v. apply fv_tm_tm_open_subset_erased.
      * apply notin_union.
        -- exact Hnota.
        -- apply notin_singleton. symmetry. exact Hyx.
  - apply AnnGood_extend_Tm.
    + exact Hgood.
    + exact Hx.
    + exact HlcA.
Qed.

(* ===== ProgressStruct ===== *)

(* ================================================================ *)
(* Semantic shape lemmas still to be supplied (development stubs).   *)
(* They are consequences of Good + AnnDefEq; see worklog.            *)
(* ================================================================ *)


Module EOK.
Require Import Wf_nat.
Require Import Lia.
Require Import List.
Import ListNotations.

(* ================================================================== *)
(* Eok is preserved by Par and MultiPar                               *)
(* ================================================================== *)

Lemma Eok_Par_aux : forall G D a b, Par G D a b -> Eok a -> Eok b.
Proof.
  apply (Par_ind (fun G D a b => Eok a -> Eok b)).
  - intros G0 D0 a0 Hlc Ha0. exact Ha0.
  - (* Par_Beta *)
    intros G0 D0 a0 rho b0 a' b' Hpar1 IH1 Hpar2 IH2 Ha0.
    inversion Ha0; subst.
    assert (Eok (a_UAbs rho a')) as HaU by (apply IH1; assumption).
    inversion HaU; subst.
    apply Eok_open_tm; [assumption | apply IH2; assumption].
  - (* Par_App *)
    intros G0 D0 a0 rho b0 a' b' Hpar1 IH1 Hpar2 IH2 Ha0.
    inversion Ha0; subst.
    apply Eok_App; [apply IH1 | apply IH2]; assumption.
  - (* Par_CBeta *)
    intros G0 D0 a0 a' Hpar IH Ha0.
    inversion Ha0; subst.
    assert (Eok (a_UCAbs a')) as HaU by (apply IH; assumption).
    inversion HaU; subst.
    apply Eok_open_co_triv; assumption.
  - (* Par_CApp *)
    intros G0 D0 a0 a' Hpar IH Ha0.
    inversion Ha0; subst.
    apply Eok_CApp. apply IH. assumption.
  - (* Par_Abs *)
    intros L G0 D0 rho a0 a' Hpar IH Ha0.
    inversion Ha0; subst.
    apply Eok_UAbs.
    destruct (atom_fresh L) as [x Hx].
    apply (Eok_open_tm_inv a' x).
    apply (IH x Hx).
    apply Eok_open_tm; [assumption | apply Eok_Var_f].
  - (* Par_Pi *)
    intros L G0 D0 rho A B A' B' HA IHA HB IHB Ha0.
    inversion Ha0; subst.
    apply Eok_Pi.
    + apply IHA. assumption.
    + destruct (atom_fresh L) as [x Hx].
      apply (Eok_open_tm_inv B' x).
      apply (IHB x Hx).
      apply Eok_open_tm; [assumption | apply Eok_Var_f].
  - (* Par_CAbs *)
    intros L G0 D0 a0 a' Hpar IH Ha0.
    inversion Ha0; subst.
    apply Eok_UCAbs.
    destruct (atom_fresh L) as [c Hc].
    apply (Eok_open_co_inv a' c).
    apply (IH c Hc).
    apply Eok_open_co_var; assumption.
  - (* Par_CPi *)
    intros L G0 D0 A B A1 a0 A' B' A1' a' HA IHA HB IHB Hbody IHbody HA1 IHA1 Ha0.
    inversion Ha0; subst.
    match goal with H : EokConstraint (Eq _ _ _) |- _ => inversion H; subst end.
    apply Eok_CPi.
    + apply Eok_Eq.
      * apply IHA. assumption.
      * apply IHB. assumption.
      * apply IHA1. assumption.
    + destruct (atom_fresh L) as [c Hc].
      apply (Eok_open_co_inv a' c).
      apply (IHbody c Hc).
      apply Eok_open_co_var; assumption.
  - (* Par_Axiom *)
    intros G0 D0 F a0 A0 Hbinds Ha0.
    destruct (toplevel_binds_eq F a0 A0 Hbinds) as [HF [Ha _]].
    subst F a0. apply Eok_erase.
Qed.

Lemma Eok_MultiPar_aux : forall G D a b, MultiPar G D a b -> Eok a -> Eok b.
Proof.
  apply (MultiPar_ind (fun G D a b => Eok a -> Eok b)).
  - intros G0 D0 a0 Hlc Ha0. exact Ha0.
  - intros G0 D0 a0 a' b0 Hpar Hmp IH Ha0.
    apply IH. apply (Eok_Par_aux _ _ _ _ Hpar Ha0).
Qed.

Lemma Eok_Par : forall G D a b, Eok a -> Par G D a b -> Eok b.
Proof. intros; eapply Eok_Par_aux; eassumption. Qed.

Lemma Eok_MultiPar : forall G D a b, Eok a -> MultiPar G D a b -> Eok b.
Proof. intros; eapply Eok_MultiPar_aux; eassumption. Qed.

(* ================================================================== *)
(* Freshness of substitution / local closure of substitution          *)
(* ================================================================== *)

Lemma notin_singleton_neq : forall (x y:atom), x `notin` {{y}} -> x <> y.
Proof. intros x y H E; apply H; destruct E; apply AtomSetImpl.singleton_2; reflexivity. Qed.

Lemma subst_tm_fresh_gen :
  (forall (a:tm) x u, x `notin` fv_tm_tm_tm a -> subst_tm_tm x u a = a) /\
  (forall (b:brs) x u, x `notin` fv_tm_tm_brs b -> subst_tm_brs x u b = b) /\
  (forall (g:co) x u, x `notin` fv_tm_tm_co g -> subst_tm_co x u g = g) /\
  (forall (p:constraint) x u, x `notin` fv_tm_tm_constraint p -> subst_tm_constraint x u p = p).
Proof.
  apply (tm_mutind
    (fun a => forall x u, x `notin` fv_tm_tm_tm a -> subst_tm_tm x u a = a)
    (fun b => forall x u, x `notin` fv_tm_tm_brs b -> subst_tm_brs x u b = b)
    (fun g => forall x u, x `notin` fv_tm_tm_co g -> subst_tm_co x u g = g)
    (fun p => forall x u, x `notin` fv_tm_tm_constraint p -> subst_tm_constraint x u p = p)).
  all: intros; cbn [subst_tm_tm subst_tm_brs subst_tm_co subst_tm_constraint
                      fv_tm_tm_tm fv_tm_tm_brs fv_tm_tm_co fv_tm_tm_constraint] in *.
  all: try reflexivity.
  all: try (repeat match goal with H : _ `notin` (_ \u _) |- _ => apply notin_union_elim in H; destruct H end).
  all: try (repeat match goal with
            | H : ?x `notin` {{?y}} |- context [KeySetFacts.eq_dec ?y ?x] =>
              destruct (KeySetFacts.eq_dec y x) as [E|E];
              [ exfalso; apply (notin_singleton_neq x y H); symmetry; exact E
              | reflexivity ]
            end).
  all: try reflexivity.
  all: try (repeat f_equal; eauto).
Qed.

Lemma subst_tm_fresh : forall (a:tm) x u, x `notin` fv_tm_tm_tm a -> subst_tm_tm x u a = a.
Proof. exact (proj1 subst_tm_fresh_gen). Qed.

Lemma subst_co_fresh_gen :
  (forall (a:tm) c h, c `notin` cfv_tm a -> subst_co_tm c h a = a) /\
  (forall (b:brs) c h, c `notin` cfv_brs b -> subst_co_brs c h b = b) /\
  (forall (g:co) c h, c `notin` cfv_co g -> subst_co_co c h g = g) /\
  (forall (p:constraint) c h, c `notin` cfv_constraint p -> subst_co_constraint c h p = p).
Proof.
  apply (tm_mutind
    (fun a => forall c h, c `notin` cfv_tm a -> subst_co_tm c h a = a)
    (fun b => forall c h, c `notin` cfv_brs b -> subst_co_brs c h b = b)
    (fun g => forall c h, c `notin` cfv_co g -> subst_co_co c h g = g)
    (fun p => forall c h, c `notin` cfv_constraint p -> subst_co_constraint c h p = p)).
  all: intros; cbn [subst_co_tm subst_co_brs subst_co_co subst_co_constraint
                      cfv_tm cfv_brs cfv_co cfv_constraint] in *.
  all: try reflexivity.
  all: try (repeat match goal with H : _ `notin` (_ \u _) |- _ => apply notin_union_elim in H; destruct H end).
  all: try (repeat match goal with
            | H : ?x `notin` {{?y}} |- context [KeySetFacts.eq_dec ?y ?x] =>
              destruct (KeySetFacts.eq_dec y x) as [E|E];
              [ exfalso; apply (notin_singleton_neq x y H); symmetry; exact E
              | reflexivity ]
            | H : ?x `notin` {{?y}} |- context [KeySetFacts.eq_dec ?x ?y] =>
              destruct (KeySetFacts.eq_dec x y) as [E|E];
              [ exfalso; apply (notin_singleton_neq x y H); exact E
              | reflexivity ]
            end).
  all: try reflexivity.
  all: try (repeat f_equal; eauto).
Qed.

Lemma subst_co_fresh : forall (a:tm) c h, c `notin` cfv_tm a -> subst_co_tm c h a = a.
Proof. exact (proj1 subst_co_fresh_gen). Qed.

(* substitution preserves local closure *)

Lemma clt_subst_tm_all :
  (forall (a:tm) n x w, clt_tm n a -> clt_tm n w -> clt_tm n (subst_tm_tm x w a)) /\
  (forall (b:brs) n x w, clt_brs n b -> clt_tm n w -> clt_brs n (subst_tm_brs x w b)) /\
  (forall (g:co) n x w, clt_co n g -> clt_tm n w -> clt_co n (subst_tm_co x w g)) /\
  (forall (p:constraint) n x w, clt_constraint n p -> clt_tm n w -> clt_constraint n (subst_tm_constraint x w p)).
Proof.
  apply (tm_mutind
    (fun a => forall n x w, clt_tm n a -> clt_tm n w -> clt_tm n (subst_tm_tm x w a))
    (fun b => forall n x w, clt_brs n b -> clt_tm n w -> clt_brs n (subst_tm_brs x w b))
    (fun g => forall n x w, clt_co n g -> clt_tm n w -> clt_co n (subst_tm_co x w g))
    (fun p => forall n x w, clt_constraint n p -> clt_tm n w -> clt_constraint n (subst_tm_constraint x w p))).
  all: intros; cbn [subst_tm_tm subst_tm_brs subst_tm_co subst_tm_constraint
                    clt_tm clt_brs clt_co clt_constraint] in *.
  all: try solve [exact I].
  all: try (repeat match goal with H : _ /\ _ |- _ => destruct H end).
  all: try (repeat split).
  all: try (destruct (KeySetFacts.eq_dec x x0) as [E|E]; [subst; assumption|exact I]).
  all: eauto using clt_tm_mono, clt_co_mono, clt_brs_mono, clt_constraint_mono.
Qed.

Lemma clc_subst_tm_all :
  (forall (a:tm) n x w, clc_tm n a -> clc_tm n w -> clc_tm n (subst_tm_tm x w a)) /\
  (forall (b:brs) n x w, clc_brs n b -> clc_tm n w -> clc_brs n (subst_tm_brs x w b)) /\
  (forall (g:co) n x w, clc_co n g -> clc_tm n w -> clc_co n (subst_tm_co x w g)) /\
  (forall (p:constraint) n x w, clc_constraint n p -> clc_tm n w -> clc_constraint n (subst_tm_constraint x w p)).
Proof.
  apply (tm_mutind
    (fun a => forall n x w, clc_tm n a -> clc_tm n w -> clc_tm n (subst_tm_tm x w a))
    (fun b => forall n x w, clc_brs n b -> clc_tm n w -> clc_brs n (subst_tm_brs x w b))
    (fun g => forall n x w, clc_co n g -> clc_tm n w -> clc_co n (subst_tm_co x w g))
    (fun p => forall n x w, clc_constraint n p -> clc_tm n w -> clc_constraint n (subst_tm_constraint x w p))).
  all: intros; cbn [subst_tm_tm subst_tm_brs subst_tm_co subst_tm_constraint
                    clc_tm clc_brs clc_co clc_constraint] in *.
  all: try solve [exact I].
  all: try (repeat match goal with H : _ /\ _ |- _ => destruct H end).
  all: try (repeat split).
  all: try (destruct (KeySetFacts.eq_dec x x0) as [E|E]; [subst; assumption|exact I]).
  all: eauto using clc_tm_mono, clc_co_mono, clc_brs_mono, clc_constraint_mono.
Qed.

Lemma lc_subst_tm_all :
  (forall (a:tm) x w, lc_tm a -> lc_tm w -> lc_tm (subst_tm_tm x w a)) /\
  (forall (b:brs) x w, lc_brs b -> lc_tm w -> lc_brs (subst_tm_brs x w b)) /\
  (forall (g:co) x w, lc_co g -> lc_tm w -> lc_co (subst_tm_co x w g)) /\
  (forall (p:constraint) x w, lc_constraint p -> lc_tm w -> lc_constraint (subst_tm_constraint x w p)).
Proof.
  repeat split; intros.
  - apply lc_tm_iff. split.
    + apply (proj1 clt_subst_tm_all a 0 x w); [apply lc_clt_tm; assumption|apply lc_clt_tm; assumption].
    + apply (proj1 clc_subst_tm_all a 0 x w); [apply lc_clc_tm; assumption|apply lc_clc_tm; assumption].
  - apply lc_brs_iff. split.
    + apply (proj1 (proj2 clt_subst_tm_all) b 0 x w); [apply lc_clt_brs; assumption|apply lc_clt_tm; assumption].
    + apply (proj1 (proj2 clc_subst_tm_all) b 0 x w); [apply lc_clc_brs; assumption|apply lc_clc_tm; assumption].
  - apply lc_co_iff. split.
    + apply (proj1 (proj2 (proj2 clt_subst_tm_all)) g 0 x w); [apply lc_clt_co; assumption|apply lc_clt_tm; assumption].
    + apply (proj1 (proj2 (proj2 clc_subst_tm_all)) g 0 x w); [apply lc_clc_co; assumption|apply lc_clc_tm; assumption].
  - apply lc_constraint_iff. split.
    + apply (proj2 (proj2 (proj2 clt_subst_tm_all)) p 0 x w); [apply lc_clt_constraint; assumption|apply lc_clt_tm; assumption].
    + apply (proj2 (proj2 (proj2 clc_subst_tm_all)) p 0 x w); [apply lc_clc_constraint; assumption|apply lc_clc_tm; assumption].
Qed.

Lemma lc_subst_tm : forall a x w, lc_tm a -> lc_tm w -> lc_tm (subst_tm_tm x w a).
Proof. exact (proj1 lc_subst_tm_all). Qed.

Lemma clt_subst_co_all :
  (forall (a:tm) n c g, clt_tm n a -> clt_co n g -> clt_tm n (subst_co_tm c g a)) /\
  (forall (b:brs) n c g, clt_brs n b -> clt_co n g -> clt_brs n (subst_co_brs c g b)) /\
  (forall (h:co) n c g, clt_co n h -> clt_co n g -> clt_co n (subst_co_co c g h)) /\
  (forall (p:constraint) n c g, clt_constraint n p -> clt_co n g -> clt_constraint n (subst_co_constraint c g p)).
Proof.
  apply (tm_mutind
    (fun a => forall n c g, clt_tm n a -> clt_co n g -> clt_tm n (subst_co_tm c g a))
    (fun b => forall n c g, clt_brs n b -> clt_co n g -> clt_brs n (subst_co_brs c g b))
    (fun h => forall n c g, clt_co n h -> clt_co n g -> clt_co n (subst_co_co c g h))
    (fun p => forall n c g, clt_constraint n p -> clt_co n g -> clt_constraint n (subst_co_constraint c g p))).
  all: intros; cbn [subst_co_tm subst_co_brs subst_co_co subst_co_constraint
                    clt_tm clt_brs clt_co clt_constraint] in *.
  all: try solve [exact I].
  all: try (repeat match goal with H : _ /\ _ |- _ => destruct H end).
  all: try (repeat split).
  all: try (match goal with |- context [KeySetFacts.eq_dec ?u ?v] => destruct (KeySetFacts.eq_dec u v) as [E|E]; [subst; assumption|exact I] end).
  all: eauto using clt_tm_mono, clt_co_mono, clt_brs_mono, clt_constraint_mono.
Qed.

Lemma clc_subst_co_all :
  (forall (a:tm) n c g, clc_tm n a -> clc_co n g -> clc_tm n (subst_co_tm c g a)) /\
  (forall (b:brs) n c g, clc_brs n b -> clc_co n g -> clc_brs n (subst_co_brs c g b)) /\
  (forall (h:co) n c g, clc_co n h -> clc_co n g -> clc_co n (subst_co_co c g h)) /\
  (forall (p:constraint) n c g, clc_constraint n p -> clc_co n g -> clc_constraint n (subst_co_constraint c g p)).
Proof.
  apply (tm_mutind
    (fun a => forall n c g, clc_tm n a -> clc_co n g -> clc_tm n (subst_co_tm c g a))
    (fun b => forall n c g, clc_brs n b -> clc_co n g -> clc_brs n (subst_co_brs c g b))
    (fun h => forall n c g, clc_co n h -> clc_co n g -> clc_co n (subst_co_co c g h))
    (fun p => forall n c g, clc_constraint n p -> clc_co n g -> clc_constraint n (subst_co_constraint c g p))).
  all: intros; cbn [subst_co_tm subst_co_brs subst_co_co subst_co_constraint
                    clc_tm clc_brs clc_co clc_constraint] in *.
  all: try solve [exact I].
  all: try (repeat match goal with H : _ /\ _ |- _ => destruct H end).
  all: try (repeat split).
  all: try (match goal with |- context [KeySetFacts.eq_dec ?u ?v] => destruct (KeySetFacts.eq_dec u v) as [E|E]; [subst; assumption|exact I] end).
  all: eauto using clc_tm_mono, clc_co_mono, clc_brs_mono, clc_constraint_mono.
Qed.

Lemma lc_subst_co_all :
  (forall (a:tm) c g, lc_tm a -> lc_co g -> lc_tm (subst_co_tm c g a)) /\
  (forall (b:brs) c g, lc_brs b -> lc_co g -> lc_brs (subst_co_brs c g b)) /\
  (forall (h:co) c g, lc_co h -> lc_co g -> lc_co (subst_co_co c g h)) /\
  (forall (p:constraint) c g, lc_constraint p -> lc_co g -> lc_constraint (subst_co_constraint c g p)).
Proof.
  repeat split; intros.
  - apply lc_tm_iff. split.
    + apply (proj1 clt_subst_co_all a 0 c g); [apply lc_clt_tm; assumption|apply lc_clt_co; assumption].
    + apply (proj1 clc_subst_co_all a 0 c g); [apply lc_clc_tm; assumption|apply lc_clc_co; assumption].
  - apply lc_brs_iff. split.
    + apply (proj1 (proj2 clt_subst_co_all) b 0 c g); [apply lc_clt_brs; assumption|apply lc_clt_co; assumption].
    + apply (proj1 (proj2 clc_subst_co_all) b 0 c g); [apply lc_clc_brs; assumption|apply lc_clc_co; assumption].
  - apply lc_co_iff. split.
    + apply (proj1 (proj2 (proj2 clt_subst_co_all)) h 0 c g); [apply lc_clt_co; assumption|apply lc_clt_co; assumption].
    + apply (proj1 (proj2 (proj2 clc_subst_co_all)) h 0 c g); [apply lc_clc_co; assumption|apply lc_clc_co; assumption].
  - apply lc_constraint_iff. split.
    + apply (proj2 (proj2 (proj2 clt_subst_co_all)) p 0 c g); [apply lc_clt_constraint; assumption|apply lc_clt_co; assumption].
    + apply (proj2 (proj2 (proj2 clc_subst_co_all)) p 0 c g); [apply lc_clc_constraint; assumption|apply lc_clc_co; assumption].
Qed.

Lemma lc_subst_co : forall a c g, lc_tm a -> lc_co g -> lc_tm (subst_co_tm c g a).
Proof. exact (proj1 lc_subst_co_all). Qed.
Lemma closeT_open_subst_gen :
  (forall a x y k,
     open_tm_wrt_tm_rec k (a_Var_f y) (closeT_tm x k a) = subst_tm_tm x (a_Var_f y) a) /\
  (forall b x y k,
     open_brs_wrt_tm_rec k (a_Var_f y) (closeT_brs x k b) = subst_tm_brs x (a_Var_f y) b) /\
  (forall g x y k,
     open_co_wrt_tm_rec k (a_Var_f y) (closeT_co x k g) = subst_tm_co x (a_Var_f y) g) /\
  (forall p x y k,
     open_constraint_wrt_tm_rec k (a_Var_f y) (closeT_constraint x k p) = subst_tm_constraint x (a_Var_f y) p).
Proof.
  apply (tm_mutind
    (fun a => forall x y k,
       open_tm_wrt_tm_rec k (a_Var_f y) (closeT_tm x k a) = subst_tm_tm x (a_Var_f y) a)
    (fun b => forall x y k,
       open_brs_wrt_tm_rec k (a_Var_f y) (closeT_brs x k b) = subst_tm_brs x (a_Var_f y) b)
    (fun g => forall x y k,
       open_co_wrt_tm_rec k (a_Var_f y) (closeT_co x k g) = subst_tm_co x (a_Var_f y) g)
    (fun p => forall x y k,
       open_constraint_wrt_tm_rec k (a_Var_f y) (closeT_constraint x k p) = subst_tm_constraint x (a_Var_f y) p)).
  all: intros.
  all: cbn [open_tm_wrt_tm_rec open_brs_wrt_tm_rec open_co_wrt_tm_rec
            open_constraint_wrt_tm_rec closeT_tm closeT_brs closeT_co
            closeT_constraint subst_tm_tm subst_tm_brs subst_tm_co
            subst_tm_constraint].
  all: try reflexivity.
  all: try (repeat f_equal; eauto).
  all: try (match goal with
     | |- open_tm_wrt_tm_rec ?k (a_Var_f ?y)
            (if le_lt_dec ?k ?n then a_Var_b (S ?n) else a_Var_b ?n) = a_Var_b ?n =>
        destruct (le_lt_dec k n) as [Hle|Hlt];
        [ cbn [open_tm_wrt_tm_rec];
          destruct (lt_eq_lt_dec (S n) k) as [[H1|H2]|H3];
          [ exfalso; lia | exfalso; lia
          | cbn [open_tm_wrt_tm_rec]; f_equal; lia ]
        | cbn [open_tm_wrt_tm_rec];
          destruct (lt_eq_lt_dec n k) as [[H1|H2]|H3];
          [ reflexivity | exfalso; lia | exfalso; lia ] ]
     end).
  all: try (match goal with
     | |- open_tm_wrt_tm_rec ?k (a_Var_f ?y)
            (if eq_var ?u ?v then a_Var_b ?k else a_Var_f ?v) =
          (if KeySetFacts.eq_dec ?v ?u then a_Var_f ?y else a_Var_f ?v) =>
        destruct (eq_var u v) eqn:E;
        [ apply eq_var_true in E; subst u;
          cbn [open_tm_wrt_tm_rec];
          destruct (lt_eq_lt_dec k k) as [[H1|H2]|H3]; [exfalso;lia| |exfalso;lia];
          cbn [open_tm_wrt_tm_rec];
          destruct (KeySetFacts.eq_dec v v) as [e|e]; [reflexivity|exfalso;auto]
        | cbn [open_tm_wrt_tm_rec];
          destruct (KeySetFacts.eq_dec v u) as [e|e];
          [ exfalso; apply eq_var_false in E; exact (E (eq_sym e)) | reflexivity ] ]
     | |- open_tm_wrt_tm_rec ?k (a_Var_f ?y)
            (if eq_var ?u ?v then a_Var_b ?k else a_Var_f ?v) =
          (if KeySetFacts.eq_dec ?u ?v then a_Var_f ?y else a_Var_f ?v) =>
        destruct (eq_var u v) eqn:E;
        [ apply eq_var_true in E; subst u;
          cbn [open_tm_wrt_tm_rec];
          destruct (lt_eq_lt_dec k k) as [[H1|H2]|H3]; [exfalso;lia| |exfalso;lia];
          cbn [open_tm_wrt_tm_rec];
          destruct (KeySetFacts.eq_dec v v) as [e|e]; [reflexivity|exfalso;auto]
        | cbn [open_tm_wrt_tm_rec];
          destruct (KeySetFacts.eq_dec u v) as [e|e];
          [ exfalso; apply eq_var_false in E; exact (E e) | reflexivity ] ]
     end).
Qed.

Lemma closeC_open_subst_gen :
  (forall a c k,
     open_tm_wrt_co_rec k (g_Var_f c) (closeC_tm c k a) = subst_co_tm c (g_Var_f c) a) /\
  (forall b c k,
     open_brs_wrt_co_rec k (g_Var_f c) (closeC_brs c k b) = subst_co_brs c (g_Var_f c) b) /\
  (forall g c k,
     open_co_wrt_co_rec k (g_Var_f c) (closeC_co c k g) = subst_co_co c (g_Var_f c) g) /\
  (forall p c k,
     open_constraint_wrt_co_rec k (g_Var_f c) (closeC_constraint c k p) = subst_co_constraint c (g_Var_f c) p).
Proof.
  apply (tm_mutind
    (fun a => forall c k,
       open_tm_wrt_co_rec k (g_Var_f c) (closeC_tm c k a) = subst_co_tm c (g_Var_f c) a)
    (fun b => forall c k,
       open_brs_wrt_co_rec k (g_Var_f c) (closeC_brs c k b) = subst_co_brs c (g_Var_f c) b)
    (fun g => forall c k,
       open_co_wrt_co_rec k (g_Var_f c) (closeC_co c k g) = subst_co_co c (g_Var_f c) g)
    (fun p => forall c k,
       open_constraint_wrt_co_rec k (g_Var_f c) (closeC_constraint c k p) = subst_co_constraint c (g_Var_f c) p)).
  all: intros.
  all: cbn [open_tm_wrt_co_rec open_brs_wrt_co_rec open_co_wrt_co_rec
            open_constraint_wrt_co_rec closeC_tm closeC_brs closeC_co
            closeC_constraint subst_co_tm subst_co_brs subst_co_co
            subst_co_constraint].
  all: try reflexivity.
  all: try (repeat f_equal; eauto).
  all: try (match goal with
     | |- open_co_wrt_co_rec ?k (g_Var_f ?c)
            (if le_lt_dec ?k ?n then g_Var_b (S ?n) else g_Var_b ?n) = g_Var_b ?n =>
        destruct (le_lt_dec k n) as [Hle|Hlt];
        [ cbn [open_co_wrt_co_rec];
          destruct (lt_eq_lt_dec (S n) k) as [[H1|H2]|H3];
          [ exfalso; lia | exfalso; lia
          | cbn [open_co_wrt_co_rec]; f_equal; lia ]
        | cbn [open_co_wrt_co_rec];
          destruct (lt_eq_lt_dec n k) as [[H1|H2]|H3];
          [ reflexivity | exfalso; lia | exfalso; lia ] ]
     end).
  all: try (match goal with
     | |- open_co_wrt_co_rec ?k (g_Var_f ?c)
            (if eq_var ?u ?v then g_Var_b ?k else g_Var_f ?v) =
          (if KeySetFacts.eq_dec ?v ?u then g_Var_f ?c else g_Var_f ?v) =>
        destruct (eq_var u v) eqn:E;
        [ apply eq_var_true in E; subst u;
          cbn [open_co_wrt_co_rec];
          destruct (lt_eq_lt_dec k k) as [[H1|H2]|H3]; [exfalso;lia| |exfalso;lia];
          cbn [open_co_wrt_co_rec];
          destruct (KeySetFacts.eq_dec v v) as [e|e]; [reflexivity|exfalso;auto]
        | cbn [open_co_wrt_co_rec];
          destruct (KeySetFacts.eq_dec v u) as [e|e];
          [ exfalso; apply eq_var_false in E; exact (E (eq_sym e)) | reflexivity ] ]
     | |- open_co_wrt_co_rec ?k (g_Var_f ?c)
            (if eq_var ?u ?v then g_Var_b ?k else g_Var_f ?v) =
          (if KeySetFacts.eq_dec ?u ?v then g_Var_f ?c else g_Var_f ?v) =>
        destruct (eq_var u v) eqn:E;
        [ apply eq_var_true in E; subst u;
          cbn [open_co_wrt_co_rec];
          destruct (lt_eq_lt_dec k k) as [[H1|H2]|H3]; [exfalso;lia| |exfalso;lia];
          cbn [open_co_wrt_co_rec];
          destruct (KeySetFacts.eq_dec v v) as [e|e]; [reflexivity|exfalso;auto]
        | cbn [open_co_wrt_co_rec];
          destruct (KeySetFacts.eq_dec u v) as [e|e];
          [ exfalso; apply eq_var_false in E; exact (E e) | reflexivity ] ]
     end).
Qed.

Lemma open_closeT_subst : forall a x y,
  open_tm_wrt_tm (closeT_tm x 0 a) (a_Var_f y) = subst_tm_tm x (a_Var_f y) a.
Proof. intros; exact (proj1 closeT_open_subst_gen a x y 0). Qed.

Lemma open_closeC_subst : forall a c,
  open_tm_wrt_co (closeC_tm c 0 a) (g_Var_f c) = subst_co_tm c (g_Var_f c) a.
Proof. intros; exact (proj1 closeC_open_subst_gen a c 0). Qed.

(* ================================================================== *)
(* Substitution into a locally closed Eok term *)
(* ================================================================== *)

Lemma Eok_subst_par : forall a, Eok a -> lc_tm a ->
  forall G D x u v, Par G D u v ->
  Par G D (subst_tm_tm x u a) (subst_tm_tm x v a).
Proof.
  apply (well_founded_ind
    (well_founded_lt_compat tm sz_tm (fun a b => sz_tm a < sz_tm b) (fun x y H => H))
    (fun a => Eok a -> lc_tm a -> forall G D x u v, Par G D u v ->
      Par G D (subst_tm_tm x u a) (subst_tm_tm x v a))).
  intros a IH He Hl G D x u v Hpar.
  destruct He as [ | | n | x0 | F | T | rho b He_b | a0 rho b He_a He_b
                 | rho A B He_A He_B | phi B He_phi He_B
                 | b He_b | a0 He_a ].
  - (* Star *) cbn [subst_tm_tm]. apply Par_Refl. apply lc_a_Star.
  - (* Bullet *) cbn [subst_tm_tm]. apply Par_Refl. apply lc_a_Bullet.
  - (* Var_b *) exfalso. inversion Hl.
  - (* Var_f *) cbn [subst_tm_tm].
    destruct (KeySetFacts.eq_dec x0 x) as [E|E]; [subst x0; exact Hpar|].
    apply Par_Refl. apply lc_a_Var_f.
  - (* Fam *) cbn [subst_tm_tm]. apply Par_Refl. apply lc_a_Fam.
  - (* Const *) cbn [subst_tm_tm]. apply Par_Refl. apply lc_a_Const.
  - (* UAbs *) cbn [subst_tm_tm].
    apply Par_Abs with (L := {{x}}).
    intros y Hy.
    assert (Hyx : y <> x) by (intro E; apply Hy; subst; apply AtomSetImpl.singleton_2; reflexivity).
    assert (Hu : lc_tm u) by (apply (proj1 (Par_lc _ _ _ _ Hpar))).
    assert (Hv : lc_tm v) by (apply (proj2 (Par_lc _ _ _ _ Hpar))).
    assert (Hlc_y : lc_tm (open_tm_wrt_tm b (a_Var_f y))) by (apply (lc_tm_uabs_inv rho b Hl y)).
    assert (Hpar_y : Par G D (subst_tm_tm x u (open_tm_wrt_tm b (a_Var_f y)))
                          (subst_tm_tm x v (open_tm_wrt_tm b (a_Var_f y)))).
    { apply (IH (open_tm_wrt_tm b (a_Var_f y))).
      - unfold open_tm_wrt_tm. rewrite sz_tm_open_tm_var. cbn [sz_tm]. lia.
      - apply Eok_open_tm; [exact He_b | apply Eok_Var_f].
      - exact Hlc_y.
      - exact Hpar. }
    pose proof (proj1 (Par_lc _ _ _ _ Hpar_y)) as Hlu.
    pose proof (proj2 (Par_lc _ _ _ _ Hpar_y)) as Hlv.
    unfold open_tm_wrt_tm.
    replace (open_tm_wrt_tm_rec 0 (a_Var_f y) (subst_tm_tm x u b))
      with (subst_tm_tm x u (open_tm_wrt_tm_rec 0 (a_Var_f y) b)).
    2: { symmetry. rewrite (proj1 subst_tm_open_tm b x u y 0 Hu).
         rewrite subst_tm_var_neq; [reflexivity|exact (not_eq_sym Hyx)]. }
    replace (open_tm_wrt_tm_rec 0 (a_Var_f y) (subst_tm_tm x v b))
      with (subst_tm_tm x v (open_tm_wrt_tm_rec 0 (a_Var_f y) b)).
    2: { symmetry. rewrite (proj1 subst_tm_open_tm b x v y 0 Hv).
         rewrite subst_tm_var_neq; [reflexivity|exact (not_eq_sym Hyx)]. }
    exact Hpar_y.
  - (* App *) cbn [subst_tm_tm].
    destruct (lc_tm_app_inv a0 rho b Hl) as [Hla Hlb].
    apply Par_App.
    + apply (IH a0); [cbn [sz_tm]; lia | exact He_a | exact Hla | exact Hpar].
    + apply (IH b); [cbn [sz_tm]; lia | exact He_b | exact Hlb | exact Hpar].
  - (* Pi *) cbn [subst_tm_tm].
    destruct (lc_tm_pi_inv rho A B Hl) as [HlA HlB].
    apply Par_Pi with (L := {{x}}).
    + apply (IH A); [cbn [sz_tm]; lia | exact He_A | exact HlA | exact Hpar].
    + intros y Hy.
      assert (Hyx : y <> x) by (intro E; apply Hy; subst; apply AtomSetImpl.singleton_2; reflexivity).
      assert (Hu : lc_tm u) by (apply (proj1 (Par_lc _ _ _ _ Hpar))).
      assert (Hv : lc_tm v) by (apply (proj2 (Par_lc _ _ _ _ Hpar))).
      assert (Hlc_y : lc_tm (open_tm_wrt_tm B (a_Var_f y))) by (apply HlB).
      assert (Hpar_y : Par G D (subst_tm_tm x u (open_tm_wrt_tm B (a_Var_f y)))
                            (subst_tm_tm x v (open_tm_wrt_tm B (a_Var_f y)))).
      { apply (IH (open_tm_wrt_tm B (a_Var_f y))).
        - unfold open_tm_wrt_tm. rewrite sz_tm_open_tm_var. cbn [sz_tm]. lia.
        - apply Eok_open_tm; [exact He_B | apply Eok_Var_f].
        - exact Hlc_y.
        - exact Hpar. }
      pose proof (proj1 (Par_lc _ _ _ _ Hpar_y)) as Hlu.
      pose proof (proj2 (Par_lc _ _ _ _ Hpar_y)) as Hlv.
      unfold open_tm_wrt_tm.
      replace (open_tm_wrt_tm_rec 0 (a_Var_f y) (subst_tm_tm x u B))
        with (subst_tm_tm x u (open_tm_wrt_tm_rec 0 (a_Var_f y) B)).
      2: { symmetry. rewrite (proj1 subst_tm_open_tm B x u y 0 Hu).
           rewrite subst_tm_var_neq; [reflexivity|exact (not_eq_sym Hyx)]. }
      replace (open_tm_wrt_tm_rec 0 (a_Var_f y) (subst_tm_tm x v B))
        with (subst_tm_tm x v (open_tm_wrt_tm_rec 0 (a_Var_f y) B)).
      2: { symmetry. rewrite (proj1 subst_tm_open_tm B x v y 0 Hv).
           rewrite subst_tm_var_neq; [reflexivity|exact (not_eq_sym Hyx)]. }
      exact Hpar_y.
  - (* CPi *) cbn [subst_tm_tm].
    destruct (lc_tm_cpi_inv phi B Hl) as [Hlphi HlB].
    destruct phi as [A Bc A1].
    destruct (EokConstraint_components A Bc A1 He_phi) as [HeA [HeBc HeA1]].
    apply Par_CPi with (L := empty).
    + apply (IH A); [cbn [sz_tm sz_constraint]; lia | exact HeA | apply (lc_constraint_eq_1 A Bc A1 Hlphi) | exact Hpar].
    + apply (IH Bc); [cbn [sz_tm sz_constraint]; lia | exact HeBc | apply (lc_constraint_eq_2 A Bc A1 Hlphi) | exact Hpar].
    + intros c Hc.
      assert (Hu : lc_tm u) by (apply (proj1 (Par_lc _ _ _ _ Hpar))).
      assert (Hv : lc_tm v) by (apply (proj2 (Par_lc _ _ _ _ Hpar))).
      assert (Hlc_c : lc_tm (open_tm_wrt_co B (g_Var_f c))) by (apply HlB).
      assert (Hpar_c : Par G D (subst_tm_tm x u (open_tm_wrt_co B (g_Var_f c)))
                             (subst_tm_tm x v (open_tm_wrt_co B (g_Var_f c)))).
      { apply (IH (open_tm_wrt_co B (g_Var_f c))).
        - unfold open_tm_wrt_co. rewrite sz_tm_open_co_var. cbn [sz_tm]. lia.
        - apply Eok_open_co_var; exact He_B.
        - exact Hlc_c.
        - exact Hpar. }
      pose proof (proj1 (Par_lc _ _ _ _ Hpar_c)) as Hlu.
      pose proof (proj2 (Par_lc _ _ _ _ Hpar_c)) as Hlv.
      unfold open_tm_wrt_co.
      replace (open_tm_wrt_co_rec 0 (g_Var_f c) (subst_tm_tm x u B))
        with (subst_tm_tm x u (open_tm_wrt_co_rec 0 (g_Var_f c) B)).
      2: { symmetry. rewrite (proj1 subst_tm_open_tm_co B x u (g_Var_f c) 0 Hu).
           cbn [subst_tm_co]. reflexivity. }
      replace (open_tm_wrt_co_rec 0 (g_Var_f c) (subst_tm_tm x v B))
        with (subst_tm_tm x v (open_tm_wrt_co_rec 0 (g_Var_f c) B)).
      2: { symmetry. rewrite (proj1 subst_tm_open_tm_co B x v (g_Var_f c) 0 Hv).
           cbn [subst_tm_co]. reflexivity. }
      exact Hpar_c.
    + apply (IH A1); [cbn [sz_tm sz_constraint]; lia | exact HeA1 | apply (lc_constraint_eq_3 A Bc A1 Hlphi) | exact Hpar].
  - (* UCAbs *) cbn [subst_tm_tm].
    apply Par_CAbs with (L := empty).
    intros c Hc.
    assert (Hu : lc_tm u) by (apply (proj1 (Par_lc _ _ _ _ Hpar))).
    assert (Hv : lc_tm v) by (apply (proj2 (Par_lc _ _ _ _ Hpar))).
    assert (Hlc_c : lc_tm (open_tm_wrt_co b (g_Var_f c))) by (apply (lc_tm_ucabs_inv b Hl c)).
    assert (Hpar_c : Par G D (subst_tm_tm x u (open_tm_wrt_co b (g_Var_f c)))
                           (subst_tm_tm x v (open_tm_wrt_co b (g_Var_f c)))).
    { apply (IH (open_tm_wrt_co b (g_Var_f c))).
      - unfold open_tm_wrt_co. rewrite sz_tm_open_co_var. cbn [sz_tm]. lia.
      - apply Eok_open_co_var; exact He_b.
      - exact Hlc_c.
      - exact Hpar. }
    pose proof (proj1 (Par_lc _ _ _ _ Hpar_c)) as Hlu.
    pose proof (proj2 (Par_lc _ _ _ _ Hpar_c)) as Hlv.
    unfold open_tm_wrt_co.
    replace (open_tm_wrt_co_rec 0 (g_Var_f c) (subst_tm_tm x u b))
      with (subst_tm_tm x u (open_tm_wrt_co_rec 0 (g_Var_f c) b)).
    2: { symmetry. rewrite (proj1 subst_tm_open_tm_co b x u (g_Var_f c) 0 Hu).
         cbn [subst_tm_co]. reflexivity. }
    replace (open_tm_wrt_co_rec 0 (g_Var_f c) (subst_tm_tm x v b))
      with (subst_tm_tm x v (open_tm_wrt_co_rec 0 (g_Var_f c) b)).
    2: { symmetry. rewrite (proj1 subst_tm_open_tm_co b x v (g_Var_f c) 0 Hv).
         cbn [subst_tm_co]. reflexivity. }
    exact Hpar_c.
  - (* CApp *) cbn [subst_tm_tm].
    destruct (lc_tm_capp_inv a0 g_Triv Hl) as [Hla _].
    apply Par_CApp.
    apply (IH a0); [cbn [sz_tm sz_co]; lia | exact He_a | exact Hla | exact Hpar].
Qed.

(* ================================================================== *)
(* Eok inversions and Par substitution *)
(* ================================================================== *)

Lemma Eok_UAbs_inv : forall rho b, Eok (a_UAbs rho b) -> Eok b.
Proof. intros; inversion H; subst; assumption. Qed.
Lemma Eok_App_inv : forall a rho b, Eok (a_App a rho b) -> Eok a /\ Eok b.
Proof. intros; inversion H; subst; auto. Qed.
Lemma Eok_Pi_inv : forall rho A B, Eok (a_Pi rho A B) -> Eok A /\ Eok B.
Proof. intros; inversion H; subst; auto. Qed.
Lemma Eok_CPi_inv : forall phi B, Eok (a_CPi phi B) -> EokConstraint phi /\ Eok B.
Proof. intros; inversion H; subst; auto. Qed.
Lemma Eok_UCAbs_inv : forall b, Eok (a_UCAbs b) -> Eok b.
Proof. intros; inversion H; subst; assumption. Qed.
Lemma Eok_CApp_inv : forall a, Eok (a_CApp a g_Triv) -> Eok a.
Proof. intros; inversion H; subst; assumption. Qed.

Lemma Par_subst_Eok :
  forall G D a b, Par G D a b -> Eok a ->
  forall x u v, x `notin` fv_tm_tm_tm (erase_tm FixDef) -> Par G D u v ->
  Par G D (subst_tm_tm x u a) (subst_tm_tm x v b).
Proof.
  intros G D a b H.
  revert H.
  apply (Par_ind (fun G D a b => Eok a ->
    forall x u v, x `notin` fv_tm_tm_tm (erase_tm FixDef) -> Par G D u v ->
    Par G D (subst_tm_tm x u a) (subst_tm_tm x v b))).
  - (* Refl *) intros G0 D0 a0 Hl He x u v Hxfix Hpar.
    apply (Eok_subst_par a0 He Hl G0 D0 x u v Hpar).
  - (* Beta *) intros G0 D0 a0 rho b0 a' b' Hfa IHfa Harg IHarg He x u v Hxfix Hpar.
    destruct (Eok_App_inv a0 rho b0 He) as [Hea Heb].
    cbn [subst_tm_tm].
    assert (Hv : lc_tm v) by (apply (proj2 (Par_lc _ _ _ _ Hpar))).
    specialize (IHfa Hea x u v Hxfix Hpar).
    specialize (IHarg Heb x u v Hxfix Hpar).
    cbn [subst_tm_tm] in IHfa.
    unfold open_tm_wrt_tm.
    rewrite (proj1 subst_tm_open_co_tm a' x v b' 0 Hv).
    apply (Par_Beta G0 D0 (subst_tm_tm x u a0) rho
             (subst_tm_tm x u b0) (subst_tm_tm x v a') (subst_tm_tm x v b') IHfa IHarg).
  - (* App *) intros G0 D0 a0 rho b0 a' b' Hfa IHfa Harg IHarg He x u v Hxfix Hpar.
    destruct (Eok_App_inv a0 rho b0 He) as [Hea Heb].
    cbn [subst_tm_tm].
    apply Par_App.
    + apply (IHfa Hea x u v Hxfix Hpar).
    + apply (IHarg Heb x u v Hxfix Hpar).
  - (* CBeta *) intros G0 D0 a0 a' Hfa IHfa He x u v Hxfix Hpar.
    pose proof (Eok_CApp_inv a0 He) as Hea.
    cbn [subst_tm_tm].
    assert (Hv : lc_tm v) by (apply (proj2 (Par_lc _ _ _ _ Hpar))).
    specialize (IHfa Hea x u v Hxfix Hpar).
    cbn [subst_tm_tm] in IHfa.
    unfold open_tm_wrt_co.
    rewrite (proj1 subst_tm_open_tm_co a' x v g_Triv 0 Hv).
    cbn [subst_tm_co].
    apply (Par_CBeta G0 D0 (subst_tm_tm x u a0) (subst_tm_tm x v a') IHfa).
  - (* CApp *) intros G0 D0 a0 a' Hfa IHfa He x u v Hxfix Hpar.
    pose proof (Eok_CApp_inv a0 He) as Hea.
    cbn [subst_tm_tm].
    apply Par_CApp. apply (IHfa Hea x u v Hxfix Hpar).
  - (* Abs *) intros L G0 D0 rho a0 a' Hbody IHbody He x u v Hxfix Hpar.
    pose proof (Eok_UAbs_inv rho a0 He) as Hea.
    cbn [subst_tm_tm].
    apply Par_Abs with (L := L \u {{x}}).
    intros y Hy.
    assert (HyL : y `notin` L) by (apply notin_union_1 in Hy; exact Hy).
    assert (Hyx : y `notin` {{x}}) by (apply notin_union_2 in Hy; exact Hy).
    assert (Hyx' : y <> x) by (intro E; apply Hyx; subst; apply AtomSetImpl.singleton_2; reflexivity).
    assert (Hu : lc_tm u) by (apply (proj1 (Par_lc _ _ _ _ Hpar))).
    assert (Hv : lc_tm v) by (apply (proj2 (Par_lc _ _ _ _ Hpar))).
    assert (He_open : Eok (open_tm_wrt_tm a0 (a_Var_f y))) by (apply Eok_open_tm; [exact Hea | apply Eok_Var_f]).
    specialize (IHbody y HyL He_open x u v Hxfix Hpar).
    unfold open_tm_wrt_tm.
    unfold open_tm_wrt_tm in IHbody.
    rewrite (proj1 subst_tm_open_co_tm a0 x u (a_Var_f y) 0 Hu) in IHbody.
    rewrite (proj1 subst_tm_open_co_tm a' x v (a_Var_f y) 0 Hv) in IHbody.
    rewrite (subst_tm_var_neq x y u (not_eq_sym Hyx')) in IHbody.
    rewrite (subst_tm_var_neq x y v (not_eq_sym Hyx')) in IHbody.
    exact IHbody.
  - (* Pi *) intros L G0 D0 rho A B A' B' HA IHA HB IHB He x u v Hxfix Hpar.
    destruct (Eok_Pi_inv rho A B He) as [HeA HeB].
    cbn [subst_tm_tm].
    assert (Hu : lc_tm u) by (apply (proj1 (Par_lc _ _ _ _ Hpar))).
    assert (Hv : lc_tm v) by (apply (proj2 (Par_lc _ _ _ _ Hpar))).
    apply Par_Pi with (L := L \u {{x}}).
    + apply (IHA HeA x u v Hxfix Hpar).
    + intros y Hy.
      assert (HyL : y `notin` L) by (apply notin_union_1 in Hy; exact Hy).
      assert (Hyx : y `notin` {{x}}) by (apply notin_union_2 in Hy; exact Hy).
      assert (Hyx' : y <> x) by (intro E; apply Hyx; subst; apply AtomSetImpl.singleton_2; reflexivity).
      assert (He_open : Eok (open_tm_wrt_tm B (a_Var_f y))) by (apply Eok_open_tm; [exact HeB | apply Eok_Var_f]).
      specialize (IHB y HyL He_open x u v Hxfix Hpar).
      unfold open_tm_wrt_tm.
      unfold open_tm_wrt_tm in IHB.
      rewrite (proj1 subst_tm_open_co_tm B x u (a_Var_f y) 0 Hu) in IHB.
      rewrite (proj1 subst_tm_open_co_tm B' x v (a_Var_f y) 0 Hv) in IHB.
      rewrite (subst_tm_var_neq x y u (not_eq_sym Hyx')) in IHB.
      rewrite (subst_tm_var_neq x y v (not_eq_sym Hyx')) in IHB.
      exact IHB.
  - (* CAbs *) intros L G0 D0 a0 a' Hbody IHbody He x u v Hxfix Hpar.
    pose proof (Eok_UCAbs_inv a0 He) as Hea.
    cbn [subst_tm_tm].
    apply Par_CAbs with (L := L).
    intros c Hc.
    assert (He_open : Eok (open_tm_wrt_co a0 (g_Var_f c))) by (apply Eok_open_co_var; exact Hea).
    specialize (IHbody c Hc He_open x u v Hxfix Hpar).
    unfold open_tm_wrt_co.
    unfold open_tm_wrt_co in IHbody.
    rewrite (proj1 subst_tm_open_tm_co a0 x u (g_Var_f c) 0
               (proj1 (Par_lc _ _ _ _ Hpar))) in IHbody.
    rewrite (proj1 subst_tm_open_tm_co a' x v (g_Var_f c) 0
               (proj2 (Par_lc _ _ _ _ Hpar))) in IHbody.
    cbn [subst_tm_co] in IHbody.
    exact IHbody.
  - (* CPi *) intros L G0 D0 A B A1 a0 A' B' A1' a'
      HA IHA HB IHB Hbody IHbody HA1 IHA1 He x u v Hxfix Hpar.
    destruct (Eok_CPi_inv (Eq A B A1) a0 He) as [He_phi Hea].
    destruct (EokConstraint_components A B A1 He_phi) as [HeA [HeB HeA1]].
    cbn [subst_tm_tm].
    assert (Hu : lc_tm u) by (apply (proj1 (Par_lc _ _ _ _ Hpar))).
    assert (Hv : lc_tm v) by (apply (proj2 (Par_lc _ _ _ _ Hpar))).
    apply Par_CPi with (L := L).
    + apply (IHA HeA x u v Hxfix Hpar).
    + apply (IHB HeB x u v Hxfix Hpar).
    + intros c Hc.
      assert (He_open : Eok (open_tm_wrt_co a0 (g_Var_f c))) by (apply Eok_open_co_var; exact Hea).
      specialize (IHbody c Hc He_open x u v Hxfix Hpar).
      unfold open_tm_wrt_co.
      unfold open_tm_wrt_co in IHbody.
      rewrite (proj1 subst_tm_open_tm_co a0 x u (g_Var_f c) 0 Hu) in IHbody.
      rewrite (proj1 subst_tm_open_tm_co a' x v (g_Var_f c) 0 Hv) in IHbody.
      cbn [subst_tm_co] in IHbody.
      exact IHbody.
    + apply (IHA1 HeA1 x u v Hxfix Hpar).
  - (* Axiom *) intros G0 D0 F a0 A0 Hbinds He x u v Hxfix Hpar.
    destruct (toplevel_binds_eq F a0 A0 Hbinds) as [HF [Ha HA]].
    subst F a0 A0.
    cbn [subst_tm_tm].
    rewrite (subst_tm_fresh (erase_tm FixDef) x v Hxfix).
    exact (Par_Axiom G0 D0 Fix (erase_tm FixDef) (erase_tm FixTy) Hbinds).
Qed.

(* ================================================================== *)
(* Co-substitution and Par substitution *)
(* ================================================================== *)

Lemma subst_co_var_neq : forall c d g, c <> d -> subst_co_co c g (g_Var_f d) = g_Var_f d.
Proof.
  intros c d g H. cbn [subst_co_co].
  destruct (KeySetFacts.eq_dec d c) as [E|E]; [exfalso; apply H; symmetry; exact E|reflexivity].
Qed.

Lemma Par_subst_co :
  forall G D a b, Par G D a b ->
  forall c g, lc_co g -> c `notin` cfv_tm (erase_tm FixDef) ->
  Par G D (subst_co_tm c g a) (subst_co_tm c g b).
Proof.
  intros G D a b H.
  revert H.
  apply (Par_ind (fun G D a b =>
    forall c g, lc_co g -> c `notin` cfv_tm (erase_tm FixDef) ->
    Par G D (subst_co_tm c g a) (subst_co_tm c g b))).
  - (* Refl *) intros G0 D0 a0 Hl c g Hg Hfix.
    cbn [subst_co_tm]. apply Par_Refl. apply (lc_subst_co a0 c g Hl Hg).
  - (* Beta *) intros G0 D0 a0 rho b0 a' b' Hfa IHfa Harg IHarg c g Hg Hfix.
    cbn [subst_co_tm].
    assert (IHfa' := IHfa c g Hg Hfix).
    assert (IHarg' := IHarg c g Hg Hfix).
    cbn [subst_co_tm] in IHfa'.
    unfold open_tm_wrt_tm.
    rewrite (proj1 subst_co_open_tm a' c g b' 0 Hg).
    apply (Par_Beta G0 D0 (subst_co_tm c g a0) rho
             (subst_co_tm c g b0) (subst_co_tm c g a') (subst_co_tm c g b') IHfa' IHarg').
  - (* App *) intros G0 D0 a0 rho b0 a' b' Hfa IHfa Harg IHarg c g Hg Hfix.
    cbn [subst_co_tm].
    apply Par_App.
    + apply (IHfa c g Hg Hfix).
    + apply (IHarg c g Hg Hfix).
  - (* CBeta *) intros G0 D0 a0 a' Hfa IHfa c g Hg Hfix.
    cbn [subst_co_tm].
    assert (IHfa' := IHfa c g Hg Hfix).
    cbn [subst_co_tm] in IHfa'.
    unfold open_tm_wrt_co.
    rewrite (proj1 subst_co_open_tm_co a' c g g_Triv 0 Hg).
    cbn [subst_co_co].
    apply (Par_CBeta G0 D0 (subst_co_tm c g a0) (subst_co_tm c g a') IHfa').
  - (* CApp *) intros G0 D0 a0 a' Hfa IHfa c g Hg Hfix.
    cbn [subst_co_tm].
    apply Par_CApp. apply (IHfa c g Hg Hfix).
  - (* Abs *) intros L G0 D0 rho a0 a' Hbody IHbody c g Hg Hfix.
    cbn [subst_co_tm].
    apply Par_Abs with (L := L).
    intros y Hy.
    specialize (IHbody y Hy c g Hg Hfix).
    unfold open_tm_wrt_tm.
    unfold open_tm_wrt_tm in IHbody.
    rewrite (proj1 subst_co_open_tm a0 c g (a_Var_f y) 0 Hg) in IHbody.
    rewrite (proj1 subst_co_open_tm a' c g (a_Var_f y) 0 Hg) in IHbody.
    cbn [subst_co_tm] in IHbody.
    exact IHbody.
  - (* Pi *) intros L G0 D0 rho A B A' B' HA IHA HB IHB c g Hg Hfix.
    cbn [subst_co_tm].
    apply Par_Pi with (L := L).
    + apply (IHA c g Hg Hfix).
    + intros y Hy.
      specialize (IHB y Hy c g Hg Hfix).
      unfold open_tm_wrt_tm.
      unfold open_tm_wrt_tm in IHB.
      rewrite (proj1 subst_co_open_tm B c g (a_Var_f y) 0 Hg) in IHB.
      rewrite (proj1 subst_co_open_tm B' c g (a_Var_f y) 0 Hg) in IHB.
      cbn [subst_co_tm] in IHB.
      exact IHB.
  - (* CAbs *) intros L G0 D0 a0 a' Hbody IHbody c g Hg Hfix.
    cbn [subst_co_tm].
    apply Par_CAbs with (L := L \u {{c}}).
    intros d Hd.
    assert (HdL : d `notin` L) by (apply notin_union_1 in Hd; exact Hd).
    assert (Hdc : d `notin` {{c}}) by (apply notin_union_2 in Hd; exact Hd).
    assert (Hdc' : d <> c) by (intro E; apply Hdc; subst; apply AtomSetImpl.singleton_2; reflexivity).
    specialize (IHbody d HdL c g Hg Hfix).
    unfold open_tm_wrt_co.
    unfold open_tm_wrt_co in IHbody.
    rewrite (proj1 subst_co_open_co a0 c g d 0 Hg) in IHbody.
    rewrite (proj1 subst_co_open_co a' c g d 0 Hg) in IHbody.
    rewrite (subst_co_var_neq c d g (not_eq_sym Hdc')) in IHbody.
    exact IHbody.
  - (* CPi *) intros L G0 D0 A B A1 a0 A' B' A1' a'
      HA IHA HB IHB Hbody IHbody HA1 IHA1 c g Hg Hfix.
    cbn [subst_co_tm].
    apply Par_CPi with (L := L \u {{c}}).
    + apply (IHA c g Hg Hfix).
    + apply (IHB c g Hg Hfix).
    + intros d Hd.
      assert (HdL : d `notin` L) by (apply notin_union_1 in Hd; exact Hd).
      assert (Hdc : d `notin` {{c}}) by (apply notin_union_2 in Hd; exact Hd).
      assert (Hdc' : d <> c) by (intro E; apply Hdc; subst; apply AtomSetImpl.singleton_2; reflexivity).
      specialize (IHbody d HdL c g Hg Hfix).
      unfold open_tm_wrt_co.
      unfold open_tm_wrt_co in IHbody.
      rewrite (proj1 subst_co_open_co a0 c g d 0 Hg) in IHbody.
      rewrite (proj1 subst_co_open_co a' c g d 0 Hg) in IHbody.
      rewrite (subst_co_var_neq c d g (not_eq_sym Hdc')) in IHbody.
      exact IHbody.
    + apply (IHA1 c g Hg Hfix).
  - (* Axiom *) intros G0 D0 F a0 A0 Hbinds c g Hg Hfix.
    destruct (toplevel_binds_eq F a0 A0 Hbinds) as [HF [Ha HA]].
    subst F a0 A0.
    cbn [subst_co_tm].
    rewrite (subst_co_fresh (erase_tm FixDef) c g Hfix).
    exact (Par_Axiom G0 D0 Fix (erase_tm FixDef) (erase_tm FixTy) Hbinds).
Qed.

(* ================================================================== *)
(* Body relations extracted from Par *)
(* ================================================================== *)

Lemma Par_UAbs_rel : forall G D rho a b,
  Par G D (a_UAbs rho a) b ->
  exists b', b = a_UAbs rho b' /\
    exists L, forall x, x `notin` L -> Par G D (open_tm_wrt_tm a (a_Var_f x))
                                                (open_tm_wrt_tm b' (a_Var_f x)).
Proof.
  intros G D rho a b H. inversion H; subst.
  - exists a. split; [reflexivity|]. exists empty. intros x Hx.
    apply Par_Refl. apply (lc_tm_uabs_inv rho a (proj1 (Par_lc _ _ _ _ H)) x).
  - exists a'. split; [reflexivity|]. exists L. intros x Hx. apply H5. exact Hx.
Qed.

Lemma Par_Pi_rel : forall G D rho A B b,
  Par G D (a_Pi rho A B) b ->
  exists A' B', b = a_Pi rho A' B' /\ Par G D A A' /\
    exists L, forall x, x `notin` L -> Par G D (open_tm_wrt_tm B (a_Var_f x))
                                                (open_tm_wrt_tm B' (a_Var_f x)).
Proof.
  intros G D rho A B b H. inversion H; subst.
  - exists A, B. split; [reflexivity|]. split.
    + apply Par_Refl. apply (proj1 (lc_tm_pi_inv rho A B (proj1 (Par_lc _ _ _ _ H)))).
    + exists empty. intros x Hx. apply Par_Refl.
      apply (proj2 (lc_tm_pi_inv rho A B (proj1 (Par_lc _ _ _ _ H))) x).
  - exists A', B'. split; [reflexivity|]. split.
    + exact H6.
    + exists L. intros x Hx. apply H7. exact Hx.
Qed.

Lemma Par_CPi_rel : forall G D A B A1 a b,
  Par G D (a_CPi (Eq A B A1) a) b ->
  exists A' B' A1' a', b = a_CPi (Eq A' B' A1') a' /\
    Par G D A A' /\ Par G D B B' /\ Par G D A1 A1' /\
    exists L, forall c, c `notin` L -> Par G D (open_tm_wrt_co a (g_Var_f c))
                                                  (open_tm_wrt_co a' (g_Var_f c)).
Proof.
  intros G D A B A1 a b H. inversion H; subst.
  - exists A, B, A1, a. split; [reflexivity|].
    destruct (lc_tm_cpi_inv (Eq A B A1) a (proj1 (Par_lc _ _ _ _ H))) as [Hlcphi Hlcb].
    split; [apply Par_Refl; apply (lc_constraint_eq_1 A B A1 Hlcphi)|].
    split; [apply Par_Refl; apply (lc_constraint_eq_2 A B A1 Hlcphi)|].
    split; [apply Par_Refl; apply (lc_constraint_eq_3 A B A1 Hlcphi)|].
    exists empty. intros c Hc. apply Par_Refl. apply Hlcb.
  - exists A', B', A1', a'. split; [reflexivity|].
    split; [exact H6|]. split; [exact H8|]. split; [exact H10|].
    exists L. intros c Hc. apply H9. exact Hc.
Qed.

Lemma Par_UCAbs_rel : forall G D a b,
  Par G D (a_UCAbs a) b ->
  exists a', b = a_UCAbs a' /\
    exists L, forall c, c `notin` L -> Par G D (open_tm_wrt_co a (g_Var_f c))
                                                (open_tm_wrt_co a' (g_Var_f c)).
Proof.
  intros G D a b H. inversion H; subst.
  - exists a. split; [reflexivity|]. exists empty. intros c Hc.
    apply Par_Refl. apply (lc_tm_ucabs_inv a (proj1 (Par_lc _ _ _ _ H)) c).
  - exists a'. split; [reflexivity|]. exists L. intros c Hc. apply H3. exact Hc.
Qed.

(* ================================================================== *)
(* Cofinite closing of opened common reducts *)
(* ================================================================== *)

Lemma closeC_open_subst_gen2 :
  (forall a c0 c k,
     open_tm_wrt_co_rec k (g_Var_f c) (closeC_tm c0 k a) = subst_co_tm c0 (g_Var_f c) a) /\
  (forall b c0 c k,
     open_brs_wrt_co_rec k (g_Var_f c) (closeC_brs c0 k b) = subst_co_brs c0 (g_Var_f c) b) /\
  (forall g c0 c k,
     open_co_wrt_co_rec k (g_Var_f c) (closeC_co c0 k g) = subst_co_co c0 (g_Var_f c) g) /\
  (forall p c0 c k,
     open_constraint_wrt_co_rec k (g_Var_f c) (closeC_constraint c0 k p) = subst_co_constraint c0 (g_Var_f c) p).
Proof.
  apply (tm_mutind
    (fun a => forall c0 c k,
       open_tm_wrt_co_rec k (g_Var_f c) (closeC_tm c0 k a) = subst_co_tm c0 (g_Var_f c) a)
    (fun b => forall c0 c k,
       open_brs_wrt_co_rec k (g_Var_f c) (closeC_brs c0 k b) = subst_co_brs c0 (g_Var_f c) b)
    (fun g => forall c0 c k,
       open_co_wrt_co_rec k (g_Var_f c) (closeC_co c0 k g) = subst_co_co c0 (g_Var_f c) g)
    (fun p => forall c0 c k,
       open_constraint_wrt_co_rec k (g_Var_f c) (closeC_constraint c0 k p) = subst_co_constraint c0 (g_Var_f c) p)).
  all: intros.
  all: cbn [open_tm_wrt_co_rec open_brs_wrt_co_rec open_co_wrt_co_rec
            open_constraint_wrt_co_rec closeC_tm closeC_brs closeC_co
            closeC_constraint subst_co_tm subst_co_brs subst_co_co
            subst_co_constraint].
  all: try reflexivity.
  all: try (repeat f_equal; eauto).
  all: try (match goal with
     | |- open_co_wrt_co_rec ?k (g_Var_f ?c)
            (if le_lt_dec ?k ?n then g_Var_b (S ?n) else g_Var_b ?n) = g_Var_b ?n =>
        destruct (le_lt_dec k n) as [Hle|Hlt];
        [ cbn [open_co_wrt_co_rec];
          destruct (lt_eq_lt_dec (S n) k) as [[H1|H2]|H3];
          [ exfalso; lia | exfalso; lia
          | cbn [open_co_wrt_co_rec]; f_equal; lia ]
        | cbn [open_co_wrt_co_rec];
          destruct (lt_eq_lt_dec n k) as [[H1|H2]|H3];
          [ reflexivity | exfalso; lia | exfalso; lia ] ]
     end).
  all: try (match goal with
     | |- open_co_wrt_co_rec ?k (g_Var_f ?c)
            (if eq_var ?c0 ?y then g_Var_b ?k else g_Var_f ?y) =
          (if KeySetFacts.eq_dec ?y ?c0 then g_Var_f ?c else g_Var_f ?y) =>
        destruct (eq_var c0 y) eqn:E;
        [ apply eq_var_true in E; subst c0;
          cbn [open_co_wrt_co_rec];
          destruct (lt_eq_lt_dec k k) as [[H1|H2]|H3]; [exfalso;lia| |exfalso;lia];
          cbn [open_co_wrt_co_rec];
          destruct (KeySetFacts.eq_dec y y) as [e|e]; [reflexivity|exfalso;auto]
        | cbn [open_co_wrt_co_rec];
          destruct (KeySetFacts.eq_dec y c0) as [e|e];
          [ exfalso; apply eq_var_false in E; exact (E (eq_sym e)) | reflexivity ] ]
     | |- open_co_wrt_co_rec ?k (g_Var_f ?c)
            (if eq_var ?c0 ?y then g_Var_b ?k else g_Var_f ?y) =
          (if KeySetFacts.eq_dec ?c0 ?y then g_Var_f ?c else g_Var_f ?y) =>
        destruct (eq_var c0 y) eqn:E;
        [ apply eq_var_true in E; subst c0;
          cbn [open_co_wrt_co_rec];
          destruct (lt_eq_lt_dec k k) as [[H1|H2]|H3]; [exfalso;lia| |exfalso;lia];
          cbn [open_co_wrt_co_rec];
          destruct (KeySetFacts.eq_dec y y) as [e|e]; [reflexivity|exfalso;auto]
        | cbn [open_co_wrt_co_rec];
          destruct (KeySetFacts.eq_dec c0 y) as [e|e];
          [ exfalso; apply eq_var_false in E; exact (E e) | reflexivity ] ]
     end).
Qed.

Lemma open_closeC_subst2 : forall a c0 c,
  open_tm_wrt_co (closeC_tm c0 0 a) (g_Var_f c) = subst_co_tm c0 (g_Var_f c) a.
Proof. intros; exact (proj1 closeC_open_subst_gen2 a c0 c 0). Qed.


Lemma diamond_open_close_tm : forall G D (a1 a2:tm) L,
  Eok a1 -> Eok a2 ->
  (forall x, x `notin` L -> exists z,
     Eok z /\ Par G D (open_tm_wrt_tm a1 (a_Var_f x)) z /\
              Par G D (open_tm_wrt_tm a2 (a_Var_f x)) z) ->
  exists L', exists d, Eok d /\
    forall x, x `notin` L' ->
      Par G D (open_tm_wrt_tm a1 (a_Var_f x)) (open_tm_wrt_tm d (a_Var_f x)) /\
      Par G D (open_tm_wrt_tm a2 (a_Var_f x)) (open_tm_wrt_tm d (a_Var_f x)).
Proof.
  intros G D a1 a2 L He1 He2 Hforall.
  destruct (atom_fresh (L \u (fv_tm_tm_tm a1 \u (fv_tm_tm_tm a2 \u fv_tm_tm_tm (erase_tm FixDef))))) as [x0 Hx0].
  pose proof Hx0 as Hx0L; apply notin_union_1 in Hx0L.
  pose proof Hx0 as Hx0R; apply notin_union_2 in Hx0R.
  pose proof Hx0R as Hx0fa1; apply notin_union_1 in Hx0fa1.
  pose proof Hx0R as Hx0R2; apply notin_union_2 in Hx0R2.
  pose proof Hx0R2 as Hx0fa2; apply notin_union_1 in Hx0fa2.
  pose proof Hx0R2 as Hx0fix; apply notin_union_2 in Hx0fix.
  destruct (Hforall x0 Hx0L) as [z0 [Hez0 [Hp1 Hp2]]].
  exists L. exists (closeT_tm x0 0 z0). split.
  - apply (Eok_closeT_tm z0 x0 0 Hez0).
  - intros x HxL.
    assert (Hu : lc_tm (a_Var_f x)) by apply lc_a_Var_f.
    assert (Hsrc1 : subst_tm_tm x0 (a_Var_f x) (open_tm_wrt_tm a1 (a_Var_f x0))
                    = open_tm_wrt_tm a1 (a_Var_f x)).
    { rewrite (subst_tm_open_tm_id a1 x0 (a_Var_f x) Hu).
      rewrite (subst_tm_fresh a1 x0 (a_Var_f x) Hx0fa1). reflexivity. }
    assert (Hsrc2 : subst_tm_tm x0 (a_Var_f x) (open_tm_wrt_tm a2 (a_Var_f x0))
                    = open_tm_wrt_tm a2 (a_Var_f x)).
    { rewrite (subst_tm_open_tm_id a2 x0 (a_Var_f x) Hu).
      rewrite (subst_tm_fresh a2 x0 (a_Var_f x) Hx0fa2). reflexivity. }
    assert (Hpar1 : Par G D (subst_tm_tm x0 (a_Var_f x) (open_tm_wrt_tm a1 (a_Var_f x0)))
                            (subst_tm_tm x0 (a_Var_f x) z0)).
    { apply (Par_subst_Eok G D (open_tm_wrt_tm a1 (a_Var_f x0)) z0 Hp1).
      - apply Eok_open_tm; [exact He1 | apply Eok_Var_f].
      - exact Hx0fix.
      - apply Par_Refl. apply lc_a_Var_f. }
    assert (Hpar2 : Par G D (subst_tm_tm x0 (a_Var_f x) (open_tm_wrt_tm a2 (a_Var_f x0)))
                            (subst_tm_tm x0 (a_Var_f x) z0)).
    { apply (Par_subst_Eok G D (open_tm_wrt_tm a2 (a_Var_f x0)) z0 Hp2).
      - apply Eok_open_tm; [exact He2 | apply Eok_Var_f].
      - exact Hx0fix.
      - apply Par_Refl. apply lc_a_Var_f. }
    rewrite Hsrc1 in Hpar1. rewrite Hsrc2 in Hpar2.
    rewrite <- (open_closeT_subst z0 x0 x) in Hpar1.
    rewrite <- (open_closeT_subst z0 x0 x) in Hpar2.
    split; assumption.
Qed.

Lemma diamond_open_close_co : forall G D (a1 a2:tm) L,
  (forall c, c `notin` L -> exists z,
     Eok z /\ Par G D (open_tm_wrt_co a1 (g_Var_f c)) z /\
              Par G D (open_tm_wrt_co a2 (g_Var_f c)) z) ->
  exists L', exists d, Eok d /\
    forall c, c `notin` L' ->
      Par G D (open_tm_wrt_co a1 (g_Var_f c)) (open_tm_wrt_co d (g_Var_f c)) /\
      Par G D (open_tm_wrt_co a2 (g_Var_f c)) (open_tm_wrt_co d (g_Var_f c)).
Proof.
  intros G D a1 a2 L Hforall.
  destruct (atom_fresh (L \u (cfv_tm a1 \u (cfv_tm a2 \u cfv_tm (erase_tm FixDef))))) as [c0 Hc0].
  pose proof Hc0 as Hc0L; apply notin_union_1 in Hc0L.
  pose proof Hc0 as Hc0R; apply notin_union_2 in Hc0R.
  pose proof Hc0R as Hc0a1; apply notin_union_1 in Hc0a1.
  pose proof Hc0R as Hc0R2; apply notin_union_2 in Hc0R2.
  pose proof Hc0R2 as Hc0a2; apply notin_union_1 in Hc0a2.
  pose proof Hc0R2 as Hc0fix; apply notin_union_2 in Hc0fix.
  destruct (Hforall c0 Hc0L) as [z0 [Hez0 [Hp1 Hp2]]].
  exists L. exists (closeC_tm c0 0 z0). split.
  - apply (Eok_closeC_tm z0 c0 0 Hez0).
  - intros c HcL.
    assert (Hg : lc_co (g_Var_f c)) by apply lc_g_Var_f.
    assert (Hsrc1 : subst_co_tm c0 (g_Var_f c) (open_tm_wrt_co a1 (g_Var_f c0))
                    = open_tm_wrt_co a1 (g_Var_f c)).
    { rewrite (subst_co_tm_open_co_id a1 c0 (g_Var_f c) Hg).
      rewrite (subst_co_fresh a1 c0 (g_Var_f c) Hc0a1). reflexivity. }
    assert (Hsrc2 : subst_co_tm c0 (g_Var_f c) (open_tm_wrt_co a2 (g_Var_f c0))
                    = open_tm_wrt_co a2 (g_Var_f c)).
    { rewrite (subst_co_tm_open_co_id a2 c0 (g_Var_f c) Hg).
      rewrite (subst_co_fresh a2 c0 (g_Var_f c) Hc0a2). reflexivity. }
    assert (Hpar1 : Par G D (subst_co_tm c0 (g_Var_f c) (open_tm_wrt_co a1 (g_Var_f c0)))
                            (subst_co_tm c0 (g_Var_f c) z0)).
    { apply (Par_subst_co G D (open_tm_wrt_co a1 (g_Var_f c0)) z0 Hp1); [exact Hg|exact Hc0fix]. }
    assert (Hpar2 : Par G D (subst_co_tm c0 (g_Var_f c) (open_tm_wrt_co a2 (g_Var_f c0)))
                            (subst_co_tm c0 (g_Var_f c) z0)).
    { apply (Par_subst_co G D (open_tm_wrt_co a2 (g_Var_f c0)) z0 Hp2); [exact Hg|exact Hc0fix]. }
    rewrite Hsrc1 in Hpar1. rewrite Hsrc2 in Hpar2.
    rewrite <- (open_closeC_subst2 z0 c0 c) in Hpar1.
    rewrite <- (open_closeC_subst2 z0 c0 c) in Hpar2.
    split; assumption.
Qed.

(* ================================================================== *)
(* Opening congruence *)
(* ================================================================== *)

Lemma Par_open_tm_cong : forall G D (a a':tm) L,
  Eok a ->
  (forall x, x `notin` L -> Par G D (open_tm_wrt_tm a (a_Var_f x))
                                     (open_tm_wrt_tm a' (a_Var_f x))) ->
  forall b b', Par G D b b' ->
  Par G D (open_tm_wrt_tm a b) (open_tm_wrt_tm a' b').
Proof.
  intros G D a a' L Hea Hbody b b' Hbb'.
  destruct (atom_fresh (L \u (fv_tm_tm_tm a \u (fv_tm_tm_tm a' \u fv_tm_tm_tm (erase_tm FixDef))))) as [x0 Hx0].
  pose proof Hx0 as Hx0L; apply notin_union_1 in Hx0L.
  pose proof Hx0 as Hx0R; apply notin_union_2 in Hx0R.
  pose proof Hx0R as Hx0a; apply notin_union_1 in Hx0a.
  pose proof Hx0R as Hx0R2; apply notin_union_2 in Hx0R2.
  pose proof Hx0R2 as Hx0a'; apply notin_union_1 in Hx0a'.
  pose proof Hx0R2 as Hx0fix; apply notin_union_2 in Hx0fix.
  pose proof (Par_lc _ _ _ _ Hbb') as [Hlb Hlb'].
  assert (Hpar := Hbody x0 Hx0L).
  assert (Hsub : Par G D (subst_tm_tm x0 b (open_tm_wrt_tm a (a_Var_f x0)))
                         (subst_tm_tm x0 b' (open_tm_wrt_tm a' (a_Var_f x0)))).
  { apply (Par_subst_Eok G D (open_tm_wrt_tm a (a_Var_f x0))
             (open_tm_wrt_tm a' (a_Var_f x0)) Hpar).
    - apply Eok_open_tm; [exact Hea | apply Eok_Var_f].
    - exact Hx0fix.
    - exact Hbb'. }
  rewrite (subst_tm_open_tm_id a x0 b Hlb) in Hsub.
  rewrite (subst_tm_open_tm_id a' x0 b' Hlb') in Hsub.
  rewrite (subst_tm_fresh a x0 b Hx0a) in Hsub.
  rewrite (subst_tm_fresh a' x0 b' Hx0a') in Hsub.
  exact Hsub.
Qed.

Lemma Par_open_co_cong : forall G D (a a':tm) L,
  (forall c, c `notin` L -> Par G D (open_tm_wrt_co a (g_Var_f c))
                                     (open_tm_wrt_co a' (g_Var_f c))) ->
  forall g, lc_co g ->
  Par G D (open_tm_wrt_co a g) (open_tm_wrt_co a' g).
Proof.
  intros G D a a' L Hbody g Hg.
  destruct (atom_fresh (L \u (cfv_tm a \u (cfv_tm a' \u cfv_tm (erase_tm FixDef))))) as [c0 Hc0].
  pose proof Hc0 as Hc0L; apply notin_union_1 in Hc0L.
  pose proof Hc0 as Hc0R; apply notin_union_2 in Hc0R.
  pose proof Hc0R as Hc0a; apply notin_union_1 in Hc0a.
  pose proof Hc0R as Hc0R2; apply notin_union_2 in Hc0R2.
  pose proof Hc0R2 as Hc0a'; apply notin_union_1 in Hc0a'.
  pose proof Hc0R2 as Hc0fix; apply notin_union_2 in Hc0fix.
  assert (Hpar := Hbody c0 Hc0L).
  assert (Hsub : Par G D (subst_co_tm c0 g (open_tm_wrt_co a (g_Var_f c0)))
                         (subst_co_tm c0 g (open_tm_wrt_co a' (g_Var_f c0)))).
  { apply (Par_subst_co G D (open_tm_wrt_co a (g_Var_f c0))
             (open_tm_wrt_co a' (g_Var_f c0)) Hpar c0 g Hg Hc0fix). }
  rewrite (subst_co_tm_open_co_id a c0 g Hg) in Hsub.
  rewrite (subst_co_tm_open_co_id a' c0 g Hg) in Hsub.
  rewrite (subst_co_fresh a c0 g Hc0a) in Hsub.
  rewrite (subst_co_fresh a' c0 g Hc0a') in Hsub.
  exact Hsub.
Qed.

(* ================================================================== *)
(* Common body relations for UAbs and UCAbs *)
(* ================================================================== *)

Lemma Par_UAbs_common_rel : forall G D rho (a b:tm) u,
  Par G D (a_UAbs rho a) u -> Par G D (a_UAbs rho b) u ->
  exists u' L, u = a_UAbs rho u' /\
    (forall x, x `notin` L -> Par G D (open_tm_wrt_tm a (a_Var_f x))
                                         (open_tm_wrt_tm u' (a_Var_f x))) /\
    (forall x, x `notin` L -> Par G D (open_tm_wrt_tm b (a_Var_f x))
                                         (open_tm_wrt_tm u' (a_Var_f x))).
Proof.
  intros G D rho a b u H1 H2.
  destruct (Par_UAbs_rel G D rho a u H1) as [u1 [Heq1 [L1 Hb1]]].
  destruct (Par_UAbs_rel G D rho b u H2) as [u2 [Heq2 [L2 Hb2]]].
  rewrite Heq1 in Heq2. inversion Heq2; subst u2.
  exists u1, (L1 \u L2). split; [exact Heq1|]. split.
  - intros x Hx. apply Hb1. apply notin_union_1 in Hx. exact Hx.
  - intros x Hx. apply Hb2. apply notin_union_2 in Hx. exact Hx.
Qed.

Lemma Par_UCAbs_common_rel : forall G D (a b:tm) u,
  Par G D (a_UCAbs a) u -> Par G D (a_UCAbs b) u ->
  exists u' L, u = a_UCAbs u' /\
    (forall c, c `notin` L -> Par G D (open_tm_wrt_co a (g_Var_f c))
                                         (open_tm_wrt_co u' (g_Var_f c))) /\
    (forall c, c `notin` L -> Par G D (open_tm_wrt_co b (g_Var_f c))
                                         (open_tm_wrt_co u' (g_Var_f c))).
Proof.
  intros G D a b u H1 H2.
  destruct (Par_UCAbs_rel G D a u H1) as [u1 [Heq1 [L1 Hb1]]].
  destruct (Par_UCAbs_rel G D b u H2) as [u2 [Heq2 [L2 Hb2]]].
  rewrite Heq1 in Heq2. inversion Heq2; subst u2.
  exists u1, (L1 \u L2). split; [exact Heq1|]. split.
  - intros c Hc. apply Hb1. apply notin_union_1 in Hc. exact Hc.
  - intros c Hc. apply Hb2. apply notin_union_2 in Hc. exact Hc.
Qed.

(* ================================================================== *)
(* Par diamond on Eok *)
(* ================================================================== *)

Lemma Par_diamond_Eok :
  forall G D a b, Eok a -> Par G D a b ->
  forall c, Par G D a c ->
  exists d, Eok d /\ Par G D b d /\ Par G D c d.
Proof.
  intros G D a b He Hpar.
  revert He.
  induction Hpar using Par_ind.
  - (* 1 Par_Refl *) intros Hea c Hc. exists c. split.
    + apply (Eok_Par G D a c Hea Hc).
    + split; [exact Hc | apply Par_Refl; exact (proj2 (Par_lc G D a c Hc))].
  - (* 2 Par_Beta *) intros Heapp c Hc.
    destruct (Eok_App_inv a rho b Heapp) as [Hea Heb].
    inversion Hc; subst; clear Hc.
    + (* second Refl *)
      exists (open_tm_wrt_tm a' b'). split.
      * pose proof (Eok_Par G D a (a_UAbs rho a') Hea Hpar1) as HAU.
        apply Eok_UAbs_inv in HAU.
        pose proof (Eok_Par G D b b' Heb Hpar2) as Hb'.
        apply (Eok_open_tm a' b' HAU Hb').
      * split.
        -- apply Par_Refl.
           apply (proj2 (Par_lc G D (a_App a rho b) (open_tm_wrt_tm a' b')
                        (Par_Beta G D a rho b a' b' Hpar1 Hpar2))).
        -- apply (Par_Beta G D a rho b a' b' Hpar1 Hpar2).
    + (* second Beta *)
      destruct (IHHpar1 Hea (a_UAbs rho a'0) H5) as [u [Heu [Hu1 Hu2]]].
      destruct (Par_UAbs_common_rel G D rho a' a'0 u Hu1 Hu2)
        as [u0 [L0 [Heq [Hb1 Hb2]]]].
      destruct (IHHpar2 Heb b'0 H6) as [w [Hew [Hw1 Hw2]]].
      exists (open_tm_wrt_tm u0 w). split.
      * apply Eok_open_tm.
        -- rewrite Heq in Heu. apply (Eok_UAbs_inv rho u0 Heu).
        -- exact Hew.
      * split.
        -- apply (Par_open_tm_cong G D a' u0 L0).
           ++ apply (Eok_UAbs_inv rho a' (Eok_Par G D a (a_UAbs rho a') Hea Hpar1)).
           ++ exact Hb1.
           ++ exact Hw1.
        -- apply (Par_open_tm_cong G D a'0 u0 L0).
           ++ apply (Eok_UAbs_inv rho a'0 (Eok_Par G D a (a_UAbs rho a'0) Hea H5)).
           ++ exact Hb2.
           ++ exact Hw2.
    + (* second App *)
      destruct (IHHpar1 Hea a'0 H5) as [u [Heu [Hu1 Hu2]]].
      destruct (Par_UAbs_rel G D rho a' u Hu1) as [u0 [Heq [L0 Hb1]]].
      rewrite Heq in Heu. rewrite Heq in Hu2.
      destruct (IHHpar2 Heb b'0 H6) as [w [Hew [Hw1 Hw2]]].
      exists (open_tm_wrt_tm u0 w). split.
      * apply Eok_open_tm.
        -- apply (Eok_UAbs_inv rho u0 Heu).
        -- exact Hew.
      * split.
        -- apply (Par_open_tm_cong G D a' u0 L0).
           ++ apply (Eok_UAbs_inv rho a' (Eok_Par G D a (a_UAbs rho a') Hea Hpar1)).
           ++ exact Hb1.
           ++ exact Hw1.
        -- apply (Par_Beta G D a'0 rho b'0 u0 w Hu2 Hw2).
  - (* 3 Par_App *) intros Heapp c Hc.
    destruct (Eok_App_inv a rho b Heapp) as [Hea Heb].
    inversion Hc; subst; clear Hc.
    + (* second Refl *)
      exists (a_App a' rho b'). split.
      * apply (Eok_Par G D (a_App a rho b) (a_App a' rho b') Heapp
               (Par_App G D a rho b a' b' Hpar1 Hpar2)).
      * split.
        -- apply Par_Refl.
           apply (proj2 (Par_lc G D (a_App a rho b) (a_App a' rho b')
                        (Par_App G D a rho b a' b' Hpar1 Hpar2))).
        -- apply (Par_App G D a rho b a' b' Hpar1 Hpar2).
    + (* second Beta *)
      destruct (IHHpar1 Hea (a_UAbs rho a'0) H5) as [u [Heu [Hu1 Hu2]]].
      destruct (Par_UAbs_rel G D rho a'0 u Hu2) as [u0 [Heq [L0 Hb2]]].
      rewrite Heq in Heu. rewrite Heq in Hu1.
      destruct (IHHpar2 Heb b'0 H6) as [w [Hew [Hw1 Hw2]]].
      exists (open_tm_wrt_tm u0 w). split.
      * apply Eok_open_tm.
        -- apply (Eok_UAbs_inv rho u0 Heu).
        -- exact Hew.
      * split.
        -- apply (Par_Beta G D a' rho b' u0 w Hu1 Hw1).
        -- apply (Par_open_tm_cong G D a'0 u0 L0).
           ++ apply (Eok_UAbs_inv rho a'0 (Eok_Par G D a (a_UAbs rho a'0) Hea H5)).
           ++ exact Hb2.
           ++ exact Hw2.
    + (* second App *)
      destruct (IHHpar1 Hea a'0 H5) as [u [Heu [Hu1 Hu2]]].
      destruct (IHHpar2 Heb b'0 H6) as [w [Hew [Hw1 Hw2]]].
      exists (a_App u rho w). split.
      * apply Eok_App; assumption.
      * split.
        -- apply (Par_App G D a' rho b' u w Hu1 Hw1).
        -- apply (Par_App G D a'0 rho b'0 u w Hu2 Hw2).
  - (* 4 Par_CBeta *) intros Heapp c Hc.
    apply Eok_CApp_inv in Heapp.
    inversion Hc; subst; clear Hc.
    + (* second Refl *)
      exists (open_tm_wrt_co a' g_Triv). split.
      * apply (Eok_Par G D (a_CApp a g_Triv) (open_tm_wrt_co a' g_Triv) (Eok_CApp a Heapp)
               (Par_CBeta G D a a' Hpar)).
      * split.
        -- apply Par_Refl.
           apply (proj2 (Par_lc G D (a_CApp a g_Triv) (open_tm_wrt_co a' g_Triv)
                        (Par_CBeta G D a a' Hpar))).
        -- apply (Par_CBeta G D a a' Hpar).
    + (* second CBeta *)
      destruct (IHHpar Heapp (a_UCAbs a'0) H2) as [u [Heu [Hu1 Hu2]]].
      destruct (Par_UCAbs_common_rel G D a' a'0 u Hu1 Hu2)
        as [u0 [L0 [Heq [Hb1 Hb2]]]].
      exists (open_tm_wrt_co u0 g_Triv). split.
      * rewrite Heq in Heu. apply Eok_open_co_triv. apply (Eok_UCAbs_inv u0 Heu).
      * split.
        -- apply (Par_open_co_cong G D a' u0 L0).
           ++ exact Hb1.
           ++ apply lc_g_Triv.
        -- apply (Par_open_co_cong G D a'0 u0 L0).
           ++ exact Hb2.
           ++ apply lc_g_Triv.
    + (* second CApp *)
      destruct (IHHpar Heapp a'0 H2) as [u [Heu [Hu1 Hu2]]].
      destruct (Par_UCAbs_rel G D a' u Hu1) as [u0 [Heq [L0 Hb1]]].
      rewrite Heq in Heu. rewrite Heq in Hu2.
      exists (open_tm_wrt_co u0 g_Triv). split.
      * apply Eok_open_co_triv. apply (Eok_UCAbs_inv u0 Heu).
      * split.
        -- apply (Par_open_co_cong G D a' u0 L0).
           ++ exact Hb1.
           ++ apply lc_g_Triv.
        -- apply (Par_CBeta G D a'0 u0 Hu2).
  - (* 5 Par_CApp *) intros Heapp c Hc.
    apply Eok_CApp_inv in Heapp.
    inversion Hc; subst; clear Hc.
    + (* second Refl *)
      exists (a_CApp a' g_Triv). split.
      * apply (Eok_Par G D (a_CApp a g_Triv) (a_CApp a' g_Triv) (Eok_CApp a Heapp)
               (Par_CApp G D a a' Hpar)).
      * split.
        -- apply Par_Refl.
           apply (proj2 (Par_lc G D (a_CApp a g_Triv) (a_CApp a' g_Triv)
                        (Par_CApp G D a a' Hpar))).
        -- apply (Par_CApp G D a a' Hpar).
    + (* second CBeta *)
      destruct (IHHpar Heapp (a_UCAbs a'0) H2) as [u [Heu [Hu1 Hu2]]].
      destruct (Par_UCAbs_rel G D a'0 u Hu2) as [u0 [Heq [L0 Hb2]]].
      rewrite Heq in Heu. rewrite Heq in Hu1.
      exists (open_tm_wrt_co u0 g_Triv). split.
      * apply Eok_open_co_triv. apply (Eok_UCAbs_inv u0 Heu).
      * split.
        -- apply (Par_CBeta G D a' u0 Hu1).
        -- apply (Par_open_co_cong G D a'0 u0 L0).
           ++ exact Hb2.
           ++ apply lc_g_Triv.
    + (* second CApp *)
      destruct (IHHpar Heapp a'0 H2) as [u [Heu [Hu1 Hu2]]].
      exists (a_CApp u g_Triv). split.
      * apply Eok_CApp. exact Heu.
      * split.
        -- apply (Par_CApp G D a' u Hu1).
        -- apply (Par_CApp G D a'0 u Hu2).
  - (* 6 Par_Abs *) intros Heabs c Hc.
    apply Eok_UAbs_inv in Heabs.
    inversion Hc; subst; clear Hc.
    + (* second Refl *)
      exists (a_UAbs rho a'). split.
      * apply (Eok_Par G D (a_UAbs rho a) (a_UAbs rho a') (Eok_UAbs rho a Heabs)
               (Par_Abs L G D rho a a' H)).
      * split.
        -- apply Par_Refl.
           apply (proj2 (Par_lc G D (a_UAbs rho a) (a_UAbs rho a')
                        (Par_Abs L G D rho a a' H))).
        -- apply (Par_Abs L G D rho a a' H).
    + (* second Abs *)
      destruct (diamond_open_close_tm G D a' a'0 (L \u L0)) as [L' [d0 [Hed0 Hopen]]].
      * apply (Eok_UAbs_inv rho a' (Eok_Par G D (a_UAbs rho a) (a_UAbs rho a') (Eok_UAbs rho a Heabs)
                                    (Par_Abs L G D rho a a' H))).
      * apply (Eok_UAbs_inv rho a'0 (Eok_Par G D (a_UAbs rho a) (a_UAbs rho a'0) (Eok_UAbs rho a Heabs)
                                     (Par_Abs L0 G D rho a a'0 H6))).
      * intros x Hx.
        pose proof Hx as Hx1; apply notin_union_1 in Hx1.
        pose proof Hx as Hx2; apply notin_union_2 in Hx2.
        destruct (H0 x Hx1 (Eok_open_tm a (a_Var_f x) Heabs (Eok_Var_f x))
                  (open_tm_wrt_tm a'0 (a_Var_f x)) (H6 x Hx2)) as [z [Hez [Hz1 Hz2]]].
        exists z. split; [exact Hez|]. split.
        -- exact Hz1.
        -- exact Hz2.
      * exists (a_UAbs rho d0). split.
        -- apply Eok_UAbs. exact Hed0.
        -- split.
           ++ apply (Par_Abs L' G D rho a' d0). intros x Hx. exact (proj1 (Hopen x Hx)).
           ++ apply (Par_Abs L' G D rho a'0 d0). intros x Hx. exact (proj2 (Hopen x Hx)).
  - (* 7 Par_Pi *) intros HePi c Hc.
    destruct (Eok_Pi_inv rho A B HePi) as [HeA HeB].
    inversion Hc; subst; clear Hc.
    + (* second Refl *)
      exists (a_Pi rho A' B'). split.
      * apply (Eok_Par G D (a_Pi rho A B) (a_Pi rho A' B') HePi
               (Par_Pi L G D rho A B A' B' Hpar H)).
      * split.
        -- apply Par_Refl.
           apply (proj2 (Par_lc G D (a_Pi rho A B) (a_Pi rho A' B')
                        (Par_Pi L G D rho A B A' B' Hpar H))).
        -- apply (Par_Pi L G D rho A B A' B' Hpar H).
    + (* second Pi *)
      destruct (IHHpar HeA A'0 H7) as [uA [HeuA [HuA1 HuA2]]].
      destruct (diamond_open_close_tm G D B' B'0 (L \u L0)) as [L' [dB [HedB HopenB]]].
      * apply (proj2 (Eok_Pi_inv rho A' B' (Eok_Par G D (a_Pi rho A B) (a_Pi rho A' B') HePi
                                     (Par_Pi L G D rho A B A' B' Hpar H)))).
      * apply (proj2 (Eok_Pi_inv rho A'0 B'0 (Eok_Par G D (a_Pi rho A B) (a_Pi rho A'0 B'0) HePi
                                     (Par_Pi L0 G D rho A B A'0 B'0 H7 H8)))).
      * intros x Hx.
        pose proof Hx as Hx1; apply notin_union_1 in Hx1.
        pose proof Hx as Hx2; apply notin_union_2 in Hx2.
        destruct (H0 x Hx1 (Eok_open_tm B (a_Var_f x) HeB (Eok_Var_f x))
                  (open_tm_wrt_tm B'0 (a_Var_f x)) (H8 x Hx2))
          as [z [Hez [Hz1 Hz2]]].
        exists z. split; [exact Hez|]. split.
        -- exact Hz1.
        -- exact Hz2.
      * exists (a_Pi rho uA dB). split.
        -- apply Eok_Pi; assumption.
        -- split.
           ++ apply (Par_Pi L' G D rho A' B' uA dB HuA1). intros x Hx. exact (proj1 (HopenB x Hx)).
           ++ apply (Par_Pi L' G D rho A'0 B'0 uA dB HuA2). intros x Hx. exact (proj2 (HopenB x Hx)).
  - (* 8 Par_CAbs *) intros Hecabs c Hc.
    apply Eok_UCAbs_inv in Hecabs.
    inversion Hc; subst; clear Hc.
    + (* second Refl *)
      exists (a_UCAbs a'). split.
      * apply (Eok_Par G D (a_UCAbs a) (a_UCAbs a') (Eok_UCAbs a Hecabs)
               (Par_CAbs L G D a a' H)).
      * split.
        -- apply Par_Refl.
           apply (proj2 (Par_lc G D (a_UCAbs a) (a_UCAbs a')
                        (Par_CAbs L G D a a' H))).
        -- apply (Par_CAbs L G D a a' H).
    + (* second CAbs *)
      destruct (diamond_open_close_co G D a' a'0 (L \u L0)) as [L' [d0 [Hed0 Hopen]]].
      * intros cc Hcc.
        pose proof Hcc as Hcc1; apply notin_union_1 in Hcc1.
        pose proof Hcc as Hcc2; apply notin_union_2 in Hcc2.
        destruct (H0 cc Hcc1 (Eok_open_co_var a cc Hecabs)
                  (open_tm_wrt_co a'0 (g_Var_f cc)) (H4 cc Hcc2))
          as [z [Hez [Hz1 Hz2]]].
        exists z. split; [exact Hez|]. split.
        -- exact Hz1.
        -- exact Hz2.
      * exists (a_UCAbs d0). split.
        -- apply Eok_UCAbs. exact Hed0.
        -- split.
           ++ apply (Par_CAbs L' G D a' d0). intros cc Hcc. exact (proj1 (Hopen cc Hcc)).
           ++ apply (Par_CAbs L' G D a'0 d0). intros cc Hcc. exact (proj2 (Hopen cc Hcc)).
  - (* 9 Par_CPi *) intros HeCPi c Hc.
    destruct (Eok_CPi_inv (Eq A B A1) a HeCPi) as [HePhi Hea].
    destruct (EokConstraint_components A B A1 HePhi) as [HeA [HeB HeA1]].
    inversion Hc; subst; clear Hc.
    + (* second Refl *)
      exists (a_CPi (Eq A' B' A1') a'). split.
      * apply (Eok_Par G D (a_CPi (Eq A B A1) a) (a_CPi (Eq A' B' A1') a') HeCPi
               (Par_CPi L G D A B A1 a A' B' A1' a' Hpar1 Hpar2 H Hpar3)).
      * split.
        -- apply Par_Refl.
           apply (proj2 (Par_lc G D (a_CPi (Eq A B A1) a) (a_CPi (Eq A' B' A1') a')
                        (Par_CPi L G D A B A1 a A' B' A1' a' Hpar1 Hpar2 H Hpar3))).
        -- apply (Par_CPi L G D A B A1 a A' B' A1' a' Hpar1 Hpar2 H Hpar3).
    + (* second CPi *)
      destruct (IHHpar1 HeA A'0 H7) as [uA [HeuA [HuA1 HuA2]]].
      destruct (IHHpar2 HeB B'0 H9) as [uB [HeuB [HuB1 HuB2]]].
      destruct (IHHpar3 HeA1 A1'0 H11) as [uA1 [HeuA1 [HuA11 HuA12]]].
      destruct (diamond_open_close_co G D a' a'0 (L \u L0)) as [L' [d0 [Hed0 Hopen]]].
      * intros cc Hcc.
        pose proof Hcc as Hcc1; apply notin_union_1 in Hcc1.
        pose proof Hcc as Hcc2; apply notin_union_2 in Hcc2.
        destruct (H0 cc Hcc1 (Eok_open_co_var a cc Hea)
                  (open_tm_wrt_co a'0 (g_Var_f cc)) (H10 cc Hcc2))
          as [z [Hez [Hz1 Hz2]]].
        exists z. split; [exact Hez|]. split.
        -- exact Hz1.
        -- exact Hz2.
      * exists (a_CPi (Eq uA uB uA1) d0). split.
        -- apply Eok_CPi.
           ++ apply Eok_Eq; assumption.
           ++ exact Hed0.
        -- split.
           ++ apply (Par_CPi L' G D A' B' A1' a' uA uB uA1 d0).
              ** exact HuA1.
              ** exact HuB1.
              ** intros cc Hcc. exact (proj1 (Hopen cc Hcc)).
              ** exact HuA11.
           ++ apply (Par_CPi L' G D A'0 B'0 A1'0 a'0 uA uB uA1 d0).
              ** exact HuA2.
              ** exact HuB2.
              ** intros cc Hcc. exact (proj2 (Hopen cc Hcc)).
              ** exact HuA12.
  - (* 10 Par_Axiom *) intros HeFam c Hc.
    inversion Hc; subst; clear Hc.
    + (* second Refl *)
      destruct (toplevel_binds_eq F a A H) as [HF [Ha HA]].
      exists a. split.
      * rewrite Ha. apply Eok_erase.
      * split.
        -- apply Par_Refl. rewrite Ha. apply lc_erase_FixDef.
        -- apply (Par_Axiom G D F a A H).
    + (* second Axiom *)
      destruct (toplevel_binds_eq F a A H) as [HF [Ha HA]].
      destruct (toplevel_binds_eq F c A0 H3) as [HF2 [HcEq HA2]].
      exists (erase_tm FixDef). split.
      * apply Eok_erase.
      * split.
        -- rewrite Ha. apply Par_Refl. apply lc_erase_FixDef.
        -- rewrite HcEq. apply Par_Refl. apply lc_erase_FixDef.
Qed.

(* ================================================================== *)
(* MultiPar diamond on Eok *)
(* ================================================================== *)

Inductive MultiParN : context -> available_props -> tm -> tm -> nat -> Prop :=
| MPN_Refl : forall G D a, lc_tm a -> MultiParN G D a a 0
| MPN_Step : forall G D a b c n,
    Par G D a b -> MultiParN G D b c n -> MultiParN G D a c (S n).

Lemma MPN_MP : forall G D a b n,
  MultiParN G D a b n -> MultiPar G D a b.
Proof.
  intros G D a b n H. induction H.
  - apply MP_Refl. exact H.
  - eapply MP_Step.
    + exact H.
    + exact IHMultiParN.
Qed.

Lemma MP_MPN : forall G D a b,
  MultiPar G D a b -> exists n, MultiParN G D a b n.
Proof.
  intros G D a b H. induction H.
  - exists 0. apply MPN_Refl. exact H.
  - destruct IHMultiPar as [n Hn].
    exists (S n). eapply MPN_Step; [exact H | exact Hn].
Qed.

Lemma MPN_trans : forall G D a b c n m,
  MultiParN G D a b n -> MultiParN G D b c m ->
  MultiParN G D a c (n + m).
Proof.
  intros G D a b c n m H.
  revert c m.
  induction H; intros c0 m Hbc.
  - cbn [Nat.add]. exact Hbc.
  - cbn [Nat.add]. eapply MPN_Step.
    + exact H.
    + apply IHMultiParN. exact Hbc.
Qed.

Lemma MPN_strip_Eok : forall M G D a b,
  Eok a -> Par G D a b ->
  forall c, MultiParN G D a c M ->
  exists d, Eok d /\ exists N1 N2,
    MultiParN G D b d N1 /\ MultiParN G D c d N2 /\
    N1 <= M /\ N2 <= 1.
Proof.
  intros M. induction M as [|M IH]; intros G D a b He Hpar c Hc.
  - inversion Hc; subst; clear Hc.
    exists b. split.
    + apply (Eok_Par G D c b He Hpar).
    + exists 0, 1. split.
      * apply MPN_Refl. apply (proj2 (Par_lc G D c b Hpar)).
      * split.
        -- apply MPN_Step with (b:=b).
           ++ exact Hpar.
           ++ apply MPN_Refl. apply (proj2 (Par_lc G D c b Hpar)).
        -- split; lia.
  - inversion Hc; subst; clear Hc.
    pose proof (Eok_Par G D a b0 He H0) as Heb0.
    destruct (Par_diamond_Eok G D a b He Hpar b0 H0) as [e [Hee [Hbe Hb0e]]].
    destruct (IH G D b0 e Heb0 Hb0e c H5) as [d [Hed [N1 [N2 [H1 [H2 [HN1 HN2]]]]]]].
    exists d. split; [exact Hed|].
    exists (S N1), N2. split.
    + eapply MPN_Step; [exact Hbe | exact H1].
    + split.
      * exact H2.
      * split; lia.
Qed.

Lemma MPN_diamond_Eok_aux :
  forall N G D a b,
    Eok a -> MultiParN G D a b N ->
    forall M c, MultiParN G D a c M ->
    exists d, Eok d /\ exists N1 M1,
      MultiParN G D b d N1 /\ MultiParN G D c d M1 /\
      N1 <= N + M /\ M1 <= N + M.
Proof.
  intros N. induction N as [|N IH]; intros G D a b He HN.
  - inversion HN; subst; clear HN.
    intros M c Hc.
    exists c. split.
    + apply (Eok_MultiPar G D b c He (MPN_MP G D b c M Hc)).
    + exists M, 0. split.
      * exact Hc.
      * split.
        -- apply MPN_Refl.
           apply (proj2 (Par_lc_MP G D b c (MPN_MP G D b c M Hc))).
        -- split; lia.
  - inversion HN; subst; clear HN.
    intros M c Hc.
    pose proof (Eok_Par G D a b0 He H0) as Heb0.
    destruct (MPN_strip_Eok M G D a b0 He H0 c Hc)
      as [d1 [Hed1 [M1 [M2 [Hm1 [Hm2 [HM1 HM2]]]]]]].
    destruct (IH G D b0 b Heb0 H5 M1 d1 Hm1)
      as [d [Hed [N1 [M1' [Hout1 [Hout2 [HN1 HM1']]]]]]].
    exists d. split; [exact Hed|].
    exists N1, (M2 + M1'). split.
    + exact Hout1.
    + split.
      * apply (MPN_trans G D c d1 d M2 M1' Hm2 Hout2).
      * split; lia.
Qed.

Lemma MultiPar_diamond_Eok :
  forall G D a b, Eok a -> MultiPar G D a b ->
  forall c, MultiPar G D a c ->
  exists d, Eok d /\ MultiPar G D b d /\ MultiPar G D c d.
Proof.
  intros G D a b He Hab c Hac.
  destruct (MP_MPN G D a b Hab) as [N HN].
  destruct (MP_MPN G D a c Hac) as [M HM].
  destruct (MPN_diamond_Eok_aux N G D a b He HN M c HM)
    as [d [Hed [N1 [M1 [Hb [Hc _]]]]]].
  exists d. split; [exact Hed|]. split.
  - apply (MPN_MP G D b d N1 Hb).
  - apply (MPN_MP G D c d M1 Hc).
Qed.

(* ================================================================== *)
(* MultiPar versions of substitution stability                        *)
(* ================================================================== *)

Lemma MultiPar_subst_Eok :
  forall G D a b, MultiPar G D a b -> Eok a ->
  forall x u v, x `notin` fv_tm_tm_tm (erase_tm FixDef) -> Par G D u v ->
  MultiPar G D (subst_tm_tm x u a) (subst_tm_tm x v b).
Proof.
  intros G D a b H. induction H as [G0 D0 a0 Hlc | G0 D0 a0 a' b0 Hpar Hmp IH].
  - intros He x u v Hxfix Huv.
    eapply MP_Step.
    + apply (Par_subst_Eok G0 D0 a0 a0 (Par_Refl G0 D0 a0 Hlc) He x u v Hxfix Huv).
    + apply MP_Refl.
      apply lc_subst_tm; [exact Hlc | exact (proj2 (Par_lc G0 D0 u v Huv))].
  - intros He x u v Hxfix Huv.
    eapply MP_Step.
    + apply (Par_subst_Eok G0 D0 a0 b0 Hpar He x u v Hxfix Huv).
    + apply (IH (Eok_Par G0 D0 a0 b0 He Hpar) x v v Hxfix).
      apply Par_Refl.
      exact (proj2 (Par_lc G0 D0 u v Huv)).
Qed.

Lemma MultiPar_subst_co :
  forall G D a b, MultiPar G D a b ->
  forall c g, lc_co g -> c `notin` cfv_tm (erase_tm FixDef) ->
  MultiPar G D (subst_co_tm c g a) (subst_co_tm c g b).
Proof.
  intros G D a b H. induction H as [G0 D0 a0 Hlc | G0 D0 a0 a' b0 Hpar Hmp IH].
  - intros c g Hg Hcfix.
    apply MP_Refl.
    apply lc_subst_co; [exact Hlc | exact Hg].
  - intros c g Hg Hcfix.
    eapply MP_Step.
    + apply (Par_subst_co G0 D0 a0 b0 Hpar c g Hg Hcfix).
    + apply IH; assumption.
Qed.
Require Import Lia.
Require Import List.
Import ListNotations.

(* ================================================================== *)
(* Basic combinators and erasure facts                                 *)
(* ================================================================== *)

Lemma MultiPar_trans : forall G D a b c,
  MultiPar G D a b -> MultiPar G D b c -> MultiPar G D a c.
Proof.
  intros G D a b c Hab.
  revert c.
  induction Hab; intros c Hbc.
  - exact Hbc.
  - eapply MP_Step.
    + exact H.
    + apply IHHab. exact Hbc.
Qed.

Ltac erase_tm_auto :=
  first
  [ match goal with
    | |- erase_tm (open_tm_wrt_tm_rec ?k ?u ?x) =
         open_tm_wrt_tm_rec ?k (erase_tm ?u) (erase_tm ?x) =>
        match goal with H : forall k0 u0,
          erase_tm (open_tm_wrt_tm_rec k0 u0 ?x) =
          open_tm_wrt_tm_rec k0 (erase_tm u0) (erase_tm ?x) |- _ =>
          exact (H k u) end
    | |- erase_brs (open_brs_wrt_tm_rec ?k ?u ?x) =
         open_brs_wrt_tm_rec ?k (erase_tm ?u) (erase_brs ?x) =>
        match goal with H : forall k0 u0,
          erase_brs (open_brs_wrt_tm_rec k0 u0 ?x) =
          open_brs_wrt_tm_rec k0 (erase_tm u0) (erase_brs ?x) |- _ =>
          exact (H k u) end
    | |- erase_constraint (open_constraint_wrt_tm_rec ?k ?u ?x) =
         open_constraint_wrt_tm_rec ?k (erase_tm ?u) (erase_constraint ?x) =>
        match goal with H : forall k0 u0,
          erase_constraint (open_constraint_wrt_tm_rec k0 u0 ?x) =
          open_constraint_wrt_tm_rec k0 (erase_tm u0) (erase_constraint ?x) |- _ =>
          exact (H k u) end
    end
  | reflexivity
  | (match goal with |- context [lt_eq_lt_dec ?a ?b] =>
       destruct (lt_eq_lt_dec a b) as [[Hlt|Heq]|Hgt];
       cbn [erase_tm]; reflexivity end)
  | (f_equal; erase_tm_auto) ].

Lemma erase_open_tm :
  (forall a, forall k u,
     erase_tm (open_tm_wrt_tm_rec k u a) =
     open_tm_wrt_tm_rec k (erase_tm u) (erase_tm a)) /\
  (forall b, forall k u,
     erase_brs (open_brs_wrt_tm_rec k u b) =
     open_brs_wrt_tm_rec k (erase_tm u) (erase_brs b)) /\
  (forall g : co, True) /\
  (forall phi, forall k u,
     erase_constraint (open_constraint_wrt_tm_rec k u phi) =
     open_constraint_wrt_tm_rec k (erase_tm u) (erase_constraint phi)).
Proof.
  apply (tm_mutind
    (fun a => forall k u,
       erase_tm (open_tm_wrt_tm_rec k u a) =
       open_tm_wrt_tm_rec k (erase_tm u) (erase_tm a))
    (fun b => forall k u,
       erase_brs (open_brs_wrt_tm_rec k u b) =
       open_brs_wrt_tm_rec k (erase_tm u) (erase_brs b))
    (fun g => True)
    (fun phi => forall k u,
       erase_constraint (open_constraint_wrt_tm_rec k u phi) =
       open_constraint_wrt_tm_rec k (erase_tm u) (erase_constraint phi))).
  all: try exact I.
  all: intros.
  all: try (match goal with |- context [a_App _ ?r _] => destruct r end).
  all: cbn [erase_tm erase_brs erase_constraint
           open_tm_wrt_tm_rec open_brs_wrt_tm_rec
           open_co_wrt_tm_rec open_constraint_wrt_tm_rec].
  all: try erase_tm_auto.
Qed.

Lemma erase_open_tm_tm : forall a k u,
  erase_tm (open_tm_wrt_tm_rec k u a) =
  open_tm_wrt_tm_rec k (erase_tm u) (erase_tm a).
Proof. intros; exact (proj1 erase_open_tm a k u). Qed.

Ltac solve_erase_co :=
  first
  [ reflexivity
  | match goal with
    | |- erase_tm (open_tm_wrt_co_rec ?k ?g ?x) = erase_tm ?x =>
        match goal with H : forall k0 g0, erase_tm (open_tm_wrt_co_rec k0 g0 ?x) = erase_tm ?x |- _ =>
          exact (H k g) end
    | |- erase_brs (open_brs_wrt_co_rec ?k ?g ?x) = erase_brs ?x =>
        match goal with H : forall k0 g0, erase_brs (open_brs_wrt_co_rec k0 g0 ?x) = erase_brs ?x |- _ =>
          exact (H k g) end
    | |- erase_constraint (open_constraint_wrt_co_rec ?k ?g ?x) = erase_constraint ?x =>
        match goal with H : forall k0 g0, erase_constraint (open_constraint_wrt_co_rec k0 g0 ?x) = erase_constraint ?x |- _ =>
          exact (H k g) end
    end ].

Ltac erase_co_auto :=
  first
  [ solve_erase_co
  | reflexivity
  | (f_equal; erase_co_auto) ].

Lemma erase_open_co :
  (forall a, forall k g,
     erase_tm (open_tm_wrt_co_rec k g a) = erase_tm a) /\
  (forall b, forall k g,
     erase_brs (open_brs_wrt_co_rec k g b) = erase_brs b) /\
  (forall g : co, True) /\
  (forall phi, forall k g,
     erase_constraint (open_constraint_wrt_co_rec k g phi) = erase_constraint phi).
Proof.
  apply (tm_mutind
    (fun a => forall k g, erase_tm (open_tm_wrt_co_rec k g a) = erase_tm a)
    (fun b => forall k g, erase_brs (open_brs_wrt_co_rec k g b) = erase_brs b)
    (fun g => True)
    (fun phi => forall k g,
       erase_constraint (open_constraint_wrt_co_rec k g phi) = erase_constraint phi)).
  all: try exact I.
  all: intros.
  all: try (match goal with |- context [a_App _ ?r _] => destruct r end).
  all: cbn [erase_tm erase_brs erase_constraint
           open_tm_wrt_co_rec open_brs_wrt_co_rec
           open_co_wrt_co_rec open_constraint_wrt_co_rec].
  all: try erase_co_auto.
Qed.

Lemma erase_open_co_tm : forall a k g,
  erase_tm (open_tm_wrt_co_rec k g a) = erase_tm a.
Proof. intros; exact (proj1 erase_open_co a k g). Qed.

Lemma lc_open_co_tm : forall a k g, lc_tm a ->
  lc_tm (open_tm_wrt_co_rec k g a).
Proof.
  intros. rewrite (proj1 clc_closed_open_co a 0 (lc_clc_tm a H) k (le_0_n k) g).
  exact H.
Qed.

Lemma lc_erase :
  (forall a (l:lc_tm a), lc_tm (erase_tm a)) /\
  (forall g (l:lc_co g), True) /\
  (forall b (l:lc_brs b), lc_brs (erase_brs b)) /\
  (forall phi (l:lc_constraint phi), lc_constraint (erase_constraint phi)).
Proof.
  apply (lc_mutind
    (fun a _ => lc_tm (erase_tm a))
    (fun g _ => True)
    (fun b _ => lc_brs (erase_brs b))
    (fun phi _ => lc_constraint (erase_constraint phi))).
  all: try exact I.
  all: intros.
  all: try (match goal with |- context [a_App _ ?r _] => destruct r end).
  all: cbn [erase_tm erase_brs erase_constraint] in *.
  all: try constructor.
  all: try assumption.
  all: try (intro x;
    match goal with
    | |- lc_tm (open_tm_wrt_tm (erase_tm ?b) (a_Var_f ?x)) =>
        match goal with
        | H : forall y, lc_tm (erase_tm (open_tm_wrt_tm ?b (a_Var_f y))) |- _ =>
            specialize (H x); unfold open_tm_wrt_tm in H;
            rewrite erase_open_tm_tm in H;
            cbn [erase_tm] in H; exact H
        end
    end).
  all: try (intro c;
    match goal with
    | |- lc_tm (open_tm_wrt_co (erase_tm ?B) (g_Var_f ?c)) =>
        match goal with
        | H : forall d, lc_tm (erase_tm (open_tm_wrt_co ?B (g_Var_f d))) |- _ =>
            specialize (H c); unfold open_tm_wrt_co in H;
            rewrite erase_open_co_tm in H;
            exact (lc_open_co_tm (erase_tm B) 0 (g_Var_f c) H)
        end
    end).
  all: try constructor.
Qed.

Definition lc_erase_tm : forall a, lc_tm a -> lc_tm (erase_tm a) :=
  fun a H => proj1 lc_erase a H.

(* Every locally closed term erases to an erased term. *)
Lemma erased_tm_erase_lc :
  (forall a, lc_tm a -> erased_tm (erase_tm a)) /\
  (forall g:co, lc_co g -> True) /\
  (forall b:brs, lc_brs b -> True) /\
  (forall p:constraint, lc_constraint p ->
     match p with
     | Eq a b A => erased_tm (erase_tm a) /\ erased_tm (erase_tm b) /\ erased_tm (erase_tm A)
     end).
Proof.
  apply (lc_mutind
    (fun a _ => erased_tm (erase_tm a))
    (fun g _ => True)
    (fun b _ => True)
    (fun p _ => (match p with
                | Eq a b A => erased_tm (erase_tm a) /\ erased_tm (erase_tm b) /\ erased_tm (erase_tm A)
                end))).
  - apply erased_a_Star.
  - apply erased_a_Var.
  - intros rho A b HlA IHA Hbody IHb. cbn [erase_tm].
    apply erased_a_Abs with (L:=empty). intros x Hx.
    change (erased_tm (open_tm_wrt_tm_rec 0 (erase_tm (a_Var_f x)) (erase_tm b))).
    rewrite <- erase_open_tm_tm. apply IHb.
  - intros rho b Hbody IHb. cbn [erase_tm].
    apply erased_a_Abs with (L:=empty). intros x Hx.
    change (erased_tm (open_tm_wrt_tm_rec 0 (erase_tm (a_Var_f x)) (erase_tm b))).
    rewrite <- erase_open_tm_tm. apply IHb.
  - intros a rho b Hla IHa Hlb IHb. destruct rho; cbn [erase_tm].
    + apply erased_a_App; assumption.
    + apply erased_a_App; [exact IHa | apply erased_a_Bullet].
  - apply erased_a_Fam.
  - apply erased_a_Const.
  - intros rho A B HlA IHA Hbody IHB. cbn [erase_tm].
    apply erased_a_Pi with (L:=empty); [exact IHA |]. intros x Hx.
    change (erased_tm (open_tm_wrt_tm_rec 0 (erase_tm (a_Var_f x)) (erase_tm B))).
    rewrite <- erase_open_tm_tm. apply IHB.
  - intros a g Hla IHa Hlg IHg. cbn [erase_tm]. exact IHa.
  - intros phi B Hphi Iphi Hbody IHB. destruct phi as [a b A]; cbn [erase_constraint erase_tm].
    apply erased_a_CPi with (L:=empty).
    + exact (proj1 Iphi).
    + exact (proj1 (proj2 Iphi)).
    + exact (proj2 (proj2 Iphi)).
    + intros c Hc.
      assert (HlcB : lc_tm (erase_tm B)).
      { specialize (Hbody c). unfold open_tm_wrt_co in Hbody.
        pose proof (lc_erase_tm (open_tm_wrt_co_rec 0 (g_Var_f c) B) Hbody) as Hx.
        rewrite erase_open_co_tm in Hx. exact Hx. }
      change (erased_tm (open_tm_wrt_co_rec 0 (g_Var_f c) (erase_tm B))).
      rewrite (open_tm_co_closed (erase_tm B) 0 (g_Var_f c) HlcB).
      specialize (IHB c). unfold open_tm_wrt_co in IHB.
      rewrite erase_open_co_tm in IHB. exact IHB.
  - intros phi b Hphi Iphi Hbody IHb. cbn [erase_tm].
    apply erased_a_CAbs with (L:=empty). intros c Hc.
    assert (HlcB : lc_tm (erase_tm b)).
    { specialize (Hbody c). unfold open_tm_wrt_co in Hbody.
      pose proof (lc_erase_tm (open_tm_wrt_co_rec 0 (g_Var_f c) b) Hbody) as Hx.
      rewrite erase_open_co_tm in Hx. exact Hx. }
    change (erased_tm (open_tm_wrt_co_rec 0 (g_Var_f c) (erase_tm b))).
    rewrite (open_tm_co_closed (erase_tm b) 0 (g_Var_f c) HlcB).
    specialize (IHb c). unfold open_tm_wrt_co in IHb.
    rewrite erase_open_co_tm in IHb. exact IHb.
  - intros b Hbody IHb. cbn [erase_tm].
    apply erased_a_CAbs with (L:=empty). intros c Hc.
    assert (HlcB : lc_tm (erase_tm b)).
    { specialize (Hbody c). unfold open_tm_wrt_co in Hbody.
      pose proof (lc_erase_tm (open_tm_wrt_co_rec 0 (g_Var_f c) b) Hbody) as Hx.
      rewrite erase_open_co_tm in Hx. exact Hx. }
    change (erased_tm (open_tm_wrt_co_rec 0 (g_Var_f c) (erase_tm b))).
    rewrite (open_tm_co_closed (erase_tm b) 0 (g_Var_f c) HlcB).
    specialize (IHb c). unfold open_tm_wrt_co in IHb.
    rewrite erase_open_co_tm in IHb. exact IHb.
  - intros a g Hla IHa Hlg IHg. cbn [erase_tm].
    apply erased_a_CApp. exact IHa.
  - apply erased_a_Bullet.
  - intros K. cbn [erase_tm]. apply erased_a_Star.
  - intros a brs5 Hla IHa Hlb IHb. cbn [erase_tm]. apply erased_a_Star.
  - intros; exact I.
  - intros; exact I.
  - intros; exact I.
  - intros; exact I.
  - intros; exact I.
  - intros; exact I.
  - intros; exact I.
  - intros; exact I.
  - intros; exact I.
  - intros; exact I.
  - intros; exact I.
  - intros; exact I.
  - intros; exact I.
  - intros; exact I.
  - intros; exact I.
  - intros; exact I.
  - intros; exact I.
  - intros; exact I.
  - intros; exact I.
  - intros; exact I.
  - intros; exact I.
  - intros; exact I.
  - intros; exact I.
  - intros; exact I.
  - intros; exact I.
  - intros; exact I.
  - intros a b A Hla IHa Hlb IHb HlA IHA. cbn [erase_constraint]. auto.
Qed.

Definition erased_tm_erase_lc_tm : forall a, lc_tm a -> erased_tm (erase_tm a) :=
  fun a H => proj1 erased_tm_erase_lc a H.

Lemma erased_tm_erase_constraint : forall a b A, lc_constraint (Eq a b A) ->
  erased_tm (erase_tm a) /\ erased_tm (erase_tm b) /\ erased_tm (erase_tm A).
Proof.
  intros a b A H.
  exact (proj2 (proj2 (proj2 erased_tm_erase_lc)) (Eq a b A) H).
Qed.

Lemma erased_tm_erase_constraint_1 : forall a b A, lc_constraint (Eq a b A) ->
  erased_tm (erase_tm a).
Proof. intros. exact (proj1 (erased_tm_erase_constraint a b A H)). Qed.
Lemma erased_tm_erase_constraint_2 : forall a b A, lc_constraint (Eq a b A) ->
  erased_tm (erase_tm b).
Proof. intros. exact (proj1 (proj2 (erased_tm_erase_constraint a b A H))). Qed.
Lemma erased_tm_erase_constraint_3 : forall a b A, lc_constraint (Eq a b A) ->
  erased_tm (erase_tm A).
Proof. intros. exact (proj2 (proj2 (erased_tm_erase_constraint a b A H))). Qed.

(* ================================================================== *)
(* Good is stable under extending the context                          *)
(* ================================================================== *)

Lemma Good_cons_Tm : forall G D x A,
  Good (erase_context G) D -> lc_tm A ->
  Good (erase_context ((x ~ Tm A) ++ G)) D.
Proof.
  intros G D x A [Hec Hjoin] HlcA. split.
  - unfold erase_context in *. cbn [EnvImpl.map]. constructor.
    + apply erased_Tm. apply (proj1 erased_tm_erase_lc A HlcA).
    + exact Hec.
  - intros c1 A' B1 T1 Hb Hin.
    unfold erase_context in Hb. cbn [EnvImpl.map] in Hb.
    change (binds c1 (Co (Eq A' B1 T1))
              ((x, Tm (erase_tm A)) :: EnvImpl.map erase_sort G)) in Hb.
    unfold binds in Hb. simpl in Hb.
    destruct Hb as [Heq | HinG].
    + inversion Heq.
    + destruct (Hjoin c1 A' B1 T1) as [C [HA HB]].
      * unfold binds. exact HinG.
      * exact Hin.
      * exists C. split.
        -- exact (Par_mono (erase_context G) D A' C HA (erase_context ((x ~ Tm A) ++ G)) D).
        -- exact (Par_mono (erase_context G) D B1 C HB (erase_context ((x ~ Tm A) ++ G)) D).
Qed.

Lemma Good_cons_Co_fresh : forall G D c phi,
  Good (erase_context G) D -> c `notin` D -> lc_constraint phi ->
  Good (erase_context ((c ~ Co phi) ++ G)) D.
Proof.
  intros G D c phi [Hec Hjoin] HcD Hlcphi. split.
  - unfold erase_context in *. cbn [EnvImpl.map]. constructor.
    + destruct phi as [a b A]; cbn [erase_sort erase_constraint].
      apply erased_Co.
      * apply (proj1 erased_tm_erase_lc a). apply (lc_constraint_eq_1 a b A Hlcphi).
      * apply (proj1 erased_tm_erase_lc b). apply (lc_constraint_eq_2 a b A Hlcphi).
      * apply (proj1 erased_tm_erase_lc A). apply (lc_constraint_eq_3 a b A Hlcphi).
    + exact Hec.
  - intros c1 A' B1 T1 Hb Hin.
    unfold erase_context in Hb. cbn [EnvImpl.map] in Hb.
    change (binds c1 (Co (Eq A' B1 T1))
              ((c, Co (erase_constraint phi)) :: EnvImpl.map erase_sort G)) in Hb.
    unfold binds in Hb. simpl in Hb.
    destruct Hb as [Heq | HinG].
    + inversion Heq. subst. exfalso. apply (HcD Hin).
    + destruct (Hjoin c1 A' B1 T1) as [C [HA HB]];
        [unfold binds; exact HinG | exact Hin |].
      exists C. split.
        -- exact (Par_mono (erase_context G) D A' C HA (erase_context ((c ~ Co phi) ++ G)) D).
        -- exact (Par_mono (erase_context G) D B1 C HB (erase_context ((c ~ Co phi) ++ G)) D).
Qed.

(* ================================================================== *)
(* Joinability predicates used by the mutual induction                 *)
(* ================================================================== *)

Definition JD (G:context) (D:available_props) (a b:tm) : Prop :=
  exists C, MultiPar (erase_context G) D (erase_tm a) C /\
            MultiPar (erase_context G) D (erase_tm b) C.

Definition JDC (G:context) (D:available_props) (p q:constraint) : Prop :=
  match p, q with
  | Eq a b A, Eq a' b' A' => JD G D a a' /\ JD G D b b' /\ JD G D A A'
  end.

Lemma JD_mono_D : forall G D D' a b,
  JD G D a b -> JD G D' a b.
Proof.
  intros G D D' a b [C [H1 H2]]. exists C. split;
    apply (MultiPar_mono (erase_context G) D);
    assumption.
Qed.

Lemma JD_sym : forall G D a b, JD G D a b -> JD G D b a.
Proof. intros G D a b [C [H1 H2]]. exists C. split; assumption. Qed.

Lemma JD_refl : forall G D a, lc_tm a -> JD G D a a.
Proof.
  intros G D a Hlc. exists (erase_tm a). split; apply MP_Refl; apply lc_erase_tm; assumption.
Qed.

Lemma JD_trans : forall G D a b c,
  JD G D a b -> JD G D b c -> JD G D a c.
Proof.
  intros G D a b c [C1 [Hab Hba]] [C2 [Hbc Hcb]].
  destruct (MultiPar_diamond_Eok (erase_context G) D (erase_tm b) C1
              (Eok_erase b) Hba C2 Hbc) as [d [_ [H1 H2]]].
  exists d. split.
  - eapply MultiPar_trans; [exact Hab | exact H1].
  - eapply MultiPar_trans; [exact Hcb | exact H2].
Qed.

Lemma JD_of_eq : forall G D a b, lc_tm a -> erase_tm a = erase_tm b -> JD G D a b.
Proof.
  intros G D a b Hlc Heq. exists (erase_tm a). split.
  - apply MP_Refl. apply lc_erase_tm. exact Hlc.
  - rewrite <- Heq. apply MP_Refl. apply lc_erase_tm. exact Hlc.
Qed.

(* ================================================================== *)
(* Step-indexed helpers                                                *)
(* ================================================================== *)

Lemma MPN_lc : forall G D a b n,
  MultiParN G D a b n -> lc_tm a /\ lc_tm b.
Proof.
  intros G D a b n H. induction H as [G0 D0 a0 Hlc | G0 D0 a0 b0 c0 n0 Hpar Hmp IH].
  - split; exact Hlc.
  - pose proof (Par_lc G0 D0 a0 b0 Hpar) as [Ha Hb].
    split; [exact Ha | exact (proj2 IH)].
Qed.

Lemma MPN_pad : forall n G D a b,
  MultiParN G D a b n -> forall m, MultiParN G D a b (n + m).
Proof.
  intros n G D a b H. induction H as [G0 D0 a0 Hlc | G0 D0 a0 b0 c0 n0 Hpar Hmp IH];
    intros m.
  - cbn [Nat.add]. induction m as [|m IHm].
    + apply MPN_Refl. exact Hlc.
    + eapply MPN_Step.
      * apply Par_Refl. exact Hlc.
      * exact IHm.
  - cbn [Nat.add]. eapply MPN_Step; [exact Hpar | apply IH].
Qed.

Lemma MPN_pad_to : forall n N G D a b,
  n <= N -> MultiParN G D a b n -> MultiParN G D a b N.
Proof.
  intros n N G D a b Hle H.
  replace N with (n + (N - n)) by lia.
  apply MPN_pad. exact H.
Qed.

Lemma MPN_subst_Eok_succ : forall n G D a b,
  MultiParN G D a b n -> Eok a ->
  forall x u v, x `notin` fv_tm_tm_tm (erase_tm FixDef) -> Par G D u v ->
  MultiParN G D (subst_tm_tm x u a) (subst_tm_tm x v b) (S n).
Proof.
  intros n G D a b H. induction H as [G0 D0 a0 Hlc | G0 D0 a0 b0 c0 n0 Hpar Hmp IH];
    intros He x u v Hx Huv.
  - cbn. eapply MPN_Step.
    + apply (Par_subst_Eok G0 D0 a0 a0 (Par_Refl G0 D0 a0 Hlc) He x u v Hx Huv).
    + apply MPN_Refl. apply lc_subst_tm; [exact Hlc | exact (proj2 (Par_lc G0 D0 u v Huv))].
  - cbn. eapply MPN_Step.
    + apply (Par_subst_Eok G0 D0 a0 b0 Hpar He x u v Hx Huv).
    + apply (IH (Eok_Par G0 D0 a0 b0 He Hpar) x v v Hx).
      apply Par_Refl. exact (proj2 (Par_lc G0 D0 u v Huv)).
Qed.

Lemma MPN_subst_co_succ : forall n G D a b,
  MultiParN G D a b n ->
  forall c g, lc_co g -> c `notin` cfv_tm (erase_tm FixDef) ->
  MultiParN G D (subst_co_tm c g a) (subst_co_tm c g b) (S n).
Proof.
  intros n G D a b H. induction H as [G0 D0 a0 Hlc | G0 D0 a0 b0 c0 n0 Hpar Hmp IH];
    intros c g Hg Hc.
  - cbn. eapply MPN_Step.
    + apply (Par_subst_co G0 D0 a0 a0 (Par_Refl G0 D0 a0 Hlc) c g Hg Hc).
    + apply MPN_Refl. apply lc_subst_co; [exact Hlc | exact Hg].
  - cbn. eapply MPN_Step.
    + apply (Par_subst_co G0 D0 a0 b0 Hpar c g Hg Hc).
    + apply (IH c g Hg Hc).
Qed.

Lemma MPN_close_open_tm : forall n G D (a1 a2:tm) x0 z0,
  Eok a1 -> Eok a2 ->
  x0 `notin` fv_tm_tm_tm a1 -> x0 `notin` fv_tm_tm_tm a2 ->
  x0 `notin` fv_tm_tm_tm (erase_tm FixDef) ->
  MultiParN G D (open_tm_wrt_tm a1 (a_Var_f x0)) z0 n ->
  MultiParN G D (open_tm_wrt_tm a2 (a_Var_f x0)) z0 n ->
  exists L', exists d,
    (forall x, x `notin` L' ->
       MultiParN G D (open_tm_wrt_tm a1 (a_Var_f x))
                     (open_tm_wrt_tm d (a_Var_f x)) (S n)) /\
    (forall x, x `notin` L' ->
       MultiParN G D (open_tm_wrt_tm a2 (a_Var_f x))
                     (open_tm_wrt_tm d (a_Var_f x)) (S n)).
Proof.
  intros n G D a1 a2 x0 z0 He1 He2 Hx0a1 Hx0a2 Hx0fix H1 H2.
  exists (fv_tm_tm_tm a1). exists (closeT_tm x0 0 z0). split.
  - intros x _.
    assert (Hu : lc_tm (a_Var_f x)) by apply lc_a_Var_f.
    pose proof (MPN_subst_Eok_succ n G D (open_tm_wrt_tm a1 (a_Var_f x0)) z0 H1
                  (Eok_open_tm a1 (a_Var_f x0) He1 (Eok_Var_f x0))
                  x0 (a_Var_f x) (a_Var_f x) Hx0fix
                  (Par_Refl G D (a_Var_f x) Hu)) as Hsub.
    assert (Hsrc : subst_tm_tm x0 (a_Var_f x) (open_tm_wrt_tm a1 (a_Var_f x0))
                   = open_tm_wrt_tm a1 (a_Var_f x)).
    { rewrite (subst_tm_open_tm_id a1 x0 (a_Var_f x) Hu).
      rewrite (subst_tm_fresh a1 x0 (a_Var_f x) Hx0a1). reflexivity. }
    rewrite Hsrc in Hsub.
    rewrite <- (open_closeT_subst z0 x0 x) in Hsub. exact Hsub.
  - intros x _.
    assert (Hu : lc_tm (a_Var_f x)) by apply lc_a_Var_f.
    pose proof (MPN_subst_Eok_succ n G D (open_tm_wrt_tm a2 (a_Var_f x0)) z0 H2
                  (Eok_open_tm a2 (a_Var_f x0) He2 (Eok_Var_f x0))
                  x0 (a_Var_f x) (a_Var_f x) Hx0fix
                  (Par_Refl G D (a_Var_f x) Hu)) as Hsub.
    assert (Hsrc : subst_tm_tm x0 (a_Var_f x) (open_tm_wrt_tm a2 (a_Var_f x0))
                   = open_tm_wrt_tm a2 (a_Var_f x)).
    { rewrite (subst_tm_open_tm_id a2 x0 (a_Var_f x) Hu).
      rewrite (subst_tm_fresh a2 x0 (a_Var_f x) Hx0a2). reflexivity. }
    rewrite Hsrc in Hsub.
    rewrite <- (open_closeT_subst z0 x0 x) in Hsub. exact Hsub.
Qed.

Lemma MPN_close_open_co : forall n G D (a1 a2:tm) c0 z0,
  c0 `notin` cfv_tm a1 -> c0 `notin` cfv_tm a2 ->
  c0 `notin` cfv_tm (erase_tm FixDef) ->
  MultiParN G D (open_tm_wrt_co a1 (g_Var_f c0)) z0 n ->
  MultiParN G D (open_tm_wrt_co a2 (g_Var_f c0)) z0 n ->
  exists L', exists d,
    (forall c, c `notin` L' ->
       MultiParN G D (open_tm_wrt_co a1 (g_Var_f c))
                     (open_tm_wrt_co d (g_Var_f c)) (S n)) /\
    (forall c, c `notin` L' ->
       MultiParN G D (open_tm_wrt_co a2 (g_Var_f c))
                     (open_tm_wrt_co d (g_Var_f c)) (S n)).
Proof.
  intros n G D a1 a2 c0 z0 Hc0a1 Hc0a2 Hc0fix H1 H2.
  exists (cfv_tm a1). exists (closeC_tm c0 0 z0). split.
  - intros c _.
    assert (Hg : lc_co (g_Var_f c)) by apply lc_g_Var_f.
    pose proof (MPN_subst_co_succ n G D (open_tm_wrt_co a1 (g_Var_f c0)) z0 H1
                  c0 (g_Var_f c) Hg Hc0fix) as Hsub.
    assert (Hsrc : subst_co_tm c0 (g_Var_f c) (open_tm_wrt_co a1 (g_Var_f c0))
                   = open_tm_wrt_co a1 (g_Var_f c)).
    { rewrite (subst_co_tm_open_co_id a1 c0 (g_Var_f c) Hg).
      rewrite (subst_co_fresh a1 c0 (g_Var_f c) Hc0a1). reflexivity. }
    rewrite Hsrc in Hsub.
    rewrite <- (open_closeC_subst2 z0 c0 c) in Hsub. exact Hsub.
  - intros c _.
    assert (Hg : lc_co (g_Var_f c)) by apply lc_g_Var_f.
    pose proof (MPN_subst_co_succ n G D (open_tm_wrt_co a2 (g_Var_f c0)) z0 H2
                  c0 (g_Var_f c) Hg Hc0fix) as Hsub.
    assert (Hsrc : subst_co_tm c0 (g_Var_f c) (open_tm_wrt_co a2 (g_Var_f c0))
                   = open_tm_wrt_co a2 (g_Var_f c)).
    { rewrite (subst_co_tm_open_co_id a2 c0 (g_Var_f c) Hg).
      rewrite (subst_co_fresh a2 c0 (g_Var_f c) Hc0a2). reflexivity. }
    rewrite Hsrc in Hsub.
    rewrite <- (open_closeC_subst2 z0 c0 c) in Hsub. exact Hsub.
Qed.

(* ================================================================== *)
(* Body relations of parallel steps on binders, for all atoms         *)
(* ================================================================== *)

Lemma Par_Pi_body_all : forall G D rho A B A' B',
  Eok B ->
  Par G D (a_Pi rho A B) (a_Pi rho A' B') ->
  forall x, Par G D (open_tm_wrt_tm B (a_Var_f x)) (open_tm_wrt_tm B' (a_Var_f x)).
Proof.
  intros G D rho A B A' B' HeB H x.
  inversion H; subst; clear H.
  - match goal with
    | Hlc : lc_tm (a_Pi ?r ?A0 ?B0) |- _ =>
      apply Par_Refl; exact (proj2 (lc_tm_pi_inv r A0 B0 Hlc) x)
    end.
  - match goal with
    | Hbody : forall y, y `notin` ?L ->
          Par G D (open_tm_wrt_tm ?B0 (a_Var_f y))
                  (open_tm_wrt_tm ?B1 (a_Var_f y)) |- _ =>
      destruct (atom_fresh (L \u (fv_tm_tm_tm B0 \u
                 (fv_tm_tm_tm B1 \u fv_tm_tm_tm (erase_tm FixDef))))) as [x0 Hx0];
      pose proof Hx0 as Hx0L; apply notin_union_1 in Hx0L;
      pose proof Hx0 as Hx0R; apply notin_union_2 in Hx0R;
      pose proof Hx0R as Hx0B; apply notin_union_1 in Hx0B;
      pose proof Hx0R as Hx0R2; apply notin_union_2 in Hx0R2;
      pose proof Hx0R2 as Hx0B'; apply notin_union_1 in Hx0B';
      pose proof Hx0R2 as Hx0fix; apply notin_union_2 in Hx0fix;
      assert (Hu : lc_tm (a_Var_f x)) by apply lc_a_Var_f;
      pose proof (Par_subst_Eok G D
                    (open_tm_wrt_tm B0 (a_Var_f x0))
                    (open_tm_wrt_tm B1 (a_Var_f x0))
                    (Hbody x0 Hx0L)
                    (Eok_open_tm B0 (a_Var_f x0) HeB (Eok_Var_f x0))
                    x0 (a_Var_f x) (a_Var_f x) Hx0fix
                    (Par_Refl G D (a_Var_f x) Hu)) as Hsub;
      rewrite (subst_tm_open_tm_id B0 x0 (a_Var_f x) Hu) in Hsub;
      rewrite (subst_tm_open_tm_id B1 x0 (a_Var_f x) Hu) in Hsub;
      rewrite (subst_tm_fresh B0 x0 (a_Var_f x) Hx0B) in Hsub;
      rewrite (subst_tm_fresh B1 x0 (a_Var_f x) Hx0B') in Hsub;
      exact Hsub
    end.
Qed.

Lemma Par_CPi_body_all : forall G D A B A1 a A' B' A1' a',
  Par G D (a_CPi (Eq A B A1) a) (a_CPi (Eq A' B' A1') a') ->
  forall c, Par G D (open_tm_wrt_co a (g_Var_f c))
                    (open_tm_wrt_co a' (g_Var_f c)).
Proof.
  intros G D A B A1 a A' B' A1' a' H c.
  inversion H; subst; clear H.
  - match goal with
    | Hlc : lc_tm (a_CPi ?phi ?a0) |- _ =>
      apply Par_Refl; exact (proj2 (lc_tm_cpi_inv phi a0 Hlc) c)
    end.
  - match goal with
    | Hbody : forall y, y `notin` ?L ->
          Par G D (open_tm_wrt_co ?a0 (g_Var_f y))
                  (open_tm_wrt_co ?a1 (g_Var_f y)) |- _ =>
      destruct (atom_fresh (L \u (cfv_tm a0 \u
                 (cfv_tm a1 \u cfv_tm (erase_tm FixDef))))) as [c0 Hc0];
      pose proof Hc0 as Hc0L; apply notin_union_1 in Hc0L;
      pose proof Hc0 as Hc0R; apply notin_union_2 in Hc0R;
      pose proof Hc0R as Hc0a; apply notin_union_1 in Hc0a;
      pose proof Hc0R as Hc0R2; apply notin_union_2 in Hc0R2;
      pose proof Hc0R2 as Hc0a'; apply notin_union_1 in Hc0a';
      pose proof Hc0R2 as Hc0fix; apply notin_union_2 in Hc0fix;
      assert (Hg : lc_co (g_Var_f c)) by apply lc_g_Var_f;
      pose proof (Par_subst_co G D
                    (open_tm_wrt_co a0 (g_Var_f c0))
                    (open_tm_wrt_co a1 (g_Var_f c0))
                    (Hbody c0 Hc0L) c0 (g_Var_f c) Hg Hc0fix) as Hsub;
      rewrite (subst_co_tm_open_co_id a0 c0 (g_Var_f c) Hg) in Hsub;
      rewrite (subst_co_tm_open_co_id a1 c0 (g_Var_f c) Hg) in Hsub;
      rewrite (subst_co_fresh a0 c0 (g_Var_f c) Hc0a) in Hsub;
      rewrite (subst_co_fresh a1 c0 (g_Var_f c) Hc0a') in Hsub;
      exact Hsub
    end.
Qed.

(* Explicit two-shape inversions of Par at Pi and CPi sources. *)

Lemma Par_Pi_inv_full : forall G D rho A B b,
  Par G D (a_Pi rho A B) b ->
  (b = a_Pi rho A B) \/
  (exists L A' B', b = a_Pi rho A' B' /\ Par G D A A' /\
     (forall x, x `notin` L ->
        Par G D (open_tm_wrt_tm B (a_Var_f x))
                (open_tm_wrt_tm B' (a_Var_f x)))).
Proof.
  intros G D rho A B b H. inversion H; subst; clear H.
  - left; reflexivity.
  - right; exists L, A', B'; split; [reflexivity|]; split; assumption.
Qed.

Lemma Par_CPi_inv_full : forall G D A B A1 a b,
  Par G D (a_CPi (Eq A B A1) a) b ->
  (b = a_CPi (Eq A B A1) a) \/
  (exists L A' B' A1' a', b = a_CPi (Eq A' B' A1') a' /\
     Par G D A A' /\ Par G D B B' /\ Par G D A1 A1' /\
     (forall c, c `notin` L ->
        Par G D (open_tm_wrt_co a (g_Var_f c))
                (open_tm_wrt_co a' (g_Var_f c)))).
Proof.
  intros G D A B A1 a b H. inversion H; subst; clear H.
  - left; reflexivity.
  - right; exists L, A', B', A1', a'.
    repeat split; assumption.
Qed.

Lemma MultiPar_Pi_inv_full : forall G D rho A B C,
  Eok A -> Eok B ->
  MultiPar G D (a_Pi rho A B) C ->
  exists CA CB, C = a_Pi rho CA CB /\
    MultiPar G D A CA /\
    (forall x, MultiPar G D (open_tm_wrt_tm B (a_Var_f x))
                             (open_tm_wrt_tm CB (a_Var_f x))).
Proof.
  intros G D rho A B C HEA HEB H.
  refine (MultiPar_ind
    (fun G0 D0 a0 b0 =>
       forall rho0 A0 B0, Eok A0 -> Eok B0 ->
       a0 = a_Pi rho0 A0 B0 ->
       exists CA CB, b0 = a_Pi rho0 CA CB /\
         MultiPar G0 D0 A0 CA /\
         (forall x, MultiPar G0 D0 (open_tm_wrt_tm B0 (a_Var_f x))
                                  (open_tm_wrt_tm CB (a_Var_f x))))
    _ _ G D (a_Pi rho A B) C H rho A B HEA HEB eq_refl).
  - intros G0 D0 a0 Hlc rho0 A0 B0 HEA0 HEB0 Heq.
    subst a0. exists A0, B0. split; [reflexivity|]. split.
    + apply MP_Refl. exact (proj1 (lc_tm_pi_inv rho0 A0 B0 Hlc)).
    + intros x. apply MP_Refl.
      exact (proj2 (lc_tm_pi_inv rho0 A0 B0 Hlc) x).
  - intros G0 D0 a0 b0 c0 Hpar Hmp IH rho0 A0 B0 HEA0 HEB0 Heq.
    subst a0. pose proof Hpar as Hpar0.
    destruct (Par_Pi_inv_full G0 D0 rho0 A0 B0 c0 Hpar)
      as [Hb | [L [A1 [B1 [Hb [HdomPar HbodyPar]]]]]].
    + subst c0. apply (IH rho0 A0 B0 HEA0 HEB0 eq_refl).
    + subst c0.
      assert (HEA1 : Eok A1) by
        (eapply Eok_Par; [exact HEA0 | exact HdomPar]);
      destruct (atom_fresh (L \u (fv_tm_tm_tm B0 \u
                 (fv_tm_tm_tm B1 \u fv_tm_tm_tm (erase_tm FixDef)))))
        as [x0 Hx0];
      pose proof Hx0 as Hx0L; apply notin_union_1 in Hx0L;
      pose proof Hx0 as Hx0R; apply notin_union_2 in Hx0R;
      pose proof Hx0R as Hx0B; apply notin_union_1 in Hx0B;
      pose proof Hx0R as Hx0R2; apply notin_union_2 in Hx0R2;
      pose proof Hx0R2 as Hx0B1; apply notin_union_1 in Hx0B1;
      pose proof Hx0R2 as Hx0fix; apply notin_union_2 in Hx0fix;
      assert (HEB1 : Eok B1) by
        (apply (Eok_open_tm_inv B1 x0); eapply Eok_Par;
         [apply (Eok_open_tm B0 (a_Var_f x0) HEB0 (Eok_Var_f x0)) |
          exact (HbodyPar x0 Hx0L)]);
      destruct (IH rho0 A1 B1 HEA1 HEB1 eq_refl)
        as [CA [CB [Heqc [Hdom Hbody]]]];
      exists CA, CB; split; [exact Heqc | split;
        [eapply MP_Step; [exact HdomPar | exact Hdom] |
         intros x; eapply MP_Step;
           [apply (Par_Pi_body_all G0 D0 rho0 A0 B0 A1 B1 HEB0 Hpar0) |
            apply Hbody]]].
Qed.

Lemma MultiPar_CPi_inv_full : forall G D A B A1 a C,
  Eok A -> Eok B -> Eok A1 -> Eok a ->
  MultiPar G D (a_CPi (Eq A B A1) a) C ->
  exists CA CB CA1 ca,
    C = a_CPi (Eq CA CB CA1) ca /\
    MultiPar G D A CA /\ MultiPar G D B CB /\
    MultiPar G D A1 CA1 /\
    (forall c, MultiPar G D (open_tm_wrt_co a (g_Var_f c))
                             (open_tm_wrt_co ca (g_Var_f c))).
Proof.
  intros G D A B A1 a C HEA HEB HEA1 HEa H.
  refine (MultiPar_ind
    (fun G0 D0 a0 b0 =>
       forall A0 B0 A10 a1, Eok A0 -> Eok B0 -> Eok A10 -> Eok a1 ->
       a0 = a_CPi (Eq A0 B0 A10) a1 ->
       exists CA CB CA1 ca,
         b0 = a_CPi (Eq CA CB CA1) ca /\
         MultiPar G0 D0 A0 CA /\ MultiPar G0 D0 B0 CB /\
         MultiPar G0 D0 A10 CA1 /\
         (forall c, MultiPar G0 D0 (open_tm_wrt_co a1 (g_Var_f c))
                                  (open_tm_wrt_co ca (g_Var_f c))))
    _ _ G D (a_CPi (Eq A B A1) a) C H A B A1 a HEA HEB HEA1 HEa eq_refl).
  - intros G0 D0 a0 Hlc A0 B0 A10 a1 HEA0 HEB0 HEA10 HEa1 Heq.
    subst a0. exists A0, B0, A10, a1. split; [reflexivity|]. split.
    + apply MP_Refl.
      exact (lc_constraint_eq_1 _ _ _
        (proj1 (lc_tm_cpi_inv (Eq A0 B0 A10) a1 Hlc))).
    + split.
      * apply MP_Refl.
        exact (lc_constraint_eq_2 _ _ _
          (proj1 (lc_tm_cpi_inv (Eq A0 B0 A10) a1 Hlc))).
      * split.
        -- apply MP_Refl.
           exact (lc_constraint_eq_3 _ _ _
             (proj1 (lc_tm_cpi_inv (Eq A0 B0 A10) a1 Hlc))).
        -- intros c. apply MP_Refl.
           exact (proj2 (lc_tm_cpi_inv (Eq A0 B0 A10) a1 Hlc) c).
  - intros G0 D0 a0 b0 c0 Hpar Hmp IH A0 B0 A10 a1 HEA0 HEB0 HEA10 HEa1 Heq.
    subst a0. pose proof Hpar as Hpar0.
    destruct (Par_CPi_inv_full G0 D0 A0 B0 A10 a1 c0 Hpar)
      as [Hb | [L [A1p [B1p [A11p [a2p [Hb [HdomA [HdomB [HdomA1 HbodyPar]]]]]]]]]];
      [subst c0; apply (IH A0 B0 A10 a1 HEA0 HEB0 HEA10 HEa1 eq_refl) |].
    subst c0.
    assert (HEA1p : Eok A1p) by
      (eapply Eok_Par; [exact HEA0 | exact HdomA]);
    assert (HEB1p : Eok B1p) by
      (eapply Eok_Par; [exact HEB0 | exact HdomB]);
    assert (HEA11p : Eok A11p) by
      (eapply Eok_Par; [exact HEA10 | exact HdomA1]);
    destruct (atom_fresh (L \u (cfv_tm a1 \u
               (cfv_tm a2p \u cfv_tm (erase_tm FixDef))))) as [c0 Hc0];
    pose proof Hc0 as Hc0L; apply notin_union_1 in Hc0L;
    pose proof Hc0 as Hc0R; apply notin_union_2 in Hc0R;
    pose proof Hc0R as Hc0a; apply notin_union_1 in Hc0a;
    pose proof Hc0R as Hc0R2; apply notin_union_2 in Hc0R2;
    pose proof Hc0R2 as Hc0a2; apply notin_union_1 in Hc0a2;
    pose proof Hc0R2 as Hc0fix; apply notin_union_2 in Hc0fix;
    assert (HEa2 : Eok a2p) by
      (apply (Eok_open_co_inv a2p c0); eapply Eok_Par;
       [apply (Eok_open_co_var a1 c0 HEa1) |
        exact (HbodyPar c0 Hc0L)]);
    destruct (IH A1p B1p A11p a2p HEA1p HEB1p HEA11p HEa2 eq_refl)
      as [CA [CB [CA1 [ca [Heqc [HdomA' [HdomB' [HdomA1' Hbody]]]]]]]];
    exists CA, CB, CA1, ca; split; [exact Heqc | split;
      [eapply MP_Step; [exact HdomA | exact HdomA'] | split;
       [eapply MP_Step; [exact HdomB | exact HdomB'] | split;
        [eapply MP_Step; [exact HdomA1 | exact HdomA1'] |
         intros c; eapply MP_Step;
           [apply (Par_CPi_body_all G0 D0 A0 B0 A10 a1 A1p B1p A11p a2p Hpar0) |
            apply Hbody]]]]].
Qed.

Lemma MPN_App_zip : forall K G D rho f1 f2 Cf g1 g2 Cg,
  MultiParN G D f1 Cf K -> MultiParN G D f2 Cf K ->
  MultiParN G D g1 Cg K -> MultiParN G D g2 Cg K ->
  MultiParN G D (a_App f1 rho g1) (a_App Cf rho Cg) K /\
  MultiParN G D (a_App f2 rho g2) (a_App Cf rho Cg) K.
Proof.
  intros K. induction K as [|K IH];
    intros G D rho f1 f2 Cf g1 g2 Cg Hf1 Hf2 Hg1 Hg2; split.
  - inversion Hf1; subst. inversion Hg1; subst.
    apply MPN_Refl. apply lc_a_App; assumption.
  - inversion Hf2; subst. inversion Hg2; subst.
    apply MPN_Refl. apply lc_a_App; assumption.
  - inversion Hf1; subst; clear Hf1. inversion Hg1; subst; clear Hg1.
    eapply MPN_Step.
    + apply Par_App; eassumption.
    + eapply IH; eassumption.
  - inversion Hf2; subst; clear Hf2. inversion Hg2; subst; clear Hg2.
    eapply MPN_Step.
    + apply Par_App; eassumption.
    + eapply IH; eassumption.
Qed.

Lemma MPN_CApp_zip : forall K G D f1 f2 Cf,
  MultiParN G D f1 Cf K -> MultiParN G D f2 Cf K ->
  MultiParN G D (a_CApp f1 g_Triv) (a_CApp Cf g_Triv) K /\
  MultiParN G D (a_CApp f2 g_Triv) (a_CApp Cf g_Triv) K.
Proof.
  intros K. induction K as [|K IH]; intros G D f1 f2 Cf Hf1 Hf2; split.
  - inversion Hf1; subst.
    apply MPN_Refl. apply lc_a_CApp; [assumption|apply lc_g_Triv].
  - inversion Hf2; subst.
    apply MPN_Refl. apply lc_a_CApp; [assumption|apply lc_g_Triv].
  - inversion Hf1; subst; clear Hf1.
    eapply MPN_Step.
    + apply Par_CApp. eassumption.
    + eapply IH; eassumption.
  - inversion Hf2; subst; clear Hf2.
    eapply MPN_Step.
    + apply Par_CApp. eassumption.
    + eapply IH; eassumption.
Qed.

(* ================================================================== *)
(* Self-substitution and fresh-opening substitution identities         *)
(* ================================================================== *)

Lemma subst_self_all :
  (forall a x, subst_tm_tm x (a_Var_f x) a = a) /\
  (forall b x, subst_tm_brs x (a_Var_f x) b = b) /\
  (forall g x, subst_tm_co x (a_Var_f x) g = g) /\
  (forall p x, subst_tm_constraint x (a_Var_f x) p = p).
Proof.
  apply (tm_mutind
    (fun a => forall x, subst_tm_tm x (a_Var_f x) a = a)
    (fun b => forall x, subst_tm_brs x (a_Var_f x) b = b)
    (fun g => forall x, subst_tm_co x (a_Var_f x) g = g)
    (fun p => forall x, subst_tm_constraint x (a_Var_f x) p = p)).
  all: intros; cbn [subst_tm_tm subst_tm_brs subst_tm_co subst_tm_constraint];
       try reflexivity;
       try (f_equal; eauto).
  all: match goal with
       | |- (if KeySetFacts.eq_dec ?y ?x then a_Var_f ?x else a_Var_f ?y) = a_Var_f ?y =>
           destruct (KeySetFacts.eq_dec y x); subst; reflexivity
       end.
Qed.

Lemma subst_tm_self : forall a x, subst_tm_tm x (a_Var_f x) a = a.
Proof. exact (proj1 subst_self_all). Qed.

Lemma subst_open_tm_fresh : forall a x u,
  lc_tm u -> x `notin` fv_tm_tm_tm a ->
  subst_tm_tm x u (open_tm_wrt_tm a (a_Var_f x)) = open_tm_wrt_tm a u.
Proof.
  intros. rewrite subst_tm_open_tm_id by assumption.
  rewrite subst_tm_fresh by assumption. reflexivity.
Qed.

Lemma subst_co_open_co_fresh : forall a c g,
  lc_co g -> c `notin` cfv_tm a ->
  subst_co_tm c g (open_tm_wrt_co a (g_Var_f c)) = open_tm_wrt_co a g.
Proof.
  intros. rewrite subst_co_tm_open_co_id by assumption.
  rewrite subst_co_fresh by assumption. reflexivity.
Qed.

Lemma subst_co_open_co_fresh2 : forall a c d,
  c `notin` cfv_tm a ->
  subst_co_tm c (g_Var_f d) (open_tm_wrt_co a (g_Var_f c))
    = open_tm_wrt_co a (g_Var_f d).
Proof.
  intros. apply subst_co_open_co_fresh. apply lc_g_Var_f. assumption.
Qed.

(* cfv freshness for open_tm_co_inj *)
Lemma open_tm_co_inj_cfv :
  (forall a k c, c `notin` cfv_tm a ->
     forall bb, c `notin` cfv_tm bb ->
       open_tm_wrt_co_rec k (g_Var_f c) a = open_tm_wrt_co_rec k (g_Var_f c) bb -> a = bb)
  /\ (forall a k c, c `notin` cfv_brs a ->
     forall bb, c `notin` cfv_brs bb ->
       open_brs_wrt_co_rec k (g_Var_f c) a = open_brs_wrt_co_rec k (g_Var_f c) bb -> a = bb)
  /\ (forall a k c, c `notin` cfv_co a ->
     forall bb, c `notin` cfv_co bb ->
       open_co_wrt_co_rec k (g_Var_f c) a = open_co_wrt_co_rec k (g_Var_f c) bb -> a = bb)
  /\ (forall a k c, c `notin` cfv_constraint a ->
     forall bb, c `notin` cfv_constraint bb ->
       open_constraint_wrt_co_rec k (g_Var_f c) a = open_constraint_wrt_co_rec k (g_Var_f c) bb -> a = bb).
Proof.
  apply (tm_mutind
    (fun a => forall k c, c `notin` cfv_tm a ->
       forall bb, c `notin` cfv_tm bb ->
         open_tm_wrt_co_rec k (g_Var_f c) a = open_tm_wrt_co_rec k (g_Var_f c) bb -> a = bb)
    (fun a => forall k c, c `notin` cfv_brs a ->
       forall bb, c `notin` cfv_brs bb ->
         open_brs_wrt_co_rec k (g_Var_f c) a = open_brs_wrt_co_rec k (g_Var_f c) bb -> a = bb)
    (fun a => forall k c, c `notin` cfv_co a ->
       forall bb, c `notin` cfv_co bb ->
         open_co_wrt_co_rec k (g_Var_f c) a = open_co_wrt_co_rec k (g_Var_f c) bb -> a = bb)
    (fun a => forall k c, c `notin` cfv_constraint a ->
       forall bb, c `notin` cfv_constraint bb ->
         open_constraint_wrt_co_rec k (g_Var_f c) a = open_constraint_wrt_co_rec k (g_Var_f c) bb -> a = bb)).
  all: intros.
  all: try (repeat match goal with
    | IH : forall (k0:nat) (c0:covar), _ |- _ =>
        pose proof (IH k c); pose proof (IH (S k) c); clear IH
    end).
  all: try (destruct bb; cbn [open_tm_wrt_co_rec open_brs_wrt_co_rec open_co_wrt_co_rec
        open_constraint_wrt_co_rec cfv_tm cfv_brs cfv_co cfv_constraint] in *;
        try discriminate).
  all: try (repeat match goal with
    | H : context [lt_eq_lt_dec ?a ?b] |- _ =>
        destruct (lt_eq_lt_dec a b) as [[?|?]|?]; cbn in *
    | |- context [lt_eq_lt_dec ?a ?b] =>
        destruct (lt_eq_lt_dec a b) as [[?|?]|?]; cbn
    end).
  all: try discriminate.
  all: try (repeat match goal with
    | H : _ `notin` (_ \u _) |- _ => apply notin_union_elim in H; destruct H
    end).
  all: try (match goal with
    | H : ?l = ?r |- _ =>
        lazymatch l with
        | context [open_tm_wrt_co_rec] => injection H; intros
        | context [open_brs_wrt_co_rec] => injection H; intros
        | context [open_co_wrt_co_rec] => injection H; intros
        | context [open_constraint_wrt_co_rec] => injection H; intros
        | g_Var_b _ => injection H; intros
        | g_Var_f _ => injection H; intros
        | _ => fail 1
        end
    end).
  all: try reflexivity.
  all: try assumption.
  all: try (f_equal; eauto 100).
  all: try eauto 100.
  all: try (f_equal; lia).
  all: try lia.
  all: try discriminate.
  all: try (exfalso; eauto using notin_singleton_1).
Qed.


Lemma closeT_tm_fv_fresh_gen :
  (forall a x k, x `notin` fv_tm_tm_tm (closeT_tm x k a)) /\
  (forall b x k, x `notin` fv_tm_tm_brs (closeT_brs x k b)) /\
  (forall g x k, x `notin` fv_tm_tm_co (closeT_co x k g)) /\
  (forall p x k, x `notin` fv_tm_tm_constraint (closeT_constraint x k p)).
Proof.
  apply (tm_mutind
    (fun a => forall x k, x `notin` fv_tm_tm_tm (closeT_tm x k a))
    (fun b => forall x k, x `notin` fv_tm_tm_brs (closeT_brs x k b))
    (fun g => forall x k, x `notin` fv_tm_tm_co (closeT_co x k g))
    (fun p => forall x k, x `notin` fv_tm_tm_constraint (closeT_constraint x k p))).
  all: intros; cbn [closeT_tm closeT_brs closeT_co closeT_constraint
                      fv_tm_tm_tm fv_tm_tm_brs fv_tm_tm_co fv_tm_tm_constraint].
  all: try (apply notin_union_3; eauto).
  all: try eauto.
  all: try apply notin_empty.
  all: try match goal with
           | |- context [if le_lt_dec ?k ?n then _ else _] =>
             destruct (le_lt_dec k n); cbn [fv_tm_tm_tm]; apply notin_empty
           end.
  all: try match goal with
           | |- context [if eq_var ?x ?y then _ else _] =>
             destruct (eq_var x y) eqn:E; cbn [fv_tm_tm_tm];
             [ apply notin_empty
             | apply (notin_singleton y x); apply eq_var_false in E;
               intro H; apply E; symmetry; exact H ]
           end.
Qed.

Lemma closeT_tm_fv_fresh : forall a x k, x `notin` fv_tm_tm_tm (closeT_tm x k a).
Proof. exact (proj1 closeT_tm_fv_fresh_gen). Qed.

Lemma closeC_tm_cfv_fresh_gen :
  (forall a c k, c `notin` cfv_tm (closeC_tm c k a)) /\
  (forall b c k, c `notin` cfv_brs (closeC_brs c k b)) /\
  (forall g c k, c `notin` cfv_co (closeC_co c k g)) /\
  (forall p c k, c `notin` cfv_constraint (closeC_constraint c k p)).
Proof.
  apply (tm_mutind
    (fun a => forall c k, c `notin` cfv_tm (closeC_tm c k a))
    (fun b => forall c k, c `notin` cfv_brs (closeC_brs c k b))
    (fun g => forall c k, c `notin` cfv_co (closeC_co c k g))
    (fun p => forall c k, c `notin` cfv_constraint (closeC_constraint c k p))).
  all: intros; cbn [closeC_tm closeC_brs closeC_co closeC_constraint
                      cfv_tm cfv_brs cfv_co cfv_constraint].
  all: try (apply notin_union_3; eauto).
  all: try eauto.
  all: try apply notin_empty.
  all: try (repeat match goal with
           | |- context [if le_lt_dec ?a ?b then _ else _] =>
             destruct (le_lt_dec a b); cbn [cfv_co]; apply notin_empty
           end).
  all: try (repeat match goal with
           | |- context [if eq_var ?a ?b then _ else _] =>
             destruct (eq_var a b) eqn:E; cbn [cfv_co];
             [ apply notin_empty | apply eq_var_false in E; fsetdec ]
           end).
Qed.

Lemma closeC_tm_cfv_fresh : forall a c k, c `notin` cfv_tm (closeC_tm c k a).
Proof. exact (proj1 closeC_tm_cfv_fresh_gen). Qed.

Lemma subst_co_self_all :
  (forall a c, subst_co_tm c (g_Var_f c) a = a) /\
  (forall b c, subst_co_brs c (g_Var_f c) b = b) /\
  (forall g c, subst_co_co c (g_Var_f c) g = g) /\
  (forall p c, subst_co_constraint c (g_Var_f c) p = p).
Proof.
  apply (tm_mutind
    (fun a => forall c, subst_co_tm c (g_Var_f c) a = a)
    (fun b => forall c, subst_co_brs c (g_Var_f c) b = b)
    (fun g => forall c, subst_co_co c (g_Var_f c) g = g)
    (fun p => forall c, subst_co_constraint c (g_Var_f c) p = p)).
  all: intros; cbn [subst_co_tm subst_co_brs subst_co_co subst_co_constraint];
       try reflexivity;
       try (f_equal; eauto).
  all: match goal with
       | |- (if KeySetFacts.eq_dec ?y ?x then g_Var_f ?x else g_Var_f ?y) = g_Var_f ?y =>
           destruct (KeySetFacts.eq_dec y x); subst; reflexivity
       end.
Qed.

Lemma subst_co_tm_self : forall a c, subst_co_tm c (g_Var_f c) a = a.
Proof. exact (proj1 subst_co_self_all). Qed.

(* ================================================================== *)
(* MultiPar congruence for the body of a Pi, with the domain fixed.    *)
(* ================================================================== *)

Lemma MultiPar_Pi_body_cong : forall G D rho A B C x0,
  lc_tm A -> Eok B -> Eok C ->
  x0 `notin` fv_tm_tm_tm B -> x0 `notin` fv_tm_tm_tm C ->
  x0 `notin` fv_tm_tm_tm (erase_tm FixDef) ->
  MultiPar G D (open_tm_wrt_tm B (a_Var_f x0))
              (open_tm_wrt_tm C (a_Var_f x0)) ->
  MultiPar G D (a_Pi rho A B) (a_Pi rho A C).
Proof.
  intros G D rho A B C x0 HA HB HC HxB HxC Hxfix H.
  generalize dependent H.
  generalize dependent C.
  generalize dependent B.
  intros B HB HxB C HC HxC H.
  refine (MultiPar_ind
    (fun G0 D0 p q =>
       forall x B0 C0, Eok B0 -> Eok C0 ->
         x `notin` fv_tm_tm_tm B0 -> x `notin` fv_tm_tm_tm C0 ->
         x `notin` fv_tm_tm_tm (erase_tm FixDef) ->
         p = open_tm_wrt_tm B0 (a_Var_f x) ->
         q = open_tm_wrt_tm C0 (a_Var_f x) ->
         MultiPar G0 D0 (a_Pi rho A B0) (a_Pi rho A C0))
    _ _ G D (open_tm_wrt_tm B (a_Var_f x0))
             (open_tm_wrt_tm C (a_Var_f x0)) H
          x0 B C HB HC HxB HxC Hxfix eq_refl eq_refl).
  - (* base *)
    intros G0 D0 p Hlc x B0 C0 HeB HeC HxBo HxCo Hxf Hp Hq.
    assert (HBopen : lc_tm (open_tm_wrt_tm B0 (a_Var_f x)))
      by (rewrite <- Hp; exact Hlc).
    assert (HCopen : lc_tm (open_tm_wrt_tm C0 (a_Var_f x)))
      by (rewrite <- Hq; exact Hlc).
    assert (Hopeneq : open_tm_wrt_tm B0 (a_Var_f x)
                    = open_tm_wrt_tm C0 (a_Var_f x))
      by (rewrite <- Hp, <- Hq; reflexivity).
    assert (Heq : B0 = C0).
    { eapply (proj1 open_tm_var_inj); [exact HxBo | exact HxCo | exact Hopeneq]. }
    subst C0.
    apply MP_Refl. apply lc_a_Pi.
    + exact HA.
    + apply (lc_open_tm_any B0 (a_Var_f x)); [apply lc_a_Var_f | exact HBopen].
  - (* step *)
    intros G0 D0 p c q Hpar Hmp IH x B0 C0 HeB HeC HxBo HxCo Hxf Hp Hq.
    rewrite Hp in Hpar. rewrite Hq in Hmp.
    set (d := closeT_tm x 0 q).
    assert (HeOpB : Eok (open_tm_wrt_tm B0 (a_Var_f x)))
      by (apply Eok_open_tm; [exact HeB | apply Eok_Var_f]).
    assert (HeCsrc : Eok q) by (eapply Eok_Par; [exact HeOpB | exact Hpar]).
    assert (HeD : Eok d) by (unfold d; apply Eok_closeT_tm; exact HeCsrc).
    assert (Hxd : x `notin` fv_tm_tm_tm d)
      by (unfold d; apply closeT_tm_fv_fresh).
    assert (HopenQ : q = open_tm_wrt_tm d (a_Var_f x)).
    { assert (Htmp : open_tm_wrt_tm d (a_Var_f x) = q).
      { unfold d. rewrite open_closeT_subst. apply subst_tm_self. }
      symmetry. exact Htmp. }
    eapply MP_Step.
    + (* head Pi step to d *)
      refine (Par_Pi (empty) G0 D0 rho A B0 A d _ _).
      * apply Par_Refl. exact HA.
      * intros y Hy.
        assert (Hsrc : subst_tm_tm x (a_Var_f y)
                         (open_tm_wrt_tm B0 (a_Var_f x))
                       = open_tm_wrt_tm B0 (a_Var_f y))
          by (apply subst_open_tm_fresh; [apply lc_a_Var_f | exact HxBo]).
        assert (Htgt : subst_tm_tm x (a_Var_f y) q
                       = open_tm_wrt_tm d (a_Var_f y)).
        { unfold d. symmetry. apply open_closeT_subst. }
        rewrite <- Hsrc, <- Htgt.
        eapply Par_subst_Eok; [exact Hpar | exact HeOpB | exact Hxf | apply Par_Refl; apply lc_a_Var_f].
    + (* tail, at the same atom *)
      eapply IH; [exact HeD | exact HeC | exact Hxd | exact HxCo | exact Hxf | exact HopenQ | exact Hq].
Qed.

(* ================================================================== *)
(* MultiPar congruence for UAbs and UCAbs bodies                       *)
(* ================================================================== *)

Lemma MultiPar_UAbs_body_cong : forall G D rho a c x0,
  Eok a -> Eok c ->
  x0 `notin` fv_tm_tm_tm a -> x0 `notin` fv_tm_tm_tm c ->
  x0 `notin` fv_tm_tm_tm (erase_tm FixDef) ->
  MultiPar G D (open_tm_wrt_tm a (a_Var_f x0))
              (open_tm_wrt_tm c (a_Var_f x0)) ->
  MultiPar G D (a_UAbs rho a) (a_UAbs rho c).
Proof.
  intros G D rho a c x0 Ha Hc Hxa Hxc Hxfix H.
  generalize dependent H.
  generalize dependent c.
  generalize dependent a.
  intros a Ha Hxa c Hc Hxc H.
  refine (MultiPar_ind
    (fun G0 D0 p q =>
       forall x A C, Eok A -> Eok C ->
         x `notin` fv_tm_tm_tm A -> x `notin` fv_tm_tm_tm C ->
         x `notin` fv_tm_tm_tm (erase_tm FixDef) ->
         p = open_tm_wrt_tm A (a_Var_f x) ->
         q = open_tm_wrt_tm C (a_Var_f x) ->
         MultiPar G0 D0 (a_UAbs rho A) (a_UAbs rho C))
    _ _ G D (open_tm_wrt_tm a (a_Var_f x0))
             (open_tm_wrt_tm c (a_Var_f x0)) H
          x0 a c Ha Hc Hxa Hxc Hxfix eq_refl eq_refl).
  - intros G0 D0 p Hlc x A C HeA HeC HxA HxC Hxf Hp Hq.
    assert (HAopen : lc_tm (open_tm_wrt_tm A (a_Var_f x)))
      by (rewrite <- Hp; exact Hlc).
    assert (Hopeneq : open_tm_wrt_tm A (a_Var_f x)
                    = open_tm_wrt_tm C (a_Var_f x))
      by (rewrite <- Hp, <- Hq; reflexivity).
    assert (Heq : A = C).
    { eapply (proj1 open_tm_var_inj); [exact HxA | exact HxC | exact Hopeneq]. }
    subst C.
    apply MP_Refl. apply lc_a_UAbs.
    apply (lc_open_tm_any A (a_Var_f x)); [apply lc_a_Var_f | exact HAopen].
  - intros G0 D0 p c0 q Hpar Hmp IH x A C HeA HeC HxA HxC Hxf Hp Hq.
    rewrite Hp in Hpar. rewrite Hq in Hmp.
    set (d := closeT_tm x 0 q).
    assert (HeOpA : Eok (open_tm_wrt_tm A (a_Var_f x)))
      by (apply Eok_open_tm; [exact HeA | apply Eok_Var_f]).
    assert (HeCsrc : Eok q) by (eapply Eok_Par; [exact HeOpA | exact Hpar]).
    assert (HeD : Eok d) by (unfold d; apply Eok_closeT_tm; exact HeCsrc).
    assert (Hxd : x `notin` fv_tm_tm_tm d)
      by (unfold d; apply closeT_tm_fv_fresh).
    assert (HopenQ : q = open_tm_wrt_tm d (a_Var_f x)).
    { assert (Htmp : open_tm_wrt_tm d (a_Var_f x) = q).
      { unfold d. rewrite open_closeT_subst. apply subst_tm_self. }
      symmetry. exact Htmp. }
    eapply MP_Step.
    + refine (Par_Abs (empty) G0 D0 rho A d _).
      intros y Hy.
      assert (Hsrc : subst_tm_tm x (a_Var_f y)
                       (open_tm_wrt_tm A (a_Var_f x))
                     = open_tm_wrt_tm A (a_Var_f y))
        by (apply subst_open_tm_fresh; [apply lc_a_Var_f | exact HxA]).
      assert (Htgt : subst_tm_tm x (a_Var_f y) q
                     = open_tm_wrt_tm d (a_Var_f y)).
      { unfold d. symmetry. apply open_closeT_subst. }
      rewrite <- Hsrc, <- Htgt.
      eapply Par_subst_Eok; [exact Hpar | exact HeOpA | exact Hxf | apply Par_Refl; apply lc_a_Var_f].
    + eapply IH; [exact HeD | exact HeC | exact Hxd | exact HxC | exact Hxf | exact HopenQ | exact Hq].
Qed.

Lemma MultiPar_UCAbs_body_cong : forall G D a c c0,
  c0 `notin` cfv_tm a -> c0 `notin` cfv_tm c ->
  c0 `notin` cfv_tm (erase_tm FixDef) ->
  MultiPar G D (open_tm_wrt_co a (g_Var_f c0))
              (open_tm_wrt_co c (g_Var_f c0)) ->
  MultiPar G D (a_UCAbs a) (a_UCAbs c).
Proof.
  intros G D a c c0 Hfa Hfc Hcf H.
  generalize dependent H.
  generalize dependent c.
  generalize dependent a.
  intros a Hfa c Hfc H.
  refine (MultiPar_ind
    (fun G0 D0 p q =>
       forall x A C, x `notin` cfv_tm A -> x `notin` cfv_tm C ->
         x `notin` cfv_tm (erase_tm FixDef) ->
         p = open_tm_wrt_co A (g_Var_f x) ->
         q = open_tm_wrt_co C (g_Var_f x) ->
         MultiPar G0 D0 (a_UCAbs A) (a_UCAbs C))
    _ _ G D (open_tm_wrt_co a (g_Var_f c0))
             (open_tm_wrt_co c (g_Var_f c0)) H
          c0 a c Hfa Hfc Hcf eq_refl eq_refl).
  - intros G0 D0 p Hlc x A C HxA HxC Hxf Hp Hq.
    assert (HAopen : lc_tm (open_tm_wrt_co A (g_Var_f x)))
      by (rewrite <- Hp; exact Hlc).
    assert (Hopeneq : open_tm_wrt_co A (g_Var_f x)
                    = open_tm_wrt_co C (g_Var_f x))
      by (rewrite <- Hp, <- Hq; reflexivity).
    assert (Heq : A = C).
    { eapply (proj1 open_tm_co_inj_cfv); [exact HxA | exact HxC | exact Hopeneq]. }
    subst C.
    apply MP_Refl. apply lc_a_UCAbs.
    intros cc. exact (lc_open_tm_co_any A (g_Var_f x) (lc_g_Var_f x) HAopen (g_Var_f cc) (lc_g_Var_f cc)).
  - intros G0 D0 p c1 q Hpar Hmp IH x A C HxA HxC Hxf Hp Hq.
    rewrite Hp in Hpar. rewrite Hq in Hmp.
    set (d := closeC_tm x 0 q).
    assert (Hxd : x `notin` cfv_tm d)
      by (unfold d; apply closeC_tm_cfv_fresh).
    assert (HopenQ : q = open_tm_wrt_co d (g_Var_f x)).
    { assert (Htmp : open_tm_wrt_co d (g_Var_f x) = q).
      { unfold d. rewrite open_closeC_subst. apply subst_co_tm_self. }
      symmetry. exact Htmp. }
    eapply MP_Step.
    + refine (Par_CAbs (empty) G0 D0 A d _).
      intros y Hy.
      assert (Hsrc : subst_co_tm x (g_Var_f y)
                       (open_tm_wrt_co A (g_Var_f x))
                     = open_tm_wrt_co A (g_Var_f y))
        by (apply subst_co_open_co_fresh2; exact HxA).
      assert (Htgt : subst_co_tm x (g_Var_f y) q
                     = open_tm_wrt_co d (g_Var_f y)).
      { unfold d. symmetry. apply open_closeC_subst2. }
      rewrite <- Hsrc, <- Htgt.
      eapply Par_subst_co; [exact Hpar | apply lc_g_Var_f | exact Hxf].
    + eapply IH; [exact Hxd | exact HxC | exact Hxf | exact HopenQ | exact Hq].
Qed.

(* ================================================================== *)
(* Congruence of MultiPar for applications and coercions             *)
(* ================================================================== *)

Lemma MultiPar_App_right : forall G D rho a b b',
  lc_tm a -> MultiPar G D b b' ->
  MultiPar G D (a_App a rho b) (a_App a rho b').
Proof.
  intros G D rho a b b' Hla H.
  induction H as [G0 D0 b0 Hlcb | G0 D0 b0 b1 b2 Hpar Hmp IH].
  - apply MP_Refl. apply lc_a_App; assumption.
  - eapply MP_Step.
    + apply Par_App; [apply Par_Refl; exact Hla | exact Hpar].
    + exact IH.
Qed.

Lemma MultiPar_App_cong : forall G D rho a a' b b',
  MultiPar G D a a' -> MultiPar G D b b' ->
  MultiPar G D (a_App a rho b) (a_App a' rho b').
Proof.
  intros G D rho a a' b b' H1.
  revert b b'.
  induction H1 as [G0 D0 a0 Hla | G0 D0 a0 a1 a2 Hpar Hmp IH];
    intros b b' H2.
  - apply (MultiPar_App_right G0 D0 rho a0 b b' Hla H2).
  - eapply MP_Step.
    + apply Par_App.
      * exact Hpar.
      * apply Par_Refl. exact (proj1 (Par_lc_MP G0 D0 b b' H2)).
    + apply IH. exact H2.
Qed.

Lemma MultiPar_CApp_cong : forall G D a b,
  MultiPar G D a b ->
  MultiPar G D (a_CApp a g_Triv) (a_CApp b g_Triv).
Proof.
  intros G D a b H.
  induction H as [G0 D0 a0 Hlc | G0 D0 a0 a1 a2 Hpar Hmp IH].
  - apply MP_Refl. apply lc_a_CApp; [exact Hlc | apply lc_g_Triv].
  - eapply MP_Step.
    + apply Par_CApp. exact Hpar.
    + exact IH.
Qed.

(* ================================================================== *)
(* Domain congruence for MultiPar over Pi                           *)
(* ================================================================== *)

Lemma MultiPar_Pi_dom_cong : forall G D rho A A' B,
  MultiPar G D A A' ->
  (forall y, lc_tm (open_tm_wrt_tm B (a_Var_f y))) ->
  MultiPar G D (a_Pi rho A B) (a_Pi rho A' B).
Proof.
  intros G D rho A A' B H.
  revert B.
  refine (MultiPar_ind
    (fun G0 D0 A0 A1 =>
       forall B0,
         (forall y, lc_tm (open_tm_wrt_tm B0 (a_Var_f y))) ->
         MultiPar G0 D0 (a_Pi rho A0 B0) (a_Pi rho A1 B0))
    _ _ G D A A' H).
  - intros G0 D0 a0 Hlc B0 HlcB.
    apply MP_Refl. apply lc_a_Pi; [exact Hlc | exact HlcB].
  - intros G0 D0 a0 b0 c0 Hpar Hmp IH B0 HlcB.
    eapply MP_Step.
    + refine (Par_Pi (empty) G0 D0 rho a0 B0 c0 B0 Hpar _).
      intros x Hx. apply Par_Refl. apply HlcB.
    + apply IH. exact HlcB.
Qed.

(* ================================================================== *)
(* Component congruence for MultiPar over CPi                        *)
(* ================================================================== *)

Lemma MultiPar_CPi_dom_cong : forall G D A CA B A1 a,
  lc_tm B -> lc_tm A1 ->
  (forall c, lc_tm (open_tm_wrt_co a (g_Var_f c))) ->
  MultiPar G D A CA ->
  MultiPar G D (a_CPi (Eq A B A1) a) (a_CPi (Eq CA B A1) a).
Proof.
  intros G D A CA B A1 a HB HA1 Hbody H.
  revert B A1 a HB HA1 Hbody.
  induction H as [G0 D0 A0 HlcA | G0 D0 A0 AF AI Hpar Hmp IH];
    intros B0 A10 a0 HB0 HA10 Hbody0.
  - apply MP_Refl. apply lc_a_CPi.
    + apply lc_Eq; assumption.
    + exact Hbody0.
  - eapply MP_Step.
    + refine (Par_CPi (empty) G0 D0 A0 B0 A10 a0 AI B0 A10 a0
                _ _ _ _).
      * exact Hpar.
      * apply Par_Refl. exact HB0.
      * intros c Hc. apply Par_Refl. exact (Hbody0 c).
      * apply Par_Refl. exact HA10.
    + apply IH; assumption.
Qed.

Lemma MultiPar_CPi_mid_cong : forall G D A B CB A1 a,
  lc_tm A -> lc_tm A1 ->
  (forall c, lc_tm (open_tm_wrt_co a (g_Var_f c))) ->
  MultiPar G D B CB ->
  MultiPar G D (a_CPi (Eq A B A1) a) (a_CPi (Eq A CB A1) a).
Proof.
  intros G D A B CB A1 a HA HA1 Hbody H.
  revert A A1 a HA HA1 Hbody.
  induction H as [G0 D0 B0 HlcB | G0 D0 B0 BF BI Hpar Hmp IH];
    intros A0 A10 a0 HA0 HA10 Hbody0.
  - apply MP_Refl. apply lc_a_CPi.
    + apply lc_Eq; assumption.
    + exact Hbody0.
  - eapply MP_Step.
    + refine (Par_CPi (empty) G0 D0 A0 B0 A10 a0 A0 BI A10 a0
                _ _ _ _).
      * apply Par_Refl. exact HA0.
      * exact Hpar.
      * intros c Hc. apply Par_Refl. exact (Hbody0 c).
      * apply Par_Refl. exact HA10.
    + apply IH; assumption.
Qed.

Lemma MultiPar_CPi_last_cong : forall G D A B A1 CA1 a,
  lc_tm A -> lc_tm B ->
  (forall c, lc_tm (open_tm_wrt_co a (g_Var_f c))) ->
  MultiPar G D A1 CA1 ->
  MultiPar G D (a_CPi (Eq A B A1) a) (a_CPi (Eq A B CA1) a).
Proof.
  intros G D A B A1 CA1 a HA HB Hbody H.
  revert A B a HA HB Hbody.
  induction H as [G0 D0 A10 HlcA1 | G0 D0 A10 A1F A1I Hpar Hmp IH];
    intros A0 B0 a0 HA0 HB0 Hbody0.
  - apply MP_Refl. apply lc_a_CPi.
    + apply lc_Eq; assumption.
    + exact Hbody0.
  - eapply MP_Step.
    + refine (Par_CPi (empty) G0 D0 A0 B0 A10 a0 A0 B0 A1I a0
                _ _ _ _).
      * apply Par_Refl. exact HA0.
      * apply Par_Refl. exact HB0.
      * intros c Hc. apply Par_Refl. exact (Hbody0 c).
      * exact Hpar.
    + apply IH; assumption.
Qed.

(* ================================================================== *)
(* Body congruence for MultiPar over CPi                            *)
(* ================================================================== *)

Lemma MultiPar_CPi_body_cong : forall G D A B A1 a c c0,
  lc_constraint (Eq A B A1) ->
  c0 `notin` cfv_tm a -> c0 `notin` cfv_tm c ->
  c0 `notin` cfv_tm (erase_tm FixDef) ->
  MultiPar G D (open_tm_wrt_co a (g_Var_f c0))
              (open_tm_wrt_co c (g_Var_f c0)) ->
  MultiPar G D (a_CPi (Eq A B A1) a) (a_CPi (Eq A B A1) c).
Proof.
  intros G D A B A1 a c c0 Hphi Hfa Hfc Hcf H.
  generalize dependent H.
  generalize dependent c.
  generalize dependent a.
  intros a Hfa c Hfc H.
  refine (MultiPar_ind
    (fun G0 D0 p q =>
       forall x A0 C0, x `notin` cfv_tm A0 -> x `notin` cfv_tm C0 ->
         x `notin` cfv_tm (erase_tm FixDef) ->
         p = open_tm_wrt_co A0 (g_Var_f x) ->
         q = open_tm_wrt_co C0 (g_Var_f x) ->
         MultiPar G0 D0 (a_CPi (Eq A B A1) A0)
                         (a_CPi (Eq A B A1) C0))
    _ _ G D (open_tm_wrt_co a (g_Var_f c0))
             (open_tm_wrt_co c (g_Var_f c0)) H
          c0 a c Hfa Hfc Hcf eq_refl eq_refl).
  - intros G0 D0 p Hlc x A0 C0 HxA HxC Hxf Hp Hq.
    assert (HAopen : lc_tm (open_tm_wrt_co A0 (g_Var_f x)))
      by (rewrite <- Hp; exact Hlc).
    assert (Hopeneq : open_tm_wrt_co A0 (g_Var_f x)
                    = open_tm_wrt_co C0 (g_Var_f x))
      by (rewrite <- Hp, <- Hq; reflexivity).
    assert (Heq : A0 = C0).
    { eapply (proj1 open_tm_co_inj_cfv); [exact HxA | exact HxC | exact Hopeneq]. }
    subst C0.
    apply MP_Refl. apply lc_a_CPi.
    + exact Hphi.
    + intros cc. exact (lc_open_tm_co_any A0 (g_Var_f x) (lc_g_Var_f x)
                          HAopen (g_Var_f cc) (lc_g_Var_f cc)).
  - intros G0 D0 p c1 q Hpar Hmp IH x A0 C0 HxA HxC Hxf Hp Hq.
    rewrite Hp in Hpar. rewrite Hq in Hmp.
    set (d := closeC_tm x 0 q).
    assert (Hxd : x `notin` cfv_tm d)
      by (unfold d; apply closeC_tm_cfv_fresh).
    assert (HopenQ : q = open_tm_wrt_co d (g_Var_f x)).
    { assert (Htmp : open_tm_wrt_co d (g_Var_f x) = q).
      { unfold d. rewrite open_closeC_subst. apply subst_co_tm_self. }
      symmetry. exact Htmp. }
    eapply MP_Step.
    + refine (Par_CPi (empty) G0 D0 A B A1 A0 A B A1 d _ _ _ _).
      * apply Par_Refl. exact (lc_constraint_eq_1 A B A1 Hphi).
      * apply Par_Refl. exact (lc_constraint_eq_2 A B A1 Hphi).
      * intros y Hy.
        assert (Hsrc : subst_co_tm x (g_Var_f y)
                         (open_tm_wrt_co A0 (g_Var_f x))
                       = open_tm_wrt_co A0 (g_Var_f y))
          by (apply subst_co_open_co_fresh2; exact HxA).
        assert (Htgt : subst_co_tm x (g_Var_f y) q
                       = open_tm_wrt_co d (g_Var_f y)).
        { unfold d. symmetry. apply open_closeC_subst2. }
        rewrite <- Hsrc, <- Htgt.
        eapply Par_subst_co; [exact Hpar | apply lc_g_Var_f | exact Hxf].
      * apply Par_Refl. exact (lc_constraint_eq_3 A B A1 Hphi).
    + eapply IH; [exact Hxd | exact HxC | exact Hxf | exact HopenQ | exact Hq].
Qed.

(* ================================================================== *)
(* Substitution congruence along a MultiPar chain of arguments       *)
(* ================================================================== *)

Lemma MultiPar_subst_Eok_multi_arg : forall G D a a',
  MultiPar G D a a' -> Eok a ->
  forall T x, Eok T -> lc_tm T ->
  x `notin` fv_tm_tm_tm (erase_tm FixDef) ->
  MultiPar G D (subst_tm_tm x a T) (subst_tm_tm x a' T).
Proof.
  intros G D a a' H.
  refine (MultiPar_ind
    (fun G0 D0 p q =>
       Eok p ->
       forall T x, Eok T -> lc_tm T ->
         x `notin` fv_tm_tm_tm (erase_tm FixDef) ->
         MultiPar G0 D0 (subst_tm_tm x p T) (subst_tm_tm x q T))
    _ _ G D a a' H).
  - intros G0 D0 p Hlc He T x HeT HlcT Hx.
    apply MP_Refl. apply lc_subst_tm; assumption.
  - intros G0 D0 p c q Hpar Hmp IH He T x HeT HlcT Hx.
    eapply MP_Step.
    + apply (Par_subst_Eok G0 D0 T T (Par_Refl G0 D0 T HlcT) HeT
               x p q Hx Hpar).
    + apply (IH (Eok_Par G0 D0 p q He Hpar) T x HeT HlcT Hx).
Qed.

(* ================================================================== *)
(* Extracting component joinability from joins of CPi and Pi terms   *)
(* ================================================================== *)

Lemma JD_CPi_components : forall G D A B A1 a A' B' A1' a',
  JD G D (a_CPi (Eq A B A1) a) (a_CPi (Eq A' B' A1') a') ->
  JD G D A A' /\ JD G D B B' /\ JD G D A1 A1'.
Proof.
  intros G D A B A1 a A' B' A1' a' H.
  destruct H as [C [H1 H2]].
  cbn [erase_tm erase_constraint] in H1, H2.
  destruct (MultiPar_CPi_inv_full (erase_context G) D
              (erase_tm A) (erase_tm B) (erase_tm A1) (erase_tm a) C
              (Eok_erase A) (Eok_erase B) (Eok_erase A1) (Eok_erase a) H1)
    as [CA [CB [CA1 [ca [HC [HA [HB [HA1 Hbody]]]]]]]].
  destruct (MultiPar_CPi_inv_full (erase_context G) D
              (erase_tm A') (erase_tm B') (erase_tm A1') (erase_tm a') C
              (Eok_erase A') (Eok_erase B') (Eok_erase A1') (Eok_erase a') H2)
    as [CA' [CB' [CA1' [ca' [HC' [HA' [HB' [HA1' Hbody']]]]]]]].
  rewrite HC' in HC.
  inversion HC; subst.
  split; [|split].
  - exists CA. split; assumption.
  - exists CB. split; assumption.
  - exists CA1. split; assumption.
Qed.

Lemma JD_CPi_body_lc : forall G D A B A1 b A' B' A1' b',
  lc_tm (erase_tm b) -> lc_tm (erase_tm b') ->
  JD G D (a_CPi (Eq A B A1) b) (a_CPi (Eq A' B' A1') b') ->
  JD G D b b'.
Proof.
  intros G D A B A1 b A' B' A1' b' Hlb Hlb' H.
  destruct H as [C [H1 H2]].
  cbn [erase_tm erase_constraint] in H1, H2.
  destruct (MultiPar_CPi_inv_full (erase_context G) D
              (erase_tm A) (erase_tm B) (erase_tm A1) (erase_tm b) C
              (Eok_erase A) (Eok_erase B) (Eok_erase A1) (Eok_erase b) H1)
    as [CA [CB [CA1 [ca [HC [HA [HB [HA1 Hbody]]]]]]]].
  destruct (MultiPar_CPi_inv_full (erase_context G) D
              (erase_tm A') (erase_tm B') (erase_tm A1') (erase_tm b') C
              (Eok_erase A') (Eok_erase B') (Eok_erase A1') (Eok_erase b') H2)
    as [CA' [CB' [CA1' [ca' [HC' [HA' [HB' [HA1' Hbody']]]]]]]].
  rewrite HC' in HC.
  inversion HC; subst.
  destruct (atom_fresh (empty:atoms)) as [c0 Hc0].
  exists (open_tm_wrt_co ca (g_Var_f c0)). split.
  - rewrite <- (open_tm_co_closed (erase_tm b) 0 (g_Var_f c0) Hlb).
    exact (Hbody c0).
  - rewrite <- (open_tm_co_closed (erase_tm b') 0 (g_Var_f c0) Hlb').
    exact (Hbody' c0).
Qed.

Lemma JD_Pi_fst : forall G D rho A B A' B',
  JD G D (a_Pi rho A B) (a_Pi rho A' B') ->
  JD G D A A'.
Proof.
  intros G D rho A B A' B' H.
  destruct H as [C [H1 H2]].
  cbn [erase_tm] in H1, H2.
  destruct (MultiPar_Pi_inv_full (erase_context G) D rho
              (erase_tm A) (erase_tm B) C
              (Eok_erase A) (Eok_erase B) H1)
    as [CA [CB [HC [HA Hbody]]]].
  destruct (MultiPar_Pi_inv_full (erase_context G) D rho
              (erase_tm A') (erase_tm B') C
              (Eok_erase A') (Eok_erase B') H2)
    as [CA' [CB' [HC' [HA' Hbody']]]].
  rewrite HC' in HC. inversion HC; subst.
  exists CA. split; assumption.
Qed.

Lemma JD_Pi_body_chain : forall G D rho A B A' B',
  JD G D (a_Pi rho A B) (a_Pi rho A' B') ->
  exists CB,
    (forall x, MultiPar (erase_context G) D
                 (open_tm_wrt_tm (erase_tm B) (a_Var_f x))
                 (open_tm_wrt_tm CB (a_Var_f x))) /\
    (forall x, MultiPar (erase_context G) D
                 (open_tm_wrt_tm (erase_tm B') (a_Var_f x))
                 (open_tm_wrt_tm CB (a_Var_f x))).
Proof.
  intros G D rho A B A' B' H.
  destruct H as [C [H1 H2]].
  cbn [erase_tm] in H1, H2.
  destruct (MultiPar_Pi_inv_full (erase_context G) D rho
              (erase_tm A) (erase_tm B) C
              (Eok_erase A) (Eok_erase B) H1)
    as [CA [CB [HC [HA Hbody]]]].
  destruct (MultiPar_Pi_inv_full (erase_context G) D rho
              (erase_tm A') (erase_tm B') C
              (Eok_erase A') (Eok_erase B') H2)
    as [CA' [CB' [HC' [HA' Hbody']]]].
  rewrite HC' in HC. inversion HC; subst.
  exists CB. split.
  - exact Hbody.
  - intros x. exact (Hbody' x).
Qed.

(* ================================================================== *)
(* Erasure of opening with a convertible term argument               *)
(* ================================================================== *)

Lemma erase_open_conv_arg : forall b x g,
  erase_tm (open_tm_wrt_tm b (a_Conv (a_Var_f x) g)) =
  erase_tm (open_tm_wrt_tm b (a_Var_f x)).
Proof.
  intros b x g.
  unfold open_tm_wrt_tm.
  rewrite (erase_open_tm_tm b 0 (a_Conv (a_Var_f x) g)).
  rewrite (erase_open_tm_tm b 0 (a_Var_f x)).
  cbn [erase_tm]. reflexivity.
Qed.

(* ================================================================== *)
(* Lifting JD through application and coercion application           *)
(* ================================================================== *)

Lemma JD_CApp : forall G D a b g1 g2,
  JD G D a b -> JD G D (a_CApp a g1) (a_CApp b g2).
Proof.
  intros G D a b g1 g2 [C [H1 H2]].
  exists (a_CApp C g_Triv). split;
    cbn [erase_tm]; apply MultiPar_CApp_cong; assumption.
Qed.

Lemma JD_App : forall G D rho a1 a2 b1 b2,
  JD G D a1 b1 -> JD G D a2 b2 ->
  JD G D (a_App a1 rho a2) (a_App b1 rho b2).
Proof.
  intros G D rho a1 a2 b1 b2 [C1 [H1a H1b]] [C2 [H2a H2b]].
  destruct rho.
  - exists (a_App C1 Rel C2). split; cbn [erase_tm].
    + apply (MultiPar_App_cong (erase_context G) D Rel
               (erase_tm a1) C1 (erase_tm a2) C2 H1a H2a).
    + apply (MultiPar_App_cong (erase_context G) D Rel
               (erase_tm b1) C1 (erase_tm b2) C2 H1b H2b).
  - exists (a_App C1 Irrel a_Bullet). split; cbn [erase_tm].
    + apply (MultiPar_App_cong (erase_context G) D Irrel
               (erase_tm a1) C1 a_Bullet a_Bullet H1a
               (MP_Refl (erase_context G) D a_Bullet lc_a_Bullet)).
    + apply (MultiPar_App_cong (erase_context G) D Irrel
               (erase_tm b1) C1 a_Bullet a_Bullet H1b
               (MP_Refl (erase_context G) D a_Bullet lc_a_Bullet)).
Qed.

(* ================================================================== *)
(* Locally closed erasures of binder bodies                          *)
(* ================================================================== *)

Lemma lc_erase_cpi_body : forall phi B,
  lc_tm (a_CPi phi B) -> lc_tm (erase_tm B).
Proof.
  intros phi B Hlc.
  destruct (atom_fresh (empty:atoms)) as [c0 Hc0].
  destruct (lc_tm_cpi_inv phi B Hlc) as [_ Hbody].
  pose proof (lc_erase_tm (open_tm_wrt_co B (g_Var_f c0)) (Hbody c0)) as H.
  unfold open_tm_wrt_co in H.
  rewrite (erase_open_co_tm B 0 (g_Var_f c0)) in H.
  exact H.
Qed.

(* ================================================================== *)
(* Motives for the mutual induction                                  *)
(* ================================================================== *)

Definition Pdef (G:context) (D:available_props) (g:co) (a b:tm)
  (_:AnnDefEq G D g a b) : Prop :=
  Good (erase_context G) D -> JD G D a b.

Definition Piso (G:context) (D:available_props) (g:co)
  (p q:constraint) (_:AnnIso G D g p q) : Prop :=
  Good (erase_context G) D -> JDC G D p q.

(* ================================================================== *)
(* The easy cases of AnnDefEq                                         *)
(* ================================================================== *)

Lemma case_An_Assn : forall (G:context) (D:available_props)
    (c:covar) (a b A:tm) (a0:AnnCtx G)
    (b0:binds c (Co (Eq a b A)) G) (i:c `in` D),
  Pdef G D (g_Var_f c) a b (An_Assn G D c a b A a0 b0 i).
Proof.
  intros. unfold Pdef. intros Hg.
  exact (Good_Assn_MultiPar_join G D c a b A Hg b0 i).
Qed.

Lemma case_An_Refl : forall (G:context) (D:available_props)
    (a A:tm) (a0:AnnTyping G a A),
  Pdef G D (g_Refl a) a a (An_Refl G D a A a0).
Proof.
  intros. unfold Pdef. intros Hg.
  apply JD_refl. exact (proj1 (AnnTyping_wf G a A a0)).
Qed.

Lemma case_An_EraseEq : forall (G:context) (D:available_props)
    (a b:tm) (g:co) (A B:tm) (a0:AnnTyping G a A)
    (a1:AnnTyping G b B) (e:erase_tm a = erase_tm b)
    (a2:AnnDefEq G (dom G) g A B),
  Pdef G (dom G) g A B a2 ->
  Pdef G D (g_Refl2 a b g) a b (An_EraseEq G D a b g A B a0 a1 e a2).
Proof.
  intros G D a b g A B Htya Htyb He Hdom IH. unfold Pdef. intros Hg.
  apply (JD_of_eq G D a b).
  - exact (proj1 (AnnTyping_wf G a A Htya)).
  - exact He.
Qed.

Lemma case_An_Sym : forall (G:context) (D:available_props)
    (g:co) (a b B A:tm) (g1:co) (a0:AnnTyping G b B)
    (a1:AnnTyping G a A) (a2:AnnDefEq G (dom G) g1 B A),
  Pdef G (dom G) g1 B A a2 ->
  forall a3:AnnDefEq G D g b a,
  Pdef G D g b a a3 ->
  Pdef G D (g_Sym g) a b (An_Sym G D g a b B A g1 a0 a1 a2 a3).
Proof.
  intros G D g a b B A g1 Htyb Htya Hdom IHdom Hmain IHmain.
  unfold Pdef in IHmain |- *. intros Hg.
  apply JD_sym. apply IHmain. exact Hg.
Qed.

Lemma case_An_Trans : forall (G:context) (D:available_props)
    (g1 g2:co) (a b a1 A A1:tm) (g3:co)
    (a0:AnnDefEq G D g1 a a1),
  Pdef G D g1 a a1 a0 ->
  forall a2:AnnDefEq G D g2 a1 b,
  Pdef G D g2 a1 b a2 ->
  forall (a3:AnnTyping G a A) (a4:AnnTyping G a1 A1)
    (a5:AnnDefEq G (dom G) g3 A A1),
  Pdef G (dom G) g3 A A1 a5 ->
  Pdef G D (g_Trans g1 g2) a b
    (An_Trans G D g1 g2 a b a1 A A1 g3 a0 a2 a3 a4 a5).
Proof.
  intros G D g1 g2 a b a1 A A1 g3 H1 IH1 H2 IH2
         Htya Htya1 Hdom IHdom.
  unfold Pdef in IH1, IH2 |- *. intros Hg.
  eapply JD_trans.
  - apply IH1. exact Hg.
  - apply IH2. exact Hg.
Qed.

Lemma case_An_Beta : forall (G:context) (D:available_props)
    (a1 a2 B0 B1:tm) (a:AnnTyping G a1 B0)
    (a0:AnnTyping G a2 B1) (e:erase_tm B0 = erase_tm B1)
    (b:Beta (erase_tm a1) (erase_tm a2)),
  Pdef G D (g_Beta a1 a2) a1 a2 (An_Beta G D a1 a2 B0 B1 a a0 e b).
Proof.
  intros G D a1 a2 B0 B1 Hty1 Hty2 He Hbeta.
  unfold Pdef. intros Hg.
  exists (erase_tm a2). split.
  - exact (Beta_MultiPar (erase_tm a1) (erase_tm a2) Hbeta
             (erase_context G) D).
  - apply MP_Refl. apply lc_erase_tm.
    exact (proj1 (AnnTyping_wf G a2 B1 Hty2)).
Qed.

Lemma case_An_AppCong : forall (G:context) (D:available_props)
    (g1:co) (rho:relflag) (g2:co) (a1 a2 b1 b2 A B:tm) (g3:co)
    (a:AnnDefEq G D g1 a1 b1),
  Pdef G D g1 a1 b1 a ->
  forall a0:AnnDefEq G D g2 a2 b2,
  Pdef G D g2 a2 b2 a0 ->
  forall (a3:AnnTyping G (a_App a1 rho a2) A)
    (a4:AnnTyping G (a_App b1 rho b2) B)
    (a5:AnnDefEq G (dom G) g3 A B),
  Pdef G (dom G) g3 A B a5 ->
  Pdef G D (g_AppCong g1 rho g2) (a_App a1 rho a2) (a_App b1 rho b2)
    (An_AppCong G D g1 rho g2 a1 a2 b1 b2 A B g3 a a0 a3 a4 a5).
Proof.
  intros G D g1 rho g2 a1 a2 b1 b2 A B g3 H1 IH1 H2 IH2
         Hty1 Hty2 Hdom IHdom.
  unfold Pdef in IH1, IH2 |- *. intros Hg.
  apply (JD_App G D rho a1 a2 b1 b2).
  - apply IH1. exact Hg.
  - apply IH2. exact Hg.
Qed.

Lemma case_An_PiFst : forall (G:context) (D:available_props)
    (g:co) (A1 A2:tm) (rho:relflag) (B1 B2:tm)
    (a:AnnDefEq G D g (a_Pi rho A1 B1) (a_Pi rho A2 B2)),
  Pdef G D g (a_Pi rho A1 B1) (a_Pi rho A2 B2) a ->
  Pdef G D (g_PiFst g) A1 A2
    (An_PiFst G D g A1 A2 rho B1 B2 a).
Proof.
  intros G D g A1 A2 rho B1 B2 H IH.
  unfold Pdef in IH |- *. intros Hg.
  exact (JD_Pi_fst G D rho A1 B1 A2 B2 (IH Hg)).
Qed.

Lemma case_An_CAppCong : forall (G:context) (D:available_props)
    (g1 g2 g3:co) (a1 b1 a2 b2 a3 b3 A B:tm) (g4:co)
    (a:AnnDefEq G D g1 a1 b1),
  Pdef G D g1 a1 b1 a ->
  forall a0:AnnDefEq G (dom G) g2 a2 b2,
  Pdef G (dom G) g2 a2 b2 a0 ->
  forall a4:AnnDefEq G (dom G) g3 a3 b3,
  Pdef G (dom G) g3 a3 b3 a4 ->
  forall (a5:AnnTyping G (a_CApp a1 g2) A)
    (a6:AnnTyping G (a_CApp b1 g3) B)
    (a7:AnnDefEq G (dom G) g4 A B),
  Pdef G (dom G) g4 A B a7 ->
  Pdef G D (g_CAppCong g1 g2 g3) (a_CApp a1 g2) (a_CApp b1 g3)
    (An_CAppCong G D g1 g2 g3 a1 b1 a2 b2 a3 b3 A B g4 a a0 a4 a5 a6 a7).
Proof.
  intros G D g1 g2 g3 a1 b1 a2 b2 a3 b3 A B g4
         H1 IH1 H2 IH2 H3 IH3 Hty1 Hty2 Hdom IHdom.
  unfold Pdef in IH1 |- *. intros Hg.
  apply (JD_CApp G D a1 b1 g2 g3). apply IH1. exact Hg.
Qed.

Lemma case_An_CPiSnd : forall (G:context) (D:available_props)
    (g1 g2 g3:co) (B1 B2 a a' A b b' B:tm)
    (a0:AnnDefEq G D g1 (a_CPi (Eq a a' A) B1)
                              (a_CPi (Eq b b' B) B2)),
  Pdef G D g1 (a_CPi (Eq a a' A) B1) (a_CPi (Eq b b' B) B2) a0 ->
  forall a1:AnnDefEq G (dom G) g2 a a',
  Pdef G (dom G) g2 a a' a1 ->
  forall a2:AnnDefEq G (dom G) g3 b b',
  Pdef G (dom G) g3 b b' a2 ->
  Pdef G D (g_CPiSnd g1 g2 g3) (open_tm_wrt_co B1 g2)
    (open_tm_wrt_co B2 g3)
    (An_CPiSnd G D g1 g2 g3 B1 B2 a a' A b b' B a0 a1 a2).
Proof.
  intros G D g1 g2 g3 B1 B2 a a' A b b' B Hprem IHprem
         H2 IH2 H3 IH3.
  unfold Pdef in IHprem |- *. intros Hg.
  destruct (AnnDefEq_wf G D g1 (a_CPi (Eq a a' A) B1)
              (a_CPi (Eq b b' B) B2) Hprem) as [_ [Hlc1 Hlc2]].
  assert (Hlb1 : lc_tm (erase_tm B1)) by (exact (lc_erase_cpi_body _ B1 Hlc1)).
  assert (Hlb2 : lc_tm (erase_tm B2)) by (exact (lc_erase_cpi_body _ B2 Hlc2)).
  destruct (JD_CPi_body_lc G D a a' A B1 b b' B B2 Hlb1 Hlb2
              (IHprem Hg)) as [C [HC1 HC2]].
  exists C. split.
  - unfold open_tm_wrt_co. rewrite (erase_open_co_tm B1 0 g2). exact HC1.
  - unfold open_tm_wrt_co. rewrite (erase_open_co_tm B2 0 g3). exact HC2.
Qed.

Lemma case_An_Cast : forall (G:context) (D:available_props)
    (g1 g2:co) (b b' a a' A B:tm)
    (a0:AnnDefEq G D g1 a a'),
  Pdef G D g1 a a' a0 ->
  forall a1:AnnIso G D g2 (Eq a a' A) (Eq b b' B),
  Piso G D g2 (Eq a a' A) (Eq b b' B) a1 ->
  Pdef G D (g_Cast g1 g2) b b'
    (An_Cast G D g1 g2 b b' a a' A B a0 a1).
Proof.
  intros G D g1 g2 b b' a a' A B H1 IH1 Hiso IH2.
  unfold Pdef in IH1 |- *. unfold Piso in IH2. intros Hg.
  destruct (IH1 Hg) as [Caa [Haa' Haa]].
  destruct (IH2 Hg) as [Hab [Ha'b' HAB]].
  assert (Hjd_a'a : JD G D a' a) by (exists Caa; split; assumption).
  assert (Ha'b : JD G D a' b) by
    (exact (JD_trans G D a' a b Hjd_a'a Hab)).
  assert (Hjd_b'a' : JD G D b' a') by (exact (JD_sym G D a' b' Ha'b')).
  assert (Hb'b : JD G D b' b) by
    (exact (JD_trans G D b' a' b Hjd_b'a' Ha'b)).
  exact (JD_sym G D b' b Hb'b).
Qed.

Lemma case_An_IsoSnd : forall (G:context) (D:available_props)
    (g:co) (A B a a' b b':tm) (a0:AnnIso G D g (Eq a a' A) (Eq b b' B)),
  Piso G D g (Eq a a' A) (Eq b b' B) a0 ->
  Pdef G D (g_IsoSnd g) A B (An_IsoSnd G D g A B a a' b b' a0).
Proof.
  intros G D g A B a a' b b' Hiso IH.
  unfold Piso in IH. unfold Pdef. intros Hg.
  destruct (IH Hg) as [_ [_ HAB]]. exact HAB.
Qed.

(* ================================================================== *)
(* The easy cases of AnnIso                                          *)
(* ================================================================== *)

Lemma case_An_PropCong : forall (G:context) (D:available_props)
    (g1:co) (A:tm) (g2:co) (A1 B1 A2 B2:tm)
    (a:AnnDefEq G D g1 A1 A2),
  Pdef G D g1 A1 A2 a ->
  forall a0:AnnDefEq G D g2 B1 B2,
  Pdef G D g2 B1 B2 a0 ->
  forall (a1:AnnPropWff G (Eq A1 B1 A))
    (a2:AnnPropWff G (Eq A2 B2 A)),
  Piso G D (g_EqCong g1 A g2) (Eq A1 B1 A) (Eq A2 B2 A)
    (An_PropCong G D g1 A g2 A1 B1 A2 B2 a a0 a1 a2).
Proof.
  intros G D g1 A g2 A1 B1 A2 B2 H1 IH1 H2 IH2 Hw1 Hw2.
  unfold Pdef in IH1, IH2. unfold Piso. intros Hg.
  unfold JDC. split; [|split].
  - apply IH1. exact Hg.
  - apply IH2. exact Hg.
  - apply JD_refl. apply (lc_constraint_eq_3 A1 B1 A).
    apply (AnnPropWff_wf G (Eq A1 B1 A) Hw1).
Qed.

Lemma case_An_CPiFst : forall (G:context) (D:available_props)
    (g:co) (phi1 phi2:constraint) (A2 B2:tm)
    (a:AnnDefEq G D g (a_CPi phi1 A2) (a_CPi phi2 B2)),
  Pdef G D g (a_CPi phi1 A2) (a_CPi phi2 B2) a ->
  Piso G D (g_CPiFst g) phi1 phi2
    (An_CPiFst G D g phi1 phi2 A2 B2 a).
Proof.
  intros G D g phi1 phi2 A2 B2 H IH.
  unfold Pdef in IH. unfold Piso. intros Hg.
  destruct phi1 as [A B A1]; destruct phi2 as [A' B' A1'].
  unfold JDC. exact (JD_CPi_components G D A B A1 A2 A' B' A1' B2 (IH Hg)).
Qed.

Lemma case_An_IsoSym : forall (G:context) (D:available_props)
    (g:co) (phi2 phi1:constraint) (a:AnnIso G D g phi1 phi2),
  Piso G D g phi1 phi2 a ->
  Piso G D (g_Sym g) phi2 phi1 (An_IsoSym G D g phi2 phi1 a).
Proof.
  intros G D g phi2 phi1 H IH.
  unfold Piso in IH |- *. intros Hg.
  destruct phi1 as [a1 a2 A]; destruct phi2 as [b1 b2 B].
  unfold JDC in *. destruct (IH Hg) as [H1 [H2 H3]].
  split; [apply JD_sym; exact H1 | split;
    [apply JD_sym; exact H2 | apply JD_sym; exact H3]].
Qed.

Lemma case_An_IsoConv : forall (G:context) (D:available_props)
    (a1 a2 A a1' a2' B:tm) (g:co) (a:AnnDefEq G D g A B),
  Pdef G D g A B a ->
  forall (a0:AnnPropWff G (Eq a1 a2 A))
    (a3:AnnPropWff G (Eq a1' a2' B))
    (e:erase_tm a1 = erase_tm a1')
    (e0:erase_tm a2 = erase_tm a2'),
  Piso G D (g_IsoConv (Eq a1 a2 A) (Eq a1' a2' B) g)
    (Eq a1 a2 A) (Eq a1' a2' B)
    (An_IsoConv G D a1 a2 A a1' a2' B g a a0 a3 e e0).
Proof.
  intros G D a1 a2 A a1' a2' B g H IH Hw1 Hw2 He1 He2.
  unfold Pdef in IH. unfold Piso. intros Hg.
  unfold JDC. split; [|split].
  - apply (JD_of_eq G D a1 a1').
    + apply (lc_constraint_eq_1 a1 a2 A).
      apply (AnnPropWff_wf G (Eq a1 a2 A) Hw1).
    + exact He1.
  - apply (JD_of_eq G D a2 a2').
    + apply (lc_constraint_eq_2 a1 a2 A).
      apply (AnnPropWff_wf G (Eq a1 a2 A) Hw1).
    + exact He2.
  - apply IH. exact Hg.
Qed.

Lemma JD_mono_G : forall G G' D a b,
  JD G D a b -> JD G' D a b.
Proof.
  intros G G' D a b [C [H1 H2]]. exists C. split.
  - exact (MultiPar_mono (erase_context G) D (erase_tm a) C H1
             (erase_context G') D).
  - exact (MultiPar_mono (erase_context G) D (erase_tm b) C H2
             (erase_context G') D).
Qed.

Lemma case_An_PiCong : forall (L:atoms) (G:context) (D:available_props)
    (rho:relflag) (g1 g2:co) (A1 B1 A2 B3 B2:tm)
    (a:AnnDefEq G D g1 A1 A2),
  Pdef G D g1 A1 A2 a ->
  forall
    (a0:forall x, x `notin` L ->
        AnnDefEq ((x ~ Tm A1) ++ G) D (open_co_wrt_tm g2 (a_Var_f x))
          (open_tm_wrt_tm B1 (a_Var_f x))
          (open_tm_wrt_tm B2 (a_Var_f x))),
  (forall (x:atom) (n:x `notin` L),
      Pdef ((x ~ Tm A1) ++ G) D (open_co_wrt_tm g2 (a_Var_f x))
        (open_tm_wrt_tm B1 (a_Var_f x))
        (open_tm_wrt_tm B2 (a_Var_f x)) (a0 x n)) ->
  forall
    (e:forall x, x `notin` L ->
        open_tm_wrt_tm B3 (a_Var_f x) =
        open_tm_wrt_tm B2 (a_Conv (a_Var_f x) (g_Sym g1)))
    (a1:AnnTyping G (a_Pi rho A1 B1) a_Star)
    (a2:AnnTyping G (a_Pi rho A1 B2) a_Star)
    (a3:AnnTyping G (a_Pi rho A2 B3) a_Star),
  Pdef G D (g_PiCong rho g1 g2) (a_Pi rho A1 B1) (a_Pi rho A2 B3)
    (An_PiCong L G D rho g1 g2 A1 B1 A2 B3 B2 a a0 e a1 a2 a3).
Proof.
  intros L G D rho g1 g2 A1 B1 A2 B3 B2 Hdom IHdom
         Hbody IHbody He Hty1 Hty2 Hty3.
  unfold Pdef in IHdom, IHbody |- *. intros Hg.
  (* locally closed components of the three Pi typings *)
  assert (HlcPi1 : lc_tm (a_Pi rho A1 B1))
    by exact (proj1 (AnnTyping_wf G (a_Pi rho A1 B1) a_Star Hty1)).
  assert (HlcPi3 : lc_tm (a_Pi rho A2 B3))
    by exact (proj1 (AnnTyping_wf G (a_Pi rho A2 B3) a_Star Hty3)).
  destruct (lc_tm_pi_inv rho A1 B1 HlcPi1) as [HlcA1 _].
  destruct (lc_tm_pi_inv rho A2 B3 HlcPi3) as [HlcA2 HlcB3body].
  (* choose a fresh atom *)
  destruct (atom_fresh (L \u fv_tm_tm_tm B1 \u fv_tm_tm_tm B2 \u
             fv_tm_tm_tm B3 \u fv_tm_tm_tm (erase_tm B1) \u
             fv_tm_tm_tm (erase_tm B3) \u
             fv_tm_tm_tm (erase_tm FixDef))) as [x0 Hx0].
  destruct (notin_union_elim x0 L
    (fv_tm_tm_tm B1 \u fv_tm_tm_tm B2 \u fv_tm_tm_tm B3 \u
     fv_tm_tm_tm (erase_tm B1) \u fv_tm_tm_tm (erase_tm B3) \u
     fv_tm_tm_tm (erase_tm FixDef)) Hx0) as [Hx0L Hx0r1].
  destruct (notin_union_elim x0 (fv_tm_tm_tm B1)
    (fv_tm_tm_tm B2 \u fv_tm_tm_tm B3 \u fv_tm_tm_tm (erase_tm B1) \u
     fv_tm_tm_tm (erase_tm B3) \u fv_tm_tm_tm (erase_tm FixDef)) Hx0r1)
    as [Hx0B1 Hx0r2].
  destruct (notin_union_elim x0 (fv_tm_tm_tm B2)
    (fv_tm_tm_tm B3 \u fv_tm_tm_tm (erase_tm B1) \u
     fv_tm_tm_tm (erase_tm B3) \u fv_tm_tm_tm (erase_tm FixDef)) Hx0r2)
    as [Hx0B2 Hx0r3].
  destruct (notin_union_elim x0 (fv_tm_tm_tm B3)
    (fv_tm_tm_tm (erase_tm B1) \u fv_tm_tm_tm (erase_tm B3) \u
     fv_tm_tm_tm (erase_tm FixDef)) Hx0r3) as [Hx0B3 Hx0r4].
  destruct (notin_union_elim x0 (fv_tm_tm_tm (erase_tm B1))
    (fv_tm_tm_tm (erase_tm B3) \u fv_tm_tm_tm (erase_tm FixDef)) Hx0r4)
    as [Hx0eB1 Hx0r5].
  destruct (notin_union_elim x0 (fv_tm_tm_tm (erase_tm B3))
    (fv_tm_tm_tm (erase_tm FixDef)) Hx0r5) as [Hx0eB3 Hx0fix].
  (* body join at the fresh atom *)
  assert (Hgx : Good (erase_context ((x0 ~ Tm A1) ++ G)) D)
    by exact (Good_cons_Tm G D x0 A1 Hg HlcA1).
  destruct (IHbody x0 Hx0L Hgx) as [C12 [H12a H12b]].
  assert (Hjd12x : JD ((x0 ~ Tm A1) ++ G) D
      (open_tm_wrt_tm B1 (a_Var_f x0))
      (open_tm_wrt_tm B2 (a_Var_f x0)))
    by (exists C12; split; assumption).
  pose proof (JD_mono_G ((x0 ~ Tm A1) ++ G) G D _ _ Hjd12x) as Hjd12.
  (* B3 and B2 are EraseEq-related at the fresh atom *)
  assert (HlcB3x : lc_tm (open_tm_wrt_tm B3 (a_Var_f x0)))
    by exact (HlcB3body x0).
  assert (HeqErase : erase_tm (open_tm_wrt_tm B3 (a_Var_f x0)) =
                     erase_tm (open_tm_wrt_tm B2 (a_Var_f x0))).
  { rewrite (He x0 Hx0L). rewrite erase_open_conv_arg. reflexivity. }
  assert (Hjd32 : JD G D (open_tm_wrt_tm B3 (a_Var_f x0))
                        (open_tm_wrt_tm B2 (a_Var_f x0)))
    by exact (JD_of_eq G D _ _ HlcB3x HeqErase).
  assert (Hjd13 : JD G D (open_tm_wrt_tm B1 (a_Var_f x0))
                        (open_tm_wrt_tm B3 (a_Var_f x0)))
    by exact (JD_trans G D _ _ _ Hjd12 (JD_sym G D _ _ Hjd32)).
  destruct Hjd13 as [Cx [H1x H3x]].
  (* close the common body *)
  set (CB := closeT_tm x0 0 Cx).
  assert (Hx0CB : x0 `notin` fv_tm_tm_tm CB)
    by (unfold CB; apply closeT_tm_fv_fresh).
  assert (HopenCB : open_tm_wrt_tm CB (a_Var_f x0) = Cx).
  { unfold CB. rewrite open_closeT_subst. apply subst_tm_self. }
  assert (HopenCB_rec : open_tm_wrt_tm_rec 0 (a_Var_f x0) CB = Cx)
    by (unfold open_tm_wrt_tm; exact HopenCB).
  assert (HeCx : Eok Cx)
    by (eapply Eok_MultiPar;
        [apply Eok_erase | exact H1x]).
  assert (HeCB : Eok CB) by (unfold CB; apply Eok_closeT_tm; exact HeCx).
  assert (HlcCx : lc_tm Cx)
    by exact (proj2 (Par_lc_MP (erase_context G) D
          (erase_tm (open_tm_wrt_tm B1 (a_Var_f x0))) Cx H1x)).
  assert (HlcBody : forall y, lc_tm (open_tm_wrt_tm CB (a_Var_f y))).
  { intro y. unfold CB. rewrite open_closeT_subst.
    apply lc_subst_tm; [exact HlcCx | apply lc_a_Var_f]. }
  (* body chains from B1 and B3 to CB at the chosen atom *)
  assert (Herase1 : erase_tm (open_tm_wrt_tm B1 (a_Var_f x0)) =
                    open_tm_wrt_tm (erase_tm B1) (a_Var_f x0)).
  { unfold open_tm_wrt_tm.
    rewrite (erase_open_tm_tm B1 0 (a_Var_f x0)).
    cbn [erase_tm]. reflexivity. }
  assert (Herase3 : erase_tm (open_tm_wrt_tm B3 (a_Var_f x0)) =
                    open_tm_wrt_tm (erase_tm B3) (a_Var_f x0)).
  { unfold open_tm_wrt_tm.
    rewrite (erase_open_tm_tm B3 0 (a_Var_f x0)).
    cbn [erase_tm]. reflexivity. }
  assert (Hrel1 : MultiPar (erase_context G) D
      (open_tm_wrt_tm (erase_tm B1) (a_Var_f x0))
      (open_tm_wrt_tm CB (a_Var_f x0))).
  { rewrite <- Herase1. rewrite HopenCB. exact H1x. }
  assert (Hrel3 : MultiPar (erase_context G) D
      (open_tm_wrt_tm (erase_tm B3) (a_Var_f x0))
      (open_tm_wrt_tm CB (a_Var_f x0))).
  { rewrite <- Herase3. rewrite HopenCB. exact H3x. }
  (* the domain join *)
  destruct (IHdom Hg) as [CA [HCA1 HCA2]].
  (* build the two Pi chains *)
  assert (HbodyChain1 : MultiPar (erase_context G) D
      (a_Pi rho (erase_tm A1) (erase_tm B1))
      (a_Pi rho (erase_tm A1) CB)).
  { apply (MultiPar_Pi_body_cong (erase_context G) D rho
             (erase_tm A1) (erase_tm B1) CB x0).
    - apply lc_erase_tm. exact HlcA1.
    - apply Eok_erase.
    - exact HeCB.
    - exact Hx0eB1.
    - exact Hx0CB.
    - exact Hx0fix.
    - exact Hrel1. }
  assert (HbodyChain3 : MultiPar (erase_context G) D
      (a_Pi rho (erase_tm A2) (erase_tm B3))
      (a_Pi rho (erase_tm A2) CB)).
  { apply (MultiPar_Pi_body_cong (erase_context G) D rho
             (erase_tm A2) (erase_tm B3) CB x0).
    - apply lc_erase_tm. exact HlcA2.
    - apply Eok_erase.
    - exact HeCB.
    - exact Hx0eB3.
    - exact Hx0CB.
    - exact Hx0fix.
    - exact Hrel3. }
  assert (HdomChain1 : MultiPar (erase_context G) D
      (a_Pi rho (erase_tm A1) CB) (a_Pi rho CA CB)).
  { apply (MultiPar_Pi_dom_cong (erase_context G) D rho
             (erase_tm A1) CA CB HCA1 HlcBody). }
  assert (HdomChain3 : MultiPar (erase_context G) D
      (a_Pi rho (erase_tm A2) CB) (a_Pi rho CA CB)).
  { apply (MultiPar_Pi_dom_cong (erase_context G) D rho
             (erase_tm A2) CA CB HCA2 HlcBody). }
  exists (a_Pi rho CA CB). split.
  - exact (MultiPar_trans _ _ _ _ _ HbodyChain1 HdomChain1).
  - exact (MultiPar_trans _ _ _ _ _ HbodyChain3 HdomChain3).
Qed.

Lemma case_An_AbsCong : forall (L:atoms) (G:context) (D:available_props)
    (rho:relflag) (g1 g2:co) (A1 b1 A2 b3 b2 B:tm)
    (a:AnnDefEq G D g1 A1 A2),
  Pdef G D g1 A1 A2 a ->
  forall
    (a0:forall x, x `notin` L ->
        AnnDefEq ((x ~ Tm A1) ++ G) D (open_co_wrt_tm g2 (a_Var_f x))
          (open_tm_wrt_tm b1 (a_Var_f x))
          (open_tm_wrt_tm b2 (a_Var_f x))),
  (forall (x:atom) (n:x `notin` L),
      Pdef ((x ~ Tm A1) ++ G) D (open_co_wrt_tm g2 (a_Var_f x))
        (open_tm_wrt_tm b1 (a_Var_f x))
        (open_tm_wrt_tm b2 (a_Var_f x)) (a0 x n)) ->
  forall
    (e:forall x, x `notin` L ->
        open_tm_wrt_tm b3 (a_Var_f x) =
        open_tm_wrt_tm b2 (a_Conv (a_Var_f x) (g_Sym g1)))
    (a1:AnnTyping G A1 a_Star) (a2:AnnTyping G A2 a_Star)
    (r:forall x, x `notin` L ->
        RhoCheck rho x (erase_tm (open_tm_wrt_tm b1 (a_Var_f x))))
    (r0:forall x, x `notin` L ->
        RhoCheck rho x (erase_tm (open_tm_wrt_tm b3 (a_Var_f x))))
    (a3:AnnTyping G (a_Abs rho A1 b2) B),
  Pdef G D (g_AbsCong rho g1 g2) (a_Abs rho A1 b1) (a_Abs rho A2 b3)
    (An_AbsCong L G D rho g1 g2 A1 b1 A2 b3 b2 B a a0 e a1 a2 r r0 a3).
Proof.
  intros L G D rho g1 g2 A1 b1 A2 b3 b2 B Hdom IHdom
         Hbody IHbody He HtyA1 HtyA2 Hrho1 Hrho3 HtyAbs.
  unfold Pdef in IHbody |- *. intros Hg.
  assert (HlcA1 : lc_tm A1)
    by exact (proj1 (AnnTyping_wf G A1 a_Star HtyA1)).
  (* local closure of the opened B3 body, from the conclusion's well-formedness *)
  pose proof (AnnDefEq_wf G D (g_AbsCong rho g1 g2)
                (a_Abs rho A1 b1) (a_Abs rho A2 b3)
                (An_AbsCong L G D rho g1 g2 A1 b1 A2 b3 b2 B
                   Hdom Hbody He HtyA1 HtyA2 Hrho1 Hrho3 HtyAbs)) as Hwf.
  destruct Hwf as [_ [_ HlcAbs2]].
  destruct (lc_tm_abs_inv rho A2 b3 HlcAbs2) as [_ HlcB3body].
  (* choose a fresh atom *)
  destruct (atom_fresh (L \u fv_tm_tm_tm b1 \u fv_tm_tm_tm b2 \u
             fv_tm_tm_tm b3 \u fv_tm_tm_tm (erase_tm b1) \u
             fv_tm_tm_tm (erase_tm b3) \u
             fv_tm_tm_tm (erase_tm FixDef))) as [x0 Hx0].
  destruct (notin_union_elim x0 L
    (fv_tm_tm_tm b1 \u fv_tm_tm_tm b2 \u fv_tm_tm_tm b3 \u
     fv_tm_tm_tm (erase_tm b1) \u fv_tm_tm_tm (erase_tm b3) \u
     fv_tm_tm_tm (erase_tm FixDef)) Hx0) as [Hx0L Hx0r1].
  destruct (notin_union_elim x0 (fv_tm_tm_tm b1)
    (fv_tm_tm_tm b2 \u fv_tm_tm_tm b3 \u fv_tm_tm_tm (erase_tm b1) \u
     fv_tm_tm_tm (erase_tm b3) \u fv_tm_tm_tm (erase_tm FixDef)) Hx0r1)
    as [Hx0b1 Hx0r2].
  destruct (notin_union_elim x0 (fv_tm_tm_tm b2)
    (fv_tm_tm_tm b3 \u fv_tm_tm_tm (erase_tm b1) \u
     fv_tm_tm_tm (erase_tm b3) \u fv_tm_tm_tm (erase_tm FixDef)) Hx0r2)
    as [Hx0b2 Hx0r3].
  destruct (notin_union_elim x0 (fv_tm_tm_tm b3)
    (fv_tm_tm_tm (erase_tm b1) \u fv_tm_tm_tm (erase_tm b3) \u
     fv_tm_tm_tm (erase_tm FixDef)) Hx0r3) as [Hx0b3 Hx0r4].
  destruct (notin_union_elim x0 (fv_tm_tm_tm (erase_tm b1))
    (fv_tm_tm_tm (erase_tm b3) \u fv_tm_tm_tm (erase_tm FixDef)) Hx0r4)
    as [Hx0eb1 Hx0r5].
  destruct (notin_union_elim x0 (fv_tm_tm_tm (erase_tm b3))
    (fv_tm_tm_tm (erase_tm FixDef)) Hx0r5) as [Hx0eb3 Hx0fix].
  (* body join at the fresh atom *)
  assert (Hgx : Good (erase_context ((x0 ~ Tm A1) ++ G)) D)
    by exact (Good_cons_Tm G D x0 A1 Hg HlcA1).
  destruct (IHbody x0 Hx0L Hgx) as [C12 [H12a H12b]].
  assert (Hjd12x : JD ((x0 ~ Tm A1) ++ G) D
      (open_tm_wrt_tm b1 (a_Var_f x0))
      (open_tm_wrt_tm b2 (a_Var_f x0)))
    by (exists C12; split; assumption).
  pose proof (JD_mono_G ((x0 ~ Tm A1) ++ G) G D _ _ Hjd12x) as Hjd12.
  assert (HlcB3x : lc_tm (open_tm_wrt_tm b3 (a_Var_f x0)))
    by exact (HlcB3body x0).
  assert (HeqErase : erase_tm (open_tm_wrt_tm b3 (a_Var_f x0)) =
                     erase_tm (open_tm_wrt_tm b2 (a_Var_f x0))).
  { rewrite (He x0 Hx0L). rewrite erase_open_conv_arg. reflexivity. }
  assert (Hjd32 : JD G D (open_tm_wrt_tm b3 (a_Var_f x0))
                        (open_tm_wrt_tm b2 (a_Var_f x0)))
    by exact (JD_of_eq G D _ _ HlcB3x HeqErase).
  assert (Hjd13 : JD G D (open_tm_wrt_tm b1 (a_Var_f x0))
                        (open_tm_wrt_tm b3 (a_Var_f x0)))
    by exact (JD_trans G D _ _ _ Hjd12 (JD_sym G D _ _ Hjd32)).
  destruct Hjd13 as [Cx [H1x H3x]].
  set (CB := closeT_tm x0 0 Cx).
  assert (Hx0CB : x0 `notin` fv_tm_tm_tm CB)
    by (unfold CB; apply closeT_tm_fv_fresh).
  assert (HopenCB : open_tm_wrt_tm CB (a_Var_f x0) = Cx).
  { unfold CB. rewrite open_closeT_subst. apply subst_tm_self. }
  assert (HeCx : Eok Cx)
    by (eapply Eok_MultiPar; [apply Eok_erase | exact H1x]).
  assert (HeCB : Eok CB) by (unfold CB; apply Eok_closeT_tm; exact HeCx).
  assert (Herase1 : erase_tm (open_tm_wrt_tm b1 (a_Var_f x0)) =
                    open_tm_wrt_tm (erase_tm b1) (a_Var_f x0)).
  { unfold open_tm_wrt_tm.
    rewrite (erase_open_tm_tm b1 0 (a_Var_f x0)).
    cbn [erase_tm]. reflexivity. }
  assert (Herase3 : erase_tm (open_tm_wrt_tm b3 (a_Var_f x0)) =
                    open_tm_wrt_tm (erase_tm b3) (a_Var_f x0)).
  { unfold open_tm_wrt_tm.
    rewrite (erase_open_tm_tm b3 0 (a_Var_f x0)).
    cbn [erase_tm]. reflexivity. }
  assert (Hrel1 : MultiPar (erase_context G) D
      (open_tm_wrt_tm (erase_tm b1) (a_Var_f x0))
      (open_tm_wrt_tm CB (a_Var_f x0))).
  { rewrite <- Herase1. rewrite HopenCB. exact H1x. }
  assert (Hrel3 : MultiPar (erase_context G) D
      (open_tm_wrt_tm (erase_tm b3) (a_Var_f x0))
      (open_tm_wrt_tm CB (a_Var_f x0))).
  { rewrite <- Herase3. rewrite HopenCB. exact H3x. }
  assert (HbodyChain1 : MultiPar (erase_context G) D
      (a_UAbs rho (erase_tm b1)) (a_UAbs rho CB)).
  { apply (MultiPar_UAbs_body_cong (erase_context G) D rho
             (erase_tm b1) CB x0).
    - apply Eok_erase.
    - exact HeCB.
    - exact Hx0eb1.
    - exact Hx0CB.
    - exact Hx0fix.
    - exact Hrel1. }
  assert (HbodyChain3 : MultiPar (erase_context G) D
      (a_UAbs rho (erase_tm b3)) (a_UAbs rho CB)).
  { apply (MultiPar_UAbs_body_cong (erase_context G) D rho
             (erase_tm b3) CB x0).
    - apply Eok_erase.
    - exact HeCB.
    - exact Hx0eb3.
    - exact Hx0CB.
    - exact Hx0fix.
    - exact Hrel3. }
  exists (a_UAbs rho CB). split.
  - cbn [erase_tm]. exact HbodyChain1.
  - cbn [erase_tm]. exact HbodyChain3.
Qed.

Lemma MultiPar_subst_arg_multi : forall G D u v,
  MultiPar G D u v -> Eok u ->
  forall x T, lc_tm T -> Eok T ->
  x `notin` fv_tm_tm_tm (erase_tm FixDef) ->
  MultiPar G D (subst_tm_tm x u T) (subst_tm_tm x v T).
Proof.
  intros G D u v H. induction H as
    [G0 D0 a Hlc | G0 D0 a b c Hpar Hmp IH];
    intros He x T HlcT HeT Hx.
  - apply MP_Refl. exact (lc_subst_tm T x a HlcT Hlc).
  - eapply MP_Step.
    + exact (Par_subst_Eok G0 D0 T T (Par_Refl G0 D0 T HlcT) HeT
               x a c Hx Hpar).
    + exact (IH (Eok_Par G0 D0 a c He Hpar) x T HlcT HeT Hx).
Qed.

Lemma case_An_PiSnd : forall (G:context) (D:available_props)
    (g1 g2:co) (B1 a1 B2 a2:tm) (rho:relflag) (A1 A2:tm)
    (a:AnnDefEq G D g1 (a_Pi rho A1 B1) (a_Pi rho A2 B2)),
  Pdef G D g1 (a_Pi rho A1 B1) (a_Pi rho A2 B2) a ->
  forall a0:AnnDefEq G D g2 a1 a2,
  Pdef G D g2 a1 a2 a0 ->
  forall (a3:AnnTyping G a1 A1) (a4:AnnTyping G a2 A2),
  Pdef G D (g_PiSnd g1 g2) (open_tm_wrt_tm B1 a1) (open_tm_wrt_tm B2 a2)
    (An_PiSnd G D g1 g2 B1 a1 B2 a2 rho A1 A2 a a0 a3 a4).
Proof.
  intros G D g1 g2 B1 a1 B2 a2 rho A1 A2 Hdom IHdom
         Harg IHarg Hty1 Hty2.
  unfold Pdef in IHdom, IHarg |- *. intros Hg.
  assert (Hlca1 : lc_tm a1) by exact (proj1 (AnnTyping_wf G a1 A1 Hty1)).
  assert (Hlca2 : lc_tm a2) by exact (proj1 (AnnTyping_wf G a2 A2 Hty2)).
  assert (Hlcea1 : lc_tm (erase_tm a1)) by exact (lc_erase_tm a1 Hlca1).
  assert (Hlcea2 : lc_tm (erase_tm a2)) by exact (lc_erase_tm a2 Hlca2).
  destruct (IHarg Hg) as [Darg [HD1 HD2]].
  assert (HlcDarg : lc_tm Darg)
    by exact (proj2 (Par_lc_MP (erase_context G) D (erase_tm a1) Darg HD1)).
  destruct (JD_Pi_body_chain G D rho A1 B1 A2 B2 (IHdom Hg))
    as [CB [Hb1 Hb2]].
  (* choose a fresh atom after CB is known *)
  destruct (atom_fresh (fv_tm_tm_tm (erase_tm B1) \u
             fv_tm_tm_tm (erase_tm B2) \u fv_tm_tm_tm CB \u
             fv_tm_tm_tm (erase_tm FixDef))) as [x0 Hx0].
  destruct (notin_union_elim x0 (fv_tm_tm_tm (erase_tm B1))
    (fv_tm_tm_tm (erase_tm B2) \u fv_tm_tm_tm CB \u
     fv_tm_tm_tm (erase_tm FixDef)) Hx0) as [Hx0eB1 Hx0r1].
  destruct (notin_union_elim x0 (fv_tm_tm_tm (erase_tm B2))
    (fv_tm_tm_tm CB \u fv_tm_tm_tm (erase_tm FixDef)) Hx0r1)
    as [Hx0eB2 Hx0r2].
  destruct (notin_union_elim x0 (fv_tm_tm_tm CB)
    (fv_tm_tm_tm (erase_tm FixDef)) Hx0r2) as [Hx0CB Hx0fix].
  (* the two body chains, transported to the actual arguments *)
  assert (HeSrc1 : Eok (open_tm_wrt_tm (erase_tm B1) (a_Var_f x0)))
    by (apply Eok_open_tm; [apply Eok_erase | apply Eok_Var_f]).
  pose proof (MultiPar_subst_Eok (erase_context G) D
      (open_tm_wrt_tm (erase_tm B1) (a_Var_f x0))
      (open_tm_wrt_tm CB (a_Var_f x0)) (Hb1 x0) HeSrc1
      x0 (erase_tm a1) (erase_tm a1) Hx0fix
      (Par_Refl (erase_context G) D (erase_tm a1) Hlcea1)) as HsubArg1.
  assert (HargChain1 : MultiPar (erase_context G) D
      (open_tm_wrt_tm (erase_tm B1) (erase_tm a1))
      (open_tm_wrt_tm CB (erase_tm a1))).
  { assert (E1 : subst_tm_tm x0 (erase_tm a1)
        (open_tm_wrt_tm (erase_tm B1) (a_Var_f x0))
        = open_tm_wrt_tm (erase_tm B1) (erase_tm a1))
      by (apply subst_open_tm_fresh; assumption).
    assert (E2 : subst_tm_tm x0 (erase_tm a1)
        (open_tm_wrt_tm CB (a_Var_f x0))
        = open_tm_wrt_tm CB (erase_tm a1))
      by (apply subst_open_tm_fresh; assumption).
    rewrite <- E1, <- E2. exact HsubArg1. }
  assert (HeSrc2 : Eok (open_tm_wrt_tm (erase_tm B2) (a_Var_f x0)))
    by (apply Eok_open_tm; [apply Eok_erase | apply Eok_Var_f]).
  pose proof (MultiPar_subst_Eok (erase_context G) D
      (open_tm_wrt_tm (erase_tm B2) (a_Var_f x0))
      (open_tm_wrt_tm CB (a_Var_f x0)) (Hb2 x0) HeSrc2
      x0 (erase_tm a2) (erase_tm a2) Hx0fix
      (Par_Refl (erase_context G) D (erase_tm a2) Hlcea2)) as HsubArg2.
  assert (HargChain2 : MultiPar (erase_context G) D
      (open_tm_wrt_tm (erase_tm B2) (erase_tm a2))
      (open_tm_wrt_tm CB (erase_tm a2))).
  { assert (E1 : subst_tm_tm x0 (erase_tm a2)
        (open_tm_wrt_tm (erase_tm B2) (a_Var_f x0))
        = open_tm_wrt_tm (erase_tm B2) (erase_tm a2))
      by (apply subst_open_tm_fresh; assumption).
    assert (E2 : subst_tm_tm x0 (erase_tm a2)
        (open_tm_wrt_tm CB (a_Var_f x0))
        = open_tm_wrt_tm CB (erase_tm a2))
      by (apply subst_open_tm_fresh; assumption).
    rewrite <- E1, <- E2. exact HsubArg2. }
  (* bridge the two arguments through the argument join *)
  assert (HlcCBOp : lc_tm (open_tm_wrt_tm CB (a_Var_f x0)))
    by exact (proj2 (Par_lc_MP (erase_context G) D
          (open_tm_wrt_tm (erase_tm B1) (a_Var_f x0))
          (open_tm_wrt_tm CB (a_Var_f x0)) (Hb1 x0))).
  assert (HeCBOp : Eok (open_tm_wrt_tm CB (a_Var_f x0)))
    by (eapply Eok_MultiPar; [exact HeSrc1 | exact (Hb1 x0)]).
  pose proof (MultiPar_subst_arg_multi (erase_context G) D
      (erase_tm a1) Darg HD1 (Eok_erase a1)
      x0 (open_tm_wrt_tm CB (a_Var_f x0)) HlcCBOp HeCBOp Hx0fix)
    as HsubBridge1.
  assert (Hbridge1 : MultiPar (erase_context G) D
      (open_tm_wrt_tm CB (erase_tm a1))
      (open_tm_wrt_tm CB Darg)).
  { assert (E1 : subst_tm_tm x0 (erase_tm a1)
        (open_tm_wrt_tm CB (a_Var_f x0))
        = open_tm_wrt_tm CB (erase_tm a1))
      by (apply subst_open_tm_fresh; assumption).
    assert (E2 : subst_tm_tm x0 Darg
        (open_tm_wrt_tm CB (a_Var_f x0))
        = open_tm_wrt_tm CB Darg)
      by (apply subst_open_tm_fresh; assumption).
    rewrite <- E1, <- E2. exact HsubBridge1. }
  pose proof (MultiPar_subst_arg_multi (erase_context G) D
      (erase_tm a2) Darg HD2 (Eok_erase a2)
      x0 (open_tm_wrt_tm CB (a_Var_f x0)) HlcCBOp HeCBOp Hx0fix)
    as HsubBridge2.
  assert (Hbridge2 : MultiPar (erase_context G) D
      (open_tm_wrt_tm CB (erase_tm a2))
      (open_tm_wrt_tm CB Darg)).
  { assert (E1 : subst_tm_tm x0 (erase_tm a2)
        (open_tm_wrt_tm CB (a_Var_f x0))
        = open_tm_wrt_tm CB (erase_tm a2))
      by (apply subst_open_tm_fresh; assumption).
    assert (E2 : subst_tm_tm x0 Darg
        (open_tm_wrt_tm CB (a_Var_f x0))
        = open_tm_wrt_tm CB Darg)
      by (apply subst_open_tm_fresh; assumption).
    rewrite <- E1, <- E2. exact HsubBridge2. }
  (* erasure commutes with opening at an arbitrary argument *)
  assert (HeraseT1 : erase_tm (open_tm_wrt_tm B1 a1) =
                     open_tm_wrt_tm (erase_tm B1) (erase_tm a1)).
  { unfold open_tm_wrt_tm.
    rewrite (erase_open_tm_tm B1 0 a1). reflexivity. }
  assert (HeraseT2 : erase_tm (open_tm_wrt_tm B2 a2) =
                     open_tm_wrt_tm (erase_tm B2) (erase_tm a2)).
  { unfold open_tm_wrt_tm.
    rewrite (erase_open_tm_tm B2 0 a2). reflexivity. }
  exists (open_tm_wrt_tm CB Darg). split.
  - rewrite HeraseT1.
    exact (MultiPar_trans _ _ _ _ _ HargChain1 Hbridge1).
  - rewrite HeraseT2.
    exact (MultiPar_trans _ _ _ _ _ HargChain2 Hbridge2).
Qed.

Lemma lc_erase_constraint : forall phi,
  lc_constraint phi -> lc_constraint (erase_constraint phi).
Proof.
  intros [A B A1] H. cbn [erase_constraint].
  inversion H; subst; clear H.
  apply lc_Eq.
  - apply lc_erase_tm. assumption.
  - apply lc_erase_tm. assumption.
  - apply lc_erase_tm. assumption.
Qed.

Lemma open_co_erase_tm_all :
  (forall (a:tm) (k:nat) (g:co),
     open_tm_wrt_co_rec k g (erase_tm a) = erase_tm a) /\
  (forall (_:brs) (k:nat) (g:co), True) /\
  (forall (_:co) (k:nat) (g:co), True) /\
  (forall (p:constraint) (k:nat) (g:co),
     open_constraint_wrt_co_rec k g (erase_constraint p) =
     erase_constraint p).
Proof.
  apply (tm_mutind
    (fun (a:tm) => forall k g, open_tm_wrt_co_rec k g (erase_tm a) = erase_tm a)
    (fun (_:brs) => forall k g, True)
    (fun (_:co) => forall k g, True)
    (fun (p:constraint) => forall k g,
       open_constraint_wrt_co_rec k g (erase_constraint p) =
       erase_constraint p)).
  all: intros; cbn [erase_tm erase_constraint
                    open_tm_wrt_co_rec open_constraint_wrt_co_rec
                    open_co_wrt_co_rec].
  all: try reflexivity.
  all: try (f_equal; eauto).
  all: try (destruct p as [A B A1]; f_equal; eauto).
  all: try (destruct rho; cbn [erase_tm open_tm_wrt_co_rec]; f_equal; eauto).
Qed.

Lemma open_co_erase_tm : forall a k g,
  open_tm_wrt_co_rec k g (erase_tm a) = erase_tm a.
Proof. exact (proj1 open_co_erase_tm_all). Qed.

Lemma Eok_cfv :
  (forall a, Eok a -> forall c, c `notin` cfv_tm a) /\
  (forall phi, EokConstraint phi -> forall c, c `notin` cfv_constraint phi).
Proof.
  apply (Eok_mutind
    (fun a _ => forall c, c `notin` cfv_tm a)
    (fun phi _ => forall c, c `notin` cfv_constraint phi)).
  all: intros; cbn [cfv_tm cfv_constraint cfv_co].
  all: try (repeat (apply notin_union || apply notin_empty)).
  all: eauto.
Qed.

Lemma Eok_cfv_tm : forall a, Eok a -> forall c, c `notin` cfv_tm a.
Proof. exact (proj1 Eok_cfv). Qed.

Lemma Eok_cfv_constraint : forall phi, EokConstraint phi ->
  forall c, c `notin` cfv_constraint phi.
Proof. exact (proj2 Eok_cfv). Qed.

Lemma case_An_CPiCong : forall (L:atoms) (G:context) (D:available_props)
    (g1 g3:co) (phi1:constraint) (B1:tm) (phi2:constraint)
    (B3 B2:tm) (a:AnnIso G D g1 phi1 phi2),
  Piso G D g1 phi1 phi2 a ->
  forall
    (a0:forall c, c `notin` L ->
        AnnDefEq ((c ~ Co phi1) ++ G) D (open_co_wrt_co g3 (g_Var_f c))
          (open_tm_wrt_co B1 (g_Var_f c))
          (open_tm_wrt_co B2 (g_Var_f c))),
  (forall (c:atom) (n:c `notin` L),
      Pdef ((c ~ Co phi1) ++ G) D (open_co_wrt_co g3 (g_Var_f c))
        (open_tm_wrt_co B1 (g_Var_f c))
        (open_tm_wrt_co B2 (g_Var_f c)) (a0 c n)) ->
  forall
    (e:forall c, c `notin` L ->
        open_tm_wrt_co B3 (g_Var_f c) =
        open_tm_wrt_co B2 (g_Cast (g_Var_f c) (g_Sym g1)))
    (a1:AnnTyping G (a_CPi phi1 B1) a_Star)
    (a2:AnnTyping G (a_CPi phi2 B3) a_Star)
    (a3:AnnTyping G (a_CPi phi1 B2) a_Star),
  Pdef G D (g_CPiCong g1 g3) (a_CPi phi1 B1) (a_CPi phi2 B3)
    (An_CPiCong L G D g1 g3 phi1 B1 phi2 B3 B2 a a0 e a1 a2 a3).
Proof.
  intros L G D g1 g3 phi1 B1 phi2 B3 B2 Hiso IHiso
         Hbody IHbody He Hty1 Hty2 Hty3.
  unfold Pdef in |- *. intros Hg.
  destruct phi1 as [A B A1]; destruct phi2 as [A' B' A1'].
  assert (Hlc1 : lc_tm (a_CPi (Eq A B A1) B1))
    by exact (proj1 (AnnTyping_wf G (a_CPi (Eq A B A1) B1) a_Star Hty1)).
  assert (Hlc3 : lc_tm (a_CPi (Eq A' B' A1') B3))
    by exact (proj1 (AnnTyping_wf G (a_CPi (Eq A' B' A1') B3) a_Star Hty2)).
  destruct (lc_tm_cpi_inv (Eq A B A1) B1 Hlc1) as [Hphi1 Hb1].
  destruct (lc_tm_cpi_inv (Eq A' B' A1') B3 Hlc3) as [Hphi2 Hb3].
  unfold Piso in IHiso.
  destruct (IHiso Hg) as [HA [HB HA1]].
  (* choose a fresh covar, also avoiding D *)
  destruct (atom_fresh (L \u D \u fv_tm_tm_tm B1 \u fv_tm_tm_tm B3 \u
             fv_tm_tm_tm (erase_tm B1) \u fv_tm_tm_tm (erase_tm B3) \u
             fv_tm_tm_tm (erase_tm FixDef))) as [c0 Hc0].
  destruct (notin_union_elim c0 L
    (D \u fv_tm_tm_tm B1 \u fv_tm_tm_tm B3 \u
     fv_tm_tm_tm (erase_tm B1) \u fv_tm_tm_tm (erase_tm B3) \u
     fv_tm_tm_tm (erase_tm FixDef)) Hc0) as [Hc0L Hc0r1].
  destruct (notin_union_elim c0 D
    (fv_tm_tm_tm B1 \u fv_tm_tm_tm B3 \u
     fv_tm_tm_tm (erase_tm B1) \u fv_tm_tm_tm (erase_tm B3) \u
     fv_tm_tm_tm (erase_tm FixDef)) Hc0r1) as [Hc0D Hc0r2].
  destruct (notin_union_elim c0 (fv_tm_tm_tm B1)
    (fv_tm_tm_tm B3 \u fv_tm_tm_tm (erase_tm B1) \u
     fv_tm_tm_tm (erase_tm B3) \u fv_tm_tm_tm (erase_tm FixDef)) Hc0r2)
    as [Hc0B1 Hc0r3].
  destruct (notin_union_elim c0 (fv_tm_tm_tm B3)
    (fv_tm_tm_tm (erase_tm B1) \u fv_tm_tm_tm (erase_tm B3) \u
     fv_tm_tm_tm (erase_tm FixDef)) Hc0r3) as [Hc0B3 Hc0r4].
  destruct (notin_union_elim c0 (fv_tm_tm_tm (erase_tm B1))
    (fv_tm_tm_tm (erase_tm B3) \u fv_tm_tm_tm (erase_tm FixDef)) Hc0r4)
    as [Hc0eB1 Hc0r5].
  destruct (notin_union_elim c0 (fv_tm_tm_tm (erase_tm B3))
    (fv_tm_tm_tm (erase_tm FixDef)) Hc0r5) as [Hc0eB3 Hc0fix].
  (* body join at the fresh covar *)
  assert (Hgc : Good (erase_context ((c0 ~ Co (Eq A B A1)) ++ G)) D)
    by exact (Good_cons_Co_fresh G D c0 (Eq A B A1) Hg Hc0D Hphi1).
  destruct (IHbody c0 Hc0L Hgc) as [C12 [H12a H12b]].
  assert (Hjd12x : JD ((c0 ~ Co (Eq A B A1)) ++ G) D
      (open_tm_wrt_co B1 (g_Var_f c0))
      (open_tm_wrt_co B2 (g_Var_f c0)))
    by (exists C12; split; assumption).
  pose proof (JD_mono_G ((c0 ~ Co (Eq A B A1)) ++ G) G D _ _ Hjd12x) as Hjd12.
  assert (HlcB3x : lc_tm (open_tm_wrt_co B3 (g_Var_f c0)))
    by exact (Hb3 c0).
  assert (HeqErase : erase_tm (open_tm_wrt_co B3 (g_Var_f c0)) =
                     erase_tm (open_tm_wrt_co B2 (g_Var_f c0))).
  { rewrite (He c0 Hc0L).
    unfold open_tm_wrt_co.
    rewrite (erase_open_co_tm B2 0 (g_Cast (g_Var_f c0) (g_Sym g1))).
    rewrite (erase_open_co_tm B2 0 (g_Var_f c0)). reflexivity. }
  assert (Hjd32 : JD G D (open_tm_wrt_co B3 (g_Var_f c0))
                        (open_tm_wrt_co B2 (g_Var_f c0)))
    by exact (JD_of_eq G D _ _ HlcB3x HeqErase).
  assert (Hjd13 : JD G D (open_tm_wrt_co B1 (g_Var_f c0))
                        (open_tm_wrt_co B3 (g_Var_f c0)))
    by exact (JD_trans G D _ _ _ Hjd12 (JD_sym G D _ _ Hjd32)).
  destruct Hjd13 as [Cx [H1x H3x]].
  (* close the common body *)
  set (CB := closeC_tm c0 0 Cx).
  assert (Hc0CB : c0 `notin` cfv_tm CB)
    by (unfold CB; apply closeC_tm_cfv_fresh).
  assert (HopenCB : open_tm_wrt_co CB (g_Var_f c0) = Cx).
  { unfold CB. rewrite (open_closeC_subst2 Cx c0 c0). apply subst_co_tm_self. }
  assert (HlcCx : lc_tm Cx)
    by exact (proj2 (Par_lc_MP (erase_context G) D
          (erase_tm (open_tm_wrt_co B1 (g_Var_f c0))) Cx H1x)).
  assert (HbodyAll : forall c, lc_tm (open_tm_wrt_co CB (g_Var_f c))).
  { intro c. unfold CB. rewrite (open_closeC_subst2 Cx c0 c).
    apply lc_subst_co; [exact HlcCx | apply lc_g_Var_f]. }
  (* opened source chains *)
  assert (Herase1 : erase_tm (open_tm_wrt_co B1 (g_Var_f c0)) =
                    open_tm_wrt_co (erase_tm B1) (g_Var_f c0)).
  { unfold open_tm_wrt_co. rewrite (erase_open_co_tm B1 0 (g_Var_f c0)).
    symmetry. apply open_co_erase_tm. }
  assert (Herase3 : erase_tm (open_tm_wrt_co B3 (g_Var_f c0)) =
                    open_tm_wrt_co (erase_tm B3) (g_Var_f c0)).
  { unfold open_tm_wrt_co. rewrite (erase_open_co_tm B3 0 (g_Var_f c0)).
    symmetry. apply open_co_erase_tm. }
  assert (Hrel1 : MultiPar (erase_context G) D
      (open_tm_wrt_co (erase_tm B1) (g_Var_f c0))
      (open_tm_wrt_co CB (g_Var_f c0))).
  { rewrite <- Herase1. rewrite HopenCB. exact H1x. }
  assert (Hrel3 : MultiPar (erase_context G) D
      (open_tm_wrt_co (erase_tm B3) (g_Var_f c0))
      (open_tm_wrt_co CB (g_Var_f c0))).
  { rewrite <- Herase3. rewrite HopenCB. exact H3x. }
  (* component lc facts *)
  assert (HlcA : lc_tm (erase_tm A))
    by (apply lc_erase_tm; apply (lc_constraint_eq_1 A B A1 Hphi1)).
  assert (HlcB : lc_tm (erase_tm B))
    by (apply lc_erase_tm; apply (lc_constraint_eq_2 A B A1 Hphi1)).
  assert (HlcA1 : lc_tm (erase_tm A1))
    by (apply lc_erase_tm; apply (lc_constraint_eq_3 A B A1 Hphi1)).
  assert (HlcA' : lc_tm (erase_tm A'))
    by (apply lc_erase_tm; apply (lc_constraint_eq_1 A' B' A1' Hphi2)).
  assert (HlcB' : lc_tm (erase_tm B'))
    by (apply lc_erase_tm; apply (lc_constraint_eq_2 A' B' A1' Hphi2)).
  assert (HlcA1' : lc_tm (erase_tm A1'))
    by (apply lc_erase_tm; apply (lc_constraint_eq_3 A' B' A1' Hphi2)).
  destruct HA as [CA [HCA1 HCA2]].
  destruct HB as [CM [HCB1 HCB2]].
  destruct HA1 as [CA1 [HCA11 HCA12]].
  assert (HlcCA : lc_tm CA)
    by exact (proj2 (Par_lc_MP (erase_context G) D (erase_tm A) CA HCA1)).
  assert (HlcCM : lc_tm CM)
    by exact (proj2 (Par_lc_MP (erase_context G) D (erase_tm B) CM HCB1)).
  assert (HlcCA1 : lc_tm CA1)
    by exact (proj2 (Par_lc_MP (erase_context G) D (erase_tm A1) CA1 HCA11)).
  (* source component chains *)
  assert (HbodyChain1 : MultiPar (erase_context G) D
      (a_CPi (Eq (erase_tm A) (erase_tm B) (erase_tm A1)) (erase_tm B1))
      (a_CPi (Eq (erase_tm A) (erase_tm B) (erase_tm A1)) CB)).
  { apply (MultiPar_CPi_body_cong (erase_context G) D
             (erase_tm A) (erase_tm B) (erase_tm A1) (erase_tm B1) CB c0).
    - exact (lc_erase_constraint (Eq A B A1) Hphi1).
    - exact (Eok_cfv_tm (erase_tm B1) (Eok_erase B1) c0).
    - exact Hc0CB.
    - exact Hc0fix.
    - exact Hrel1. }
  assert (HdomChain1 : MultiPar (erase_context G) D
      (a_CPi (Eq (erase_tm A) (erase_tm B) (erase_tm A1)) CB)
      (a_CPi (Eq CA (erase_tm B) (erase_tm A1)) CB)).
  { apply (MultiPar_CPi_dom_cong (erase_context G) D
             (erase_tm A) CA (erase_tm B) (erase_tm A1) CB).
    - exact HlcB.
    - exact HlcA1.
    - exact HbodyAll.
    - exact HCA1. }
  assert (HmidChain1 : MultiPar (erase_context G) D
      (a_CPi (Eq CA (erase_tm B) (erase_tm A1)) CB)
      (a_CPi (Eq CA CM (erase_tm A1)) CB)).
  { apply (MultiPar_CPi_mid_cong (erase_context G) D
             CA (erase_tm B) CM (erase_tm A1) CB).
    - exact HlcCA.
    - exact HlcA1.
    - exact HbodyAll.
    - exact HCB1. }
  assert (HlastChain1 : MultiPar (erase_context G) D
      (a_CPi (Eq CA CM (erase_tm A1)) CB)
      (a_CPi (Eq CA CM CA1) CB)).
  { apply (MultiPar_CPi_last_cong (erase_context G) D
             CA CM (erase_tm A1) CA1 CB).
    - exact HlcCA.
    - exact HlcCM.
    - exact HbodyAll.
    - exact HCA11. }
  (* target component chains *)
  assert (HbodyChain3 : MultiPar (erase_context G) D
      (a_CPi (Eq (erase_tm A') (erase_tm B') (erase_tm A1')) (erase_tm B3))
      (a_CPi (Eq (erase_tm A') (erase_tm B') (erase_tm A1')) CB)).
  { apply (MultiPar_CPi_body_cong (erase_context G) D
             (erase_tm A') (erase_tm B') (erase_tm A1') (erase_tm B3) CB c0).
    - exact (lc_erase_constraint (Eq A' B' A1') Hphi2).
    - exact (Eok_cfv_tm (erase_tm B3) (Eok_erase B3) c0).
    - exact Hc0CB.
    - exact Hc0fix.
    - exact Hrel3. }
  assert (HdomChain3 : MultiPar (erase_context G) D
      (a_CPi (Eq (erase_tm A') (erase_tm B') (erase_tm A1')) CB)
      (a_CPi (Eq CA (erase_tm B') (erase_tm A1')) CB)).
  { apply (MultiPar_CPi_dom_cong (erase_context G) D
             (erase_tm A') CA (erase_tm B') (erase_tm A1') CB).
    - exact HlcB'.
    - exact HlcA1'.
    - exact HbodyAll.
    - exact HCA2. }
  assert (HmidChain3 : MultiPar (erase_context G) D
      (a_CPi (Eq CA (erase_tm B') (erase_tm A1')) CB)
      (a_CPi (Eq CA CM (erase_tm A1')) CB)).
  { apply (MultiPar_CPi_mid_cong (erase_context G) D
             CA (erase_tm B') CM (erase_tm A1') CB).
    - exact HlcCA.
    - exact HlcA1'.
    - exact HbodyAll.
    - exact HCB2. }
  assert (HlastChain3 : MultiPar (erase_context G) D
      (a_CPi (Eq CA CM (erase_tm A1')) CB)
      (a_CPi (Eq CA CM CA1) CB)).
  { apply (MultiPar_CPi_last_cong (erase_context G) D
             CA CM (erase_tm A1') CA1 CB).
    - exact HlcCA.
    - exact HlcCM.
    - exact HbodyAll.
    - exact HCA12. }
  (* assemble *)
  assert (Hfinal1 : MultiPar (erase_context G) D
      (erase_tm (a_CPi (Eq A B A1) B1)) (a_CPi (Eq CA CM CA1) CB)).
  { cbn [erase_tm erase_constraint].
    exact (MultiPar_trans _ _ _ _ _ HbodyChain1
             (MultiPar_trans _ _ _ _ _ HdomChain1
               (MultiPar_trans _ _ _ _ _ HmidChain1 HlastChain1))). }
  assert (Hfinal3 : MultiPar (erase_context G) D
      (erase_tm (a_CPi (Eq A' B' A1') B3)) (a_CPi (Eq CA CM CA1) CB)).
  { cbn [erase_tm erase_constraint].
    exact (MultiPar_trans _ _ _ _ _ HbodyChain3
             (MultiPar_trans _ _ _ _ _ HdomChain3
               (MultiPar_trans _ _ _ _ _ HmidChain3 HlastChain3))). }
  exists (a_CPi (Eq CA CM CA1) CB). split; assumption.
Qed.

Lemma case_An_CAbsCong : forall (L:atoms) (G:context) (D:available_props)
    (g1 g3 g4:co) (phi1:constraint) (a1:tm) (phi2:constraint)
    (a3 a2 B1 B B2:tm) (a:AnnIso G D g1 phi1 phi2),
  Piso G D g1 phi1 phi2 a ->
  forall
    (a0:forall c, c `notin` L ->
        AnnDefEq ((c ~ Co phi1) ++ G) D (open_co_wrt_co g3 (g_Var_f c))
          (open_tm_wrt_co a1 (g_Var_f c))
          (open_tm_wrt_co a2 (g_Var_f c))),
  (forall (c:atom) (n:c `notin` L),
      Pdef ((c ~ Co phi1) ++ G) D (open_co_wrt_co g3 (g_Var_f c))
        (open_tm_wrt_co a1 (g_Var_f c))
        (open_tm_wrt_co a2 (g_Var_f c)) (a0 c n)) ->
  forall
    (e:forall c, c `notin` L ->
        open_tm_wrt_co a3 (g_Var_f c) =
        open_tm_wrt_co a2 (g_Cast (g_Var_f c) (g_Sym g1)))
    (a4:AnnTyping G (a_CAbs phi1 a1) (a_CPi phi1 B1))
    (a5:AnnTyping G (a_CAbs phi1 a2) B)
    (a6:AnnTyping G (a_CAbs phi2 a3) (a_CPi phi2 B2))
    (a7:AnnDefEq G (dom G) g4 (a_CPi phi1 B1) (a_CPi phi2 B2)),
  Pdef G (dom G) g4 (a_CPi phi1 B1) (a_CPi phi2 B2) a7 ->
  Pdef G D (g_CAbsCong g1 g3 g4) (a_CAbs phi1 a1) (a_CAbs phi2 a3)
    (An_CAbsCong L G D g1 g3 g4 phi1 a1 phi2 a3 a2 B1 B B2 a a0 e a4 a5
       a6 a7).
Proof.
  intros L G D g1 g3 g4 phi1 a1 phi2 a3 a2 B1 B B2 Hiso IHiso
         Hbody IHbody He Hty1 Hty2 Hty3 Hty4 IHty4.
  unfold Pdef in |- *. intros Hg.
  assert (Hlc1 : lc_tm (a_CAbs phi1 a1))
    by exact (proj1 (AnnTyping_wf G (a_CAbs phi1 a1) (a_CPi phi1 B1) Hty1)).
  assert (Hlc3 : lc_tm (a_CAbs phi2 a3))
    by exact (proj1 (AnnTyping_wf G (a_CAbs phi2 a3) (a_CPi phi2 B2) Hty3)).
  destruct (lc_tm_cabs_inv phi1 a1 Hlc1) as [Hphi1 Hb1].
  destruct (lc_tm_cabs_inv phi2 a3 Hlc3) as [Hphi2 Hb3].
  (* choose a fresh covar, also avoiding D *)
  destruct (atom_fresh (L \u D \u cfv_tm (erase_tm FixDef))) as [c0 Hc0].
  destruct (notin_union_elim c0 L (D \u cfv_tm (erase_tm FixDef)) Hc0)
    as [Hc0L Hc0r1].
  destruct (notin_union_elim c0 D (cfv_tm (erase_tm FixDef)) Hc0r1)
    as [Hc0D Hc0fix].
  (* body join at the fresh covar *)
  assert (Hgc : Good (erase_context ((c0 ~ Co phi1) ++ G)) D)
    by exact (Good_cons_Co_fresh G D c0 phi1 Hg Hc0D Hphi1).
  destruct (IHbody c0 Hc0L Hgc) as [C12 [H12a H12b]].
  assert (Hjd12x : JD ((c0 ~ Co phi1) ++ G) D
      (open_tm_wrt_co a1 (g_Var_f c0))
      (open_tm_wrt_co a2 (g_Var_f c0)))
    by (exists C12; split; assumption).
  pose proof (JD_mono_G ((c0 ~ Co phi1) ++ G) G D _ _ Hjd12x) as Hjd12.
  assert (Hlc3x : lc_tm (open_tm_wrt_co a3 (g_Var_f c0)))
    by exact (Hb3 c0).
  assert (HeqErase : erase_tm (open_tm_wrt_co a3 (g_Var_f c0)) =
                     erase_tm (open_tm_wrt_co a2 (g_Var_f c0))).
  { rewrite (He c0 Hc0L).
    unfold open_tm_wrt_co.
    rewrite (erase_open_co_tm a2 0 (g_Cast (g_Var_f c0) (g_Sym g1))).
    rewrite (erase_open_co_tm a2 0 (g_Var_f c0)). reflexivity. }
  assert (Hjd32 : JD G D (open_tm_wrt_co a3 (g_Var_f c0))
                        (open_tm_wrt_co a2 (g_Var_f c0)))
    by exact (JD_of_eq G D _ _ Hlc3x HeqErase).
  assert (Hjd13 : JD G D (open_tm_wrt_co a1 (g_Var_f c0))
                        (open_tm_wrt_co a3 (g_Var_f c0)))
    by exact (JD_trans G D _ _ _ Hjd12 (JD_sym G D _ _ Hjd32)).
  destruct Hjd13 as [Cx [H1x H3x]].
  (* close the common body *)
  set (CB := closeC_tm c0 0 Cx).
  assert (Hc0CB : c0 `notin` cfv_tm CB)
    by (unfold CB; apply closeC_tm_cfv_fresh).
  assert (HopenCB : open_tm_wrt_co CB (g_Var_f c0) = Cx).
  { unfold CB. rewrite (open_closeC_subst2 Cx c0 c0). apply subst_co_tm_self. }
  assert (HeCx : Eok Cx)
    by (eapply Eok_MultiPar;
        [apply Eok_erase | exact H1x]).
  assert (HeCB : Eok CB) by (unfold CB; apply Eok_closeC_tm; exact HeCx).
  (* opened source chains *)
  assert (Herase1 : erase_tm (open_tm_wrt_co a1 (g_Var_f c0)) =
                    open_tm_wrt_co (erase_tm a1) (g_Var_f c0)).
  { unfold open_tm_wrt_co. rewrite (erase_open_co_tm a1 0 (g_Var_f c0)).
    symmetry. apply open_co_erase_tm. }
  assert (Herase3 : erase_tm (open_tm_wrt_co a3 (g_Var_f c0)) =
                    open_tm_wrt_co (erase_tm a3) (g_Var_f c0)).
  { unfold open_tm_wrt_co. rewrite (erase_open_co_tm a3 0 (g_Var_f c0)).
    symmetry. apply open_co_erase_tm. }
  assert (Hrel1 : MultiPar (erase_context G) D
      (open_tm_wrt_co (erase_tm a1) (g_Var_f c0))
      (open_tm_wrt_co CB (g_Var_f c0))).
  { rewrite <- Herase1. rewrite HopenCB. exact H1x. }
  assert (Hrel3 : MultiPar (erase_context G) D
      (open_tm_wrt_co (erase_tm a3) (g_Var_f c0))
      (open_tm_wrt_co CB (g_Var_f c0))).
  { rewrite <- Herase3. rewrite HopenCB. exact H3x. }
  (* body chains *)
  assert (HbodyChain1 : MultiPar (erase_context G) D
      (a_UCAbs (erase_tm a1)) (a_UCAbs CB)).
  { apply (MultiPar_UCAbs_body_cong (erase_context G) D
             (erase_tm a1) CB c0).
    - exact (Eok_cfv_tm (erase_tm a1) (Eok_erase a1) c0).
    - exact Hc0CB.
    - exact Hc0fix.
    - exact Hrel1. }
  assert (HbodyChain3 : MultiPar (erase_context G) D
      (a_UCAbs (erase_tm a3)) (a_UCAbs CB)).
  { apply (MultiPar_UCAbs_body_cong (erase_context G) D
             (erase_tm a3) CB c0).
    - exact (Eok_cfv_tm (erase_tm a3) (Eok_erase a3) c0).
    - exact Hc0CB.
    - exact Hc0fix.
    - exact Hrel3. }
  exists (a_UCAbs CB). split; cbn [erase_tm]; assumption.
Qed.

(* ================================================================== *)
(* Main theorem: Good contexts preserve joinability of AnnDefEq     *)
(* ================================================================== *)

Theorem AnnDefEq_Good_join : forall (G:context) (D:available_props)
    (g:co) (a b:tm),
  Good (erase_context G) D -> AnnDefEq G D g a b ->
  exists C, MultiPar (erase_context G) D (erase_tm a) C /\
            MultiPar (erase_context G) D (erase_tm b) C.
Proof.
  intros G D g a b Hg Hdef.
  exact (AnnDefEq_ind2 Pdef Piso
    case_An_Assn case_An_Refl case_An_EraseEq case_An_Sym case_An_Trans
    case_An_Beta case_An_PiCong case_An_AbsCong case_An_AppCong
    case_An_PiFst case_An_PiSnd case_An_CPiCong case_An_CAbsCong
    case_An_CAppCong case_An_CPiSnd case_An_Cast case_An_IsoSnd
    case_An_PropCong case_An_CPiFst case_An_IsoSym case_An_IsoConv
    G D g a b Hdef Hg).
Qed.
End EOK.


Lemma AnnDefEq_Good_join : forall (G:context) (D:available_props) (g:co) (a b:tm),
  Good (erase_context G) D ->
  AnnDefEq G D g a b ->
  exists C, MultiPar (erase_context G) D (erase_tm a) C /\
            MultiPar (erase_context G) D (erase_tm b) C.
Proof. exact EOK.AnnDefEq_Good_join. Qed.

(* Source inversions for Par and MultiPar, for rigid source heads. *)



(* Shape facts used by progress, derived from Good joinability. *)
Lemma AnnDefEq_Good_Pi_Pi : forall (G:context) (D:available_props) (g:co) (a b:tm)
       (rho1:relflag) (A1 B1:tm) (rho2:relflag) (A2 B2:tm),
  Good (erase_context G) D -> AnnDefEq G D g a b ->
  erase_tm a = a_Pi rho1 A1 B1 -> erase_tm b = a_Pi rho2 A2 B2 ->
  rho1 = rho2.
Proof.
  intros G D g a b rho1 A1 B1 rho2 A2 B2 Hgood Hdef Ha Hb.
  destruct (AnnDefEq_Good_join G D g a b Hgood Hdef) as [C [H1 H2]].
  rewrite Ha in H1. rewrite Hb in H2.
  destruct (MultiPar_Pi_src_inv _ _ _ _ _ _ H1) as [A1' [B1' HC1]].
  destruct (MultiPar_Pi_src_inv _ _ _ _ _ _ H2) as [A2' [B2' HC2]].
  rewrite HC1 in HC2. injection HC2 as Hr _ _. exact Hr.
Qed.

Lemma AnnDefEq_Good_Star_Pi : forall (G:context) (D:available_props) (g:co) (a b:tm)
       (rho:relflag) (A B:tm),
  Good (erase_context G) D -> AnnDefEq G D g a b ->
  erase_tm a = a_Star -> erase_tm b = a_Pi rho A B -> False.
Proof.
  intros G D g a b rho A B Hgood Hdef Ha Hb.
  destruct (AnnDefEq_Good_join G D g a b Hgood Hdef) as [C [H1 H2]].
  rewrite Ha in H1. rewrite Hb in H2.
  pose proof (MultiPar_Star_src_inv _ _ _ H1) as HC1.
  destruct (MultiPar_Pi_src_inv _ _ _ _ _ _ H2) as [A' [B' HC2]].
  rewrite HC1 in HC2. discriminate HC2.
Qed.

Lemma AnnDefEq_Good_Star_CPi : forall (G:context) (D:available_props) (g:co) (a b:tm)
       (phi:constraint) (B:tm),
  Good (erase_context G) D -> AnnDefEq G D g a b ->
  erase_tm a = a_Star -> erase_tm b = a_CPi phi B -> False.
Proof.
  intros G D g a b phi B Hgood Hdef Ha Hb.
  destruct (AnnDefEq_Good_join G D g a b Hgood Hdef) as [C [H1 H2]].
  rewrite Ha in H1. rewrite Hb in H2.
  pose proof (MultiPar_Star_src_inv _ _ _ H1) as HC1.
  destruct (MultiPar_CPi_src_inv _ _ _ _ _ H2) as [phi' [B' HC2]].
  rewrite HC1 in HC2. discriminate HC2.
Qed.

Lemma AnnDefEq_Good_Pi_CPi : forall (G:context) (D:available_props) (g:co) (a b:tm)
       (rho:relflag) (A B:tm) (phi:constraint) (B2:tm),
  Good (erase_context G) D -> AnnDefEq G D g a b ->
  erase_tm a = a_Pi rho A B -> erase_tm b = a_CPi phi B2 -> False.
Proof.
  intros G D g a b rho A B phi B2 Hgood Hdef Ha Hb.
  destruct (AnnDefEq_Good_join G D g a b Hgood Hdef) as [C [H1 H2]].
  rewrite Ha in H1. rewrite Hb in H2.
  destruct (MultiPar_Pi_src_inv _ _ _ _ _ _ H1) as [A' [B' HC1]].
  destruct (MultiPar_CPi_src_inv _ _ _ _ _ H2) as [phi' [B2' HC2]].
  rewrite HC1 in HC2. discriminate HC2.
Qed.

Lemma AnnDefEq_Good_CPi_Pi : forall (G:context) (D:available_props) (g:co) (a b:tm)
       (phi:constraint) (B2:tm) (rho:relflag) (A B:tm),
  Good (erase_context G) D -> AnnDefEq G D g a b ->
  erase_tm a = a_CPi phi B2 -> erase_tm b = a_Pi rho A B -> False.
Proof.
  intros G D g a b phi B2 rho A B Hgood Hdef Ha Hb.
  destruct (AnnDefEq_Good_join G D g a b Hgood Hdef) as [C [H1 H2]].
  rewrite Ha in H1. rewrite Hb in H2.
  destruct (MultiPar_CPi_src_inv _ _ _ _ _ H1) as [phi' [B2' HC1]].
  destruct (MultiPar_Pi_src_inv _ _ _ _ _ _ H2) as [A' [B' HC2]].
  rewrite HC1 in HC2. discriminate HC2.
Qed.

(* ================================================================ *)
(* Relevant fv facts                                                 *)
(* ================================================================ *)

Lemma fv_erase_App_fun : forall (b:tm) (rho:relflag) (a:tm),
  AtomSetImpl.Subset (fv_tm_tm_tm (erase_tm b))
                     (fv_tm_tm_tm (erase_tm (a_App b rho a))).
Proof.
  intros b rho a. destruct rho; cbn [erase_tm fv_tm_tm_tm]; intros x Hx;
  apply AtomSetImpl.union_2; exact Hx.
Qed.

Lemma fv_erase_CApp_fun : forall (a:tm) (g:co),
  AtomSetImpl.Subset (fv_tm_tm_tm (erase_tm a))
                     (fv_tm_tm_tm (erase_tm (a_CApp a g))).
Proof.
  intros a g. cbn [erase_tm fv_tm_tm_tm].
  intros x Hx. apply AtomSetImpl.union_2; exact Hx.
Qed.

Lemma fv_erase_Conv_fun : forall (a:tm) (g:co),
  AtomSetImpl.Subset (fv_tm_tm_tm (erase_tm a))
                     (fv_tm_tm_tm (erase_tm (a_Conv a g))).
Proof.
  intros. cbn [erase_tm]. intros x Hx. exact Hx.
Qed.

Lemma irrelevant_App_fun : forall (G:context) (D:available_props)
       (b:tm) (rho:relflag) (a:tm),
  irrelevant G D (a_App b rho a) -> irrelevant G D b.
Proof.
  intros G D b rho a [Hfv Hgood]. split; [|exact Hgood].
  intros x A Hb.
  eapply notin_subset; [apply fv_erase_App_fun | exact (Hfv x A Hb)].
Qed.

Lemma irrelevant_CApp_fun : forall (G:context) (D:available_props)
       (a:tm) (g:co),
  irrelevant G D (a_CApp a g) -> irrelevant G D a.
Proof.
  intros G D a g [Hfv Hgood]. split; [|exact Hgood].
  intros x A Hb.
  eapply notin_subset; [apply fv_erase_CApp_fun | exact (Hfv x A Hb)].
Qed.

Lemma irrelevant_Conv_fun : forall (G:context) (D:available_props)
       (a:tm) (g:co),
  irrelevant G D (a_Conv a g) -> irrelevant G D a.
Proof.
  intros G D a g [Hfv Hgood]. split; [|exact Hgood].
  intros x A Hb.
  eapply notin_subset; [apply fv_erase_Conv_fun | exact (Hfv x A Hb)].
Qed.

(* ================================================================ *)
(* Canonical typing shapes of values                                 *)
(* ================================================================ *)

(* ===== ProgressConv ===== *)

Lemma Value_typing_Conv_Pi :
  forall (G:context) (D:available_props) (g:co) (T:tm)
         (rho:relflag) (A B:tm) (v:tm),
  Good (erase_context G) D ->
  AnnDefEq G D g T (a_Pi rho A B) ->
  Value v -> AnnTyping G v T ->
  exists A0 b0 B0, T = a_Pi rho A0 B0 /\
               v = a_Abs rho A0 b0.
Proof.
  intros G D g T rho A B v Hgood Hdef Hv Hty.
  pose proof (Value_AnnTyping_shape G v T Hv Hty) as Hsh.
  destruct Hsh as [Hsh | Hsh].
  - destruct Hsh as [Hv0 HT].
    exfalso.
    eapply (AnnDefEq_Good_Star_Pi G D g T (a_Pi rho A B)
              rho (erase_tm A) (erase_tm B)).
    + exact Hgood.
    + exact Hdef.
    + rewrite HT. reflexivity.
    + reflexivity.
  - destruct Hsh as [Hsh | Hsh].
    + destruct Hsh as [rho0 [A0 [B0 [Hv0 HT]]]].
      exfalso.
      eapply (AnnDefEq_Good_Star_Pi G D g T (a_Pi rho A B)
                rho (erase_tm A) (erase_tm B)).
      * exact Hgood.
      * exact Hdef.
      * rewrite HT. reflexivity.
      * reflexivity.
    + destruct Hsh as [Hsh | Hsh].
      * destruct Hsh as [phi0 [B0 [Hv0 HT]]].
        exfalso.
        eapply (AnnDefEq_Good_Star_Pi G D g T (a_Pi rho A B)
                  rho (erase_tm A) (erase_tm B)).
        -- exact Hgood.
        -- exact Hdef.
        -- rewrite HT. reflexivity.
        -- reflexivity.
      * destruct Hsh as [Hsh | Hsh].
        -- destruct Hsh as [A0 [b0 [Hv0 [B0 HT]]]].
           assert (Hrho : Rel = rho).
           { eapply (AnnDefEq_Good_Pi_Pi G D g T (a_Pi rho A B)
                       Rel (erase_tm A0) (erase_tm B0)
                       rho (erase_tm A) (erase_tm B)).
             + exact Hgood.
             + exact Hdef.
             + rewrite HT. reflexivity.
             + reflexivity. }
           subst rho. subst v. eauto.
        -- destruct Hsh as [Hsh | Hsh].
           ++ destruct Hsh as [A0 [b0 [Hv0 [B0 HT]]]].
              assert (Hrho : Irrel = rho).
              { eapply (AnnDefEq_Good_Pi_Pi G D g T (a_Pi rho A B)
                          Irrel (erase_tm A0) (erase_tm B0)
                          rho (erase_tm A) (erase_tm B)).
                + exact Hgood.
                + exact Hdef.
                + rewrite HT. reflexivity.
                + reflexivity. }
              subst rho. subst v. eauto.
           ++ destruct Hsh as [phi0 [b0 [Hv0 [B0 HT]]]].
              exfalso.
              eapply (AnnDefEq_Good_CPi_Pi G D g T (a_Pi rho A B)
                        (erase_constraint phi0) (erase_tm B0)
                        rho (erase_tm A) (erase_tm B)).
              ** exact Hgood.
              ** exact Hdef.
              ** rewrite HT. reflexivity.
              ** reflexivity.
Qed.

Lemma Value_typing_Conv_CPi :
  forall (G:context) (D:available_props) (g:co) (T:tm)
         (phi:constraint) (B:tm) (v:tm),
  Good (erase_context G) D ->
  AnnDefEq G D g T (a_CPi phi B) ->
  Value v -> AnnTyping G v T ->
  exists phi0 b0 B0, T = a_CPi phi0 B0 /\ v = a_CAbs phi0 b0.
Proof.
  intros G D g T phi B v Hgood Hdef Hv Hty.
  pose proof (Value_AnnTyping_shape G v T Hv Hty) as Hsh.
  destruct Hsh as [Hsh | Hsh].
  - destruct Hsh as [Hv0 HT]. exfalso.
    eapply (AnnDefEq_Good_Star_CPi G D g T (a_CPi phi B)
              (erase_constraint phi) (erase_tm B)).
    + exact Hgood.
    + exact Hdef.
    + rewrite HT. reflexivity.
    + reflexivity.
  - destruct Hsh as [Hsh | Hsh].
    + destruct Hsh as [rho0 [A0 [B0 [Hv0 HT]]]]. exfalso.
      eapply (AnnDefEq_Good_Star_CPi G D g T (a_CPi phi B)
                (erase_constraint phi) (erase_tm B)).
      * exact Hgood.
      * exact Hdef.
      * rewrite HT. reflexivity.
      * reflexivity.
    + destruct Hsh as [Hsh | Hsh].
      * destruct Hsh as [phi0 [B0 [Hv0 HT]]]. exfalso.
        eapply (AnnDefEq_Good_Star_CPi G D g T (a_CPi phi B)
                  (erase_constraint phi) (erase_tm B)).
        -- exact Hgood.
        -- exact Hdef.
        -- rewrite HT. reflexivity.
        -- reflexivity.
      * destruct Hsh as [Hsh | Hsh].
        -- destruct Hsh as [A0 [b0 [Hv0 [B0 HT]]]]. exfalso.
           eapply (AnnDefEq_Good_Pi_CPi G D g T (a_CPi phi B)
                     Rel (erase_tm A0) (erase_tm B0) (erase_constraint phi) (erase_tm B)).
           ++ exact Hgood.
           ++ exact Hdef.
           ++ rewrite HT. reflexivity.
           ++ reflexivity.
        -- destruct Hsh as [Hsh | Hsh].
           ++ destruct Hsh as [A0 [b0 [Hv0 [B0 HT]]]]. exfalso.
              eapply (AnnDefEq_Good_Pi_CPi G D g T (a_CPi phi B)
                        Irrel (erase_tm A0) (erase_tm B0) (erase_constraint phi) (erase_tm B)).
              ** exact Hgood.
              ** exact Hdef.
              ** rewrite HT. reflexivity.
              ** reflexivity.
           ++ destruct Hsh as [phi0 [b0 [Hv0 [B0 HT]]]].
              subst v. eauto.
Qed.

(* ===== SwapRename ===== *)

(* swap-renaming invariance of Value / CoercedValue *)

Lemma sw_surj_all : forall x y z, exists w, sw x y w = z.
Proof.
  intros x y z. destruct (KeySetFacts.eq_dec x y) as [E|H].
  - subst y. destruct (KeySetFacts.eq_dec z x) as [Ez|Hz].
    + subst z. exists x. unfold sw. rewrite eq_var_true'. reflexivity.
    + exists z. unfold sw.
      assert (Ex : eq_var z x = false).
      { destruct (eq_var z x) eqn:E2.
        - exfalso. apply Hz. apply eq_var_true. exact E2.
        - reflexivity. }
      rewrite Ex. reflexivity.
  - exact (sw_surj x y H z).
Qed.

Lemma lc_tm_rename_sw : forall x y a, lc_tm a -> lc_tm (rename_tm (sw x y) (sw x y) a).
Proof.
  intros. exact (proj1 (lc_rename (sw x y) (sw x y)
    (sw_surj_all x y) (sw_surj_all x y)) a H).
Qed.
Lemma lc_co_rename_sw : forall x y g, lc_co g -> lc_co (rename_co (sw x y) (sw x y) g).
Proof.
  intros. exact (proj1 (proj2 (lc_rename (sw x y) (sw x y)
    (sw_surj_all x y) (sw_surj_all x y))) g H).
Qed.
Lemma lc_constraint_rename_sw : forall x y phi,
  lc_constraint phi -> lc_constraint (rename_constraint (sw x y) (sw x y) phi).
Proof.
  intros. exact (proj2 (proj2 (proj2 (lc_rename (sw x y) (sw x y)
    (sw_surj_all x y) (sw_surj_all x y)))) phi H).
Qed.

Lemma Value_rename_sw : forall x y a,
  Value a -> Value (rename_tm (sw x y) (sw x y) a).
Proof.
  intros x y.
  apply (Value_mut
    (fun a _ => Value (rename_tm (sw x y) (sw x y) a))
    (fun a _ => CoercedValue (rename_tm (sw x y) (sw x y) a))).
  - cbn [rename_tm]. apply Value_Star.
  - intros rho A B lcA lcPi. cbn [rename_tm].
    apply Value_Pi.
    + exact (lc_tm_rename_sw x y _ lcA).
    + exact (lc_tm_rename_sw x y _ lcPi).
  - intros phi B lcphi lcCPi. cbn [rename_tm].
    apply Value_CPi.
    + exact (lc_constraint_rename_sw x y _ lcphi).
    + exact (lc_tm_rename_sw x y _ lcCPi).
  - intros A a lcA lcAbs. cbn [rename_tm].
    apply Value_AbsRel.
    + exact (lc_tm_rename_sw x y _ lcA).
    + exact (lc_tm_rename_sw x y _ lcAbs).
  - intros a lcUAbs. cbn [rename_tm]. apply Value_UAbsRel.
    exact (lc_tm_rename_sw x y _ lcUAbs).
  - intros L a H IH. cbn [rename_tm].
    apply (Value_UAbsIrrel (L \u {{x}} \u {{y}})).
    intros z Hz.
    assert (HzL : z `notin` L) by fsetdec.
    assert (Hzx : z <> x) by (intro E; subst z; fsetdec).
    assert (Hzy : z <> y) by (intro E; subst z; fsetdec).
    specialize (IH z HzL).
    unfold open_tm_wrt_tm in IH.
    rewrite rename_open_tm_tm in IH.
    cbn [rename_tm] in IH.
    rewrite (sw_fix x y z Hzx Hzy) in IH. exact IH.
  - intros L A a lcA H IH. cbn [rename_tm].
    apply (Value_AbsIrrel (L \u {{x}} \u {{y}})).
    + exact (lc_tm_rename_sw x y _ lcA).
    + intros z Hz.
      assert (HzL : z `notin` L) by fsetdec.
      assert (Hzx : z <> x) by (intro E; subst z; fsetdec).
      assert (Hzy : z <> y) by (intro E; subst z; fsetdec).
      specialize (IH z HzL).
      unfold open_tm_wrt_tm in IH.
      rewrite rename_open_tm_tm in IH.
      cbn [rename_tm] in IH.
      rewrite (sw_fix x y z Hzx Hzy) in IH. exact IH.
  - intros phi a lcphi lcCAbs. cbn [rename_tm].
    apply Value_CAbs.
    + exact (lc_constraint_rename_sw x y _ lcphi).
    + exact (lc_tm_rename_sw x y _ lcCAbs).
  - intros a lcUCAbs. cbn [rename_tm]. apply Value_UCAbs.
    exact (lc_tm_rename_sw x y _ lcUCAbs).
  - intros a Ha IHa. cbn [rename_tm]. apply CV. exact IHa.
  - intros a g lcg Ha IHa. cbn [rename_tm]. apply CC.
    + exact (lc_co_rename_sw x y _ lcg).
    + exact IHa.
Qed.

Lemma CoercedValue_rename_sw : forall x y a,
  CoercedValue a -> CoercedValue (rename_tm (sw x y) (sw x y) a).
Proof.
  intros x y a H. inversion H; subst.
  - apply CV. apply Value_rename_sw. assumption.
  - apply CC.
    + exact (lc_co_rename_sw x y _ H0).
    + apply Value_rename_sw. assumption.
Qed.

(* ===== CoercedLift ===== *)

(* Cofinite lifting of CoercedValue at openings: a single fresh witness
   suffices, using swap-renaming invariance. *)

Lemma CoercedValue_open_swap : forall (x y:atom) (a:tm),
  x <> y ->
  x `notin` fvx_tm a ->
  y `notin` fvx_tm a ->
  CoercedValue (open_tm_wrt_tm a (a_Var_f x)) ->
  CoercedValue (open_tm_wrt_tm a (a_Var_f y)).
Proof.
  intros x y a Hxy Hx Hy Hcv.
  assert (Hren : rename_tm (sw x y) (sw x y)
                   (open_tm_wrt_tm a (a_Var_f x))
                 = open_tm_wrt_tm a (a_Var_f y)).
  { unfold open_tm_wrt_tm.
    rewrite rename_open_tm_tm.
    assert (Ha : rename_tm (sw x y) (sw x y) a = a).
    { apply (proj1 rename_fresh).
      - intros z Hz. apply sw_fix.
        + intro E. subst z. exact (Hx Hz).
        + intro E. subst z. exact (Hy Hz).
      - intros c Hc. apply sw_fix.
        + intro E. subst c. exact (Hx Hc).
        + intro E. subst c. exact (Hy Hc). }
    rewrite Ha. cbn [rename_tm]. rewrite sw_same. reflexivity. }
  rewrite <- Hren.
  apply CoercedValue_rename_sw. exact Hcv.
Qed.

Lemma CoercedValue_swap_any : forall (x y:atom) (a:tm),
  x `notin` fvx_tm a ->
  y `notin` fvx_tm a ->
  CoercedValue (open_tm_wrt_tm a (a_Var_f x)) ->
  CoercedValue (open_tm_wrt_tm a (a_Var_f y)).
Proof.
  intros x y a Hx Hy H.
  destruct (KeySetFacts.eq_dec x y) as [E|Hne].
  - subst y. exact H.
  - apply (CoercedValue_open_swap x y a Hne Hx Hy H).
Qed.

Lemma Value_AbsIrrel_of_CV : forall (L:vars) (A a:tm) (x:atom),
  lc_tm A ->
  x `notin` L ->
  x `notin` fvx_tm a ->
  CoercedValue (open_tm_wrt_tm a (a_Var_f x)) ->
  Value (a_Abs Irrel A a).
Proof.
  intros L A a x HlcA HxL Hxa Hcv.
  apply (Value_AbsIrrel (L \u fvx_tm a \u {{x}}) A a HlcA).
  intros y Hy.
  assert (HyL : y `notin` L) by fsetdec.
  assert (Hya : y `notin` fvx_tm a) by fsetdec.
  assert (Hyx : y <> x) by (intro E; subst y; fsetdec).
  apply (CoercedValue_open_swap x y a).
  - intro E. apply Hyx. symmetry. exact E.
  - exact Hxa.
  - exact Hya.
  - exact Hcv.
Qed.

(* No value (and no coerced value) admits a head reduction.  Proven by
   mutual induction over the Value/CoercedValue derivations. *)

Lemma Value_no_head_reduction : forall a,
  Value a -> forall (G:context) a', ~ head_reduction G a a'.
Proof.
  apply (Value_mut
    (fun a _ => forall (G:context) a', ~ head_reduction G a a')
    (fun a _ => forall (G:context) a', ~ head_reduction G a a')).
  - intros G a' H. inversion H.
  - intros rho A B lcA lcPi G a' H. inversion H.
  - intros phi B lcphi lcCPi G a' H. inversion H.
  - intros A a lcA lcAbs G a' H. inversion H.
  - intros a lcUAbs G a' H. inversion H.
  - intros L a Hbody IH G a' Hred. inversion Hred.
  - intros L A a lcA Hbody IH G a' Hred.
    inversion Hred; subst; try discriminate.
    match goal with
    | L0 : vars,
      Hcof : forall x, x `notin` L0 ->
          head_reduction ((x ~ Tm ?A0) ++ G) (open_tm_wrt_tm a (a_Var_f x))
                         (open_tm_wrt_tm ?b' (a_Var_f x)) |- _ =>
        destruct (atom_fresh (L \u L0)) as [z Hz];
        assert (HzL : z `notin` L) by fsetdec;
        assert (HzL0 : z `notin` L0) by fsetdec;
        exact (IH z HzL ((z ~ Tm A0) ++ G)
                 (open_tm_wrt_tm b' (a_Var_f z)) (Hcof z HzL0))
    end.
  - intros phi a lcphi lcCAbs G a' H. inversion H.
  - intros a lcUCAbs G a' H. inversion H.
  - intros a v IH G a' Hr. exact (IH G a' Hr).
  - intros a g Hlcg v IH G a' Hr.
    inversion Hr; subst; try discriminate;
      try (match goal with
           | Hstep : head_reduction ?G0 ?x ?r |- _ => exact (IH G0 r Hstep)
           end);
      try (match goal with
           | Hv : Value (a_Conv _ _) |- _ => inversion Hv
           end).
Qed.

Lemma CoercedValue_no_head_reduction : forall a,
  CoercedValue a -> forall (G:context) a', ~ head_reduction G a a'.
Proof.
  intros a H. inversion H; subst.
  - intros G a' Hr. exact (Value_no_head_reduction a H0 G a' Hr).
  - intros G a' Hr.
    inversion Hr; subst; try discriminate;
      try (match goal with
           | Hstep : head_reduction ?G0 ?x ?r |- _ =>
               exact (Value_no_head_reduction x H1 G0 r Hstep)
           end);
      try (match goal with
           | Hv : Value (a_Conv _ _) |- _ => inversion Hv
           end).
Qed.

Lemma Value_head_reduction_False : forall (G:context) (a a':tm),
  Value a -> head_reduction G a a' -> False.
Proof. intros G a a' Hv Hr. exact (Value_no_head_reduction a Hv G a' Hr). Qed.

Lemma CoercedValue_head_reduction_False : forall (G:context) (a a':tm),
  CoercedValue a -> head_reduction G a a' -> False.
Proof. intros G a a' Hv Hr. exact (CoercedValue_no_head_reduction a Hv G a' Hr). Qed.

(* ===== ProgressAbs ===== *)

(* ================================================================ *)
(* Cofinite head-reduction step interface.                          *)
(*                                                                  *)
(* This is the one remaining genuinely semantic ingredient of the   *)
(* Abs-Irrel case of progress: from a cofinite family of head      *)
(* reductions of the opened body one must extract a common reduct   *)
(* body whose openings are the targets.  It follows from renaming   *)
(* equivariance of head_reduction (with AnnTyping/AnnDefEq          *)
(* equivariance for An_AbsTerm/An_Push/An_CPush); the swap          *)
(* machinery is available, the typing equivariance remains to be    *)
(* built.                                                           *)
(* ================================================================ *)


Module COF.
(* ==== SwapRename ==== *)

(* swap-renaming invariance of Value / CoercedValue *)

Lemma sw_surj_all : forall x y z, exists w, sw x y w = z.
Proof.
  intros x y z. destruct (KeySetFacts.eq_dec x y) as [E|H].
  - subst y. destruct (KeySetFacts.eq_dec z x) as [Ez|Hz].
    + subst z. exists x. unfold sw. rewrite eq_var_true'. reflexivity.
    + exists z. unfold sw.
      assert (Ex : eq_var z x = false).
      { destruct (eq_var z x) eqn:E2.
        - exfalso. apply Hz. apply eq_var_true. exact E2.
        - reflexivity. }
      rewrite Ex. reflexivity.
  - exact (sw_surj x y H z).
Qed.

Lemma lc_tm_rename_sw : forall x y a, lc_tm a -> lc_tm (rename_tm (sw x y) (sw x y) a).
Proof.
  intros. exact (proj1 (lc_rename (sw x y) (sw x y)
    (sw_surj_all x y) (sw_surj_all x y)) a H).
Qed.
Lemma lc_co_rename_sw : forall x y g, lc_co g -> lc_co (rename_co (sw x y) (sw x y) g).
Proof.
  intros. exact (proj1 (proj2 (lc_rename (sw x y) (sw x y)
    (sw_surj_all x y) (sw_surj_all x y))) g H).
Qed.
Lemma lc_constraint_rename_sw : forall x y phi,
  lc_constraint phi -> lc_constraint (rename_constraint (sw x y) (sw x y) phi).
Proof.
  intros. exact (proj2 (proj2 (proj2 (lc_rename (sw x y) (sw x y)
    (sw_surj_all x y) (sw_surj_all x y)))) phi H).
Qed.

Lemma Value_rename_sw : forall x y a,
  Value a -> Value (rename_tm (sw x y) (sw x y) a).
Proof.
  intros x y.
  apply (Value_mut
    (fun a _ => Value (rename_tm (sw x y) (sw x y) a))
    (fun a _ => CoercedValue (rename_tm (sw x y) (sw x y) a))).
  - cbn [rename_tm]. apply Value_Star.
  - intros rho A B lcA lcPi. cbn [rename_tm].
    apply Value_Pi.
    + exact (lc_tm_rename_sw x y _ lcA).
    + exact (lc_tm_rename_sw x y _ lcPi).
  - intros phi B lcphi lcCPi. cbn [rename_tm].
    apply Value_CPi.
    + exact (lc_constraint_rename_sw x y _ lcphi).
    + exact (lc_tm_rename_sw x y _ lcCPi).
  - intros A a lcA lcAbs. cbn [rename_tm].
    apply Value_AbsRel.
    + exact (lc_tm_rename_sw x y _ lcA).
    + exact (lc_tm_rename_sw x y _ lcAbs).
  - intros a lcUAbs. cbn [rename_tm]. apply Value_UAbsRel.
    exact (lc_tm_rename_sw x y _ lcUAbs).
  - intros L a H IH. cbn [rename_tm].
    apply (Value_UAbsIrrel (L \u {{x}} \u {{y}})).
    intros z Hz.
    assert (HzL : z `notin` L) by fsetdec.
    assert (Hzx : z <> x) by (intro E; subst z; fsetdec).
    assert (Hzy : z <> y) by (intro E; subst z; fsetdec).
    specialize (IH z HzL).
    unfold open_tm_wrt_tm in IH.
    rewrite rename_open_tm_tm in IH.
    cbn [rename_tm] in IH.
    rewrite (sw_fix x y z Hzx Hzy) in IH. exact IH.
  - intros L A a lcA H IH. cbn [rename_tm].
    apply (Value_AbsIrrel (L \u {{x}} \u {{y}})).
    + exact (lc_tm_rename_sw x y _ lcA).
    + intros z Hz.
      assert (HzL : z `notin` L) by fsetdec.
      assert (Hzx : z <> x) by (intro E; subst z; fsetdec).
      assert (Hzy : z <> y) by (intro E; subst z; fsetdec).
      specialize (IH z HzL).
      unfold open_tm_wrt_tm in IH.
      rewrite rename_open_tm_tm in IH.
      cbn [rename_tm] in IH.
      rewrite (sw_fix x y z Hzx Hzy) in IH. exact IH.
  - intros phi a lcphi lcCAbs. cbn [rename_tm].
    apply Value_CAbs.
    + exact (lc_constraint_rename_sw x y _ lcphi).
    + exact (lc_tm_rename_sw x y _ lcCAbs).
  - intros a lcUCAbs. cbn [rename_tm]. apply Value_UCAbs.
    exact (lc_tm_rename_sw x y _ lcUCAbs).
  - intros a Ha IHa. cbn [rename_tm]. apply CV. exact IHa.
  - intros a g lcg Ha IHa. cbn [rename_tm]. apply CC.
    + exact (lc_co_rename_sw x y _ lcg).
    + exact IHa.
Qed.

Lemma CoercedValue_rename_sw : forall x y a,
  CoercedValue a -> CoercedValue (rename_tm (sw x y) (sw x y) a).
Proof.
  intros x y a H. inversion H; subst.
  - apply CV. apply Value_rename_sw. assumption.
  - apply CC.
    + exact (lc_co_rename_sw x y _ H0).
    + apply Value_rename_sw. assumption.
Qed.
(* ==== Eqv ==== *)

(* ================================================================== *)
(* Swap properties                                                     *)
(* ================================================================== *)

Lemma sw_same_at_y : forall x y, sw x y y = x.
Proof.
  intros x y. destruct (KeySetFacts.eq_dec x y) as [->|Hxy].
  - rewrite sw_same. reflexivity.
  - apply sw_same'. exact Hxy.
Qed.

Lemma sw_invol : forall x y z, sw x y (sw x y z) = z.
Proof.
  intros x y z.
  destruct (KeySetFacts.eq_dec z x) as [->|Hzx].
  - rewrite sw_same. rewrite sw_same_at_y. reflexivity.
  - destruct (KeySetFacts.eq_dec z y) as [->|Hzy].
    + rewrite sw_same_at_y. rewrite sw_same. reflexivity.
    + rewrite (sw_fix x y z Hzx Hzy).
      rewrite (sw_fix x y z Hzx Hzy). reflexivity.
Qed.

Lemma sw_inj : forall x y a b, sw x y a = sw x y b -> a = b.
Proof.
  intros x y a b H.
  assert (H' := f_equal (sw x y) H).
  rewrite !sw_invol in H'. exact H'.
Qed.

Lemma sw_fix_notin : forall x y z, z <> x -> z <> y -> sw x y z = z.
Proof. intros; apply sw_fix; assumption. Qed.

(* ================================================================== *)
(* Renaming of sorts and contexts                                      *)
(* ================================================================== *)

Definition rename_sort_sw (x y:atom) (s:sort) : sort :=
  match s with
  | Tm A => Tm (rename_tm (sw x y) (sw x y) A)
  | Co phi => Co (rename_constraint (sw x y) (sw x y) phi)
  end.

Definition rename_pair_sw (x y:atom) (p:atom * sort) : atom * sort :=
  (sw x y (fst p), rename_sort_sw x y (snd p)).

Definition rename_ctx_sw (x y:atom) (G:context) : context :=
  List.map (rename_pair_sw x y) G.

Lemma rename_ctx_sw_cons : forall x y z s G,
  rename_ctx_sw x y ((z,s)::G) = (sw x y z, rename_sort_sw x y s) :: rename_ctx_sw x y G.
Proof. intros; reflexivity. Qed.
Lemma rename_ctx_sw_nil : forall x y, rename_ctx_sw x y nil = nil.
Proof. reflexivity. Qed.

Lemma binds_rename_ctx_sw : forall x y (z:atom) s G,
  binds z s G -> binds (sw x y z) (rename_sort_sw x y s) (rename_ctx_sw x y G).
Proof.
  intros x y z s G H. unfold binds in *.
  unfold rename_ctx_sw.
  apply (List.in_map (rename_pair_sw x y) G (z,s)) in H.
  simpl in H. exact H.
Qed.

Lemma dom_rename_ctx_sw_fwd : forall x y G c,
  c `in` dom G -> sw x y c `in` dom (rename_ctx_sw x y G).
Proof.
  intros x y G c Hc.
  destruct (@in_dom_binds sort c G Hc) as [s Hs].
  apply binds_In with (a := rename_sort_sw x y s).
  apply binds_rename_ctx_sw. exact Hs.
Qed.

Lemma dom_rename_ctx_sw_bwd : forall x y G c,
  c `in` dom (rename_ctx_sw x y G) -> sw x y c `in` dom G.
Proof.
  intros x y G c Hc.
  destruct (@in_dom_binds sort c (rename_ctx_sw x y G) Hc) as [s Hs].
  unfold binds in Hs. unfold rename_ctx_sw in Hs.
  apply List.in_map_iff in Hs. destruct Hs as [[b t] [Heq Hin]].
  cbn [rename_pair_sw] in Heq.
  injection Heq as Hbc Hts. subst c.
  apply binds_In with (a := t).
  unfold binds.
  rewrite sw_invol.
  exact Hin.
Qed.

(* ================================================================== *)
(* D relation                                                          *)
(* ================================================================== *)

Definition Drel_sw (x y:atom) (D D':available_props) :=
  forall c, c `in` D -> sw x y c `in` D'.

Lemma Drel_sw_dom : forall x y G,
  Drel_sw x y (dom G) (dom (rename_ctx_sw x y G)).
Proof. intros x y G c Hc; apply dom_rename_ctx_sw_fwd; exact Hc. Qed.


(* ================================================================== *)
(* Free (term) variables under renaming                                *)
(* ================================================================== *)

Lemma fv_union_in_l : forall (S T:vars) x, x `in` S -> x `in` (S \u T).
Proof. intros; fsetdec. Qed.
Lemma fv_union_in_r : forall (S T:vars) x, x `in` T -> x `in` (S \u T).
Proof. intros; fsetdec. Qed.
Hint Resolve fv_union_in_l fv_union_in_r : fvset.

Ltac fv_decomp :=
  repeat match goal with
  | H : _ `in` (_ \u _) |- _ =>
      apply AtomSetFacts.union_iff in H; destruct H as [H|H]
  end.

Ltac fv_base :=
  try match goal with
  | H : _ `in` empty |- _ =>
      apply AtomSetFacts.empty_iff in H; contradiction
  end;
  try match goal with
  | H : _ `in` {{?st ?xx}} |- _ =>
      apply AtomSetFacts.singleton_iff in H; subst;
      exists xx; split; [fsetdec | reflexivity]
  end.

Ltac fv_use_ih :=
  match goal with
  | H : ?zz `in` ?S |- exists w, _ /\ _ =>
      match goal with
      | IH : forall st sc z, z `in` ?S -> _ |- _ =>
          let w := fresh "w" in
          let Hw := fresh "Hw" in
          let He := fresh "He" in
          destruct (IH _ _ _ H) as [w [Hw He]];
          exists w; split; [fsetdec | exact He]
      end
  end.

Lemma fv_tm_rename_subset :
  (forall a st sc z,
     z `in` fv_tm_tm_tm (rename_tm st sc a) ->
     exists w, w `in` fv_tm_tm_tm a /\ st w = z) /\
  (forall b st sc z,
     z `in` fv_tm_tm_brs (rename_brs st sc b) ->
     exists w, w `in` fv_tm_tm_brs b /\ st w = z) /\
  (forall g st sc z,
     z `in` fv_tm_tm_co (rename_co st sc g) ->
     exists w, w `in` fv_tm_tm_co g /\ st w = z) /\
  (forall p st sc z,
     z `in` fv_tm_tm_constraint (rename_constraint st sc p) ->
     exists w, w `in` fv_tm_tm_constraint p /\ st w = z).
Proof.
  apply (tm_mutind
    (fun a => forall st sc z,
       z `in` fv_tm_tm_tm (rename_tm st sc a) ->
       exists w, w `in` fv_tm_tm_tm a /\ st w = z)
    (fun b => forall st sc z,
       z `in` fv_tm_tm_brs (rename_brs st sc b) ->
       exists w, w `in` fv_tm_tm_brs b /\ st w = z)
    (fun g => forall st sc z,
       z `in` fv_tm_tm_co (rename_co st sc g) ->
       exists w, w `in` fv_tm_tm_co g /\ st w = z)
    (fun p => forall st sc z,
       z `in` fv_tm_tm_constraint (rename_constraint st sc p) ->
       exists w, w `in` fv_tm_tm_constraint p /\ st w = z)).
  all: intros.
  all: cbn [rename_tm rename_brs rename_co rename_constraint
            fv_tm_tm_tm fv_tm_tm_brs fv_tm_tm_co fv_tm_tm_constraint] in *.
  all: try fv_decomp.
  all: try fv_base.
  all: try fv_use_ih.
Qed.

Corollary fv_tm_rename_notin : forall a st sc z,
  z `notin` fv_tm_tm_tm a ->
  (forall w, st w = z -> w = z) ->
  z `notin` fv_tm_tm_tm (rename_tm st sc a).
Proof.
  intros a st sc z Hz Hinj Hcontra.
  destruct (proj1 fv_tm_rename_subset a st sc z Hcontra) as [w [Hw He]].
  apply Hinj in He. subst w. exact (Hz Hw).
Qed.

(* ================================================================== *)
(* Erasure commutes with renaming                                      *)
(* ================================================================== *)

Lemma erase_rename_all :
  (forall a st sc, erase_tm (rename_tm st sc a) = rename_tm st sc (erase_tm a)) /\
  (forall b st sc, erase_brs (rename_brs st sc b) = rename_brs st sc (erase_brs b)) /\
  (forall g:co, True) /\
  (forall p st sc,
      erase_constraint (rename_constraint st sc p) =
      rename_constraint st sc (erase_constraint p)).
Proof.
  apply (tm_mutind
    (fun a => forall st sc, erase_tm (rename_tm st sc a) = rename_tm st sc (erase_tm a))
    (fun b => forall st sc, erase_brs (rename_brs st sc b) = rename_brs st sc (erase_brs b))
    (fun g => True)
    (fun p => forall st sc,
        erase_constraint (rename_constraint st sc p) =
        rename_constraint st sc (erase_constraint p))).
  all: intros.
  all: try (cbn [rename_tm rename_brs rename_co rename_constraint
                   erase_tm erase_brs erase_constraint]; reflexivity).
  all: try (cbn [rename_tm rename_brs rename_co rename_constraint
                   erase_tm erase_brs erase_constraint]; f_equal; eauto).
  all: try (destruct rho; cbn [rename_tm rename_brs rename_co rename_constraint
                   erase_tm erase_brs erase_constraint]; f_equal; eauto).
Qed.

Lemma erase_rename_tm : forall a st sc,
  erase_tm (rename_tm st sc a) = rename_tm st sc (erase_tm a).
Proof. intros; exact (proj1 erase_rename_all a st sc). Qed.
Lemma erase_rename_constraint : forall p st sc,
  erase_constraint (rename_constraint st sc p) =
  rename_constraint st sc (erase_constraint p).
Proof. intros; exact (proj2 (proj2 (proj2 erase_rename_all)) p st sc). Qed.

(* ================================================================== *)
(* RhoCheck is stable under swaps fixing the checked variable          *)
(* ================================================================== *)

Lemma RhoCheck_rename_sw : forall x y rho z a,
  z <> x -> z <> y ->
  RhoCheck rho z a ->
  RhoCheck rho z (rename_tm (sw x y) (sw x y) a).
Proof.
  intros x y rho z a Hzx Hzy H. inversion H; subst.
  - apply (Rho_Rel z (rename_tm (sw x y) (sw x y) a) I).
  - apply Rho_IrrRel.
    match goal with
    | Hn : _ `notin` _ |- _ =>
        eapply fv_tm_rename_notin; [ exact Hn | intros w Hw; apply (sw_inj x y w z); rewrite Hw; symmetry; apply sw_fix; assumption ]
    end.
Qed.

Lemma rename_tm_FixDef : forall st sc, rename_tm st sc FixDef = FixDef.
Proof. intros; vm_compute; reflexivity. Qed.
Lemma rename_tm_FixTy : forall st sc, rename_tm st sc FixTy = FixTy.
Proof. intros; vm_compute; reflexivity. Qed.

(* ================================================================== *)
(* Helpers for context extension under a swap                          *)
(* ================================================================== *)

Lemma rename_ctx_sw_cons_tm : forall x y z A G,
  z <> x -> z <> y ->
  rename_ctx_sw x y ((z ~ Tm A) ++ G) =
  (z ~ Tm (rename_tm (sw x y) (sw x y) A)) ++ rename_ctx_sw x y G.
Proof.
  intros. unfold rename_ctx_sw. rewrite List.map_app.
  simpl. unfold rename_pair_sw, rename_sort_sw. simpl.
  rewrite sw_fix; auto.
Qed.

Lemma rename_ctx_sw_cons_tm_any : forall x y z A G,
  rename_ctx_sw x y ((z ~ Tm A) ++ G) =
  (sw x y z ~ Tm (rename_tm (sw x y) (sw x y) A)) ++ rename_ctx_sw x y G.
Proof.
  intros. unfold rename_ctx_sw. rewrite List.map_app.
  simpl. unfold rename_pair_sw, rename_sort_sw. simpl. reflexivity.
Qed.

Lemma rename_ctx_sw_cons_co_any : forall x y c phi G,
  rename_ctx_sw x y ((c ~ Co phi) ++ G) =
  (sw x y c ~ Co (rename_constraint (sw x y) (sw x y) phi)) ++ rename_ctx_sw x y G.
Proof.
  intros. unfold rename_ctx_sw. rewrite List.map_app.
  simpl. unfold rename_pair_sw, rename_sort_sw. simpl. reflexivity.
Qed.

Lemma rename_ctx_sw_cons_co : forall x y c phi G,
  c <> x -> c <> y ->
  rename_ctx_sw x y ((c ~ Co phi) ++ G) =
  (c ~ Co (rename_constraint (sw x y) (sw x y) phi)) ++ rename_ctx_sw x y G.
Proof.
  intros. unfold rename_ctx_sw. rewrite List.map_app.
  simpl. unfold rename_pair_sw, rename_sort_sw. simpl.
  rewrite sw_fix; auto.
Qed.

Lemma rename_open_tm_sw_any : forall x y b u,
  rename_tm (sw x y) (sw x y) (open_tm_wrt_tm b u) =
  open_tm_wrt_tm (rename_tm (sw x y) (sw x y) b)
                 (rename_tm (sw x y) (sw x y) u).
Proof.
  intros. unfold open_tm_wrt_tm.
  apply (rename_open_tm_tm b (sw x y) (sw x y) 0 u).
Qed.

Lemma rename_open_tm_sw_fix : forall x y z b,
  z <> x -> z <> y ->
  rename_tm (sw x y) (sw x y) (open_tm_wrt_tm b (a_Var_f z)) =
  open_tm_wrt_tm (rename_tm (sw x y) (sw x y) b) (a_Var_f z).
Proof.
  intros. rewrite rename_open_tm_sw_any.
  cbn [rename_tm]. rewrite sw_fix; auto.
Qed.

Lemma rename_open_co_tm_sw_any : forall x y b g,
  rename_tm (sw x y) (sw x y) (open_tm_wrt_co b g) =
  open_tm_wrt_co (rename_tm (sw x y) (sw x y) b)
                 (rename_co (sw x y) (sw x y) g).
Proof.
  intros. unfold open_tm_wrt_co.
  apply (rename_open_co_tm b (sw x y) (sw x y) 0 g).
Qed.

Lemma rename_open_co_tm_sw_fix : forall x y c b,
  c <> x -> c <> y ->
  rename_tm (sw x y) (sw x y) (open_tm_wrt_co b (g_Var_f c)) =
  open_tm_wrt_co (rename_tm (sw x y) (sw x y) b) (g_Var_f c).
Proof.
  intros. rewrite rename_open_co_tm_sw_any.
  cbn [rename_co]. rewrite sw_fix; auto.
Qed.

Lemma rename_open_co_wrt_tm_sw_any : forall x y u g,
  rename_co (sw x y) (sw x y) (open_co_wrt_tm g u) =
  open_co_wrt_tm (rename_co (sw x y) (sw x y) g)
                 (rename_tm (sw x y) (sw x y) u).
Proof.
  intros. unfold open_co_wrt_tm.
  apply (rename_open_tm_co g (sw x y) (sw x y) 0 u).
Qed.

Lemma rename_open_co_wrt_tm_sw_fix : forall x y z g,
  z <> x -> z <> y ->
  rename_co (sw x y) (sw x y) (open_co_wrt_tm g (a_Var_f z)) =
  open_co_wrt_tm (rename_co (sw x y) (sw x y) g) (a_Var_f z).
Proof.
  intros. rewrite rename_open_co_wrt_tm_sw_any.
  cbn [rename_tm]. rewrite sw_fix; auto.
Qed.

Lemma rename_open_co_co_sw_any : forall x y h g,
  rename_co (sw x y) (sw x y) (open_co_wrt_co h g) =
  open_co_wrt_co (rename_co (sw x y) (sw x y) h)
                 (rename_co (sw x y) (sw x y) g).
Proof.
  intros. unfold open_co_wrt_co.
  apply (rename_open_co_co h (sw x y) (sw x y) 0 g).
Qed.

Lemma rename_open_co_co_sw_fix : forall x y c h,
  c <> x -> c <> y ->
  rename_co (sw x y) (sw x y) (open_co_wrt_co h (g_Var_f c)) =
  open_co_wrt_co (rename_co (sw x y) (sw x y) h) (g_Var_f c).
Proof.
  intros. rewrite rename_open_co_co_sw_any.
  cbn [rename_co]. rewrite sw_fix; auto.
Qed.

Lemma erase_open_tm_rename_sw : forall x y z b,
  z <> x -> z <> y ->
  erase_tm (open_tm_wrt_tm (rename_tm (sw x y) (sw x y) b) (a_Var_f z))
  = rename_tm (sw x y) (sw x y) (erase_tm (open_tm_wrt_tm b (a_Var_f z))).
Proof.
  intros. rewrite <- rename_open_tm_sw_fix; auto.
  rewrite erase_rename_tm. reflexivity.
Qed.

Lemma erase_open_co_rename_sw : forall x y c b,
  c <> x -> c <> y ->
  erase_tm (open_tm_wrt_co (rename_tm (sw x y) (sw x y) b) (g_Var_f c))
  = rename_tm (sw x y) (sw x y) (erase_tm (open_tm_wrt_co b (g_Var_f c))).
Proof.
  intros. rewrite <- rename_open_co_tm_sw_fix; auto.
  rewrite erase_rename_tm. reflexivity.
Qed.
(* ==== AnnEqv ==== *)

(* ================================================================== *)
(* Predicates for mutual renaming equivariance of the Ann block        *)
(* ================================================================== *)

Definition AnnP_sw (p q:atom) (G:context) (phi:constraint)
    (_ : AnnPropWff G phi) : Prop :=
  AnnPropWff (rename_ctx_sw p q G) (rename_constraint (sw p q) (sw p q) phi).

Definition AnnT_sw (p q:atom) (G:context) (a A:tm)
    (_ : AnnTyping G a A) : Prop :=
  AnnTyping (rename_ctx_sw p q G)
            (rename_tm (sw p q) (sw p q) a)
            (rename_tm (sw p q) (sw p q) A).

Definition AnnI_sw (p q:atom) (G:context) (D:available_props)
    (g:co) (phi1 phi2:constraint) (_ : AnnIso G D g phi1 phi2) : Prop :=
  forall D', Drel_sw p q D D' ->
    AnnIso (rename_ctx_sw p q G) D'
           (rename_co (sw p q) (sw p q) g)
           (rename_constraint (sw p q) (sw p q) phi1)
           (rename_constraint (sw p q) (sw p q) phi2).

Definition AnnD_sw (p q:atom) (G:context) (D:available_props)
    (g:co) (a b:tm) (_ : AnnDefEq G D g a b) : Prop :=
  forall D', Drel_sw p q D D' ->
    AnnDefEq (rename_ctx_sw p q G) D'
             (rename_co (sw p q) (sw p q) g)
             (rename_tm (sw p q) (sw p q) a)
             (rename_tm (sw p q) (sw p q) b).

Definition AnnC_sw (p q:atom) (G:context) (_ : AnnCtx G) : Prop :=
  AnnCtx (rename_ctx_sw p q G).

Definition AnnS_sw (p q:atom) (S:sig) (_ : AnnSig S) : Prop := True.

Scheme AnnPropWff_mut := Induction for AnnPropWff Sort Prop
with AnnTyping_mut := Induction for AnnTyping Sort Prop
with AnnIso_mut := Induction for AnnIso Sort Prop
with AnnDefEq_mut := Induction for AnnDefEq Sort Prop
with AnnCtx_mut := Induction for AnnCtx Sort Prop
with AnnSig_mut := Induction for AnnSig Sort Prop.

Section AnnEqv.
Variables p q : atom.

Lemma Beta_rename_sw : forall a b,
  Beta a b -> Beta (rename_tm (sw p q) (sw p q) a)
                 (rename_tm (sw p q) (sw p q) b).
Proof.
  intros a b H. destruct H.
  - cbn [rename_tm]. rewrite rename_open_tm_sw_any.
    apply (Beta_AppAbs rho (rename_tm (sw p q) (sw p q) v)
                      (rename_tm (sw p q) (sw p q) b)).
    + apply (lc_tm_rename_sw p q). exact H.
    + apply (Value_rename_sw p q) in H0. cbn [rename_tm] in H0. exact H0.
  - cbn [rename_tm]. rewrite rename_open_co_tm_sw_any. cbn [rename_co].
    apply (Beta_CAppCAbs (rename_tm (sw p q) (sw p q) a')).
    change (lc_tm (rename_tm (sw p q) (sw p q) (a_UCAbs a'))).
    apply (lc_tm_rename_sw p q). exact H.
  - destruct (toplevel_binds_eq F a A H) as [-> [-> ->]].
    cbn [rename_tm]. rewrite rename_tm_erase_FixDef.
    apply (Beta_Axiom Fix (erase_tm FixDef) (erase_tm FixTy)). exact H.
Qed.

(* ================================================================== *)
(* Cases of the mutual induction.  They are shared by the AnnTyping   *)
(* and AnnDefEq instantiations of the scheme.                          *)
(* ================================================================== *)

Ltac ann_fresh Hz Lset :=
  let z := match type of Hz with ?zz `notin` _ => constr:(zz) end in
  assert (HzL : z `notin` Lset) by fsetdec;
  assert (Hzp : z <> p) by (intro E; subst z; fsetdec);
  assert (Hzq : z <> q) by (intro E; subst z; fsetdec).

Ltac ann_case_An_Wff :=
  idtac "CASE An_Wff";
  intros G a b A B H1 IH1 H2 IH2 He;
  unfold AnnP_sw; cbn [rename_constraint];
  apply (An_Wff (rename_ctx_sw p q G)
                (rename_tm (sw p q) (sw p q) a)
                (rename_tm (sw p q) (sw p q) b)
                (rename_tm (sw p q) (sw p q) A)
                (rename_tm (sw p q) (sw p q) B));
  [ unfold AnnT_sw in IH1; apply IH1
  | unfold AnnT_sw in IH2; apply IH2
  | rewrite !erase_rename_tm; rewrite He; reflexivity ].

Ltac ann_case_An_Star :=
  idtac "CASE An_Star";
  intros G Hctx IHC; unfold AnnT_sw;
  apply An_Star; unfold AnnC_sw in IHC; apply IHC.

Ltac ann_case_An_Var :=
  idtac "CASE An_Var";
  intros G x A Hctx IHC Hb; unfold AnnT_sw;
  apply (An_Var (rename_ctx_sw p q G) (sw p q x)
                (rename_tm (sw p q) (sw p q) A));
  [ unfold AnnC_sw in IHC; apply IHC
  | exact (binds_rename_ctx_sw p q x (Tm A) G Hb) ].

Ltac ann_case_An_Pi :=
  idtac "CASE An_Pi";
  intros L G rho A B a IHa a0 IHA0; unfold AnnT_sw;
  eapply (An_Pi (L \u {{p}} \u {{q}}));
  [ intros z Hz; assert (HzL : z `notin` L) by fsetdec;
    assert (Hzp : z <> p) by (intro E; subst z; fsetdec);
    assert (Hzq : z <> q) by (intro E; subst z; fsetdec);
    specialize (IHa z HzL); unfold AnnT_sw in IHa;
    rewrite (rename_ctx_sw_cons_tm p q z A G Hzp Hzq) in IHa;
    rewrite (rename_open_tm_sw_fix p q z B Hzp Hzq) in IHa;
    exact IHa
  | unfold AnnT_sw in IHA0; apply IHA0 ].

Ltac ann_case_An_Abs :=
  idtac "CASE An_Abs";
  intros L G rho A a B Hty IHAty a1 IHa r0; unfold AnnT_sw;
  eapply (An_Abs (L \u {{p}} \u {{q}}));
  [ unfold AnnT_sw in IHAty; exact IHAty
  | intros z Hz; assert (HzL : z `notin` L) by fsetdec;
    assert (Hzp : z <> p) by (intro E; subst z; fsetdec);
    assert (Hzq : z <> q) by (intro E; subst z; fsetdec);
    specialize (IHa z HzL); unfold AnnT_sw in IHa;
    rewrite (rename_ctx_sw_cons_tm p q z A G Hzp Hzq) in IHa;
    rewrite (rename_open_tm_sw_fix p q z a Hzp Hzq) in IHa;
    rewrite (rename_open_tm_sw_fix p q z B Hzp Hzq) in IHa;
    exact IHa
  | intros z Hz; assert (HzL : z `notin` L) by fsetdec;
    assert (Hzp : z <> p) by (intro E; subst z; fsetdec);
    assert (Hzq : z <> q) by (intro E; subst z; fsetdec);
    specialize (r0 z HzL);
    change (RhoCheck rho z
      (erase_tm (open_tm_wrt_tm (rename_tm (sw p q) (sw p q) a)
                               (a_Var_f z))));
    rewrite (erase_open_tm_rename_sw p q z a Hzp Hzq);
    apply (RhoCheck_rename_sw p q rho z
             (erase_tm (open_tm_wrt_tm a (a_Var_f z))) Hzp Hzq);
    exact r0 ].

Ltac ann_case_An_App :=
  idtac "CASE An_App";
  intros G b rho a B A Hb IHb Ha IHa; unfold AnnT_sw;
  rewrite rename_open_tm_sw_any;
  eapply (An_App (rename_ctx_sw p q G)
                 (rename_tm (sw p q) (sw p q) b) rho
                 (rename_tm (sw p q) (sw p q) a)
                 (rename_tm (sw p q) (sw p q) B)
                 (rename_tm (sw p q) (sw p q) A));
  [ unfold AnnT_sw in IHb; apply IHb
  | unfold AnnT_sw in IHa; apply IHa ].

Ltac ann_case_An_Conv :=
  idtac "CASE An_Conv";
  intros G a g B A Ha IHa Hd IHd HB IHB; unfold AnnT_sw;
  eapply (An_Conv (rename_ctx_sw p q G)
                  (rename_tm (sw p q) (sw p q) a)
                  (rename_co (sw p q) (sw p q) g)
                  (rename_tm (sw p q) (sw p q) B)
                  (rename_tm (sw p q) (sw p q) A));
  [ unfold AnnT_sw in IHa; apply IHa
  | unfold AnnD_sw in IHd; apply IHd; apply Drel_sw_dom
  | unfold AnnT_sw in IHB; apply IHB ].

Ltac ann_case_An_CPi :=
  idtac "CASE An_CPi";
  intros L G phi B Hp IHP a IHa; unfold AnnT_sw;
  eapply (An_CPi (L \u {{p}} \u {{q}}));
  [ unfold AnnP_sw in IHP; apply IHP
  | intros c Hc; assert (HcL : c `notin` L) by fsetdec;
    assert (Hcp : c <> p) by (intro E; subst c; fsetdec);
    assert (Hcq : c <> q) by (intro E; subst c; fsetdec);
    specialize (IHa c HcL); unfold AnnT_sw in IHa;
    rewrite (rename_ctx_sw_cons_co p q c phi G Hcp Hcq) in IHa;
    rewrite (rename_open_co_tm_sw_fix p q c B Hcp Hcq) in IHa;
    exact IHa ].

Ltac ann_case_An_CAbs :=
  idtac "CASE An_CAbs";
  intros L G phi a B Hp IHP a1 IHa; unfold AnnT_sw;
  eapply (An_CAbs (L \u {{p}} \u {{q}}));
  [ unfold AnnP_sw in IHP; apply IHP
  | intros c Hc; assert (HcL : c `notin` L) by fsetdec;
    assert (Hcp : c <> p) by (intro E; subst c; fsetdec);
    assert (Hcq : c <> q) by (intro E; subst c; fsetdec);
    specialize (IHa c HcL); unfold AnnT_sw in IHa;
    rewrite (rename_ctx_sw_cons_co p q c phi G Hcp Hcq) in IHa;
    rewrite (rename_open_co_tm_sw_fix p q c a Hcp Hcq) in IHa;
    rewrite (rename_open_co_tm_sw_fix p q c B Hcp Hcq) in IHa;
    exact IHa ].

Ltac ann_case_An_CApp :=
  idtac "CASE An_CApp";
  intros G a1 g B a b A1 H1 IH1 H2 IH2; unfold AnnT_sw;
  rewrite rename_open_co_tm_sw_any;
  eapply (An_CApp (rename_ctx_sw p q G)
                  (rename_tm (sw p q) (sw p q) a1)
                  (rename_co (sw p q) (sw p q) g)
                  (rename_tm (sw p q) (sw p q) B)
                  (rename_tm (sw p q) (sw p q) a)
                  (rename_tm (sw p q) (sw p q) b)
                  (rename_tm (sw p q) (sw p q) A1));
  [ unfold AnnT_sw in IH1; apply IH1
  | unfold AnnD_sw in IH2; apply IH2; apply Drel_sw_dom ].

Lemma an_toplevel_binds_eq : forall (F:tyfam) (a A:tm),
  binds F (Ax a A) an_toplevel ->
  F = Fix /\ a = FixDef /\ A = FixTy.
Proof.
  intros F a A H. unfold an_toplevel in H. simpl in H.
  destruct H as [Heq | Hnil].
  - inversion Heq. subst. repeat split; reflexivity.
  - contradiction.
Qed.

Ltac ann_case_An_Fam :=
  idtac "CASE An_Fam";
  intros G F A a0 Hctx IHC Hb HA IHA; unfold AnnT_sw;
  destruct (an_toplevel_binds_eq F a0 A Hb) as [-> [-> ->]];
  cbn [rename_tm]; rewrite rename_tm_FixTy;
  apply (An_Fam (rename_ctx_sw p q G) Fix FixTy FixDef);
  [ unfold AnnC_sw in IHC; apply IHC
  | exact Hb
  | unfold AnnT_sw in IHA; rewrite rename_ctx_sw_nil in IHA;
    rewrite rename_tm_FixTy in IHA; cbn [rename_tm] in IHA; exact IHA ].

Ltac ann_case_An_PropCong :=
  idtac "CASE An_PropCong";
  intros G D g1 A0 g2 A1 B1 A2 B2 H1 IH1 H2 IH2 HP1 IHP1 HP2 IHP2;
  unfold AnnI_sw; intros D' HD'; cbn [rename_co rename_constraint];
  eapply (An_PropCong (rename_ctx_sw p q G) D'
                      (rename_co (sw p q) (sw p q) g1)
                      (rename_tm (sw p q) (sw p q) A0)
                      (rename_co (sw p q) (sw p q) g2)
                      (rename_tm (sw p q) (sw p q) A1)
                      (rename_tm (sw p q) (sw p q) B1)
                      (rename_tm (sw p q) (sw p q) A2)
                      (rename_tm (sw p q) (sw p q) B2));
  [ unfold AnnD_sw in IH1; apply IH1; exact HD'
  | unfold AnnD_sw in IH2; apply IH2; exact HD'
  | unfold AnnP_sw in IHP1; apply IHP1
  | unfold AnnP_sw in IHP2; apply IHP2 ].

Ltac ann_case_An_CPiFst :=
  idtac "CASE An_CPiFst";
  intros G D g phi1 phi2 A2 B2 H IH;
  unfold AnnI_sw; intros D' HD'; cbn [rename_co rename_tm rename_constraint];
  eapply (An_CPiFst (rename_ctx_sw p q G) D'
                    (rename_co (sw p q) (sw p q) g)
                    (rename_constraint (sw p q) (sw p q) phi1)
                    (rename_constraint (sw p q) (sw p q) phi2)
                    (rename_tm (sw p q) (sw p q) A2)
                    (rename_tm (sw p q) (sw p q) B2));
  unfold AnnD_sw in IH; apply IH; exact HD'.

Ltac ann_case_An_IsoSym :=
  idtac "CASE An_IsoSym";
  intros G D g phi2 phi1 H IH;
  unfold AnnI_sw; intros D' HD'; cbn [rename_co];
  eapply (An_IsoSym (rename_ctx_sw p q G) D'
                    (rename_co (sw p q) (sw p q) g)
                    (rename_constraint (sw p q) (sw p q) phi2)
                    (rename_constraint (sw p q) (sw p q) phi1));
  unfold AnnI_sw in IH; apply IH; exact HD'.

Ltac ann_case_An_IsoConv :=
  idtac "CASE An_IsoConv";
  intros G D a1 a2 A a1' a2' B g H IH Ha IHa Hb IHb He1 He2;
  unfold AnnI_sw; intros D' HD'; cbn [rename_co rename_constraint];
  eapply (An_IsoConv (rename_ctx_sw p q G) D'
                     (rename_tm (sw p q) (sw p q) a1)
                     (rename_tm (sw p q) (sw p q) a2)
                     (rename_tm (sw p q) (sw p q) A)
                     (rename_tm (sw p q) (sw p q) a1')
                     (rename_tm (sw p q) (sw p q) a2')
                     (rename_tm (sw p q) (sw p q) B)
                     (rename_co (sw p q) (sw p q) g));
  [ unfold AnnD_sw in IH; apply IH; exact HD'
  | unfold AnnP_sw in IHa; apply IHa
  | unfold AnnP_sw in IHb; apply IHb
  | rewrite !erase_rename_tm; rewrite He1; reflexivity
  | rewrite !erase_rename_tm; rewrite He2; reflexivity ].

Ltac ann_case_An_Assn :=
  idtac "CASE An_Assn";
  intros G D c a b A Hctx IHC Hb Hin;
  unfold AnnD_sw; intros D' HD'; cbn [rename_co rename_sort_sw rename_constraint];
  eapply (An_Assn (rename_ctx_sw p q G) D' (sw p q c)
                  (rename_tm (sw p q) (sw p q) a)
                  (rename_tm (sw p q) (sw p q) b)
                  (rename_tm (sw p q) (sw p q) A));
  [ unfold AnnC_sw in IHC; apply IHC
  | exact (binds_rename_ctx_sw p q c (Co (Eq a b A)) G Hb)
  | apply HD'; exact Hin ].

Ltac ann_case_An_Refl :=
  idtac "CASE An_Refl";
  intros G D a A H IH; unfold AnnD_sw; intros D' HD'; cbn [rename_co];
  apply (An_Refl (rename_ctx_sw p q G) D'
                 (rename_tm (sw p q) (sw p q) a)
                 (rename_tm (sw p q) (sw p q) A));
  unfold AnnT_sw in IH; apply IH.

Ltac ann_case_An_EraseEq :=
  idtac "CASE An_EraseEq";
  intros G D a b g A B Ha IHa Hb IHb He Hd IHd;
  unfold AnnD_sw; intros D' HD'; cbn [rename_co];
  eapply (An_EraseEq (rename_ctx_sw p q G) D'
                    (rename_tm (sw p q) (sw p q) a)
                    (rename_tm (sw p q) (sw p q) b)
                    (rename_co (sw p q) (sw p q) g)
                    (rename_tm (sw p q) (sw p q) A)
                    (rename_tm (sw p q) (sw p q) B));
  [ unfold AnnT_sw in IHa; apply IHa
  | unfold AnnT_sw in IHb; apply IHb
  | rewrite !erase_rename_tm; rewrite He; reflexivity
  | unfold AnnD_sw in IHd; apply IHd; apply Drel_sw_dom ].

Ltac ann_case_An_Sym :=
  idtac "CASE An_Sym";
  intros G D g a b B A g1 Hb IHb Ha IHa Hd IHd Hrec IHrec;
  unfold AnnD_sw; intros D' HD'; cbn [rename_co];
  eapply (An_Sym (rename_ctx_sw p q G) D'
                 (rename_co (sw p q) (sw p q) g)
                 (rename_tm (sw p q) (sw p q) a)
                 (rename_tm (sw p q) (sw p q) b)
                 (rename_tm (sw p q) (sw p q) B)
                 (rename_tm (sw p q) (sw p q) A)
                 (rename_co (sw p q) (sw p q) g1));
  [ unfold AnnT_sw in IHb; apply IHb
  | unfold AnnT_sw in IHa; apply IHa
  | unfold AnnD_sw in IHd; apply IHd; apply Drel_sw_dom
  | unfold AnnD_sw in IHrec; apply IHrec; exact HD' ].

Ltac ann_case_An_Trans :=
  idtac "CASE An_Trans";
  intros G D g1 g2 a b a1 A A1 g3 H1 IH1 H2 IH2 Ha IHa Ha1 IHa1 Hd IHd;
  unfold AnnD_sw; intros D' HD'; cbn [rename_co];
  eapply (An_Trans (rename_ctx_sw p q G) D'
                   (rename_co (sw p q) (sw p q) g1)
                   (rename_co (sw p q) (sw p q) g2)
                   (rename_tm (sw p q) (sw p q) a)
                   (rename_tm (sw p q) (sw p q) b)
                   (rename_tm (sw p q) (sw p q) a1)
                   (rename_tm (sw p q) (sw p q) A)
                   (rename_tm (sw p q) (sw p q) A1)
                   (rename_co (sw p q) (sw p q) g3));
  [ unfold AnnD_sw in IH1; apply IH1; exact HD'
  | unfold AnnD_sw in IH2; apply IH2; exact HD'
  | unfold AnnT_sw in IHa; apply IHa
  | unfold AnnT_sw in IHa1; apply IHa1
  | unfold AnnD_sw in IHd; apply IHd; apply Drel_sw_dom ].

Ltac ann_case_An_Beta :=
  idtac "CASE An_Beta";
  intros G D a1 a2 B0 B1 H1 IH1 H2 IH2 He HB;
  unfold AnnD_sw; intros D' HD'; cbn [rename_co rename_tm];
  eapply (An_Beta (rename_ctx_sw p q G) D'
                  (rename_tm (sw p q) (sw p q) a1)
                  (rename_tm (sw p q) (sw p q) a2)
                  (rename_tm (sw p q) (sw p q) B0)
                  (rename_tm (sw p q) (sw p q) B1));
  [ unfold AnnT_sw in IH1; apply IH1
  | unfold AnnT_sw in IH2; apply IH2
  | rewrite !erase_rename_tm; rewrite He; reflexivity
  | rewrite !erase_rename_tm; apply Beta_rename_sw; exact HB ].

Ltac ann_case_An_PiCong :=
  idtac "CASE An_PiCong";
  intros L G D rho g1 g2 A1 B1 A2 B3 B2 H1 IH1 Hcof IHcof Heq
         Ht1 IHt1 Ht2 IHt2 Ht3 IHt3;
  unfold AnnD_sw; intros D' HD'; cbn [rename_co rename_tm];
  eapply (An_PiCong (L \u {{p}} \u {{q}}) (rename_ctx_sw p q G) D' rho
                    (rename_co (sw p q) (sw p q) g1)
                    (rename_co (sw p q) (sw p q) g2)
                    (rename_tm (sw p q) (sw p q) A1)
                    (rename_tm (sw p q) (sw p q) B1)
                    (rename_tm (sw p q) (sw p q) A2)
                    (rename_tm (sw p q) (sw p q) B3)
                    (rename_tm (sw p q) (sw p q) B2));
  [ unfold AnnD_sw in IH1; apply IH1; exact HD'
  | intros z Hz; assert (HzL : z `notin` L) by fsetdec;
    assert (Hzp : z <> p) by (intro E; subst z; fsetdec);
    assert (Hzq : z <> q) by (intro E; subst z; fsetdec);
    specialize (IHcof z HzL); unfold AnnD_sw in IHcof;
    rewrite (rename_ctx_sw_cons_tm p q z A1 G Hzp Hzq) in IHcof;
    rewrite (rename_open_co_wrt_tm_sw_fix p q z g2 Hzp Hzq) in IHcof;
    rewrite (rename_open_tm_sw_fix p q z B1 Hzp Hzq) in IHcof;
    rewrite (rename_open_tm_sw_fix p q z B2 Hzp Hzq) in IHcof;
    apply IHcof; exact HD'
  | intros z Hz; assert (HzL : z `notin` L) by fsetdec;
    assert (Hzp : z <> p) by (intro E; subst z; fsetdec);
    assert (Hzq : z <> q) by (intro E; subst z; fsetdec);
    specialize (Heq z HzL);
    apply (f_equal (rename_tm (sw p q) (sw p q))) in Heq;
    rewrite (rename_open_tm_sw_fix p q z B3 Hzp Hzq) in Heq;
    rewrite rename_open_tm_sw_any in Heq;
    cbn [rename_tm rename_co] in Heq;
    rewrite (sw_fix p q z Hzp Hzq) in Heq;
    exact Heq
  | unfold AnnT_sw in IHt1; apply IHt1
  | unfold AnnT_sw in IHt2; apply IHt2
  | unfold AnnT_sw in IHt3; apply IHt3 ].

Ltac ann_case_An_AbsCong :=
  idtac "CASE An_AbsCong";
  intros L G D rho g1 g2 A1 b1 A2 b3 b2 B H1 IH1 Hcof IHcof Heq
         Ht1 IHt1 Ht2 IHt2 R1 R3 HB IHB;
  unfold AnnD_sw; intros D' HD'; cbn [rename_co rename_tm];
  eapply (An_AbsCong (L \u {{p}} \u {{q}}) (rename_ctx_sw p q G) D' rho
                     (rename_co (sw p q) (sw p q) g1)
                     (rename_co (sw p q) (sw p q) g2)
                     (rename_tm (sw p q) (sw p q) A1)
                     (rename_tm (sw p q) (sw p q) b1)
                     (rename_tm (sw p q) (sw p q) A2)
                     (rename_tm (sw p q) (sw p q) b3)
                     (rename_tm (sw p q) (sw p q) b2)
                     (rename_tm (sw p q) (sw p q) B));
  [ unfold AnnD_sw in IH1; apply IH1; exact HD'
  | intros z Hz; assert (HzL : z `notin` L) by fsetdec;
    assert (Hzp : z <> p) by (intro E; subst z; fsetdec);
    assert (Hzq : z <> q) by (intro E; subst z; fsetdec);
    specialize (IHcof z HzL); unfold AnnD_sw in IHcof;
    rewrite (rename_ctx_sw_cons_tm p q z A1 G Hzp Hzq) in IHcof;
    rewrite (rename_open_co_wrt_tm_sw_fix p q z g2 Hzp Hzq) in IHcof;
    rewrite (rename_open_tm_sw_fix p q z b1 Hzp Hzq) in IHcof;
    rewrite (rename_open_tm_sw_fix p q z b2 Hzp Hzq) in IHcof;
    apply IHcof; exact HD'
  | intros z Hz; assert (HzL : z `notin` L) by fsetdec;
    assert (Hzp : z <> p) by (intro E; subst z; fsetdec);
    assert (Hzq : z <> q) by (intro E; subst z; fsetdec);
    specialize (Heq z HzL);
    apply (f_equal (rename_tm (sw p q) (sw p q))) in Heq;
    rewrite (rename_open_tm_sw_fix p q z b3 Hzp Hzq) in Heq;
    rewrite rename_open_tm_sw_any in Heq;
    cbn [rename_tm rename_co] in Heq;
    rewrite (sw_fix p q z Hzp Hzq) in Heq;
    exact Heq
  | unfold AnnT_sw in IHt1; apply IHt1
  | unfold AnnT_sw in IHt2; apply IHt2
  | intros z Hz; assert (HzL : z `notin` L) by fsetdec;
    assert (Hzp : z <> p) by (intro E; subst z; fsetdec);
    assert (Hzq : z <> q) by (intro E; subst z; fsetdec);
    specialize (R1 z HzL);
    rewrite (erase_open_tm_rename_sw p q z b1 Hzp Hzq);
    apply (RhoCheck_rename_sw p q rho z
             (erase_tm (open_tm_wrt_tm b1 (a_Var_f z))) Hzp Hzq);
    exact R1
  | intros z Hz; assert (HzL : z `notin` L) by fsetdec;
    assert (Hzp : z <> p) by (intro E; subst z; fsetdec);
    assert (Hzq : z <> q) by (intro E; subst z; fsetdec);
    specialize (R3 z HzL);
    rewrite (erase_open_tm_rename_sw p q z b3 Hzp Hzq);
    apply (RhoCheck_rename_sw p q rho z
             (erase_tm (open_tm_wrt_tm b3 (a_Var_f z))) Hzp Hzq);
    exact R3
  | unfold AnnT_sw in IHB; apply IHB ].

Ltac ann_case_An_AppCong :=
  idtac "CASE An_AppCong";
  intros G D g1 rho g2 a1 a2 b1 b2 A B g3
         H1 IH1 H2 IH2 Ht1 IHt1 Ht2 IHt2 Hd IHd;
  unfold AnnD_sw; intros D' HD'; cbn [rename_co];
  eapply (An_AppCong (rename_ctx_sw p q G) D'
                     (rename_co (sw p q) (sw p q) g1) rho
                     (rename_co (sw p q) (sw p q) g2)
                     (rename_tm (sw p q) (sw p q) a1)
                     (rename_tm (sw p q) (sw p q) a2)
                     (rename_tm (sw p q) (sw p q) b1)
                     (rename_tm (sw p q) (sw p q) b2)
                     (rename_tm (sw p q) (sw p q) A)
                     (rename_tm (sw p q) (sw p q) B)
                     (rename_co (sw p q) (sw p q) g3));
  [ unfold AnnD_sw in IH1; apply IH1; exact HD'
  | unfold AnnD_sw in IH2; apply IH2; exact HD'
  | unfold AnnT_sw in IHt1; apply IHt1
  | unfold AnnT_sw in IHt2; apply IHt2
  | unfold AnnD_sw in IHd; apply IHd; apply Drel_sw_dom ].

Ltac ann_case_An_PiFst :=
  idtac "CASE An_PiFst";
  intros G D g A1 A2 rho B1 B2 H IH; unfold AnnD_sw; intros D' HD';
  cbn [rename_co rename_tm];
  eapply (An_PiFst (rename_ctx_sw p q G) D'
                   (rename_co (sw p q) (sw p q) g)
                   (rename_tm (sw p q) (sw p q) A1)
                   (rename_tm (sw p q) (sw p q) A2) rho
                   (rename_tm (sw p q) (sw p q) B1)
                   (rename_tm (sw p q) (sw p q) B2));
  unfold AnnD_sw in IH; apply IH; exact HD'.

Ltac ann_case_An_PiSnd :=
  idtac "CASE An_PiSnd";
  intros G D g1 g2 B1 a1 B2 a2 rho A1 A2 H1 IH1 H2 IH2
         Ha1 IHa1 Ha2 IHa2;
  unfold AnnD_sw; intros D' HD'; cbn [rename_co];
  rewrite !rename_open_tm_sw_any;
  eapply (An_PiSnd (rename_ctx_sw p q G) D'
                   (rename_co (sw p q) (sw p q) g1)
                   (rename_co (sw p q) (sw p q) g2)
                   (rename_tm (sw p q) (sw p q) B1)
                   (rename_tm (sw p q) (sw p q) a1)
                   (rename_tm (sw p q) (sw p q) B2)
                   (rename_tm (sw p q) (sw p q) a2) rho
                   (rename_tm (sw p q) (sw p q) A1)
                   (rename_tm (sw p q) (sw p q) A2));
  [ unfold AnnD_sw in IH1; apply IH1; exact HD'
  | unfold AnnD_sw in IH2; apply IH2; exact HD'
  | unfold AnnT_sw in IHa1; apply IHa1
  | unfold AnnT_sw in IHa2; apply IHa2 ].

Ltac ann_case_An_CPiCong :=
  idtac "CASE An_CPiCong";
  intros L G D g1 g3 phi1 B1 phi2 B3 B2 H1 IH1 Hcof IHcof Heq
         Ht1 IHt1 Ht2 IHt2 Ht3 IHt3;
  unfold AnnD_sw; intros D' HD'; cbn [rename_co rename_tm];
  eapply (An_CPiCong (L \u {{p}} \u {{q}}) (rename_ctx_sw p q G) D'
                     (rename_co (sw p q) (sw p q) g1)
                     (rename_co (sw p q) (sw p q) g3)
                     (rename_constraint (sw p q) (sw p q) phi1)
                     (rename_tm (sw p q) (sw p q) B1)
                     (rename_constraint (sw p q) (sw p q) phi2)
                     (rename_tm (sw p q) (sw p q) B3)
                     (rename_tm (sw p q) (sw p q) B2));
  [ unfold AnnI_sw in IH1; apply IH1; exact HD'
  | intros c Hc; assert (HcL : c `notin` L) by fsetdec;
    assert (Hcp : c <> p) by (intro E; subst c; fsetdec);
    assert (Hcq : c <> q) by (intro E; subst c; fsetdec);
    specialize (IHcof c HcL); unfold AnnD_sw in IHcof;
    rewrite (rename_ctx_sw_cons_co p q c phi1 G Hcp Hcq) in IHcof;
    rewrite (rename_open_co_co_sw_fix p q c g3 Hcp Hcq) in IHcof;
    rewrite (rename_open_co_tm_sw_fix p q c B1 Hcp Hcq) in IHcof;
    rewrite (rename_open_co_tm_sw_fix p q c B2 Hcp Hcq) in IHcof;
    apply IHcof; exact HD'
  | intros c Hc; assert (HcL : c `notin` L) by fsetdec;
    assert (Hcp : c <> p) by (intro E; subst c; fsetdec);
    assert (Hcq : c <> q) by (intro E; subst c; fsetdec);
    specialize (Heq c HcL);
    apply (f_equal (rename_tm (sw p q) (sw p q))) in Heq;
    rewrite (rename_open_co_tm_sw_fix p q c B3 Hcp Hcq) in Heq;
    rewrite rename_open_co_tm_sw_any in Heq;
    cbn [rename_tm rename_co] in Heq;
    rewrite (sw_fix p q c Hcp Hcq) in Heq;
    exact Heq
  | unfold AnnT_sw in IHt1; apply IHt1
  | unfold AnnT_sw in IHt2; apply IHt2
  | unfold AnnT_sw in IHt3; apply IHt3 ].

Ltac ann_case_An_CAbsCong :=
  idtac "CASE An_CAbsCong";
  intros L G D g1 g3 g4 phi1 a1 phi2 a3 a2 B1 B B2 H1 IH1
         Hcof IHcof Heq Ht1 IHt1 Ht2 IHt2 Ht3 IHt3 Hd IHd;
  unfold AnnD_sw; intros D' HD'; cbn [rename_co rename_tm];
  eapply (An_CAbsCong (L \u {{p}} \u {{q}}) (rename_ctx_sw p q G) D'
                     (rename_co (sw p q) (sw p q) g1)
                     (rename_co (sw p q) (sw p q) g3)
                     (rename_co (sw p q) (sw p q) g4)
                     (rename_constraint (sw p q) (sw p q) phi1)
                     (rename_tm (sw p q) (sw p q) a1)
                     (rename_constraint (sw p q) (sw p q) phi2)
                     (rename_tm (sw p q) (sw p q) a3)
                     (rename_tm (sw p q) (sw p q) a2)
                     (rename_tm (sw p q) (sw p q) B1)
                     (rename_tm (sw p q) (sw p q) B)
                     (rename_tm (sw p q) (sw p q) B2));
  [ unfold AnnI_sw in IH1; apply IH1; exact HD'
  | intros c Hc; assert (HcL : c `notin` L) by fsetdec;
    assert (Hcp : c <> p) by (intro E; subst c; fsetdec);
    assert (Hcq : c <> q) by (intro E; subst c; fsetdec);
    specialize (IHcof c HcL); unfold AnnD_sw in IHcof;
    rewrite (rename_ctx_sw_cons_co p q c phi1 G Hcp Hcq) in IHcof;
    rewrite (rename_open_co_co_sw_fix p q c g3 Hcp Hcq) in IHcof;
    rewrite (rename_open_co_tm_sw_fix p q c a1 Hcp Hcq) in IHcof;
    rewrite (rename_open_co_tm_sw_fix p q c a2 Hcp Hcq) in IHcof;
    apply IHcof; exact HD'
  | intros c Hc; assert (HcL : c `notin` L) by fsetdec;
    assert (Hcp : c <> p) by (intro E; subst c; fsetdec);
    assert (Hcq : c <> q) by (intro E; subst c; fsetdec);
    specialize (Heq c HcL);
    apply (f_equal (rename_tm (sw p q) (sw p q))) in Heq;
    rewrite (rename_open_co_tm_sw_fix p q c a3 Hcp Hcq) in Heq;
    rewrite rename_open_co_tm_sw_any in Heq;
    cbn [rename_tm rename_co] in Heq;
    rewrite (sw_fix p q c Hcp Hcq) in Heq;
    exact Heq
  | unfold AnnT_sw in IHt1; apply IHt1
  | unfold AnnT_sw in IHt2; apply IHt2
  | unfold AnnT_sw in IHt3; apply IHt3
  | unfold AnnD_sw in IHd; apply IHd; apply Drel_sw_dom ].

Ltac ann_case_An_CAppCong :=
  idtac "CASE An_CAppCong";
  intros G D g1 g2 g3 a1 b1 a2 b2 a3 b3 A B g4
         H1 IH1 H2 IH2 H3 IH3 Ht1 IHt1 Ht2 IHt2 Hd IHd;
  unfold AnnD_sw; intros D' HD'; cbn [rename_co];
  eapply (An_CAppCong (rename_ctx_sw p q G) D'
                      (rename_co (sw p q) (sw p q) g1)
                      (rename_co (sw p q) (sw p q) g2)
                      (rename_co (sw p q) (sw p q) g3)
                      (rename_tm (sw p q) (sw p q) a1)
                      (rename_tm (sw p q) (sw p q) b1)
                      (rename_tm (sw p q) (sw p q) a2)
                      (rename_tm (sw p q) (sw p q) b2)
                      (rename_tm (sw p q) (sw p q) a3)
                      (rename_tm (sw p q) (sw p q) b3)
                      (rename_tm (sw p q) (sw p q) A)
                      (rename_tm (sw p q) (sw p q) B)
                      (rename_co (sw p q) (sw p q) g4));
  [ unfold AnnD_sw in IH1; apply IH1; exact HD'
  | unfold AnnD_sw in IH2; apply IH2; apply Drel_sw_dom
  | unfold AnnD_sw in IH3; apply IH3; apply Drel_sw_dom
  | unfold AnnT_sw in IHt1; apply IHt1
  | unfold AnnT_sw in IHt2; apply IHt2
  | unfold AnnD_sw in IHd; apply IHd; apply Drel_sw_dom ].

Ltac ann_case_An_CPiSnd :=
  idtac "CASE An_CPiSnd";
  intros G D g1 g2 g3 B1 B2 a a' A b b' B H1 IH1 H2 IH2 H3 IH3;
  unfold AnnD_sw; intros D' HD'; cbn [rename_co];
  rewrite !rename_open_co_tm_sw_any;
  eapply (An_CPiSnd (rename_ctx_sw p q G) D'
                     (rename_co (sw p q) (sw p q) g1)
                     (rename_co (sw p q) (sw p q) g2)
                     (rename_co (sw p q) (sw p q) g3)
                     (rename_tm (sw p q) (sw p q) B1)
                     (rename_tm (sw p q) (sw p q) B2)
                     (rename_tm (sw p q) (sw p q) a)
                     (rename_tm (sw p q) (sw p q) a')
                     (rename_tm (sw p q) (sw p q) A)
                     (rename_tm (sw p q) (sw p q) b)
                     (rename_tm (sw p q) (sw p q) b')
                     (rename_tm (sw p q) (sw p q) B));
  [ unfold AnnD_sw in IH1; apply IH1; exact HD'
  | unfold AnnD_sw in IH2; apply IH2; apply Drel_sw_dom
  | unfold AnnD_sw in IH3; apply IH3; apply Drel_sw_dom ].

Ltac ann_case_An_Cast :=
  idtac "CASE An_Cast";
  intros G D g1 g2 b b' a a' A B H1 IH1 H2 IH2;
  unfold AnnD_sw; intros D' HD'; cbn [rename_co rename_constraint];
  eapply (An_Cast (rename_ctx_sw p q G) D'
                  (rename_co (sw p q) (sw p q) g1)
                  (rename_co (sw p q) (sw p q) g2)
                  (rename_tm (sw p q) (sw p q) b)
                  (rename_tm (sw p q) (sw p q) b')
                  (rename_tm (sw p q) (sw p q) a)
                  (rename_tm (sw p q) (sw p q) a')
                  (rename_tm (sw p q) (sw p q) A)
                  (rename_tm (sw p q) (sw p q) B));
  [ unfold AnnD_sw in IH1; apply IH1; exact HD'
  | unfold AnnI_sw in IH2; apply IH2; exact HD' ].

Ltac ann_case_An_IsoSnd :=
  idtac "CASE An_IsoSnd";
  intros G D g A B a a' b b' H IH;
  unfold AnnD_sw; intros D' HD'; cbn [rename_co rename_tm rename_constraint];
  eapply (An_IsoSnd (rename_ctx_sw p q G) D'
                    (rename_co (sw p q) (sw p q) g)
                    (rename_tm (sw p q) (sw p q) A)
                    (rename_tm (sw p q) (sw p q) B)
                    (rename_tm (sw p q) (sw p q) a)
                    (rename_tm (sw p q) (sw p q) a')
                    (rename_tm (sw p q) (sw p q) b)
                    (rename_tm (sw p q) (sw p q) b'));
  unfold AnnI_sw in IH; apply IH; exact HD'.

Ltac ann_case_An_Empty :=
  idtac "CASE An_Empty";
  intros; unfold AnnC_sw; cbn [rename_ctx_sw]; apply An_Empty.

Ltac ann_case_An_ConsTm :=
  idtac "CASE An_ConsTm";
  intros G x A Hctx IHC HA IHA Hnot; unfold AnnC_sw;
  rewrite rename_ctx_sw_cons_tm_any;
  apply (An_ConsTm (rename_ctx_sw p q G) (sw p q x)
                   (rename_tm (sw p q) (sw p q) A));
  [ unfold AnnC_sw in IHC; apply IHC
  | unfold AnnT_sw in IHA; apply IHA
  | let Hcontra := fresh "Hcontra" in intro Hcontra;
    pose proof (dom_rename_ctx_sw_bwd p q G (sw p q x) Hcontra) as Hb;
    rewrite sw_invol in Hb; apply Hnot; exact Hb ].

Ltac ann_case_An_ConsCo :=
  idtac "CASE An_ConsCo";
  intros G c phi Hctx IHC HP IHP Hnot; unfold AnnC_sw;
  rewrite rename_ctx_sw_cons_co_any;
  apply (An_ConsCo (rename_ctx_sw p q G) (sw p q c)
                   (rename_constraint (sw p q) (sw p q) phi));
  [ unfold AnnC_sw in IHC; apply IHC
  | unfold AnnP_sw in IHP; apply IHP
  | let Hcontra := fresh "Hcontra" in intro Hcontra;
    pose proof (dom_rename_ctx_sw_bwd p q G (sw p q c) Hcontra) as Hb;
    rewrite sw_invol in Hb; apply Hnot; exact Hb ].

Ltac ann_case_An_Sig_Empty :=
  idtac "CASE An_Sig_Empty"; intros; unfold AnnS_sw; exact I.
Ltac ann_case_An_Sig_ConsAx :=
  idtac "CASE An_Sig_ConsAx"; intros; unfold AnnS_sw; exact I.

Ltac ann_case_dispatch :=
  idtac "CASE dispatch";
  [> ann_case_An_Wff
  | ann_case_An_Star
  | ann_case_An_Var
  | ann_case_An_Pi
  | ann_case_An_Abs
  | ann_case_An_App
  | ann_case_An_Conv
  | ann_case_An_CPi
  | ann_case_An_CAbs
  | ann_case_An_CApp
  | ann_case_An_Fam
  | ann_case_An_PropCong
  | ann_case_An_CPiFst
  | ann_case_An_IsoSym
  | ann_case_An_IsoConv
  | ann_case_An_Assn
  | ann_case_An_Refl
  | ann_case_An_EraseEq
  | ann_case_An_Sym
  | ann_case_An_Trans
  | ann_case_An_Beta
  | ann_case_An_PiCong
  | ann_case_An_AbsCong
  | ann_case_An_AppCong
  | ann_case_An_PiFst
  | ann_case_An_PiSnd
  | ann_case_An_CPiCong
  | ann_case_An_CAbsCong
  | ann_case_An_CAppCong
  | ann_case_An_CPiSnd
  | ann_case_An_Cast
  | ann_case_An_IsoSnd
  | ann_case_An_Empty
  | ann_case_An_ConsTm
  | ann_case_An_ConsCo
  | ann_case_An_Sig_Empty
  | ann_case_An_Sig_ConsAx ].

Ltac ann_mut_typing :=
  apply (AnnTyping_mut (AnnP_sw p q) (AnnT_sw p q) (AnnI_sw p q)
                       (AnnD_sw p q) (AnnC_sw p q) (AnnS_sw p q));
  ann_case_dispatch.

Ltac ann_mut_defeq :=
  apply (AnnDefEq_mut (AnnP_sw p q) (AnnT_sw p q) (AnnI_sw p q)
                      (AnnD_sw p q) (AnnC_sw p q) (AnnS_sw p q));
  ann_case_dispatch.

(* ================================================================== *)
(* The exported renaming lemmas                                        *)
(* ================================================================== *)

Lemma AnnTyping_rename_sw : forall G a A,
  AnnTyping G a A ->
  AnnTyping (rename_ctx_sw p q G)
            (rename_tm (sw p q) (sw p q) a)
            (rename_tm (sw p q) (sw p q) A).
Proof.
  ann_mut_typing.
Qed.

Lemma AnnDefEq_rename_sw : forall G D g a b,
  AnnDefEq G D g a b ->
  forall D', Drel_sw p q D D' ->
  AnnDefEq (rename_ctx_sw p q G) D'
           (rename_co (sw p q) (sw p q) g)
           (rename_tm (sw p q) (sw p q) a)
           (rename_tm (sw p q) (sw p q) b).
Proof.
  ann_mut_defeq.
Qed.

End AnnEqv.
(* ==== HeadEqv ==== *)

(* ================================================================== *)
(* head_reduction is equivariant under fresh swaps, with no freshness  *)
(* hypotheses: contexts and D are renamed along.                       *)
(* ================================================================== *)

Lemma head_reduction_rename_sw : forall p q G a a',
  head_reduction G a a' ->
  head_reduction (rename_ctx_sw p q G)
                 (rename_tm (sw p q) (sw p q) a)
                 (rename_tm (sw p q) (sw p q) a').
Proof.
  intros p q G a a' H.
  rename G into Gfix. rename a into afix. rename a' into a'fix.
  refine (head_reduction_ind
    (fun G a a' => head_reduction (rename_ctx_sw p q G)
                                 (rename_tm (sw p q) (sw p q) a)
                                 (rename_tm (sw p q) (sw p q) a'))
    _ _ _ _ _ _ _ _ _ _ Gfix afix a'fix H).
  - (* An_AppLeft *)
    intros G a rho b a' Hlcb Hred IH. cbn [rename_tm].
    eapply An_AppLeft.
    + apply (lc_tm_rename_sw p q). exact Hlcb.
    + exact IH.
  - (* An_AppAbs *)
    intros G rho A w a Hlca Hval. cbn [rename_tm].
    rewrite rename_open_tm_sw_any.
    eapply An_AppAbs.
    + apply (lc_tm_rename_sw p q). exact Hlca.
    + exact (Value_rename_sw p q (a_Abs rho A w) Hval).
  - (* An_CAppLeft *)
    intros G a g a' Hlcg Hred IH. cbn [rename_tm].
    eapply An_CAppLeft.
    + apply (lc_co_rename_sw p q). exact Hlcg.
    + exact IH.
  - (* An_CAppCAbs *)
    intros G phi b g Hlcphi Hlcb Hlcg. cbn [rename_tm].
    rewrite rename_open_co_tm_sw_any. cbn [rename_co].
    eapply An_CAppCAbs.
    + apply (lc_constraint_rename_sw p q). exact Hlcphi.
    + change (lc_tm (rename_tm (sw p q) (sw p q) (a_CAbs phi b))).
      apply (lc_tm_rename_sw p q). exact Hlcb.
    + apply (lc_co_rename_sw p q). exact Hlcg.
  - (* An_AbsTerm *)
    intros L G A b b' Hty Hcof IHcof. cbn [rename_tm].
    eapply (An_AbsTerm (L \u {{p}} \u {{q}})).
    + apply (AnnTyping_rename_sw p q G A a_Star). exact Hty.
    + intros z Hz.
      assert (HzL : z `notin` L) by fsetdec.
      assert (Hzp : z <> p) by (intro E; subst z; fsetdec).
      assert (Hzq : z <> q) by (intro E; subst z; fsetdec).
      specialize (IHcof z HzL).
      rewrite (rename_ctx_sw_cons_tm p q z A G Hzp Hzq) in IHcof.
      rewrite (rename_open_tm_sw_fix p q z b Hzp Hzq) in IHcof.
      rewrite (rename_open_tm_sw_fix p q z b' Hzp Hzq) in IHcof.
      exact IHcof.
  - (* An_Axiom *)
    intros G F a A Hb.
    destruct (an_toplevel_binds_eq F a A Hb) as [-> [-> ->]].
    cbn [rename_tm]. rewrite rename_tm_FixDef.
    apply (An_Axiom (rename_ctx_sw p q G) Fix FixDef FixTy). exact Hb.
  - (* An_ConvTerm *)
    intros G a g a' Hlcg Hred IH. cbn [rename_tm].
    eapply An_ConvTerm.
    + apply (lc_co_rename_sw p q). exact Hlcg.
    + exact IH.
  - (* An_Combine *)
    intros G v g1 g2 Hlc1 Hlc2 Hval. cbn [rename_tm]. cbn [rename_co].
    eapply An_Combine.
    + apply (lc_co_rename_sw p q). exact Hlc1.
    + apply (lc_co_rename_sw p q). exact Hlc2.
    + exact (Value_rename_sw p q v Hval).
  - (* An_Push *)
    intros G v g rho b b' g' A1 B1 A2 B2 Hval Hdef Hb' Hg'.
    cbn [rename_tm].
    eapply (An_Push (rename_ctx_sw p q G)
                    (rename_tm (sw p q) (sw p q) v)
                    (rename_co (sw p q) (sw p q) g) rho
                    (rename_tm (sw p q) (sw p q) b)
                    (rename_tm (sw p q) (sw p q) b')
                    (rename_co (sw p q) (sw p q) g')
                    (rename_tm (sw p q) (sw p q) A1)
                    (rename_tm (sw p q) (sw p q) B1)
                    (rename_tm (sw p q) (sw p q) A2)
                    (rename_tm (sw p q) (sw p q) B2)).
    + exact (Value_rename_sw p q v Hval).
    + pose proof (AnnDefEq_rename_sw p q G (dom G) g
                    (a_Pi rho A1 B1) (a_Pi rho A2 B2) Hdef
                    (dom (rename_ctx_sw p q G))
                    (Drel_sw_dom p q G)) as Hd.
      cbn [rename_tm] in Hd. exact Hd.
    + apply (f_equal (rename_tm (sw p q) (sw p q))) in Hb'.
      cbn [rename_tm rename_co] in Hb'. exact Hb'.
    + apply (f_equal (rename_co (sw p q) (sw p q))) in Hg'.
      cbn [rename_co] in Hg'. exact Hg'.
  - (* An_CPush *)
    intros G v g g1 g1' g' phi1 A1 phi2 A2 Hval Hdef Hg1' Hg'.
    cbn [rename_tm].
    eapply (An_CPush (rename_ctx_sw p q G)
                     (rename_tm (sw p q) (sw p q) v)
                     (rename_co (sw p q) (sw p q) g)
                     (rename_co (sw p q) (sw p q) g1)
                     (rename_co (sw p q) (sw p q) g1')
                     (rename_co (sw p q) (sw p q) g')
                     (rename_constraint (sw p q) (sw p q) phi1)
                     (rename_tm (sw p q) (sw p q) A1)
                     (rename_constraint (sw p q) (sw p q) phi2)
                     (rename_tm (sw p q) (sw p q) A2)).
    + exact (Value_rename_sw p q v Hval).
    + pose proof (AnnDefEq_rename_sw p q G (dom G) g
                    (a_CPi phi1 A1) (a_CPi phi2 A2) Hdef
                    (dom (rename_ctx_sw p q G))
                    (Drel_sw_dom p q G)) as Hd.
      cbn [rename_tm] in Hd. exact Hd.
    + apply (f_equal (rename_co (sw p q) (sw p q))) in Hg1'.
      cbn [rename_co] in Hg1'. exact Hg1'.
    + apply (f_equal (rename_co (sw p q) (sw p q))) in Hg'.
      cbn [rename_co] in Hg'. exact Hg'.
Qed.
(* ==== HeadLc ==== *)
Require Import Lia.

(* ================================================================== *)
(* Locally-closedness of head reducts.                                 *)
(* ================================================================== *)

Lemma lc_FixDef : lc_tm FixDef.
Proof.
  apply closed_to_lc_tm.
  - unfold FixDef. cbn. repeat split; try lia; trivial.
  - unfold FixDef. cbn. repeat split; try lia; trivial.
Qed.

Lemma head_reduction_lc : forall G a a',
  head_reduction G a a' -> lc_tm a -> lc_tm a'.
Proof.
  intros G a a' H.
  rename G into Gfix. rename a into afix. rename a' into a'fix.
  refine (head_reduction_ind
    (fun G a a' => lc_tm a -> lc_tm a')
    _ _ _ _ _ _ _ _ _ _ Gfix afix a'fix H).
  - (* An_AppLeft *)
    intros G0 a rho b a' Hlcb Hred IH Hlc.
    apply lc_tm_app_inv in Hlc as [Hlca Hlcb2].
    apply lc_a_App.
    + apply IH. exact Hlca.
    + exact Hlcb.
  - (* An_AppAbs *)
    intros G0 rho A w a Hlca Hval Hlc.
    apply lc_tm_app_inv in Hlc as [HlcAbs Hlca2].
    apply (lc_open_body_abs rho A w HlcAbs a Hlca2).
  - (* An_CAppLeft *)
    intros G0 a g a' Hlcg Hred IH Hlc.
    apply lc_tm_capp_inv in Hlc as [Hlca Hlcg2].
    apply lc_a_CApp.
    + apply IH. exact Hlca.
    + exact Hlcg.
  - (* An_CAppCAbs *)
    intros G0 phi b g Hlcphi HlcCabs Hlcg Hlc.
    apply (lc_open_body_cabs phi b HlcCabs g Hlcg).
  - (* An_AbsTerm *)
    intros L G0 A b b' Hty Hcof IHcof Hlc.
    apply lc_tm_abs_inv in Hlc as [HlcA HlcBody].
    apply lc_a_Abs.
    + exact HlcA.
    + intro y.
      destruct (atom_fresh L) as [x0 Hx0].
      assert (Hlcx0 : lc_tm (open_tm_wrt_tm b' (a_Var_f x0))).
      { apply (IHcof x0 Hx0). apply HlcBody. }
      assert (Hclt : clt_tm 1 b').
      { apply (clt_tm_open_tm_var_inv b' 0 x0). apply lc_clt_tm. exact Hlcx0. }
      assert (Hclc : clc_tm 0 b').
      { apply (clc_tm_open_tm_fwd b' 0 0 x0). apply lc_clc_tm. exact Hlcx0. }
      apply closed_to_lc_tm.
      * apply (clt_tm_open_tm_fwd_gen b' 0 (a_Var_f y)).
        -- cbn. exact I.
        -- exact Hclt.
      * apply (clc_tm_open_tm_fwd_gen b' 0 0 (a_Var_f y)).
        -- cbn. exact I.
        -- exact Hclc.
  - (* An_Axiom *)
    intros G0 F a0 A Hb Hlc.
    destruct (an_toplevel_binds_eq F a0 A Hb) as [-> [-> ->]].
    exact lc_FixDef.
  - (* An_ConvTerm *)
    intros G0 a g a' Hlcg Hred IH Hlc.
    apply lc_tm_conv_inv in Hlc as [Hlca Hlcg2].
    apply lc_a_Conv.
    + apply IH. exact Hlca.
    + exact Hlcg.
  - (* An_Combine *)
    intros G0 v g1 g2 Hlcg1 Hlcg2 Hval Hlc.
    apply lc_tm_conv_inv in Hlc as [Hlc1 Hlcg2'].
    apply lc_tm_conv_inv in Hlc1 as [Hlcv Hlcg1'].
    apply lc_a_Conv.
    + exact Hlcv.
    + apply lc_g_Trans; assumption.
  - (* An_Push *)
    intros G0 v g rho b b' g' A1 B1 A2 B2 Hval Hdef Hb' Hg' Hlc.
    apply lc_tm_app_inv in Hlc as [Hlcvg Hlcb].
    apply lc_tm_conv_inv in Hlcvg as [Hlcv Hlcg].
    subst b'. subst g'.
    apply lc_a_Conv.
    + apply lc_a_App.
      * exact Hlcv.
      * apply lc_a_Conv.
        -- exact Hlcb.
        -- apply lc_g_Sym. apply lc_g_PiFst. exact Hlcg.
    + apply lc_g_PiSnd.
      * exact Hlcg.
      * apply lc_g_Refl2.
        -- apply lc_a_Conv.
           ++ exact Hlcb.
           ++ apply lc_g_Sym. apply lc_g_PiFst. exact Hlcg.
        -- exact Hlcb.
        -- apply lc_g_PiFst. exact Hlcg.
  - (* An_CPush *)
    intros G0 v g g1 g1' g' phi1 A1 phi2 A2 Hval Hdef Hg1' Hg' Hlc.
    apply lc_tm_capp_inv in Hlc as [Hlcvg Hlcg1].
    apply lc_tm_conv_inv in Hlcvg as [Hlcv Hlcg].
    subst g1'. subst g'.
    apply lc_a_Conv.
    + apply lc_a_CApp.
      * exact Hlcv.
      * apply lc_g_Cast.
        -- exact Hlcg1.
        -- apply lc_g_Sym. apply lc_g_CPiFst. exact Hlcg.
    + apply lc_g_CPiSnd.
      * exact Hlcg.
      * apply lc_g_Cast.
        -- exact Hlcg1.
        -- apply lc_g_Sym. apply lc_g_CPiFst. exact Hlcg.
      * exact Hlcg1.
Qed.
(* ==== Cvf ==== *)

(* ================================================================== *)
(* Free coercion variables (atoms occurring as free [g_Var_f]).        *)
(* Term variables are deliberately ignored: they are tracked          *)
(* separately by [fv_tm_tm_tm].                                       *)
(* ================================================================== *)

Fixpoint cfv_tm (a:tm) : vars :=
  match a with
  | a_Star => {}
  | a_Var_b _ => {}
  | a_Var_f _ => {}
  | a_Abs _ A b => cfv_tm A \u cfv_tm b
  | a_UAbs _ b => cfv_tm b
  | a_App a _ b => cfv_tm a \u cfv_tm b
  | a_Fam _ => {}
  | a_Const _ => {}
  | a_Pi _ A B => cfv_tm A \u cfv_tm B
  | a_Conv a g => cfv_tm a \u cfv_co g
  | a_CPi phi B => cfv_constraint phi \u cfv_tm B
  | a_CAbs phi b => cfv_constraint phi \u cfv_tm b
  | a_UCAbs b => cfv_tm b
  | a_CApp a g => cfv_tm a \u cfv_co g
  | a_Bullet => {}
  | a_DataCon _ => {}
  | a_Case a br => cfv_tm a \u cfv_brs br
  end
with cfv_brs (b:brs) : vars :=
  match b with
  | br_None => {}
  | br_One _ a r => cfv_tm a \u cfv_brs r
  end
with cfv_co (g:co) : vars :=
  match g with
  | g_Triv => {}
  | g_Var_b _ => {}
  | g_Var_f c => {{c}}
  | g_Beta a b => cfv_tm a \u cfv_tm b
  | g_Refl a => cfv_tm a
  | g_Refl2 a b g' => cfv_tm a \u cfv_tm b \u cfv_co g'
  | g_Sym g' => cfv_co g'
  | g_Trans g1 g2 => cfv_co g1 \u cfv_co g2
  | g_PiCong _ g1 g2 => cfv_co g1 \u cfv_co g2
  | g_AbsCong _ g1 g2 => cfv_co g1 \u cfv_co g2
  | g_AppCong g1 _ g2 => cfv_co g1 \u cfv_co g2
  | g_PiFst g' => cfv_co g'
  | g_CPiFst g' => cfv_co g'
  | g_IsoSnd g' => cfv_co g'
  | g_PiSnd g1 g2 => cfv_co g1 \u cfv_co g2
  | g_CPiCong g1 g3 => cfv_co g1 \u cfv_co g3
  | g_CAbsCong g1 g3 g4 => cfv_co g1 \u cfv_co g3 \u cfv_co g4
  | g_CAppCong g g1 g2 => cfv_co g \u cfv_co g1 \u cfv_co g2
  | g_CPiSnd g g1 g2 => cfv_co g \u cfv_co g1 \u cfv_co g2
  | g_Cast g1 g2 => cfv_co g1 \u cfv_co g2
  | g_EqCong g1 A g2 => cfv_co g1 \u cfv_tm A \u cfv_co g2
  | g_IsoConv phi1 phi2 g => cfv_constraint phi1 \u cfv_constraint phi2 \u cfv_co g
  | g_Eta a => cfv_tm a
  | g_Left g g' => cfv_co g \u cfv_co g'
  | g_Right g g' => cfv_co g \u cfv_co g'
  end
with cfv_constraint (p:constraint) : vars :=
  match p with
  | Eq a b A => cfv_tm a \u cfv_tm b \u cfv_tm A
  end.

(* ================================================================== *)
(* Term-opening at a variable preserves (and reflects) free coercion  *)
(* variables; here we only need the direction [a] subset [open a].    *)
(* ================================================================== *)

Lemma cfv_open_tm_var_subset :
  (forall a k z,
     AtomSetImpl.Subset (cfv_tm a)
                        (cfv_tm (open_tm_wrt_tm_rec k (a_Var_f z) a))) /\
  (forall b k z,
     AtomSetImpl.Subset (cfv_brs b)
                        (cfv_brs (open_brs_wrt_tm_rec k (a_Var_f z) b))) /\
  (forall g k z,
     AtomSetImpl.Subset (cfv_co g)
                        (cfv_co (open_co_wrt_tm_rec k (a_Var_f z) g))) /\
  (forall p k z,
     AtomSetImpl.Subset (cfv_constraint p)
                        (cfv_constraint (open_constraint_wrt_tm_rec k (a_Var_f z) p))).
Proof.
  apply (tm_mutind
    (fun a => forall k z, AtomSetImpl.Subset (cfv_tm a)
                           (cfv_tm (open_tm_wrt_tm_rec k (a_Var_f z) a)))
    (fun b => forall k z, AtomSetImpl.Subset (cfv_brs b)
                           (cfv_brs (open_brs_wrt_tm_rec k (a_Var_f z) b)))
    (fun g => forall k z, AtomSetImpl.Subset (cfv_co g)
                           (cfv_co (open_co_wrt_tm_rec k (a_Var_f z) g)))
    (fun p => forall k z, AtomSetImpl.Subset (cfv_constraint p)
                           (cfv_constraint (open_constraint_wrt_tm_rec k (a_Var_f z) p)))).
  all: intros.
  all: cbn [cfv_tm cfv_brs cfv_co cfv_constraint
            open_tm_wrt_tm_rec open_brs_wrt_tm_rec
            open_co_wrt_tm_rec open_constraint_wrt_tm_rec].
  all: try (match goal with |- context [lt_eq_lt_dec ?a ?b] =>
              destruct (lt_eq_lt_dec a b) as [[Hlt|Heq]|Hgt];
              cbn [cfv_tm cfv_co] end).
  all: try mem_solve.
Qed.

(* ================================================================== *)
(* Subset lemmas for openings                                        *)
(* ================================================================== *)

Lemma cfv_open_tm_subset :
  (forall a k u,
     AtomSetImpl.Subset (cfv_tm (open_tm_wrt_tm_rec k u a))
                        (cfv_tm a \u cfv_tm u)) /\
  (forall b k u,
     AtomSetImpl.Subset (cfv_brs (open_brs_wrt_tm_rec k u b))
                        (cfv_brs b \u cfv_tm u)) /\
  (forall g k u,
     AtomSetImpl.Subset (cfv_co (open_co_wrt_tm_rec k u g))
                        (cfv_co g \u cfv_tm u)) /\
  (forall p k u,
     AtomSetImpl.Subset (cfv_constraint (open_constraint_wrt_tm_rec k u p))
                        (cfv_constraint p \u cfv_tm u)).
Proof.
  apply (tm_mutind
    (fun a => forall k u, AtomSetImpl.Subset (cfv_tm (open_tm_wrt_tm_rec k u a))
                           (cfv_tm a \u cfv_tm u))
    (fun b => forall k u, AtomSetImpl.Subset (cfv_brs (open_brs_wrt_tm_rec k u b))
                           (cfv_brs b \u cfv_tm u))
    (fun g => forall k u, AtomSetImpl.Subset (cfv_co (open_co_wrt_tm_rec k u g))
                           (cfv_co g \u cfv_tm u))
    (fun p => forall k u, AtomSetImpl.Subset (cfv_constraint (open_constraint_wrt_tm_rec k u p))
                           (cfv_constraint p \u cfv_tm u))).
  all: intros.
  all: cbn [cfv_tm cfv_brs cfv_co cfv_constraint
            open_tm_wrt_tm_rec open_brs_wrt_tm_rec
            open_co_wrt_tm_rec open_constraint_wrt_tm_rec].
  all: try (match goal with |- context [lt_eq_lt_dec ?a ?b] =>
              destruct (lt_eq_lt_dec a b) as [[Hlt|Heq]|Hgt];
              cbn [cfv_tm cfv_co] end).
  all: try mem_solve.
Qed.

Lemma cfv_open_co_subset :
  (forall a k g,
     AtomSetImpl.Subset (cfv_tm (open_tm_wrt_co_rec k g a))
                        (cfv_tm a \u cfv_co g)) /\
  (forall b k g,
     AtomSetImpl.Subset (cfv_brs (open_brs_wrt_co_rec k g b))
                        (cfv_brs b \u cfv_co g)) /\
  (forall g0 k g,
     AtomSetImpl.Subset (cfv_co (open_co_wrt_co_rec k g g0))
                        (cfv_co g0 \u cfv_co g)) /\
  (forall p k g,
     AtomSetImpl.Subset (cfv_constraint (open_constraint_wrt_co_rec k g p))
                        (cfv_constraint p \u cfv_co g)).
Proof.
  apply (tm_mutind
    (fun a => forall k g, AtomSetImpl.Subset (cfv_tm (open_tm_wrt_co_rec k g a))
                           (cfv_tm a \u cfv_co g))
    (fun b => forall k g, AtomSetImpl.Subset (cfv_brs (open_brs_wrt_co_rec k g b))
                           (cfv_brs b \u cfv_co g))
    (fun g0 => forall k g, AtomSetImpl.Subset (cfv_co (open_co_wrt_co_rec k g g0))
                           (cfv_co g0 \u cfv_co g))
    (fun p => forall k g, AtomSetImpl.Subset (cfv_constraint (open_constraint_wrt_co_rec k g p))
                           (cfv_constraint p \u cfv_co g))).
  all: intros.
  all: cbn [cfv_tm cfv_brs cfv_co cfv_constraint
            open_tm_wrt_co_rec open_brs_wrt_co_rec
            open_co_wrt_co_rec open_constraint_wrt_co_rec].
  all: try (match goal with |- context [lt_eq_lt_dec ?a ?b] =>
              destruct (lt_eq_lt_dec a b) as [[Hlt|Heq]|Hgt];
              cbn [cfv_co] end).
  all: try mem_solve.
Qed.

Lemma cfv_open_tm_subset_tm : forall a k u,
  AtomSetImpl.Subset (cfv_tm (open_tm_wrt_tm_rec k u a))
                     (cfv_tm a \u cfv_tm u).
Proof. intros; exact (proj1 cfv_open_tm_subset a k u). Qed.
Lemma cfv_open_co_subset_tm : forall a k g,
  AtomSetImpl.Subset (cfv_tm (open_tm_wrt_co_rec k g a))
                     (cfv_tm a \u cfv_co g).
Proof. intros; exact (proj1 cfv_open_co_subset a k g). Qed.
(* ==== CvfHead ==== *)

(* ================================================================== *)
(* [cfv] is invariant under nothing interesting, but the key fact is  *)
(* that head reduction cannot introduce a free coercion variable      *)
(* that was not free in the source.  This lets us pick a fresh term   *)
(* variable for the cofinite [An_AbsTerm] rule without accidentally   *)
(* capturing a coercion variable.                                     *)
(* ================================================================== *)

Lemma cfv_FixDef_notin : forall c:atom, c `notin` cfv_tm FixDef.
Proof.
  intro c. intro H. unfold FixDef in H. cbn [cfv_tm] in H.
  repeat match goal with
  | H : _ \in (_ \u _) |- _ =>
      apply AtomSetImpl.union_1 in H; destruct H
  | H : _ \in _ |- _ => apply AtomSetImpl.empty_1 in H
  | H : False |- _ => exact H
  end.
Qed.

Ltac split_notin :=
  repeat match goal with
  | H : _ \notin (_ \u _) |- _ =>
      let H1 := fresh "Hn" in
      let H2 := fresh "Hn" in
      pose proof (notin_union_1 _ _ _ H) as H1;
      pose proof (notin_union_2 _ _ _ H) as H2;
      clear H
  end.

Ltac close_notin :=
  intro Hz;
  repeat match goal with
  | H : _ \in (_ \u _) |- _ =>
      apply AtomSetImpl.union_1 in H; destruct H
  | H : _ \in _ |- _ => apply AtomSetImpl.empty_1 in H
  | H : False |- _ => exact H
  end;
  repeat match goal with
  | Hnt : ?x \notin ?S, Hin : ?x \in ?S |- _ => exact (Hnt Hin)
  end.

Lemma head_reduction_cfv_notin : forall G a a',
  head_reduction G a a' ->
  forall c, c `notin` cfv_tm a -> c `notin` cfv_tm a'.
Proof.
  intros G a a' H.
  rename G into Gfix. rename a into afix. rename a' into a'fix.
  refine (head_reduction_ind
    (fun G a a' => forall c, c `notin` cfv_tm a -> c `notin` cfv_tm a')
    _ _ _ _ _ _ _ _ _ _ Gfix afix a'fix H).
  - (* An_AppLeft *)
    intros G0 a rho b a' Hlcb Hred IH c Hc.
    cbn [cfv_tm] in Hc |- *.
    split_notin.
    assert (Hna' : c `notin` cfv_tm a') by (apply IH; assumption).
    apply notin_union_3; [exact Hna' | assumption].
  - (* An_AppAbs *)
    intros G0 rho A w a Hlca Hval c Hc.
    cbn [cfv_tm] in Hc |- *.
    split_notin.
    eapply notin_subset; [apply cfv_open_tm_subset_tm |].
    cbn [cfv_tm].
    apply notin_union_3; eassumption.
  - (* An_CAppLeft *)
    intros G0 a g a' Hlcg Hred IH c Hc.
    cbn [cfv_tm] in Hc |- *.
    split_notin.
    assert (Hna' : c `notin` cfv_tm a') by (apply IH; assumption).
    apply notin_union_3; [exact Hna' | assumption].
  - (* An_CAppCAbs *)
    intros G0 phi b g Hlcphi Hlcb Hlcg c Hc.
    cbn [cfv_tm] in Hc |- *.
    split_notin.
    eapply notin_subset; [apply cfv_open_co_subset_tm |].
    apply notin_union_3; eassumption.
  - (* An_AbsTerm *)
    intros L G0 A b b' Hty Hcof IHcof c Hc.
    cbn [cfv_tm] in Hc |- *.
    pose proof (notin_union_1 _ _ _ Hc) as HcA.
    pose proof (notin_union_2 _ _ _ Hc) as Hcb.
    destruct (atom_fresh (L \u {{c}})) as [z Hz].
    assert (HzL : z `notin` L) by (intro E; apply Hz; fsetdec).
    assert (Hzc : z <> c) by (intro E; subst z; apply Hz; fsetdec).
    assert (Hbo : c `notin` cfv_tm (open_tm_wrt_tm b (a_Var_f z))).
    { eapply notin_subset; [apply cfv_open_tm_subset_tm |].
      cbn [cfv_tm].
      apply notin_union_3; [exact Hcb | apply AtomSetImpl.empty_1]. }
    assert (Hbo' : c `notin` cfv_tm (open_tm_wrt_tm b' (a_Var_f z)))
      by (apply (IHcof z HzL c Hbo)).
    assert (Hcb' : c `notin` cfv_tm b').
    { exact (notin_subset c (cfv_tm b')
               (cfv_tm (open_tm_wrt_tm b' (a_Var_f z)))
               (proj1 cfv_open_tm_var_subset b' 0 z) Hbo'). }
    apply notin_union_3; [exact HcA | exact Hcb'].
  - (* An_Axiom *)
    intros G0 F a0 A Hb c Hc.
    destruct (an_toplevel_binds_eq F a0 A Hb) as [-> [-> ->]].
    apply cfv_FixDef_notin.
  - (* An_ConvTerm *)
    intros G0 a g a' Hlcg Hred IH c Hc.
    cbn [cfv_tm] in Hc |- *.
    split_notin.
    assert (Hna' : c `notin` cfv_tm a') by (apply IH; assumption).
    apply notin_union_3; [exact Hna' | assumption].
  - (* An_Combine *)
    intros G0 v g1 g2 Hlcg1 Hlcg2 Hval c Hc.
    cbn [cfv_tm cfv_co] in Hc |- *.
    split_notin.
    close_notin.
  - (* An_Push *)
    intros G0 v g rho b b' g' A1 B1 A2 B2 Hval Hdef Hb' Hg' c Hc.
    subst b'. subst g'.
    cbn [cfv_tm cfv_co] in Hc |- *.
    split_notin.
    close_notin.
  - (* An_CPush *)
    intros G0 v g g1 g1' g' phi1 A1 phi2 A2 Hval Hdef Hg1' Hg' c Hc.
    subst g1'. subst g'.
    cbn [cfv_tm cfv_co] in Hc |- *.
    split_notin.
    close_notin.
Qed.
(* ==== CofinitePrep ==== *)

(* ================================================================== *)
(* The set of all atoms mentioned by a context.                        *)
(* ================================================================== *)

Fixpoint ctx_atoms (G:context) : vars :=
  match G with
  | nil => empty
  | (z, Tm A) :: G' => {{z}} \u fvx_tm A \u ctx_atoms G'
  | (z, Co phi) :: G' => {{z}} \u fvx_constraint phi \u ctx_atoms G'
  end.

(* ================================================================== *)
(* Swaps fixing all atoms of a context fix the context.                *)
(* ================================================================== *)

Lemma rename_tm_sw_fix_notin : forall x y a,
  x `notin` fvx_tm a -> y `notin` fvx_tm a ->
  rename_tm (sw x y) (sw x y) a = a.
Proof.
  intros x y a Hx Hy.
  apply (proj1 rename_fresh).
  - intros w Hw. apply sw_fix.
    + intro E; subst w; exact (Hx Hw).
    + intro E; subst w; exact (Hy Hw).
  - intros c Hc. apply sw_fix.
    + intro E; subst c; exact (Hx Hc).
    + intro E; subst c; exact (Hy Hc).
Qed.

Lemma rename_constraint_sw_fix_notin : forall x y p,
  x `notin` fvx_constraint p -> y `notin` fvx_constraint p ->
  rename_constraint (sw x y) (sw x y) p = p.
Proof.
  intros x y p Hx Hy.
  apply (proj2 (proj2 (proj2 rename_fresh))).
  - intros w Hw. apply sw_fix.
    + intro E; subst w; exact (Hx Hw).
    + intro E; subst w; exact (Hy Hw).
  - intros c Hc. apply sw_fix.
    + intro E; subst c; exact (Hx Hc).
    + intro E; subst c; exact (Hy Hc).
Qed.

Lemma rename_ctx_sw_fix : forall x y G,
  x `notin` ctx_atoms G -> y `notin` ctx_atoms G ->
  rename_ctx_sw x y G = G.
Proof.
  intros x y G. induction G as [| [z s] G IH]; intros Hx Hy.
  - reflexivity.
  - destruct s as [A | phi]; cbn [ctx_atoms] in Hx, Hy.
    + (* Tm *)
      pose proof (notin_union_1 _ _ _ Hx) as Hxz.
      pose proof (notin_union_2 _ _ _ Hx) as Hx1.
      pose proof (notin_union_1 _ _ _ Hy) as Hyz.
      pose proof (notin_union_2 _ _ _ Hy) as Hy1.
      pose proof (notin_union_1 _ _ _ Hx1) as HxA.
      pose proof (notin_union_2 _ _ _ Hx1) as HxG.
      pose proof (notin_union_1 _ _ _ Hy1) as HyA.
      pose proof (notin_union_2 _ _ _ Hy1) as HyG.
      rewrite rename_ctx_sw_cons. cbn [rename_sort_sw].
      rewrite (sw_fix x y z (notin_singleton_1 z x Hxz)
                              (notin_singleton_1 z y Hyz)).
      rewrite (rename_tm_sw_fix_notin x y A HxA HyA).
      rewrite IH; [reflexivity | exact HxG | exact HyG].
    + (* Co *)
      pose proof (notin_union_1 _ _ _ Hx) as Hxz.
      pose proof (notin_union_2 _ _ _ Hx) as Hx1.
      pose proof (notin_union_1 _ _ _ Hy) as Hyz.
      pose proof (notin_union_2 _ _ _ Hy) as Hy1.
      pose proof (notin_union_1 _ _ _ Hx1) as Hxp.
      pose proof (notin_union_2 _ _ _ Hx1) as HxG.
      pose proof (notin_union_1 _ _ _ Hy1) as Hyp.
      pose proof (notin_union_2 _ _ _ Hy1) as HyG.
      rewrite rename_ctx_sw_cons. cbn [rename_sort_sw].
      rewrite (sw_fix x y z (notin_singleton_1 z x Hxz)
                              (notin_singleton_1 z y Hyz)).
      rewrite (rename_constraint_sw_fix_notin x y phi Hxp Hyp).
      rewrite IH; [reflexivity | exact HxG | exact HyG].
Qed.

(* ================================================================== *)
(* If a swap fixes all free coercion variables, then it may be used    *)
(* for the coercion component of a simultaneous renaming without       *)
(* changing the result.                                                *)
(* ================================================================== *)

Lemma rename_tm_sc_sw_idv :
  (forall a x y, x `notin` cfv_tm a -> y `notin` cfv_tm a ->
     rename_tm (sw x y) (sw x y) a = rename_tm (sw x y) idv a) /\
  (forall b x y, x `notin` cfv_brs b -> y `notin` cfv_brs b ->
     rename_brs (sw x y) (sw x y) b = rename_brs (sw x y) idv b) /\
  (forall g x y, x `notin` cfv_co g -> y `notin` cfv_co g ->
     rename_co (sw x y) (sw x y) g = rename_co (sw x y) idv g) /\
  (forall p x y, x `notin` cfv_constraint p -> y `notin` cfv_constraint p ->
     rename_constraint (sw x y) (sw x y) p = rename_constraint (sw x y) idv p).
Proof.
  apply (tm_mutind
    (fun a => forall x y, x `notin` cfv_tm a -> y `notin` cfv_tm a ->
       rename_tm (sw x y) (sw x y) a = rename_tm (sw x y) idv a)
    (fun b => forall x y, x `notin` cfv_brs b -> y `notin` cfv_brs b ->
       rename_brs (sw x y) (sw x y) b = rename_brs (sw x y) idv b)
    (fun g => forall x y, x `notin` cfv_co g -> y `notin` cfv_co g ->
       rename_co (sw x y) (sw x y) g = rename_co (sw x y) idv g)
    (fun p => forall x y,
       x `notin` cfv_constraint p -> y `notin` cfv_constraint p ->
       rename_constraint (sw x y) (sw x y) p = rename_constraint (sw x y) idv p)).
  all: intros.
  all: cbn [rename_tm rename_brs rename_co rename_constraint idv
            cfv_tm cfv_brs cfv_co cfv_constraint] in * |- *.
  all: try (match goal with H : _ `notin` (_ \u _) |- _ => split_notin end).
  all: try reflexivity.
  all: try (f_equal; eauto).
  all: try (match goal with
    | Hx : ?x `notin` singleton ?c, Hy : ?y `notin` singleton ?c |-
        sw ?x ?y ?c = idv ?c =>
        rewrite (sw_fix x y c);
        [reflexivity
        | apply (notin_singleton_1 c x Hx)
        | apply (notin_singleton_1 c y Hy)]
    | Hx : ?x `notin` singleton ?c, Hy : ?y `notin` singleton ?c |-
        g_Var_f (sw ?x ?y ?c) = g_Var_f ?c =>
        rewrite (sw_fix x y c);
        [reflexivity
        | apply (notin_singleton_1 c x Hx)
        | apply (notin_singleton_1 c y Hy)]
    end).
  all: try (f_equal; eauto).
Qed.

Lemma rename_tm_sc_sw_idv_tm : forall a x y,
  x `notin` cfv_tm a -> y `notin` cfv_tm a ->
  rename_tm (sw x y) (sw x y) a = rename_tm (sw x y) idv a.
Proof. intros a x y Hx Hy. exact (proj1 rename_tm_sc_sw_idv a x y Hx Hy). Qed.

(* ================================================================== *)
(* The cofinite head-step extraction for the Abs-Irrel case.            *)
(*                                                                     *)
(* Given a cofinite family of head reductions of [open a x], pick a    *)
(* fresh [x0] and a reduct [r0] of [open a x0].  Closing [r0] at [x0]  *)
(* gives a candidate reduct body [a']; every other fresh opening is    *)
(* obtained by swap-renaming the [x0] step.  Freshness is chosen to    *)
(* keep the context, [A] and [a] fixed and to ensure that [x0] does    *)
(* not occur as a free coercion variable in [r0], so the coercion      *)
(* component of the swap-renaming is invisible.                        *)
(* ================================================================== *)

Lemma cofinite_head_step :
  forall (G:context) (A:tm) (a B:tm) (L:vars),
  lc_tm A ->
  (forall x, x `notin` L ->
     AnnTyping ((x ~ Tm A) ++ G)
               (open_tm_wrt_tm a (a_Var_f x))
               (open_tm_wrt_tm B (a_Var_f x))) ->
  (forall x, x `notin` L ->
     irrelevant ((x ~ Tm A) ++ G) (add x (dom G))
                (open_tm_wrt_tm a (a_Var_f x))) ->
  (forall x, x `notin` L ->
     ~ CoercedValue (open_tm_wrt_tm a (a_Var_f x))) ->
  (forall x, x `notin` L ->
     exists r, head_reduction ((x ~ Tm A) ++ G)
                 (open_tm_wrt_tm a (a_Var_f x)) r) ->
  exists L' a', forall x, x `notin` L' ->
     head_reduction ((x ~ Tm A) ++ G)
       (open_tm_wrt_tm a (a_Var_f x))
       (open_tm_wrt_tm a' (a_Var_f x)).
Proof.
  intros G A a B L HlcA Hbodyty Hirr HnoCV Hallstep.
  destruct (atom_fresh
    (L \u fvx_tm a \u fvx_tm A \u cfv_tm a \u ctx_atoms G)) as [x0 Hx0].
  repeat match goal with
  | H : _ `notin` (_ \u _) |- _ =>
      let H1 := fresh "Hf" in
      let H2 := fresh "Hf" in
      pose proof (notin_union_1 _ _ _ H) as H1;
      pose proof (notin_union_2 _ _ _ H) as H2;
      clear H
  end.
  assert (Hx0L : x0 `notin` L) by eassumption.
  assert (Hx0fvxa : x0 `notin` fvx_tm a) by eassumption.
  assert (Hx0fvxA : x0 `notin` fvx_tm A) by eassumption.
  assert (Hx0cfva : x0 `notin` cfv_tm a) by eassumption.
  assert (Hx0ctx : x0 `notin` ctx_atoms G) by eassumption.
  destruct (Hallstep x0 Hx0L) as [r0 Hstep0].
  assert (Hlcsrc : lc_tm (open_tm_wrt_tm a (a_Var_f x0))).
  { exact (proj1 (AnnTyping_wf ((x0 ~ Tm A) ++ G)
                    (open_tm_wrt_tm a (a_Var_f x0))
                    (open_tm_wrt_tm B (a_Var_f x0))
                    (Hbodyty x0 Hx0L))). }
  assert (Hcltr0 : clt_tm 0 r0).
  { apply lc_clt_tm.
    exact (head_reduction_lc ((x0 ~ Tm A) ++ G) _ _ Hstep0 Hlcsrc). }
  assert (Hx0opencfv :
            x0 `notin` cfv_tm (open_tm_wrt_tm a (a_Var_f x0))).
  { eapply notin_subset; [apply cfv_open_tm_subset_tm |].
    cbn [cfv_tm].
    apply notin_union_3; [exact Hx0cfva | apply AtomSetImpl.empty_1]. }
  assert (Hx0cfvr0 : x0 `notin` cfv_tm r0).
  { exact (head_reduction_cfv_notin ((x0 ~ Tm A) ++ G) _ _ Hstep0
             x0 Hx0opencfv). }
  set (a' := close_tm x0 0 r0).
  set (L' := L \u ctx_atoms G \u fvx_tm a \u fvx_tm A
                \u fvx_tm r0 \u cfv_tm r0 \u {{x0}} \u fvx_tm a').
  exists L'. exists a'. intros x HxL'.
  unfold L', a' in *.
  repeat match goal with
  | H : _ `notin` (_ \u _) |- _ =>
      let H1 := fresh "Hx" in
      let H2 := fresh "Hx" in
      pose proof (notin_union_1 _ _ _ H) as H1;
      pose proof (notin_union_2 _ _ _ H) as H2;
      clear H
  end.
  assert (Hxctx : x `notin` ctx_atoms G) by eassumption.
  assert (Hxfvxa : x `notin` fvx_tm a) by eassumption.
  assert (HxfvxA : x `notin` fvx_tm A) by eassumption.
  assert (Hxfvxr0 : x `notin` fvx_tm r0) by eassumption.
  assert (Hxcfvr0 : x `notin` cfv_tm r0) by eassumption.
  assert (Hxx0 : x <> x0).
  { symmetry. apply (notin_singleton_1 x0 x). eassumption. }
  pose proof (head_reduction_rename_sw x0 x ((x0 ~ Tm A) ++ G)
                _ _ Hstep0) as Hren.
  rewrite rename_ctx_sw_cons_tm_any in Hren.
  rewrite (sw_same x0 x) in Hren.
  rewrite (rename_tm_sw_fix_notin x0 x A Hx0fvxA HxfvxA) in Hren.
  rewrite (rename_ctx_sw_fix x0 x G Hx0ctx Hxctx) in Hren.
  rewrite rename_open_tm_sw_any in Hren.
  rewrite (rename_tm_sw_fix_notin x0 x a Hx0fvxa Hxfvxa) in Hren.
  cbn [rename_tm] in Hren.
  rewrite (sw_same x0 x) in Hren.
  rewrite (rename_tm_sc_sw_idv_tm r0 x0 x Hx0cfvr0 Hxcfvr0) in Hren.
  rewrite <- (proj1 open_close_rename_tm r0 0 x0 x Hcltr0 Hxfvxr0) in Hren.
  exact Hren.
Qed.
End COF.


Lemma cofinite_head_step :
  forall (G:context) (A:tm) (a B:tm) (L:vars),
  lc_tm A ->
  (forall x, x `notin` L ->
     AnnTyping ((x ~ Tm A) ++ G)
               (open_tm_wrt_tm a (a_Var_f x))
               (open_tm_wrt_tm B (a_Var_f x))) ->
  (forall x, x `notin` L ->
     irrelevant ((x ~ Tm A) ++ G) (add x (dom G))
                (open_tm_wrt_tm a (a_Var_f x))) ->
  (forall x, x `notin` L ->
     ~ CoercedValue (open_tm_wrt_tm a (a_Var_f x))) ->
  (forall x, x `notin` L ->
     exists r, head_reduction ((x ~ Tm A) ++ G)
                 (open_tm_wrt_tm a (a_Var_f x)) r) ->
  exists L' a', forall x, x `notin` L' ->
     head_reduction ((x ~ Tm A) ++ G)
       (open_tm_wrt_tm a (a_Var_f x))
       (open_tm_wrt_tm a' (a_Var_f x)).
Proof. exact COF.cofinite_head_step. Qed.

(* ================================================================ *)
(* The Abs-Irrel dichotomy, proven from the cofinite step interface *)
(* and swap-renaming invariance of CoercedValue.                    *)
(* ================================================================ *)

Lemma progress_abs_irrel :
  forall (G:context) (A a B:tm) (L:vars),
  AnnTyping G A a_Star ->
  lc_tm A ->
  (forall x, x `notin` L ->
     AnnTyping ((x ~ Tm A) ++ G)
               (open_tm_wrt_tm a (a_Var_f x))
               (open_tm_wrt_tm B (a_Var_f x))) ->
  (forall x, x `notin` L ->
     irrelevant ((x ~ Tm A) ++ G) (add x (dom G))
                (open_tm_wrt_tm a (a_Var_f x))) ->
  (forall x, x `notin` L ->
     irrelevant ((x ~ Tm A) ++ G) (add x (dom G))
                (open_tm_wrt_tm a (a_Var_f x)) ->
     CoercedValue (open_tm_wrt_tm a (a_Var_f x)) \/
     exists r, head_reduction ((x ~ Tm A) ++ G)
                                (open_tm_wrt_tm a (a_Var_f x)) r) ->
  CoercedValue (a_Abs Irrel A a) \/
  exists a', head_reduction G (a_Abs Irrel A a) a'.
Proof.
  intros G A a B L HAty HlcA Hbodyty Hirrbody IH.
  set (L' := L \u fvx_tm a).
  destruct (atom_fresh L') as [x0 Hx0].
  assert (Hx0L : x0 `notin` L) by (subst L'; fsetdec).
  assert (Hx0a : x0 `notin` fvx_tm a) by (subst L'; fsetdec).
  destruct (IH x0 Hx0L (Hirrbody x0 Hx0L)) as [Hcv0 | [r0 Hstep0]].
  - (* body value: lift cofinitely by swap invariance *)
    left. apply CV.
    apply (Value_AbsIrrel_of_CV L A a x0 HlcA Hx0L Hx0a Hcv0).
  - (* body steps: every fresh opening steps, then use cofinite step *)
    assert (HnoCV : forall y, y `notin` L' ->
              ~ CoercedValue (open_tm_wrt_tm a (a_Var_f y))).
    { intros y Hy Hcvy.
      assert (HyL : y `notin` L) by (subst L'; fsetdec).
      assert (Hya : y `notin` fvx_tm a) by (subst L'; fsetdec).
      assert (Hcvx : CoercedValue (open_tm_wrt_tm a (a_Var_f x0)))
        by (apply (CoercedValue_swap_any y x0 a Hya Hx0a Hcvy)).
      exact (CoercedValue_no_head_reduction
               (open_tm_wrt_tm a (a_Var_f x0)) Hcvx
               ((x0 ~ Tm A) ++ G) r0 Hstep0). }
    assert (Hallstep : forall y, y `notin` L' ->
              exists r, head_reduction ((y ~ Tm A) ++ G)
                          (open_tm_wrt_tm a (a_Var_f y)) r).
    { intros y Hy.
      assert (HyL : y `notin` L) by (subst L'; fsetdec).
      destruct (IH y HyL (Hirrbody y HyL)) as [Hcvy | Hstep].
      - exfalso. exact (HnoCV y Hy Hcvy).
      - exact Hstep. }
    destruct (cofinite_head_step G A a B L' HlcA
                (fun y Hy => Hbodyty y (ltac:(subst L'; fsetdec)))
                (fun y Hy => Hirrbody y (ltac:(subst L'; fsetdec)))
                HnoCV Hallstep)
      as [Lcof [a' Hcof]].
    right. exists (a_Abs Irrel A a').
    apply (An_AbsTerm Lcof G A a a').
    + exact HAty.
    + exact Hcof.
Qed.

(* ===== ProgressMain ===== *)

(* ================================================================ *)
(* Progress by mutual induction over the annotated judgments         *)
(* ================================================================ *)

Definition prog (G:context) (a:tm) : Prop :=
  CoercedValue a \/ exists a', head_reduction G a a'.

Definition Pmot (G:context) (a A:tm) (_:AnnTyping G a A) : Prop :=
  irrelevant G (dom G) a -> prog G a.

Lemma progress_all :
  (forall G a A (H:AnnTyping G a A), Pmot G a A H) /\
  (forall G p (H:AnnPropWff G p), True) /\
  (forall G D g p q (H:AnnIso G D g p q), True) /\
  (forall G D g a b (H:AnnDefEq G D g a b), True) /\
  (forall G (H:AnnCtx G), True) /\
  (forall S (H:AnnSig S), True).
Proof.
  apply (AnnTyping_comb Pmot (fun _ _ _ => True)
                      (fun _ _ _ _ _ _ => True)
                      (fun _ _ _ _ _ _ => True)
                      (fun _ _ => True) (fun _ _ => True)).
  (* An_Star *)
  - intros G actx IHctx Hirr. left. apply CV. apply Value_Star.
  (* An_Var *)
  - intros G x A actx IHctx Hb Hirr. exfalso.
    destruct Hirr as [Hfv Hgood].
    apply (Hfv x A Hb). cbn [erase_tm fv_tm_tm_tm].
    apply AtomSetImpl.singleton_2. reflexivity.
  (* An_Pi *)
  - intros L G rho A B bodyty IHbody Aty IHA Hirr.
    assert (Hty : AnnTyping G (a_Pi rho A B) a_Star)
      by (apply (An_Pi L G rho A B); [exact bodyty | exact Aty]).
    left. apply CV. apply Value_Pi.
    + exact (proj1 (AnnTyping_wf G A a_Star Aty)).
    + exact (proj1 (AnnTyping_wf G (a_Pi rho A B) a_Star Hty)).
  (* An_Abs *)
  - intros L G rho A a B Aty IHA bodyty IHbody rhochk Hirr.
    assert (Hty : AnnTyping G (a_Abs rho A a) (a_Pi rho A B))
      by (apply (An_Abs L G rho A a B); [exact Aty | exact bodyty | exact rhochk]).
    assert (HlcA : lc_tm A) by exact (proj1 (AnnTyping_wf G A a_Star Aty)).
    destruct rho.
    + left. apply CV. apply Value_AbsRel.
      * exact HlcA.
      * exact (proj1 (AnnTyping_wf G (a_Abs Rel A a) (a_Pi Rel A B) Hty)).
    + apply (progress_abs_irrel G A a B (L \u dom G) Aty HlcA).
      * intros x Hx. apply bodyty. apply notin_union_1 in Hx. exact Hx.
      * intros x Hx.
        destruct Hirr as [Hfv Hgood].
        apply (irrelevant_open_AbsIrrel G (dom G) x A a).
        -- exact (conj Hfv Hgood).
        -- apply notin_union_2 in Hx. exact Hx.
        -- exact HlcA.
        -- apply rhochk. apply notin_union_1 in Hx. exact Hx.
      * intros x Hx Hirr_x.
        apply (IHbody x).
        -- apply notin_union_1 in Hx. exact Hx.
        -- exact Hirr_x.
  (* An_App *)
  - intros G b rho a B A bty IHb aty IHa Hirr.
    destruct Hirr as [Hfv Hgood].
    destruct (IHb (irrelevant_App_fun G (dom G) b rho a (conj Hfv Hgood)))
      as [Hbv | [b' Hstep]].
    + destruct Hbv as [bv Hbval | bv g Hlcg Hbval].
      * destruct (Value_typing_Pi G bv rho A B Hbval bty)
          as [A0 [b0 Hb]].
        subst bv.
        right. exists (open_tm_wrt_tm b0 a).
        eapply (An_AppAbs G rho A0 b0 a).
        -- exact (proj1 (AnnTyping_wf G a A aty)).
        -- exact Hbval.
      * destruct (AnnTyping_Conv_inv G bv g (a_Pi rho A B) bty)
          as [T [Htyv [Hdef HtyPi]]].
        destruct (Value_typing_Conv_Pi G (dom G) g T rho A B bv
                    Hgood Hdef Hbval Htyv)
          as [A0 [b0 [B0 [HT Hveq]]]].
        subst T. subst bv.
        right.
        exists (a_Conv
                  (a_App (a_Abs rho A0 b0) rho
                         (a_Conv a (g_Sym (g_PiFst g))))
                  (g_PiSnd g
                     (g_Refl2 (a_Conv a (g_Sym (g_PiFst g))) a
                        (g_PiFst g)))).
        eapply (An_Push G (a_Abs rho A0 b0) g rho a
                  (a_Conv a (g_Sym (g_PiFst g)))
                  (g_PiSnd g
                     (g_Refl2 (a_Conv a (g_Sym (g_PiFst g))) a
                        (g_PiFst g)))
                  A0 B0 A B).
        -- exact Hbval.
        -- exact Hdef.
        -- reflexivity.
        -- reflexivity.
    + right. exists (a_App b' rho a).
      eapply (An_AppLeft G b rho a b').
      * exact (proj1 (AnnTyping_wf G a A aty)).
      * exact Hstep.
  (* An_Conv *)
  - intros G a g B A aty IHa def IHdef Bty IHB Hirr.
    destruct Hirr as [Hfv Hgood].
    assert (Hlcg : lc_co g)
      by exact (proj1 (AnnDefEq_wf G (dom G) g A B def)).
    destruct (IHa (irrelevant_Conv_fun G (dom G) a g (conj Hfv Hgood)))
      as [Hcv | [a' Hstep]].
    + destruct Hcv as [av Hav | av h Hlch Hav].
      * left. apply CC.
        -- exact Hlcg.
        -- exact Hav.
      * right. exists (a_Conv av (g_Trans h g)).
        eapply (An_Combine G av h g).
        -- exact Hlch.
        -- exact Hlcg.
        -- exact Hav.
    + right. exists (a_Conv a' g).
      eapply (An_ConvTerm G a g a').
      * exact Hlcg.
      * exact Hstep.
  (* An_CPi *)
  - intros L G phi B prop IHprop bodyty IHbody Hirr.
    assert (Hty : AnnTyping G (a_CPi phi B) a_Star)
      by (apply (An_CPi L G phi B); [exact prop | exact bodyty]).
    left. apply CV. apply Value_CPi.
    + exact (AnnPropWff_wf G phi prop).
    + exact (proj1 (AnnTyping_wf G (a_CPi phi B) a_Star Hty)).
  (* An_CAbs *)
  - intros L G phi a B prop IHprop bodyty IHbody Hirr.
    assert (Hty : AnnTyping G (a_CAbs phi a) (a_CPi phi B))
      by (apply (An_CAbs L G phi a B); [exact prop | exact bodyty]).
    left. apply CV. apply Value_CAbs.
    + exact (AnnPropWff_wf G phi prop).
    + exact (proj1 (AnnTyping_wf G (a_CAbs phi a) (a_CPi phi B) Hty)).
  (* An_CApp *)
  - intros G a1 g B a b A1 a1ty IHa1 def IHdef Hirr.
    destruct Hirr as [Hfv Hgood].
    assert (Hlcg : lc_co g)
      by exact (proj1 (AnnDefEq_wf G (dom G) g a b def)).
    destruct (IHa1 (irrelevant_CApp_fun G (dom G) a1 g (conj Hfv Hgood)))
      as [Hcv | [a1' Hstep]].
    + destruct Hcv as [av Hav | av h Hlch Hav].
      * destruct (Value_typing_CPi_Eq G av a b A1 B Hav a1ty)
          as [b0 Hveq].
        subst av.
        inversion Hav; subst.
        right. exists (open_tm_wrt_co b0 g).
        eapply (An_CAppCAbs G (Eq a b A1) b0 g).
        -- assumption.
        -- exact (proj1 (AnnTyping_wf G (a_CAbs (Eq a b A1) b0)
                         (a_CPi (Eq a b A1) B) a1ty)).
        -- exact Hlcg.
      * destruct (AnnTyping_Conv_inv G av h (a_CPi (Eq a b A1) B) a1ty)
          as [T [Htyv [Hdef HtyPi]]].
        destruct (Value_typing_Conv_CPi G (dom G) h T (Eq a b A1) B av
                    Hgood Hdef Hav Htyv)
          as [phi0 [b0 [B0 [HT Hveq]]]].
        subst T. subst av.
        right.
        exists (a_Conv
                  (a_CApp (a_CAbs phi0 b0)
                     (g_Cast g (g_Sym (g_CPiFst h))))
                  (g_CPiSnd h (g_Cast g (g_Sym (g_CPiFst h))) g)).
        eapply (An_CPush G (a_CAbs phi0 b0) h g
                  (g_Cast g (g_Sym (g_CPiFst h)))
                  (g_CPiSnd h (g_Cast g (g_Sym (g_CPiFst h))) g)
                  phi0 B0 (Eq a b A1) B).
        -- exact Hav.
        -- exact Hdef.
        -- reflexivity.
        -- reflexivity.
    + right. exists (a_CApp a1' g).
      eapply (An_CAppLeft G a1 g a1').
      * exact Hlcg.
      * exact Hstep.
  (* An_Fam *)
  - intros G F A a actx IHctx Hb Aty IHA Hirr.
    right. exists a. apply (An_Axiom G F a A Hb).
  (* all remaining (prop wff, iso, defeq, ctx, sig) motives are True *)
  (* remaining propwff/iso/defeq/ctx/sig motives: all True *)
  - intros; exact I.
  - intros; exact I.
  - intros; exact I.
  - intros; exact I.
  - intros; exact I.
  - intros; exact I.
  - intros; exact I.
  - intros; exact I.
  - intros; exact I.
  - intros; exact I.
  - intros; exact I.
  - intros; exact I.
  - intros; exact I.
  - intros; exact I.
  - intros; exact I.
  - intros; exact I.
  - intros; exact I.
  - intros; exact I.
  - intros; exact I.
  - intros; exact I.
  - intros; exact I.
  - intros; exact I.
  - intros; exact I.
  - intros; exact I.
  - intros; exact I.
  - intros; exact I.
  - intros; exact I.
Qed.

Theorem progress : forall G a A, irrelevant G (dom G) a -> AnnTyping G a A -> CoercedValue a \/ exists a', head_reduction G a a'.
Proof.
  intros G a A Hirr H.
  exact (proj1 progress_all G a A H Hirr).
Qed.
