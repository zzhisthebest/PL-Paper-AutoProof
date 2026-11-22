Require Import CBPV.SyntacticTyping CBPV.AbstractReductionSystems CBPV.StrongReduction.

Set Implicit Arguments.

Require Import Logic List.

Require Import Classes.Morphisms.

Import List Notations.

Import CommaNotation.

(** * Basic substitution / renaming algebra *)

Definition idsv {n} : fin n -> value n := @ids value VarInstance_value n.

Definition renv {n m} (xi : fin n -> fin m) : fin n -> value m :=
  fun i => @var_value m (xi i).

Definition scomp {n m k} (s : fin n -> value m) (t : fin m -> value k) : fin n -> value k :=
  fun i => (s i)[t].

Definition sren {n m k} (s : fin n -> value m) (xi : fin m -> fin k) : fin n -> value k :=
  fun i => (s i)⟨xi⟩.

Definition rscomp {n m k} (xi : fin n -> fin m) (s : fin m -> value k) : fin n -> value k :=
  fun i => s (xi i).

(** Pointwise helpers *)

Lemma up_subst_eq n m (sigma tau: fin n -> value m) (H: forall i, sigma i = tau i) :
  forall (j : fin (S n)), (up_value_value sigma) j = (up_value_value tau) j.
Proof.
  intros [j|].
  - unfold up_value_value, scons, funcomp. cbn. f_equal. apply H.
  - unfold up_value_value, scons. cbn. reflexivity.
Qed.

Lemma up_ren_eq n m (xi zeta: fin n -> fin m) (H: forall i, xi i = zeta i) :
  forall (j : fin (S n)), (up_ren xi) j = (up_ren zeta) j.
Proof.
  intros [j|].
  - unfold up_ren, scons, funcomp. cbn. f_equal. apply H.
  - unfold up_ren, scons. cbn. reflexivity.
Qed.

Lemma up2_subst_eq n m (s t: fin n -> value m) (H: forall i, s i = t i) :
  forall (j : fin (S (S n))),
   @up_value_value (S n) (S m) (@up_value_value n m s) j
   = @up_value_value (S n) (S m) (@up_value_value n m t) j.
Proof.
  apply up_subst_eq. apply up_subst_eq. apply H.
Qed.

Lemma up2_ren_eq n m (xi zeta: fin n -> fin m) (H: forall i, xi i = zeta i) :
  forall (j : fin (S (S n))),
   @up_ren (S n) (S m) (@up_ren n m xi) j = @up_ren (S n) (S m) (@up_ren n m zeta) j.
Proof.
  apply up_ren_eq. apply up_ren_eq. apply H.
Qed.

Lemma up_rscomp n m k (xi: ren n m) (s: fin m -> value k) :
  forall (j : fin (S n)),
  @rscomp (S n) (S m) (S k) (@up_ren n m xi) (@up_value_value m k s) j
    = @up_value_value n k (@rscomp n m k xi s) j.
Proof.
  intros [j|]; cbn.
  - unfold up_value_value, scons, funcomp, rscomp. cbn. reflexivity.
  - unfold up_value_value, scons, rscomp. cbn. reflexivity.
Qed.

Lemma up2_rscomp n m k (xi: ren n m) (s: fin m -> value k) :
  forall (j : fin (S (S n))),
    (rscomp (up_ren (up_ren xi)) (up_value_value (up_value_value s))) j
    = (up_value_value (up_value_value (rscomp xi s))) j.
Proof.
  intros j.
  transitivity ((up_value_value (rscomp (up_ren xi) (up_value_value s))) j).
  - apply (@up_rscomp (S n) (S m) (S k) (@up_ren n m xi) (@up_value_value m k s)).
  - apply (@up_subst_eq (S n) (S k) (rscomp (up_ren xi) (up_value_value s))
        (up_value_value (rscomp xi s)) (up_rscomp xi s)).
Qed.

Lemma up_ren_comp n m k (xi: ren n m) (zeta: ren m k) :
  forall (j : fin (S n)), @up_ren m k zeta (up_ren xi j) = @up_ren n k (fun i => zeta (xi i)) j.
Proof.
  intros [j|]; cbn. reflexivity. reflexivity.
Qed.

Lemma up2_ren_comp n m k (xi: ren n m) (zeta: ren m k) :
  forall (j : fin (S (S n))),
    @up_ren (S m) (S k) (@up_ren m k zeta) (up_ren (up_ren xi) j)
    = @up_ren (S n) (S k) (@up_ren n k (fun i => zeta (xi i))) j.
Proof.
  intros j. destruct j as [j|].
  - destruct j as [j|]; cbn; reflexivity.
  - cbn; reflexivity.
Qed.

(** Substitution and renaming extensionality *)

Lemma subst_ext :
  forall n,
  (forall (v:value n) m (s t : fin n -> value m),
      (forall i, s i = t i) -> v[s] = v[t]) /\
  (forall (c:comp n) m (s t : fin n -> value m),
      (forall i, s i = t i) -> c[s] = c[t]).
Proof.
  apply (mutind_val_comp
    (fun n (v:value n) => forall m (s t: fin n -> value m), (forall i, s i = t i) -> v[s] = v[t])
    (fun n (c:comp n) => forall m (s t: fin n -> value m), (forall i, s i = t i) -> c[s] = c[t])).
  - intros n i m s t H. cbn. apply H.
  - intros n m s t H. reflexivity.
  - intros n v1 IH1 v2 IH2 m s t H. cbn. f_equal; [apply IH1; auto|apply IH2; auto].
  - intros n b v IH m s t H. cbn. f_equal. apply IH; auto.
  - intros n c IH m s t H. cbn. f_equal. apply IH; auto.
  - intros n m s t H. reflexivity.
  - intros n v IH m s t H. cbn. f_equal. apply IH; auto.
  - intros n c IH m s t H. cbn. f_equal. apply IH. apply (@up_subst_eq n m s t H).
  - intros n c IH1 v IH2 m s t H. cbn. f_equal; [apply IH1; auto|apply IH2; auto].
  - intros n c1 IH1 c2 IH2 m s t H. cbn. f_equal; [apply IH1; auto|apply IH2; auto].
  - intros n v IH m s t H. cbn. f_equal. apply IH; auto.
  - intros n c1 IH1 c2 IH2 m s t H. cbn. f_equal;
      [apply IH1; auto|apply IH2; apply (@up_subst_eq n m s t H)].
  - intros n b c IH m s t H. cbn. f_equal. apply IH; auto.
  - intros n v IH m s t H. cbn. f_equal. apply IH; auto.
  - intros n v IHv c1 IH1 c2 IH2 m s t H. cbn. f_equal;
      [apply IHv; auto|apply IH1; apply (@up_subst_eq n m s t H)|apply IH2; apply (@up_subst_eq n m s t H)].
  - intros n v IHv c IH m s t H. cbn. f_equal;
      [apply IHv; auto|apply IH; apply (@up2_subst_eq n m s t H)].
Qed.

Lemma ren_ext :
  forall n,
  (forall (v:value n) m (xi zeta : fin n -> fin m),
      (forall i, xi i = zeta i) -> v⟨xi⟩ = v⟨zeta⟩) /\
  (forall (c:comp n) m (xi zeta : fin n -> fin m),
      (forall i, xi i = zeta i) -> c⟨xi⟩ = c⟨zeta⟩).
Proof.
  apply (mutind_val_comp
    (fun n (v:value n) => forall m (xi zeta: fin n -> fin m), (forall i, xi i = zeta i) -> v⟨xi⟩ = v⟨zeta⟩)
    (fun n (c:comp n) => forall m (xi zeta: fin n -> fin m), (forall i, xi i = zeta i) -> c⟨xi⟩ = c⟨zeta⟩)).
  - intros n i m xi zeta H. cbn. f_equal. apply H.
  - intros n m xi zeta H. reflexivity.
  - intros n v1 IH1 v2 IH2 m xi zeta H. cbn. f_equal; [apply IH1; auto|apply IH2; auto].
  - intros n b v IH m xi zeta H. cbn. f_equal. apply IH; auto.
  - intros n c IH m xi zeta H. cbn. f_equal. apply IH; auto.
  - intros n m xi zeta H. reflexivity.
  - intros n v IH m xi zeta H. cbn. f_equal. apply IH; auto.
  - intros n c IH m xi zeta H. cbn. f_equal. apply IH. apply (@up_ren_eq n m xi zeta H).
  - intros n c IH1 v IH2 m xi zeta H. cbn. f_equal; [apply IH1; auto|apply IH2; auto].
  - intros n c1 IH1 c2 IH2 m xi zeta H. cbn. f_equal; [apply IH1; auto|apply IH2; auto].
  - intros n v IH m xi zeta H. cbn. f_equal. apply IH; auto.
  - intros n c1 IH1 c2 IH2 m xi zeta H. cbn. f_equal;
      [apply IH1; auto|apply IH2; apply (@up_ren_eq n m xi zeta H)].
  - intros n b c IH m xi zeta H. cbn. f_equal. apply IH; auto.
  - intros n v IH m xi zeta H. cbn. f_equal. apply IH; auto.
  - intros n v IHv c1 IH1 c2 IH2 m xi zeta H. cbn. f_equal;
      [apply IHv; auto|apply IH1; apply (@up_ren_eq n m xi zeta H)|apply IH2; apply (@up_ren_eq n m xi zeta H)].
  - intros n v IHv c IH m xi zeta H. cbn. f_equal;
      [apply IHv; auto|apply IH; apply (@up2_ren_eq n m xi zeta H)].
Qed.

Lemma up_renv n m (xi: ren n m) :
  forall (j : fin (S n)), (up_value_value (renv xi)) j = renv (up_ren xi) j.
Proof.
  intros [j|].
  - unfold up_value_value, scons, funcomp, renv. cbn. reflexivity.
  - unfold up_value_value, scons, renv. cbn. reflexivity.
Qed.

Lemma up2_renv n m (xi: ren n m) :
  forall (j : fin (S (S n))),
    (up_value_value (up_value_value (renv xi))) j = renv (up_ren (up_ren xi)) j.
Proof.
  intros j.
  transitivity ((up_value_value (renv (up_ren xi))) j).
  - apply (@up_subst_eq (S n) (S m) (up_value_value (renv xi)) (renv (up_ren xi)) (up_renv xi)).
  - apply up_renv.
Qed.

Lemma ren_is_subst :
  forall n,
  (forall (v:value n) m (xi: fin n -> fin m), v⟨xi⟩ = v[renv xi]) /\
  (forall (c:comp n) m (xi: fin n -> fin m), c⟨xi⟩ = c[renv xi]).
Proof.
  apply (mutind_val_comp
    (fun n (v:value n) => forall m (xi: fin n -> fin m), v⟨xi⟩ = v[renv xi])
    (fun n (c:comp n) => forall m (xi: fin n -> fin m), c⟨xi⟩ = c[renv xi])).
  - intros n i m xi. reflexivity.
  - intros n m xi. reflexivity.
  - intros n v1 IH1 v2 IH2 m xi. cbn. f_equal; [apply IH1|apply IH2].
  - intros n b v IH m xi. cbn. f_equal. apply IH.
  - intros n c IH m xi. cbn. f_equal. apply IH.
  - intros n m xi. reflexivity.
  - intros n v IH m xi. cbn. f_equal. apply IH.
  - intros n c IH m xi. cbn. f_equal.
    transitivity (c[renv (up_ren xi)]).
    + apply IH.
    + apply (proj2 (subst_ext (S n))). intros j. symmetry. apply up_renv.
  - intros n c IH1 v IH2 m xi. cbn. f_equal; [apply IH1|apply IH2].
  - intros n c1 IH1 c2 IH2 m xi. cbn. f_equal; [apply IH1|apply IH2].
  - intros n v IH m xi. cbn. f_equal. apply IH.
  - intros n c1 IH1 c2 IH2 m xi. cbn. f_equal; [apply IH1|].
    transitivity (c2[renv (up_ren xi)]).
    + apply IH2.
    + apply (proj2 (subst_ext (S n))). intros j. symmetry. apply up_renv.
  - intros n b c IH m xi. cbn. f_equal. apply IH.
  - intros n v IH m xi. cbn. f_equal. apply IH.
  - intros n v IHv c1 IH1 c2 IH2 m xi. cbn. f_equal; [apply IHv| |].
    + transitivity (c1[renv (up_ren xi)]).
      * apply IH1.
      * apply (proj2 (subst_ext (S n))). intros j. symmetry. apply up_renv.
    + transitivity (c2[renv (up_ren xi)]).
      * apply IH2.
      * apply (proj2 (subst_ext (S n))). intros j. symmetry. apply up_renv.
  - intros n v IHv c IH m xi. cbn. f_equal; [apply IHv|].
    transitivity (c[renv (up_ren (up_ren xi))]).
    + apply IH.
    + apply (proj2 (subst_ext (S (S n)))). intros j. symmetry. apply up2_renv.
Qed.

Lemma ren_subst :
  forall n,
  (forall (v:value n) m (xi: ren n m) k (s: fin m -> value k),
      (v⟨xi⟩)[s] = v[rscomp xi s]) /\
  (forall (c:comp n) m (xi: ren n m) k (s: fin m -> value k),
      (c⟨xi⟩)[s] = c[rscomp xi s]).
Proof.
  apply (mutind_val_comp
    (fun n (v:value n) => forall m (xi: ren n m) k (s: fin m -> value k), (v⟨xi⟩)[s] = v[rscomp xi s])
    (fun n (c:comp n) => forall m (xi: ren n m) k (s: fin m -> value k), (c⟨xi⟩)[s] = c[rscomp xi s])).
  - intros n i m xi k s. reflexivity.
  - intros n m xi k s. reflexivity.
  - intros n v1 IH1 v2 IH2 m xi k s. cbn. f_equal; [apply IH1|apply IH2].
  - intros n b v IH m xi k s. cbn. f_equal. apply IH.
  - intros n c IH m xi k s. cbn. f_equal. apply IH.
  - intros n m xi k s. reflexivity.
  - intros n v IH m xi k s. cbn. f_equal. apply IH.
  - intros n c IH m xi k s. cbn. f_equal.
    transitivity (c[rscomp (up_ren xi) (up_value_value s)]).
    + apply IH.
    + apply (proj2 (subst_ext (S n))). intros j. apply up_rscomp.
  - intros n c IH1 v IH2 m xi k s. cbn. f_equal; [apply IH1|apply IH2].
  - intros n c1 IH1 c2 IH2 m xi k s. cbn. f_equal; [apply IH1|apply IH2].
  - intros n v IH m xi k s. cbn. f_equal. apply IH.
  - intros n c1 IH1 c2 IH2 m xi k s. cbn. f_equal; [apply IH1|].
    transitivity (c2[rscomp (up_ren xi) (up_value_value s)]).
    + apply IH2.
    + apply (proj2 (subst_ext (S n))). intros j. apply up_rscomp.
  - intros n b c IH m xi k s. cbn. f_equal. apply IH.
  - intros n v IH m xi k s. cbn. f_equal. apply IH.
  - intros n v IHv c1 IH1 c2 IH2 m xi k s. cbn. f_equal; [apply IHv| |].
    + transitivity (c1[rscomp (up_ren xi) (up_value_value s)]).
      * apply IH1.
      * apply (proj2 (subst_ext (S n))). intros j. apply up_rscomp.
    + transitivity (c2[rscomp (up_ren xi) (up_value_value s)]).
      * apply IH2.
      * apply (proj2 (subst_ext (S n))). intros j. apply up_rscomp.
  - intros n v IHv c IH m xi k s. cbn. f_equal; [apply IHv|].
    transitivity (c[rscomp (up_ren (up_ren xi)) (up_value_value (up_value_value s))]).
    + apply IH.
    + apply (proj2 (subst_ext (S (S n)))). intros j. apply up2_rscomp.
Qed.

Lemma ren_ren :
  forall n,
  (forall (v:value n) m (xi: ren n m) k (zeta: ren m k),
      (v⟨xi⟩)⟨zeta⟩ = v⟨fun i => zeta (xi i)⟩) /\
  (forall (c:comp n) m (xi: ren n m) k (zeta: ren m k),
      (c⟨xi⟩)⟨zeta⟩ = c⟨fun i => zeta (xi i)⟩).
Proof.
  apply (mutind_val_comp
    (fun n (v:value n) => forall m (xi: ren n m) k (zeta: ren m k), (v⟨xi⟩)⟨zeta⟩ = v⟨fun i => zeta (xi i)⟩)
    (fun n (c:comp n) => forall m (xi: ren n m) k (zeta: ren m k), (c⟨xi⟩)⟨zeta⟩ = c⟨fun i => zeta (xi i)⟩)).
  - intros n i m xi k zeta. cbn. reflexivity.
  - intros n m xi k zeta. reflexivity.
  - intros n v1 IH1 v2 IH2 m xi k zeta. cbn. f_equal; [apply IH1|apply IH2].
  - intros n b v IH m xi k zeta. cbn. f_equal. apply IH.
  - intros n c IH m xi k zeta. cbn. f_equal. apply IH.
  - intros n m xi k zeta. reflexivity.
  - intros n v IH m xi k zeta. cbn. f_equal. apply IH.
  - intros n c IH m xi k zeta. cbn. f_equal.
    transitivity (c⟨fun j => up_ren zeta (up_ren xi j)⟩).
    + apply IH.
    + apply (proj2 (ren_ext (S n))). intros j. apply up_ren_comp.
  - intros n c IH1 v IH2 m xi k zeta. cbn. f_equal; [apply IH1|apply IH2].
  - intros n c1 IH1 c2 IH2 m xi k zeta. cbn. f_equal; [apply IH1|apply IH2].
  - intros n v IH m xi k zeta. cbn. f_equal. apply IH.
  - intros n c1 IH1 c2 IH2 m xi k zeta. cbn. f_equal; [apply IH1|].
    transitivity (c2⟨fun j => up_ren zeta (up_ren xi j)⟩).
    + apply IH2.
    + apply (proj2 (ren_ext (S n))). intros j. apply up_ren_comp.
  - intros n b c IH m xi k zeta. cbn. f_equal. apply IH.
  - intros n v IH m xi k zeta. cbn. f_equal. apply IH.
  - intros n v IHv c1 IH1 c2 IH2 m xi k zeta. cbn. f_equal; [apply IHv| |].
    + transitivity (c1⟨fun j => up_ren zeta (up_ren xi j)⟩).
      * apply IH1.
      * apply (proj2 (ren_ext (S n))). intros j. apply up_ren_comp.
    + transitivity (c2⟨fun j => up_ren zeta (up_ren xi j)⟩).
      * apply IH2.
      * apply (proj2 (ren_ext (S n))). intros j. apply up_ren_comp.
  - intros n v IHv c IH m xi k zeta. cbn. f_equal; [apply IHv|].
    transitivity (c⟨fun j => up_ren (up_ren zeta) (up_ren (up_ren xi) j)⟩).
    + apply IH.
    + apply (proj2 (ren_ext (S (S n)))). intros j. apply up2_ren_comp.
Qed.

Lemma up_sren n m k (s: fin n -> value m) (xi: ren m k) :
  forall (j : fin (S n)),
    ((up_value_value s) j)⟨up_ren xi⟩ = (up_value_value (sren s xi)) j.
Proof.
  intros [j|].
  - unfold up_value_value, scons, funcomp, sren. cbn.
    transitivity ((s j)⟨fun l => up_ren xi (shift l)⟩).
    + exact (proj1 (ren_ren m) (s j) (S m) shift (S k) (up_ren xi)).
    + transitivity ((s j)⟨fun l => shift (xi l)⟩).
      * apply (proj1 (ren_ext m)). intros l. cbn. reflexivity.
      * symmetry. exact (proj1 (ren_ren m) (s j) k xi (S k) shift).
  - unfold up_value_value, scons, sren. cbn. reflexivity.
Qed.

Lemma up2_sren n m k (s: fin n -> value m) (xi: ren m k) :
  forall (j : fin (S (S n))),
    ((up_value_value (up_value_value s)) j)⟨up_ren (up_ren xi)⟩
    = (up_value_value (up_value_value (sren s xi))) j.
Proof.
  intros j.
  transitivity ((up_value_value (sren (up_value_value s) (up_ren xi))) j).
  - apply (@up_sren (S n) (S m) (S k) (@up_value_value n m s) (@up_ren m k xi)).
  - apply (@up_subst_eq (S n) (S k) (sren (up_value_value s) (up_ren xi))
        (up_value_value (sren s xi)) (up_sren s xi)).
Qed.

Lemma subst_ren :
  forall n,
  (forall (v:value n) m (s: fin n -> value m) k (xi: ren m k),
      (v[s])⟨xi⟩ = v[sren s xi]) /\
  (forall (c:comp n) m (s: fin n -> value m) k (xi: ren m k),
      (c[s])⟨xi⟩ = c[sren s xi]).
Proof.
  apply (mutind_val_comp
    (fun n (v:value n) => forall m (s: fin n -> value m) k (xi: ren m k), (v[s])⟨xi⟩ = v[sren s xi])
    (fun n (c:comp n) => forall m (s: fin n -> value m) k (xi: ren m k), (c[s])⟨xi⟩ = c[sren s xi])).
  - intros n i m s k xi. reflexivity.
  - intros n m s k xi. reflexivity.
  - intros n v1 IH1 v2 IH2 m s k xi. cbn. f_equal; [apply IH1|apply IH2].
  - intros n b v IH m s k xi. cbn. f_equal. apply IH.
  - intros n c IH m s k xi. cbn. f_equal. apply IH.
  - intros n m s k xi. reflexivity.
  - intros n v IH m s k xi. cbn. f_equal. apply IH.
  - intros n c IH m s k xi. cbn. f_equal.
    transitivity (c[sren (up_value_value s) (up_ren xi)]).
    + apply IH.
    + apply (proj2 (subst_ext (S n))). intros j. apply up_sren.
  - intros n c IH1 v IH2 m s k xi. cbn. f_equal; [apply IH1|apply IH2].
  - intros n c1 IH1 c2 IH2 m s k xi. cbn. f_equal; [apply IH1|apply IH2].
  - intros n v IH m s k xi. cbn. f_equal. apply IH.
  - intros n c1 IH1 c2 IH2 m s k xi. cbn. f_equal; [apply IH1|].
    transitivity (c2[sren (up_value_value s) (up_ren xi)]).
    + apply IH2.
    + apply (proj2 (subst_ext (S n))). intros j. apply up_sren.
  - intros n b c IH m s k xi. cbn. f_equal. apply IH.
  - intros n v IH m s k xi. cbn. f_equal. apply IH.
  - intros n v IHv c1 IH1 c2 IH2 m s k xi. cbn. f_equal; [apply IHv| |].
    + transitivity (c1[sren (up_value_value s) (up_ren xi)]).
      * apply IH1.
      * apply (proj2 (subst_ext (S n))). intros j. apply up_sren.
    + transitivity (c2[sren (up_value_value s) (up_ren xi)]).
      * apply IH2.
      * apply (proj2 (subst_ext (S n))). intros j. apply up_sren.
  - intros n v IHv c IH m s k xi. cbn. f_equal; [apply IHv|].
    transitivity (c[sren (up_value_value (up_value_value s)) (up_ren (up_ren xi))]).
    + apply IH.
    + apply (proj2 (subst_ext (S (S n)))). intros j. apply up2_sren.
Qed.

Lemma up_scomp n m k (s: fin n -> value m) (t: fin m -> value k) :
  forall (j : fin (S n)),
    ((up_value_value s) j)[up_value_value t] = (up_value_value (fun i => (s i)[t])) j.
Proof.
  intros [j|].
  - unfold up_value_value, scons, funcomp. cbn.
    transitivity ((s j)[rscomp shift (up_value_value t)]).
    + apply (proj1 (ren_subst m) (s j) (S m) shift (S k) (up_value_value t)).
    + transitivity ((s j)[sren t shift]).
      * apply (proj1 (subst_ext m)). intros l. unfold rscomp, sren, up_value_value, scons, funcomp. cbn. reflexivity.
      * symmetry. apply (proj1 (subst_ren m) (s j) k t (S k) shift).
  - unfold up_value_value, scons. cbn. reflexivity.
Qed.

Lemma up2_scomp n m k (s: fin n -> value m) (t: fin m -> value k) :
  forall (j : fin (S (S n))),
    ((up_value_value (up_value_value s)) j)[up_value_value (up_value_value t)]
    = (up_value_value (up_value_value (fun i => (s i)[t]))) j.
Proof.
  intros j.
  transitivity ((up_value_value (fun i => ((up_value_value s) i)[up_value_value t])) j).
  - apply (@up_scomp (S n) (S m) (S k) (@up_value_value n m s) (@up_value_value m k t)).
  - apply (@up_subst_eq (S n) (S k) (fun i => ((up_value_value s) i)[up_value_value t])
        (up_value_value (fun i => (s i)[t])) (up_scomp s t)).
Qed.

Lemma subst_subst :
  forall n,
  (forall (v:value n) m (s: fin n -> value m) k (t: fin m -> value k),
      (v[s])[t] = v[scomp s t]) /\
  (forall (c:comp n) m (s: fin n -> value m) k (t: fin m -> value k),
      (c[s])[t] = c[scomp s t]).
Proof.
  apply (mutind_val_comp
    (fun n (v:value n) => forall m (s: fin n -> value m) k (t: fin m -> value k), (v[s])[t] = v[scomp s t])
    (fun n (c:comp n) => forall m (s: fin n -> value m) k (t: fin m -> value k), (c[s])[t] = c[scomp s t])).
  - intros n i m s k t. reflexivity.
  - intros n m s k t. reflexivity.
  - intros n v1 IH1 v2 IH2 m s k t. cbn. f_equal; [apply IH1|apply IH2].
  - intros n b v IH m s k t. cbn. f_equal. apply IH.
  - intros n c IH m s k t. cbn. f_equal. apply IH.
  - intros n m s k t. reflexivity.
  - intros n v IH m s k t. cbn. f_equal. apply IH.
  - intros n c IH m s k t. cbn. f_equal.
    transitivity (c[scomp (up_value_value s) (up_value_value t)]).
    + apply IH.
    + apply (proj2 (subst_ext (S n))). intros j. apply up_scomp.
  - intros n c IH1 v IH2 m s k t. cbn. f_equal; [apply IH1|apply IH2].
  - intros n c1 IH1 c2 IH2 m s k t. cbn. f_equal; [apply IH1|apply IH2].
  - intros n v IH m s k t. cbn. f_equal. apply IH.
  - intros n c1 IH1 c2 IH2 m s k t. cbn. f_equal; [apply IH1|].
    transitivity (c2[scomp (up_value_value s) (up_value_value t)]).
    + apply IH2.
    + apply (proj2 (subst_ext (S n))). intros j. apply up_scomp.
  - intros n b c IH m s k t. cbn. f_equal. apply IH.
  - intros n v IH m s k t. cbn. f_equal. apply IH.
  - intros n v IHv c1 IH1 c2 IH2 m s k t. cbn. f_equal; [apply IHv| |].
    + transitivity (c1[scomp (up_value_value s) (up_value_value t)]).
      * apply IH1.
      * apply (proj2 (subst_ext (S n))). intros j. apply up_scomp.
    + transitivity (c2[scomp (up_value_value s) (up_value_value t)]).
      * apply IH2.
      * apply (proj2 (subst_ext (S n))). intros j. apply up_scomp.
  - intros n v IHv c IH m s k t. cbn. f_equal; [apply IHv|].
    transitivity (c[scomp (up_value_value (up_value_value s)) (up_value_value (up_value_value t))]).
    + apply IH.
    + apply (proj2 (subst_ext (S (S n)))). intros j. apply up2_scomp.
Qed.

Lemma up_idsv n :
  forall (j : fin (S n)), (up_value_value (@idsv n)) j = @idsv (S n) j.
Proof.
  intros [j|].
  - unfold up_value_value, scons, funcomp, idsv. cbn. reflexivity.
  - unfold up_value_value, scons, idsv. cbn. reflexivity.
Qed.

Lemma up2_idsv n :
  forall (j : fin (S (S n))), (up_value_value (up_value_value (@idsv n))) j = @idsv (S (S n)) j.
Proof.
  intros j.
  transitivity ((up_value_value (@idsv (S n))) j).
  - apply (@up_subst_eq (S n) (S n) (up_value_value (@idsv n)) (@idsv (S n)) (@up_idsv n)).
  - apply up_idsv.
Qed.

Lemma subst_ids n : (forall (v:value n), v[idsv] = v) /\ (forall (c:comp n), c[idsv] = c).
Proof.
  apply (mutind_val_comp (fun n (v:value n) => v[idsv] = v) (fun n (c:comp n) => c[idsv] = c)).
  - intros nv i. cbn. reflexivity.
  - intros nv. reflexivity.
  - intros nv v1 IH1 v2 IH2. cbn. f_equal; [apply IH1|apply IH2].
  - intros nv b v IH. cbn. f_equal. apply IH.
  - intros nv c IH. cbn. f_equal. apply IH.
  - intros nv. reflexivity.
  - intros nv v IH. cbn. f_equal. apply IH.
  - intros nv c IH. cbn. f_equal.
    transitivity (c[idsv]).
    + apply (proj2 (subst_ext (S nv))). intros j. apply up_idsv.
    + apply IH.
  - intros nv c IH1 v IH2. cbn. f_equal; [apply IH1|apply IH2].
  - intros nv c1 IH1 c2 IH2. cbn. f_equal; [apply IH1|apply IH2].
  - intros nv v IH. cbn. f_equal. apply IH.
  - intros nv c1 IH1 c2 IH2. cbn. f_equal; [apply IH1|].
    transitivity (c2[idsv]).
    + apply (proj2 (subst_ext (S nv))). intros j. apply up_idsv.
    + apply IH2.
  - intros nv b c IH. cbn. f_equal. apply IH.
  - intros nv v IH. cbn. f_equal. apply IH.
  - intros nv v IHv c1 IH1 c2 IH2. cbn. f_equal; [apply IHv| |].
    + transitivity (c1[idsv]).
      * apply (proj2 (subst_ext (S nv))). intros j. apply up_idsv.
      * apply IH1.
    + transitivity (c2[idsv]).
      * apply (proj2 (subst_ext (S nv))). intros j. apply up_idsv.
      * apply IH2.
  - intros nv v IHv c IH. cbn. f_equal; [apply IHv|].
    transitivity (c[idsv]).
    + apply (proj2 (subst_ext (S (S nv)))). intros j. apply up2_idsv.
    + apply IH.
Qed.



(** Beta-substitution commutation helpers *)

Lemma subst_beta_subst n m (c:comp (S n)) (v:value n) (sigma: fin n -> value m) :
  (c[up_value_value sigma])[(v[sigma])..] = (c[v..])[sigma].
Proof.
  rewrite (proj2 (subst_subst (S n)) c (S m) (up_value_value sigma) m ((v[sigma])..)).
  rewrite (proj2 (subst_subst (S n)) c n (v..) m sigma).
  apply (proj2 (subst_ext (S n))). intros [j|].
  - unfold scomp, up_value_value, scons, funcomp, idsv. cbn.
    transitivity ((sigma j)[@idsv m]).
    + transitivity ((sigma j)[rscomp shift ((v[sigma])..)]).
      * apply (proj1 (ren_subst m) (sigma j) (S m) shift m ((v[sigma])..)).
      * apply (proj1 (subst_ext m)). intros l. unfold rscomp, idsv. cbn. reflexivity.
    + apply (proj1 (subst_ids m)).
  - unfold scomp, up_value_value, scons, funcomp, idsv. cbn. reflexivity.
Qed.

Lemma subst_beta2_subst n m (c:comp (S (S n))) (v1 v2:value n) (sigma: fin n -> value m) :
  (c[up_value_value (up_value_value sigma)])[v2[sigma],(v1[sigma])..] = (c[v2,v1..])[sigma].
Proof.
  rewrite (proj2 (subst_subst (S (S n))) c (S (S m)) (up_value_value (up_value_value sigma)) m
             (v2[sigma],(v1[sigma])..)).
  rewrite (proj2 (subst_subst (S (S n))) c n (v2,v1..) m sigma).
  apply (proj2 (subst_ext (S (S n)))). intros j. destruct j as [j|].
  - destruct j as [j|]; cbn.
    + transitivity ((ren_value shift (sigma j))[rscomp shift (v2[sigma],(v1[sigma])..)]).
      * apply (proj1 (ren_subst (S m)) (ren_value shift (sigma j)) (S (S m)) shift m (v2[sigma],(v1[sigma])..)).
      * transitivity ((sigma j)[rscomp shift (rscomp shift (v2[sigma],(v1[sigma])..))]).
        -- apply (proj1 (ren_subst m) (sigma j) (S m) shift m (rscomp shift (v2[sigma],(v1[sigma])..))).
        -- transitivity ((sigma j)[@idsv m]).
           ++ apply (proj1 (subst_ext m)). intros l. unfold rscomp, idsv, scons. cbn. reflexivity.
           ++ apply (proj1 (subst_ids m)).
    + unfold scomp, up_value_value, scons, funcomp, idsv. cbn. reflexivity.
  - unfold scomp, up_value_value, scons, funcomp, idsv. cbn. reflexivity.
Qed.

Lemma subst_beta_ren n m (c:comp (S n)) (v:value n) (xi: ren n m) :
  (c⟨up_ren xi⟩)[(v⟨xi⟩)..] = (c[v..])⟨xi⟩.
Proof.
  assert (Hc : c⟨up_ren xi⟩ = c[up_value_value (renv xi)]).
  { rewrite (proj2 (ren_is_subst (S n)) c (S m) (up_ren xi)).
    apply (proj2 (subst_ext (S n))). intros j. symmetry. apply up_renv. }
  assert (Hv : v⟨xi⟩ = v[renv xi]) by (apply (proj1 (ren_is_subst n))).
  rewrite Hc, Hv.
  rewrite (@subst_beta_subst n m c v (renv xi)).
  rewrite (proj2 (ren_is_subst n) (c[v..]) m xi).
  reflexivity.
Qed.

Lemma subst_beta2_ren n m (c:comp (S (S n))) (v1 v2:value n) (xi: ren n m) :
  (c⟨up_ren (up_ren xi)⟩)[v2⟨xi⟩,(v1⟨xi⟩)..] = (c[v2,v1..])⟨xi⟩.
Proof.
  assert (Hc : c⟨up_ren (up_ren xi)⟩ = c[up_value_value (up_value_value (renv xi))]).
  { rewrite (proj2 (ren_is_subst (S (S n))) c (S (S m)) (up_ren (up_ren xi))).
    apply (proj2 (subst_ext (S (S n)))). intros j. symmetry. apply up2_renv. }
  assert (Hv1 : v1⟨xi⟩ = v1[renv xi]) by (apply (proj1 (ren_is_subst n))).
  assert (Hv2 : v2⟨xi⟩ = v2[renv xi]) by (apply (proj1 (ren_is_subst n))).
  rewrite Hc, Hv1, Hv2.
  rewrite (@subst_beta2_subst n m c v1 v2 (renv xi)).
  rewrite (proj2 (ren_is_subst n) (c[v2,v1..]) m xi).
  reflexivity.
Qed.

Lemma pstep_subst n (c c':comp n) (H: c ≽ c') :
  forall m (sigma: fin n -> value m), c[sigma] ≽ c'[sigma].
Proof.
  induction H; intros m sigma; cbn.
  - apply pstepForce.
  - apply pstepApp. rewrite subst_beta_subst. rewrite H. reflexivity.
  - apply pstepProj. subst c. destruct b; cbn; reflexivity.
  - apply pstepLetin. rewrite subst_beta_subst. rewrite H. reflexivity.
  - apply pstepCaseS. destruct b; cbn.
    + change ((c1[up_value_value sigma])[(v[sigma])..] = c[sigma]).
      rewrite (@subst_beta_subst n m c1 v sigma).
      rewrite H. reflexivity.
    + change ((c2[up_value_value sigma])[(v[sigma])..] = c[sigma]).
      rewrite (@subst_beta_subst n m c2 v sigma).
      rewrite H. reflexivity.
  - apply pstepCaseP.
    change ((c[up_value_value (up_value_value sigma)])[v2[sigma],(v1[sigma])..] = c'[sigma]).
    rewrite (@subst_beta2_subst n m c v1 v2 sigma).
    rewrite H. reflexivity.
Qed.

Lemma sstep_subst :
  forall n,
  (forall (c c':comp n), c ↪ c' -> forall m (sigma: fin n -> value m), c[sigma] ↪ c'[sigma]) /\
  (forall (v v':value n), v ↪ᵥ v' -> forall m (sigma: fin n -> value m), v[sigma] ↪ᵥ v'[sigma]).
Proof.
  apply (mutind_sstep
    (fun n (v v':value n) _ => forall m (sigma: fin n -> value m), v[sigma] ↪ᵥ v'[sigma])
    (fun n (c c':comp n) _ => forall m (sigma: fin n -> value m), c[sigma] ↪ c'[sigma])).
  - intros nv v1 v1' v2 s IH m sigma. cbn. apply sstepValuePairL. apply IH.
  - intros nv v1 v2 v2' s IH m sigma. cbn. apply sstepValuePairR. apply IH.
  - intros nv b v v' s IH m sigma. cbn. apply sstepValueInj. apply IH.
  - intros nv c c' s IH m sigma. cbn. apply sstepValueThunk. apply IH.
  - intros nv v v' s IH m sigma. cbn. apply sstepForce. apply IH.
  - intros nv c c' s IH m sigma. cbn. apply sstepLambda. apply IH.
  - intros nv c c' v s IH m sigma. cbn. apply sstepAppL. apply IH.
  - intros nv c v v' s IH m sigma. cbn. apply sstepAppR. apply IH.
  - intros nv c1 c1' c2 s IH m sigma. cbn. apply sstepTupleL. apply IH.
  - intros nv c1 c2 c2' s IH m sigma. cbn. apply sstepTupleR. apply IH.
  - intros nv v v' s IH m sigma. cbn. apply sstepRet. apply IH.
  - intros nv c1 c1' c2 s IH m sigma. cbn. apply sstepLetinL. apply IH.
  - intros nv c1 c2 c2' s IH m sigma. cbn. apply sstepLetinR. apply IH.
  - intros nv c c' b s IH m sigma. cbn. apply sstepProj. apply IH.
  - intros nv v v' s IH m sigma. cbn. apply sstepCaseZ. apply IH.
  - intros nv v v' c1 c2 s IH m sigma. cbn. apply sstepCaseSV. apply IH.
  - intros nv v c1 c1' c2 s IH m sigma. cbn. apply sstepCaseSL. apply IH.
  - intros nv v c1 c2 c2' s IH m sigma. cbn. apply sstepCaseSR. apply IH.
  - intros nv v v' c s IH m sigma. cbn. apply sstepCasePV. apply IH.
  - intros nv v c c' s IH m sigma. cbn. apply sstepCasePC. apply IH.
  - intros nv c c' p m sigma. cbn. apply sstepPrimitive. apply pstep_subst. apply p.
Qed.

Lemma sstep_ren n (c c':comp n) (H: c ↪ c') :
  forall m (xi: ren n m), c⟨xi⟩ ↪ c'⟨xi⟩.
Proof.
  intros m xi.
  rewrite (proj2 (ren_is_subst n) c m xi).
  rewrite (proj2 (ren_is_subst n) c' m xi).
  apply (proj1 (sstep_subst n) c c' H m (renv xi)).
Qed.

Lemma sstep_value_ren n (v v':value n) (H: v ↪ᵥ v') :
  forall m (xi: ren n m), v⟨xi⟩ ↪ᵥ v'⟨xi⟩.
Proof.
  intros m xi.
  rewrite (proj1 (ren_is_subst n) v m xi).
  rewrite (proj1 (ren_is_subst n) v' m xi).
  apply (proj2 (sstep_subst n) v v' H m (renv xi)).
Qed.

Lemma star_sstep_subst n (c c':comp n) (H: star sstep c c') :
  forall m (sigma: fin n -> value m), star sstep (c[sigma]) (c'[sigma]).
Proof.
  induction H as [| x x' y step rest IH]; intros m sigma.
  - apply starRefl.
  - eapply starStep.
    + apply (proj1 (sstep_subst n) x x' step m sigma).
    + apply IH.
Qed.

Lemma star_sstep_value_subst n (v v':value n) (H: star sstep_value v v') :
  forall m (sigma: fin n -> value m), star sstep_value (v[sigma]) (v'[sigma]).
Proof.
  induction H as [| x x' y step rest IH]; intros m sigma.
  - apply starRefl.
  - eapply starStep.
    + apply (proj2 (sstep_subst n) x x' step m sigma).
    + apply IH.
Qed.

Lemma star_sstep_ren n (c c':comp n) (H: star sstep c c') :
  forall m (xi: ren n m), star sstep (c⟨xi⟩) (c'⟨xi⟩).
Proof.
  induction H as [| x x' y step rest IH]; intros m xi.
  - apply starRefl.
  - eapply starStep.
    + apply (sstep_ren step).
    + apply IH.
Qed.

Lemma star_sstep_value_ren n (v v':value n) (H: star sstep_value v v') :
  forall m (xi: ren n m), star sstep_value (v⟨xi⟩) (v'⟨xi⟩).
Proof.
  induction H as [| x x' y step rest IH]; intros m xi.
  - apply starRefl.
  - eapply starStep.
    + apply (sstep_value_ren step).
    + apply IH.
Qed.

Lemma ren_val_thunk {n m} (xi: ren n m) (v:value n) (c:comp m) :
  v⟨xi⟩ = thunk c -> exists c', v = thunk c' /\ c = c'⟨xi⟩.
Proof.
  destruct v; cbn; intros H; try discriminate; injection H; intros; subst; eauto.
Qed.

Lemma ren_val_inj {n m} (xi: ren n m) (v:value n) b (w:value m) :
  v⟨xi⟩ = inj b w -> exists w', v = inj b w' /\ w = w'⟨xi⟩.
Proof.
  destruct v; cbn; intros H; try discriminate; injection H; intros; subst; eauto.
Qed.

Lemma ren_val_pair {n m} (xi: ren n m) (v:value n) (a b:value m) :
  v⟨xi⟩ = pair a b -> exists a' b', v = pair a' b' /\ a = a'⟨xi⟩ /\ b = b'⟨xi⟩.
Proof.
  destruct v; cbn; intros H; try discriminate; injection H; intros; subst; eauto.
Qed.

Lemma ren_comp_lambda {n m} (xi: ren n m) (c:comp n) (b:comp (S m)) :
  c⟨xi⟩ = lambda b -> exists b', c = lambda b' /\ b = b'⟨up_ren xi⟩.
Proof.
  destruct c; cbn; intros H; try discriminate; injection H; intros; subst; eauto.
Qed.

Lemma ren_comp_ret {n m} (xi: ren n m) (c:comp n) (v:value m) :
  c⟨xi⟩ = ret v -> exists v', c = ret v' /\ v = v'⟨xi⟩.
Proof.
  destruct c; cbn; intros H; try discriminate; injection H; intros; subst; eauto.
Qed.

Lemma ren_comp_tuple {n m} (xi: ren n m) (c:comp n) (a b:comp m) :
  c⟨xi⟩ = tuple a b -> exists a' b', c = tuple a' b' /\ a = a'⟨xi⟩ /\ b = b'⟨xi⟩.
Proof.
  destruct c; cbn; intros H; try discriminate; injection H; intros; subst; eauto.
Qed.
Ltac inv_v IH k :=
  match goal with
  | Hv : @sstep_value _ ?x ?y |- _ =>
      let w := fresh "w" in let Hrest := fresh "Hrest" in
      let Hw := fresh "Hw" in let He := fresh "He" in
      destruct (IH y Hv) as [w Hrest]; destruct Hrest as [Hw He];
      subst; k w Hw
  end.

Ltac inv_c IH k :=
  match goal with
  | Hv : @sstep _ ?x ?y |- _ =>
      let w := fresh "w" in let Hrest := fresh "Hrest" in
      let Hw := fresh "Hw" in let He := fresh "He" in
      destruct (IH y Hv) as [w Hrest]; destruct Hrest as [Hw He];
      subst; k w Hw
  end.

Lemma sstep_ren_inv :
  forall n,
  (forall (v:value n), forall m (xi: ren n m) d,
      v⟨xi⟩ ↪ᵥ d -> exists v', v ↪ᵥ v' /\ d = v'⟨xi⟩) /\
  (forall (c:comp n), forall m (xi: ren n m) d,
      c⟨xi⟩ ↪ d -> exists c', c ↪ c' /\ d = c'⟨xi⟩).
Proof.
  apply (mutind_val_comp
    (fun n (v:value n) => forall m (xi: ren n m) d, v⟨xi⟩ ↪ᵥ d -> exists v', v ↪ᵥ v' /\ d = v'⟨xi⟩)
    (fun n (c:comp n) => forall m (xi: ren n m) d, c⟨xi⟩ ↪ d -> exists c', c ↪ c' /\ d = c'⟨xi⟩)).
  - intros nv i m xi d H. cbn in H. inversion H.
  - intros nv m xi d H. cbn in H. inversion H.
  - intros nv v1 IH1 v2 IH2 m xi d H. cbn in H. inversion H; subst; try clear H.
    + inv_v (IH1 m xi) ltac:(fun w Hw => exists (pair w v2); split;
        [apply sstepValuePairL; exact Hw | cbn; reflexivity]).
    + inv_v (IH2 m xi) ltac:(fun w Hw => exists (pair v1 w); split;
        [apply sstepValuePairR; exact Hw | cbn; reflexivity]).
  - intros nv b v IH m xi d H. cbn in H. inversion H; subst; try clear H.
    inv_v (IH m xi) ltac:(fun w Hw => exists (inj b w); split;
      [apply sstepValueInj; exact Hw | cbn; reflexivity]).
  - intros nv c IH m xi d H. cbn in H. inversion H; subst; try clear H.
    inv_c (IH m xi) ltac:(fun w Hw => exists (thunk w); split;
      [apply sstepValueThunk; exact Hw | cbn; reflexivity]).
  - intros nv m xi d H. cbn in H. inversion H; subst;
      try (match goal with Hp : @pstep ?a ?b ?c |- _ => inversion Hp end).
  - intros nv v IH m xi d H. cbn in H. inversion H; subst; try clear H.
    + inv_v (IH m xi) ltac:(fun w Hw => exists (force w); split;
        [apply sstepForce; exact Hw | cbn; reflexivity]).
    + match goal with Hp : @pstep ?a ?b ?c |- _ => inversion Hp; subst; try clear Hp end.
      match goal with
      | Heq : thunk ?dd = _ |- _ =>
          change (thunk dd = v⟨xi⟩) in Heq; symmetry in Heq;
          destruct (ren_val_thunk xi v Heq) as [cc Hrest];
          destruct Hrest as [Hv Hc]; subst
      | Heq : _ = thunk ?dd |- _ =>
          change (v⟨xi⟩ = thunk dd) in Heq;
          destruct (ren_val_thunk xi v Heq) as [cc Hrest];
          destruct Hrest as [Hv Hc]; subst
      end.
      exists cc. split; [apply sstepPrimitive; apply pstepForce | reflexivity].
  - intros nv c IH m xi d H. cbn in H. inversion H; subst; try clear H.
    inv_c (IH (S m) (up_ren xi)) ltac:(fun w Hw => exists (lambda w); split;
      [apply sstepLambda; exact Hw | cbn; reflexivity]).
    + match goal with Hp : @pstep ?a ?b ?c |- _ => inversion Hp end.
  - intros nv c IH1 v IH2 m xi d H. cbn in H. inversion H; subst; try clear H.
    + inv_c (IH1 m xi) ltac:(fun w Hw => exists (w v); split;
        [apply sstepAppL; exact Hw | cbn; reflexivity]).
    + inv_v (IH2 m xi) ltac:(fun w Hw => exists (c w); split;
        [apply sstepAppR; exact Hw | cbn; reflexivity]).
    + match goal with Hp : @pstep ?a ?b ?c |- _ => inversion Hp; subst; try clear Hp end.
      match goal with
      | Heq : lambda ?bb = _ |- _ =>
          change (lambda bb = c⟨xi⟩) in Heq; symmetry in Heq;
          destruct (ren_comp_lambda xi c Heq) as [b0 Hrest];
          destruct Hrest as [Hc Hb]; subst
      | Heq : _ = lambda ?bb |- _ =>
          change (c⟨xi⟩ = lambda bb) in Heq;
          destruct (ren_comp_lambda xi c Heq) as [b0 Hrest];
          destruct Hrest as [Hc Hb]; subst
      end.
      exists (b0[v..]). split.
      * apply sstepPrimitive; apply pstepApp; reflexivity.
      * rewrite <- (@subst_beta_ren nv m b0 v xi). reflexivity.
  - intros nv c1 IH1 c2 IH2 m xi d H. cbn in H. inversion H; subst; try clear H.
    + inv_c (IH1 m xi) ltac:(fun w Hw => exists (tuple w c2); split;
        [apply sstepTupleL; exact Hw | cbn; reflexivity]).
    + inv_c (IH2 m xi) ltac:(fun w Hw => exists (tuple c1 w); split;
        [apply sstepTupleR; exact Hw | cbn; reflexivity]).
    + match goal with Hp : @pstep ?a ?b ?c |- _ => inversion Hp end.
  - intros nv v IH m xi d H. cbn in H. inversion H; subst; try clear H.
    inv_v (IH m xi) ltac:(fun w Hw => exists (ret w); split;
      [apply sstepRet; exact Hw | cbn; reflexivity]).
    + match goal with Hp : @pstep ?a ?b ?c |- _ => inversion Hp end.
  - intros nv c1 IH1 c2 IH2 m xi d H. cbn in H. inversion H; subst; try clear H.
    + inv_c (IH1 m xi) ltac:(fun w Hw => exists (letin w c2); split;
        [apply sstepLetinL; exact Hw | cbn; reflexivity]).
    + inv_c (IH2 (S m) (up_ren xi)) ltac:(fun w Hw => exists (letin c1 w); split;
        [apply sstepLetinR; exact Hw | cbn; reflexivity]).
    + match goal with Hp : @pstep ?a ?b ?c |- _ => inversion Hp; subst; try clear Hp end.
      match goal with
      | Heq : ret ?vv = _ |- _ =>
          change (ret vv = c1⟨xi⟩) in Heq; symmetry in Heq;
          destruct (ren_comp_ret xi c1 Heq) as [v0 Hrest];
          destruct Hrest as [Hc Hv]; subst
      | Heq : _ = ret ?vv |- _ =>
          change (c1⟨xi⟩ = ret vv) in Heq;
          destruct (ren_comp_ret xi c1 Heq) as [v0 Hrest];
          destruct Hrest as [Hc Hv]; subst
      end.
      exists (c2[v0..]). split.
      * apply sstepPrimitive; apply pstepLetin; reflexivity.
      * rewrite <- (@subst_beta_ren nv m c2 v0 xi). reflexivity.
  - intros nv b c IH m xi d H. cbn in H. inversion H; subst; try clear H.
    + inv_c (IH m xi) ltac:(fun w Hw => exists (proj b w); split;
        [apply sstepProj; exact Hw | cbn; reflexivity]).
    + match goal with Hp : @pstep ?a ?b ?c |- _ => inversion Hp; subst; try clear Hp end.
      match goal with
      | Heq : tuple ?aa ?bb = _ |- _ =>
          change (tuple aa bb = c⟨xi⟩) in Heq; symmetry in Heq;
          destruct (ren_comp_tuple xi c Heq) as [a1 Hrest];
          destruct Hrest as [a2 Hrest2]; destruct Hrest2 as [Hc Hrest3];
          destruct Hrest3 as [Ha Hb]; subst
      | Heq : _ = tuple ?aa ?bb |- _ =>
          change (c⟨xi⟩ = tuple aa bb) in Heq;
          destruct (ren_comp_tuple xi c Heq) as [a1 Hrest];
          destruct Hrest as [a2 Hrest2]; destruct Hrest2 as [Hc Hrest3];
          destruct Hrest3 as [Ha Hb]; subst
      end.
      exists (if b then a1 else a2). split.
      * apply sstepPrimitive; apply pstepProj. destruct b; reflexivity.
      * destruct b; reflexivity.
  - intros nv v IH m xi d H. cbn in H. inversion H; subst; try clear H.
    inv_v (IH m xi) ltac:(fun w Hw => exists (caseZ w); split;
      [apply sstepCaseZ; exact Hw | cbn; reflexivity]).
    + match goal with Hp : @pstep ?a ?b ?c |- _ => inversion Hp end.
  - intros nv v IHv c1 IH1 c2 IH2 m xi d H. cbn in H. inversion H; subst; try clear H.
    + inv_v (IHv m xi) ltac:(fun w Hw => exists (caseS w c1 c2); split;
        [apply sstepCaseSV; exact Hw | cbn; reflexivity]).
    + inv_c (IH1 (S m) (up_ren xi)) ltac:(fun w Hw => exists (caseS v w c2); split;
        [apply sstepCaseSL; exact Hw | cbn; reflexivity]).
    + inv_c (IH2 (S m) (up_ren xi)) ltac:(fun w Hw => exists (caseS v c1 w); split;
        [apply sstepCaseSR; exact Hw | cbn; reflexivity]).
    + match goal with Hp : @pstep ?a ?b ?c |- _ => inversion Hp; subst; try clear Hp end.
      match goal with
      | Heq : inj ?bb ?ww = _ |- _ =>
          change (inj bb ww = v⟨xi⟩) in Heq; symmetry in Heq;
          destruct (ren_val_inj xi v Heq) as [ww0 Hrest];
          destruct Hrest as [Hv Hw]; subst v; subst ww;
          exists ((if bb then c1 else c2)[ww0..]); split;
          [ apply sstepPrimitive; apply pstepCaseS; reflexivity
          | rewrite <- (@subst_beta_ren nv m (if bb then c1 else c2) ww0 xi);
            destruct bb; reflexivity ]
      | Heq : _ = inj ?bb ?ww |- _ =>
          change (v⟨xi⟩ = inj bb ww) in Heq;
          destruct (ren_val_inj xi v Heq) as [ww0 Hrest];
          destruct Hrest as [Hv Hw]; subst v; subst ww;
          exists ((if bb then c1 else c2)[ww0..]); split;
          [ apply sstepPrimitive; apply pstepCaseS; reflexivity
          | rewrite <- (@subst_beta_ren nv m (if bb then c1 else c2) ww0 xi);
            destruct bb; reflexivity ]
      end.
  - intros nv v IHv c IH m xi d H. cbn in H. inversion H; subst; try clear H.
    + inv_v (IHv m xi) ltac:(fun w Hw => exists (caseP w c); split;
        [apply sstepCasePV; exact Hw | cbn; reflexivity]).
    + inv_c (IH (S (S m)) (up_ren (up_ren xi))) ltac:(fun w Hw => exists (caseP v w); split;
        [apply sstepCasePC; exact Hw | cbn; reflexivity]).
    + match goal with Hp : @pstep ?a ?b ?c |- _ => inversion Hp; subst; try clear Hp end.
      change (pair v1 v2 = v⟨xi⟩) in H. symmetry in H.
      destruct (ren_val_pair xi v H) as [v1' Hrest].
      destruct Hrest as [v2' Hrest2]; destruct Hrest2 as [Hv Hrest3];
      destruct Hrest3 as [Ha Hb]; subst v; rewrite Ha, Hb.
      exists (c[v2',v1'..]). split.
      * apply sstepPrimitive; apply pstepCaseP; reflexivity.
      * rewrite <- (@subst_beta2_ren nv m c v1' v2' xi). reflexivity.
Qed.



Lemma star_sstep_ren_inv n m (xi: ren n m) (cc d:comp m) :
  star sstep cc d -> forall c, cc = c⟨xi⟩ -> exists c', star sstep c c' /\ d = c'⟨xi⟩.
Proof.
  induction 1 as [| x x' y step rest IH]; intros c Heq.
  - exists c. split; [apply starRefl | rewrite <- Heq; reflexivity].
  - rewrite Heq in step.
    destruct (proj2 (sstep_ren_inv n) c m xi x' step) as [c1 Hrest1]; destruct Hrest1 as [Hs He].
    destruct (IH c1 He) as [c2 Hrest2]; destruct Hrest2 as [Hstar He2].
    exists c2. split. + eapply starStep; eauto. + exact He2.
Qed.

Lemma star_sstep_value_ren_inv n m (xi: ren n m) (cc d:value m) :
  star sstep_value cc d -> forall c, cc = c⟨xi⟩ -> exists c', star sstep_value c c' /\ d = c'⟨xi⟩.
Proof.
  induction 1 as [| x x' y step rest IH]; intros c Heq.
  - exists c. split; [apply starRefl | rewrite <- Heq; reflexivity].
  - rewrite Heq in step.
    destruct (proj1 (sstep_ren_inv n) c m xi x' step) as [c1 Hrest1]; destruct Hrest1 as [Hs He].
    destruct (IH c1 He) as [c2 Hrest2]; destruct Hrest2 as [Hstar He2].
    exists c2. split. + eapply starStep; eauto. + exact He2.
Qed.

Lemma SN_sstep_ren n (c:comp n) (H: SN sstep c) : forall m (xi: ren n m), SN sstep (c⟨xi⟩).
Proof.
  induction H as [c Hstep IH]; intros m xi.
  apply SNC. intros d Hs.
  destruct (proj2 (sstep_ren_inv n) c m xi d Hs) as [c' Hrest]; destruct Hrest as [Hc' Heq].
  subst d. apply IH. exact Hc'.
Qed.

Lemma SN_sstep_value_ren n (c:value n) (H: SN sstep_value c) : forall m (xi: ren n m), SN sstep_value (c⟨xi⟩).
Proof.
  induction H as [c Hstep IH]; intros m xi.
  apply SNC. intros d Hs.
  destruct (proj1 (sstep_ren_inv n) c m xi d Hs) as [c' Hrest]; destruct Hrest as [Hc' Heq].
  subst d. apply IH. exact Hc'.
Qed.

(** * Reducibility candidates *)

Fixpoint Vv (A: valtype) (n: nat) (v: value n) {struct A} : Prop :=
  match A with
  | zero => SN sstep_value v
  | one => SN sstep_value v
  | U B => SN sstep_value v /\ Vc B (force v)
  | Sigma A1 A2 =>
      SN sstep_value v /\
      match v with
      | inj b w => if b then Vv A1 w else Vv A2 w
      | _ => True
      end
  | cross A1 A2 =>
      SN sstep_value v /\
      match v with
      | pair a b => Vv A1 a /\ Vv A2 b
      | _ => True
      end
  end
with Vc (B: comptype) (n: nat) (c: comp n) {struct B} : Prop :=
  match B with
  | cone => SN sstep c
  | F A => SN sstep c /\ (forall v, star sstep c (ret v) -> Vv A v)
  | Pi B1 B2 => SN sstep c /\
      (forall c1 c2, star sstep c (tuple c1 c2) -> Vc B1 c1 /\ Vc B2 c2)
  | arrow A B => SN sstep c /\
      (forall m (xi: ren n m) body, star sstep (c⟨xi⟩) (lambda body) ->
         forall v, Vv A v -> Vc B (body[v..]))
  end.

Lemma Vv_SN n (A:valtype) (v:value n) : Vv A v -> SN sstep_value v.
Proof. destruct A; cbn; intros H; apply H. Qed.

Lemma SN_inv X (R:X->X->Prop) x (H: SN R x) : forall y, R x y -> SN R y.
Proof. intros y Hy. induction H as [x Hf]. apply Hf. exact Hy. Qed.

Lemma Vc_SN n (B:comptype) (c:comp n) : Vc B c -> SN sstep c.
Proof. destruct B; cbn; intros H; apply H. Qed.

Lemma Vc_step n (B:comptype) (c c':comp n) : Vc B c -> sstep c c' -> Vc B c'.
Proof.
  destruct B; cbn in *; intros H Hs.
  - apply SN_inv with c; auto.
  - destruct H as [Hsn Hcl]. split.
    + apply SN_inv with c; auto.
    + intros vv Hstar. apply (Hcl vv). eapply starStep; eauto.
  - destruct H as [Hsn Hcl]. split.
    + apply SN_inv with c; auto.
    + intros c1 c2 Hstar. apply (Hcl c1 c2). eapply starStep; eauto.
  - destruct H as [Hsn Hcl]. split.
    + apply SN_inv with c; auto.
    + intros m xi body Hstar vv Hv. apply (Hcl m xi body).
      * eapply starStep. apply sstep_ren. exact Hs. exact Hstar.
      * exact Hv.
Qed.

Lemma Vc_star n (B:comptype) (c c':comp n) : Vc B c -> star sstep c c' -> Vc B c'.
Proof.
  intros H S. revert H. induction S as [| x x' y st rest IH]; intros H.
  - exact H.
  - apply IH. eapply Vc_step. exact H. exact st.
Qed.

Ltac finish_sn Hsn := repeat match goal with
  | |- True => exact I
  | |- _ /\ _ => split
  | |- SN sstep_value ?w => eapply SN_inv; [exact Hsn | eassumption]
  end.

Lemma Vv_step : forall (A:valtype), forall n (v v':value n),
  Vv A v -> sstep_value v v' -> Vv A v'.
Proof.
  fix IH 1. intros A. destruct A; intros n v v' H Hs.
  - cbn in *. apply SN_inv with v; auto.
  - cbn in *. apply SN_inv with v; auto.
  - cbn in *. destruct H as [Hsn Hcl]. split.
    + apply SN_inv with v; auto.
    + eapply Vc_step. exact Hcl. apply sstepForce. exact Hs.
  - cbn in *. destruct H as [Hsn Hm]. split.
    + apply SN_inv with v; auto.
    + destruct v as [i0| |a0 b0|b0 w0|c0]; cbn in Hm.
      * inversion Hs.
      * inversion Hs.
      * inversion Hs; subst; cbn; finish_sn Hsn.
      * inversion Hs; subst. destruct b0.
        -- eapply (IH A1); [exact Hm|assumption].
        -- eapply (IH A2); [exact Hm|assumption].
      * inversion Hs; subst; cbn; finish_sn Hsn.
  - cbn in *. destruct H as [Hsn Hm]. split.
    + apply SN_inv with v; auto.
    + destruct v as [i0| |a0 b0|b0 w0|c0]; cbn in Hm.
      * inversion Hs.
      * inversion Hs.
      * inversion Hs; subst; cbn; destruct Hm as [HA1 HA2].
        -- split.
           ++ eapply (IH A1). exact HA1. assumption.
           ++ exact HA2.
        -- split.
           ++ exact HA1.
           ++ eapply (IH A2). exact HA2. assumption.
      * inversion Hs; subst; cbn; finish_sn Hsn.
      * inversion Hs; subst; cbn; finish_sn Hsn.
Qed.

Lemma Vv_star : forall (A:valtype), forall n (v v':value n),
  Vv A v -> star sstep_value v v' -> Vv A v'.
Proof.
  intros A n v v' H S. revert H. induction S as [| x x' y st rest IH]; intros H.
  - exact H.
  - apply IH. eapply Vv_step. exact H. exact st.
Qed.

Lemma ren_comp_comp n (c:comp n) m (xi:ren n m) k (zeta:ren m k) :
  (c⟨xi⟩)⟨zeta⟩ = c⟨fun i => zeta (xi i)⟩.
Proof. apply (proj2 (ren_ren n)). Qed.

Lemma V_ren :
  (forall A, forall n (v:value n) m (xi:ren n m), Vv A v -> Vv A (v⟨xi⟩)) /\
  (forall B, forall n (c:comp n) m (xi:ren n m), Vc B c -> Vc B (c⟨xi⟩)).
Proof.
  apply (mutind_valtype_comptype
    (fun A => forall n (v:value n) m (xi:ren n m), Vv A v -> Vv A (v⟨xi⟩))
    (fun B => forall n (c:comp n) m (xi:ren n m), Vc B c -> Vc B (c⟨xi⟩))).
  - intros n v m xi H. cbn in *. apply SN_sstep_value_ren; exact H.
  - intros n v m xi H. cbn in *. apply SN_sstep_value_ren; exact H.
  - intros A IH n v m xi H. cbn in *. destruct H as [Hsn Hc]. split.
    + apply SN_sstep_value_ren; exact Hsn.
    + change (Vc A (force (v⟨xi⟩))). apply (IH n (force v) m xi Hc).
  - intros A1 IH1 A2 IH2 n v m xi H. cbn in *. destruct H as [Hsn Hm]. split.
    + apply SN_sstep_value_ren; exact Hsn.
    + destruct v as [i0| |a0 b0|b0 w0|c0]; cbn in Hm |- *; try exact I.
      * destruct b0; [apply (IH1 n w0 m xi Hm)|apply (IH2 n w0 m xi Hm)].
  - intros A1 IH1 A2 IH2 n v m xi H. cbn in *. destruct H as [Hsn Hm]. split.
    + apply SN_sstep_value_ren; exact Hsn.
    + destruct v as [i0| |a0 b0|b0 w0|c0]; cbn in Hm |- *; try exact I.
      destruct Hm as [H1 H2]. split.
      * apply (IH1 n a0 m xi H1).
      * apply (IH2 n b0 m xi H2).
  - intros n c m xi H. cbn in *. apply SN_sstep_ren; exact H.
  - intros A IH n c m xi H. cbn in *. destruct H as [Hsn Hc]. split.
    + apply SN_sstep_ren; exact Hsn.
    + intros v Hstar.
      destruct (@star_sstep_ren_inv n m xi (c⟨xi⟩) (ret v) Hstar c eq_refl) as [c0 Hrest0].
      destruct Hrest0 as [Hsc Heq]. symmetry in Heq.
      destruct (@ren_comp_ret n m xi c0 v Heq) as [v0 Hrest2].
      destruct Hrest2 as [Hc0 Hv]; subst c0; subst v.
      apply (IH n v0 m xi). apply (Hc v0). exact Hsc.
  - intros B1 IH1 B2 IH2 n c m xi H. cbn in *. destruct H as [Hsn Hc]. split.
    + apply SN_sstep_ren; exact Hsn.
    + intros c1 c2 Hstar.
      destruct (@star_sstep_ren_inv n m xi (c⟨xi⟩) (tuple c1 c2) Hstar c eq_refl) as [c0 Hrest0].
      destruct Hrest0 as [Hsc Heq]. symmetry in Heq.
      destruct (@ren_comp_tuple n m xi c0 c1 c2 Heq) as [a0 Hrest2].
      destruct Hrest2 as [b0 Hrest3]; destruct Hrest3 as [Hc0 Hrest4].
      destruct Hrest4 as [Ha Hb]; subst c0; subst c1; subst c2.
      destruct (Hc a0 b0 Hsc) as [H1 H2]. split.
      * apply (IH1 n a0 m xi H1).
      * apply (IH2 n b0 m xi H2).
  - intros A IH1 B IH2 n c m xi H. cbn in *. destruct H as [Hsn Hc]. split.
    + apply SN_sstep_ren; exact Hsn.
    + intros m' xi' body Hstar. rewrite ren_comp_comp in Hstar.
      apply (Hc m' (fun i => xi' (xi i)) body Hstar).
Qed.

Lemma SNv_var n i : SN sstep_value (@var_value n i).
Proof. apply SNC. intros d H. inversion H. Qed.

Lemma no_sstep_force_var n i d : ~ sstep (force (@var_value n i)) d.
Proof.
  intros H. inversion H; subst;
    try discriminate;
    try (match goal with Hv : @sstep_value _ _ _ |- _ => inversion Hv end);
    try (match goal with Hp : @pstep _ _ _ |- _ => inversion Hp end).
Qed.

Lemma no_sstep_force_var_gen n i m (xi: ren n m) d :
  ~ sstep ((force (@var_value n i))⟨xi⟩) d.
Proof.
  intros H. inversion H; subst; try discriminate;
    try (match goal with Hv : @sstep_value _ _ _ |- _ => cbn in Hv; inversion Hv end);
    try (match goal with Hp : @pstep _ _ _ |- _ => cbn in Hp; inversion Hp end);
    try discriminate.
Qed.

Lemma star_force_var_gen n i m (xi: ren n m) cc d :
  star sstep cc d -> cc = (force (@var_value n i))⟨xi⟩ -> d = cc.
Proof.
  intros S. induction S as [| x x' y st rest IH]; intros Heq.
  - reflexivity.
  - rewrite Heq in st. exfalso. eapply (@no_sstep_force_var_gen n i m xi x'). exact st.
Qed.

Lemma SNc_force_var n i : SN sstep (force (@var_value n i)).
Proof. apply SNC. intros d H. exfalso. exact (@no_sstep_force_var n i d H). Qed.

Lemma ren_ids n : (forall (v:value n), v⟨idren⟩ = v) /\ (forall (c:comp n), c⟨idren⟩ = c).
Proof.
  split; intros x.
  - rewrite (proj1 (ren_is_subst n) x n idren).
    change (x[idsv] = x). apply (proj1 (subst_ids n)).
  - rewrite (proj2 (ren_is_subst n) x n idren).
    change (x[idsv] = x). apply (proj2 (subst_ids n)).
Qed.

Lemma Vc_force_var : forall B (n:nat) (i:fin n), Vc B (force (@var_value n i)).
Proof.
  intros B. induction B as [| A | B1 IH1 B2 IH2 | A B IH]; intros n i; cbn.
  - apply SNc_force_var.
  - split; [apply SNc_force_var|]. intros v Hstar.
    exfalso. pose proof (@star_force_var_gen n i n idren ((force (@var_value n i))⟨idren⟩) (ret v) Hstar eq_refl) as Heq.
    rewrite (proj2 (ren_ids n) (force (@var_value n i))) in Heq. discriminate.
  - split; [apply SNc_force_var|]. intros c1 c2 Hstar.
    exfalso. pose proof (@star_force_var_gen n i n idren ((force (@var_value n i))⟨idren⟩) (tuple c1 c2) Hstar eq_refl) as Heq.
    rewrite (proj2 (ren_ids n) (force (@var_value n i))) in Heq. discriminate.
  - split; [apply SNc_force_var|]. intros m xi body Hstar v Hv.
    exfalso. pose proof (@star_force_var_gen n i m xi ((force (@var_value n i))⟨xi⟩) (lambda body) Hstar eq_refl). discriminate.
Qed.

Lemma Vv_var : forall A (n:nat) (i:fin n), Vv A (@var_value n i).
Proof.
  intro A. induction A as [| | A IH | A1 IH1 A2 IH2 | A1 IH1 A2 IH2]; intros n i; cbn.
  - apply SNv_var.
  - apply SNv_var.
  - split; [apply SNv_var|apply Vc_force_var].
  - split; [apply SNv_var|]. cbn. exact I.
  - split; [apply SNv_var|]. cbn. exact I.
Qed.

Lemma star_ret_inv n (v:value n) d (S: star sstep (ret v) d) :
  exists w, d = ret w /\ star sstep_value v w.
Proof.
  remember (ret v) as cc eqn:E. revert v E. induction S as [| x x' y st rest IH]; intros v0 E.
  - subst x. exists v0. split; [reflexivity|apply starRefl].
  - subst x. inversion st; subst; try (match goal with Hp : @pstep ?a ?b ?c |- _ => inversion Hp end).
    destruct (IH _ eq_refl) as [w Hrest]; destruct Hrest as [Hd Hstar].
    exists w. split; [exact Hd|]. eapply starStep; eauto.
Qed.

Lemma star_tuple_inv n (c1 c2:comp n) d (S: star sstep (tuple c1 c2) d) :
  exists d1 d2, d = tuple d1 d2 /\ star sstep c1 d1 /\ star sstep c2 d2.
Proof.
  remember (tuple c1 c2) as cc eqn:E. revert c1 c2 E.
  induction S as [| x x' y st rest IH]; intros c1 c2 E.
  - subst x. exists c1, c2. split; [reflexivity|]. split; apply starRefl.
  - subst x. inversion st; subst; try (match goal with Hp : @pstep ?a ?b ?c |- _ => inversion Hp end).
    + (* tupleL *) destruct (IH _ _ eq_refl) as [d1 Hrest]; destruct Hrest as [d2 Hrest2];
        destruct Hrest2 as [Hd Hrest3]; destruct Hrest3 as [Hs1 Hs2].
      exists d1, d2. split; [exact Hd|]. split; [|exact Hs2]. eapply starStep; eauto.
    + (* tupleR *) destruct (IH _ _ eq_refl) as [d1 Hrest]; destruct Hrest as [d2 Hrest2];
        destruct Hrest2 as [Hd Hrest3]; destruct Hrest3 as [Hs1 Hs2].
      exists d1, d2. split; [exact Hd|]. split; [exact Hs1|]. eapply starStep; eauto.
Qed.

Lemma star_lambda_inv n (b:comp (S n)) d (S: star sstep (lambda b) d) :
  exists b', d = lambda b' /\ star sstep b b'.
Proof.
  remember (lambda b) as cc eqn:E. revert b E. induction S as [| x x' y st rest IH]; intros b0 E.
  - subst x. exists b0. split; [reflexivity|apply starRefl].
  - subst x. inversion st; subst; try (match goal with Hp : @pstep ?a ?b ?c |- _ => inversion Hp end).
    destruct (IH _ eq_refl) as [b'' Hrest]; destruct Hrest as [Hd Hstar].
    exists b''. split; [exact Hd|]. eapply starStep; eauto.
Qed.

Lemma star_cases X (R:X->X->Prop) x y (S: star R x y) :
  x = y \/ exists z, R x z /\ star R z y.
Proof. destruct S as [| z z' w st rest]; [left;reflexivity|right;eauto]. Qed.

Definition NC n (B:comptype) (c:comp n) : Prop :=
  match B with
  | cone => True
  | F _ => forall v, c = ret v -> False
  | Pi _ _ => forall c1 c2, c = tuple c1 c2 -> False
  | arrow _ _ => forall body, c = lambda body -> False
  end.

Lemma Vc_intro_noncanon n (B:comptype) (c:comp n) :
  SN sstep c -> (forall c', sstep c c' -> Vc B c') -> NC B c -> Vc B c.
Proof.
  destruct B; cbn in *; intros Hsn Hstep Hnc.
  - exact Hsn.
  - split; [exact Hsn|]. intros vv S.
    destruct (star_cases S) as [Heq | Hrest0].
    + exfalso. apply (Hnc vv). exact Heq.
    + destruct Hrest0 as [x Hrest1]; destruct Hrest1 as [st rest].
      apply (proj2 (Hstep x st) vv rest).
  - split; [exact Hsn|]. intros c1 c2 S.
    destruct (star_cases S) as [Heq | Hrest0].
    + exfalso. apply (Hnc c1 c2). exact Heq.
    + destruct Hrest0 as [x Hrest1]; destruct Hrest1 as [st rest].
      apply (proj2 (Hstep x st) c1 c2 rest).
  - split; [exact Hsn|]. intros m xi body S vv Hv.
    destruct (star_cases S) as [Heq | Hrest0].
    + destruct (@ren_comp_lambda n m xi c body Heq) as [b0 Hrest0].
      destruct Hrest0 as [Hc0 Hb]. exfalso. apply (Hnc b0). exact Hc0.
    + destruct Hrest0 as [x Hrest1]; destruct Hrest1 as [st rest].
      destruct (proj2 (sstep_ren_inv n) c m xi x st) as [c1 Hrest2].
      destruct Hrest2 as [Hs Hx]. subst x.
      apply (proj2 (Hstep c1 Hs) m xi body rest vv Hv).
Qed.

Lemma SNc_ret n (v:value n) : SN sstep_value v -> SN sstep (ret v).
Proof.
  intros H. induction H as [v Hf IH]. apply SNC. intros d Hd. inversion Hd; subst.
  - apply IH. assumption.
  - match goal with Hp : @pstep ?a ?b ?c |- _ => inversion Hp end.
Qed.

Lemma SNc_tuple n (c1 c2:comp n) : SN sstep c1 -> SN sstep c2 -> SN sstep (tuple c1 c2).
Proof.
  intros H1 H2. revert c2 H2.
  induction H1 as [c10 Hf1 IH1]; intros c2 H2.
  pose proof H2 as H2'. induction H2 as [c20 Hf2 IH2].
  apply SNC. intros d Hd. inversion Hd; subst.
  - eapply (IH1 c1'); eauto.
  - eapply (IH2 c2'); eauto.
  - match goal with Hp : @pstep ?a ?b ?c |- _ => inversion Hp end.
Qed.

Lemma SNc_lambda n (b:comp (S n)) : SN sstep b -> SN sstep (lambda b).
Proof.
  intros H. induction H as [b Hf IH]. apply SNC. intros d Hd. inversion Hd; subst.
  - apply IH. assumption.
  - match goal with Hp : @pstep ?a ?b ?c |- _ => inversion Hp end.
Qed.

Lemma SNv_pair n (v1 v2:value n) : SN sstep_value v1 -> SN sstep_value v2 -> SN sstep_value (pair v1 v2).
Proof.
  intros H1 H2. revert v2 H2.
  induction H1 as [v10 Hf1 IH1]; intros v2 H2.
  pose proof H2 as H2'. induction H2 as [v20 Hf2 IH2].
  apply SNC. intros d Hd. inversion Hd; subst.
  - eapply (IH1 v1'); eauto.
  - eapply (IH2 v2'); eauto.
Qed.

Lemma SNv_inj n (b:bool) (v:value n) : SN sstep_value v -> SN sstep_value (inj b v).
Proof.
  intros H. induction H as [v Hf IH]. apply SNC. intros d Hd. inversion Hd; subst.
  apply IH. assumption.
Qed.

Lemma SNv_thunk n (c:comp n) : SN sstep c -> SN sstep_value (thunk c).
Proof.
  intros H. induction H as [c Hf IH]. apply SNC. intros d Hd. inversion Hd; subst.
  apply IH. assumption.
Qed.

Lemma SNv_u n : SN sstep_value (@u n).
Proof. apply SNC. intros d Hd. inversion Hd. Qed.

Lemma SNc_cu n : SN sstep (@cu n).
Proof. apply SNC. intros d Hd. inversion Hd; subst;
  match goal with Hp : @pstep ?a ?b ?c |- _ => inversion Hp end.
Qed.

Lemma Vv_u : forall n, Vv one (@u n).
Proof. intros n. cbn. apply SNv_u. Qed.

Lemma Vv_pair : forall A1 A2 n (a b:value n),
  Vv A1 a -> Vv A2 b -> Vv (cross A1 A2) (pair a b).
Proof.
  intros A1 A2 n a b H1 H2. cbn. split.
  - apply SNv_pair.
    + eapply Vv_SN. exact H1.
    + eapply Vv_SN. exact H2.
  - split; assumption.
Qed.

Lemma Vv_inj : forall (A1 A2:valtype) (n:nat) (b:bool) (w:value n),
  Vv (if b then A1 else A2) w -> Vv (Sigma A1 A2) (inj b w).
Proof.
  intros A1 A2 n b w H. cbn. split.
  - apply SNv_inj. apply (Vv_SN (if b then A1 else A2)). exact H.
  - destruct b; cbn; exact H.
Qed.

Lemma Vc_ret : forall A n (v:value n), Vv A v -> Vc (F A) (ret v).
Proof.
  intros A n v H. cbn. split.
  - apply SNc_ret. eapply Vv_SN. exact H.
  - intros w S. destruct (star_ret_inv S) as [w0 Hrest].
    destruct Hrest as [Heq Hstar]. injection Heq; intros; subst.
    apply (Vv_star A H Hstar).
Qed.

Lemma Vc_tuple : forall B1 B2 n (c1 c2:comp n),
  Vc B1 c1 -> Vc B2 c2 -> Vc (Pi B1 B2) (tuple c1 c2).
Proof.
  intros B1 B2 n c1 c2 H1 H2. cbn. split.
  - apply SNc_tuple.
    + eapply Vc_SN. exact H1.
    + eapply Vc_SN. exact H2.
  - intros d1 d2 S. destruct (star_tuple_inv S) as [e1 Hrest].
    destruct Hrest as [e2 Hrest2]; destruct Hrest2 as [Heq Hrest3].
    destruct Hrest3 as [Hstar1 Hstar2]. injection Heq; intros; subst.
    split.
    + eapply Vc_star; [exact H1|exact Hstar1].
    + eapply Vc_star; [exact H2|exact Hstar2].
Qed.


Lemma Vc_force_thunk : forall A n (c:comp n), Vc A c -> Vc A (force (thunk c)).
Proof.
  intros A n c Hc. pose proof (@Vc_SN n A c Hc) as Hs. revert Hc.
  induction Hs as [c0 Hf IH]; intros Hc.
  apply Vc_intro_noncanon.
  - apply SNC. intros d Hd. inversion Hd; subst.
    + match goal with Hv : @sstep_value _ (thunk c0) _ |- _ => inversion Hv; subst end.
      eapply Vc_SN. eapply IH. eassumption. eapply Vc_step; [exact Hc | eassumption].
    + match goal with Hp : @pstep ?a ?b ?c |- _ => inversion Hp end.
      match goal with
      | Heq : c0 = _ |- _ => rewrite <- Heq; eapply Vc_SN; exact Hc
      | Heq : _ = c0 |- _ => rewrite Heq; eapply Vc_SN; exact Hc
      | |- SN sstep c0 => eapply Vc_SN; exact Hc
      end.
  - intros d Hd. inversion Hd; subst.
    + match goal with Hv : @sstep_value _ (thunk c0) _ |- _ => inversion Hv; subst end.
      eapply IH. eassumption. eapply Vc_step; [exact Hc | eassumption].
    + match goal with Hp : @pstep ?a ?b ?c |- _ => inversion Hp end.
      match goal with
      | Heq : c0 = _ |- _ => rewrite <- Heq; exact Hc
      | Heq : _ = c0 |- _ => rewrite Heq; exact Hc
      | |- Vc A c0 => exact Hc
      end.
  - destruct A; cbn; intros; try exact I; discriminate.
Qed.

Lemma Vv_thunk : forall A n (c:comp n), Vc A c -> Vv (U A) (thunk c).
Proof.
  intros A n c Hc. cbn. split.
  - apply SNv_thunk. apply (@Vc_SN n A c Hc).
  - apply Vc_force_thunk. exact Hc.
Qed.

Lemma Vc_lambda : forall A B n (body:comp (S n)),
  SN sstep body ->
  (forall m (xi:ren n m) (v:value m), Vv A v -> Vc B ((body⟨up_ren xi⟩)[v..])) ->
  Vc (arrow A B) (lambda body).
Proof.
  intros A B n body Hsn Hbody. cbn. split.
  - apply SNc_lambda. exact Hsn.
  - intros m xi body2 S vv Hv. cbn in S.
    destruct (star_lambda_inv S) as [b' Hrest0].
    destruct Hrest0 as [Heq Hstar]. injection Heq; intros Hb; subst body2.
    eapply Vc_star.
    + apply (Hbody m xi vv Hv).
    + exact (star_sstep_subst Hstar (vv..)).
Qed.

Lemma Vc_caseZ : forall n C (v:value n), Vv zero v -> Vc C (caseZ v).
Proof.
  intros n C v Hv. pose proof (@Vv_SN n zero v Hv) as Hs. revert Hv.
  induction Hs as [v0 Hf IH]; intros Hv.
  apply Vc_intro_noncanon.
  - apply SNC. intros d Hd. inversion Hd; subst.
    + match goal with Hs2 : @sstep_value _ v0 ?y |- _ =>
        eapply Vc_SN; apply (IH y Hs2); eapply Vv_step; [exact Hv|exact Hs2] end.
    + match goal with Hp : @pstep ?a ?b ?c |- _ => inversion Hp end.
  - intros d Hd. inversion Hd; subst.
    + match goal with Hs2 : @sstep_value _ v0 ?y |- _ =>
        apply (IH y Hs2); eapply Vv_step; [exact Hv|exact Hs2] end.
    + match goal with Hp : @pstep ?a ?b ?c |- _ => inversion Hp end.
  - destruct C; cbn; intros; try exact I; discriminate.
Qed.

Lemma Vc_arrow_clause : forall A B n (c:comp (S n)) m (xi:ren n m) (body:comp (S m)) (v:value m),
  Vc (arrow A B) (lambda c) ->
  star sstep ((lambda c)⟨xi⟩) (lambda body) ->
  Vv A v -> Vc B (body[v..]).
Proof.
  intros A B n c m xi body v Hc Hstar Hv.
  cbn in Hc. destruct Hc as [_ Hcl].
  exact (Hcl m xi body Hstar v Hv).
Qed.

Lemma Vc_app : forall n A B (c:comp n) (v:value n),
  Vc (arrow A B) c -> Vv A v -> Vc B (c v).
Proof.
  intros n A B c v Hc Hv.
  pose proof (@Vc_SN n (arrow A B) c Hc) as Hsc.
  revert v Hv. induction Hsc as [c0 Hf IH].
  intros v Hv. pose proof (@Vv_SN n A v Hv) as Hsv. revert Hv.
  induction Hsv as [v0 Hf2 IH2]; intros Hv.
  apply Vc_intro_noncanon.
  - apply SNC. intros d Hd. inversion Hd; subst.
    + eapply Vc_SN. apply (IH c' H2). eapply Vc_step; [exact Hc|exact H2]. exact Hv.
    + eapply Vc_SN. apply (IH2 v' H2). apply (@Vv_step A n v0 v' Hv H2).
    + match goal with Hp : @pstep ?a ?b ?c |- _ => inversion Hp; subst end.
      eapply Vc_SN. apply (@Vc_arrow_clause A B n c n (@idren n) c v0 Hc).
      * rewrite (proj2 (ren_ids n) (lambda c)). apply starRefl.
      * exact Hv.
  - intros d Hd. inversion Hd; subst.
    + apply (IH c' H2). eapply Vc_step; [exact Hc|exact H2]. exact Hv.
    + apply (IH2 v' H2). apply (@Vv_step A n v0 v' Hv H2).
    + match goal with Hp : @pstep ?a ?b ?c |- _ => inversion Hp; subst end.
      apply (@Vc_arrow_clause A B n c n (@idren n) c v0 Hc).
      * rewrite (proj2 (ren_ids n) (lambda c)). apply starRefl.
      * exact Hv.
  - destruct B; cbn; intros; try exact I; discriminate.
Qed.

Lemma Vc_proj : forall (n:nat) (B1 B2:comptype) (c:comp n) (b:bool),
  Vc (Pi B1 B2) c -> Vc (if b then B1 else B2) (proj b c).
Proof.
  intros n B1 B2 c b Hc.
  pose proof (@Vc_SN n (Pi B1 B2) c Hc) as Hsc.
  revert b. induction Hsc as [c0 Hf IH]; intros b.
  apply Vc_intro_noncanon.
  - apply SNC. intros d Hd. inversion Hd; subst.
    + apply (@Vc_SN n (if b then B1 else B2) (proj b c')). apply (IH c' H2). eapply Vc_step; [exact Hc|exact H2].
    + match goal with Hp : @pstep ?a ?b2 ?c2 |- _ => inversion Hp; subst end.
      cbn in Hc. destruct (proj2 Hc c1 c2 (@starRefl (comp n) sstep (tuple c1 c2))) as [HC1 HC2].
      destruct b; cbn in *; [eapply Vc_SN; exact HC1 | eapply Vc_SN; exact HC2].
  - intros d Hd. inversion Hd; subst.
    + apply (IH c' H2). eapply Vc_step; [exact Hc|exact H2].
    + match goal with Hp : @pstep ?a ?b2 ?c2 |- _ => inversion Hp; subst end.
      cbn in Hc. destruct (proj2 Hc c1 c2 (@starRefl (comp n) sstep (tuple c1 c2))) as [HC1 HC2].
      destruct b; cbn in *; assumption.
  - destruct b; [destruct B1 | destruct B2]; cbn; intros; try exact I; discriminate.
Qed.

Lemma Vc_letin n (A:valtype) (B:comptype) (c1:comp n) (c2:comp (S n)) :
  Vc (F A) c1 ->
  SN sstep c2 ->
  (forall (v:value n), Vv A v -> Vc B (c2[v..])) ->
  Vc B (letin c1 c2).
Proof.
  intros Hc1 Hsn2 Hstab.
  pose proof (@Vc_SN n (F A) c1 Hc1) as Hs1.
  revert c2 Hsn2 Hstab. induction Hs1 as [c10 Hf1 IH1]; intros c2 Hsn2 Hstab.
  pose proof Hsn2 as Hsn2'. revert Hstab.
  induction Hsn2 as [c20 Hf2 IH2]; intros Hstab.
  apply Vc_intro_noncanon.
  - apply SNC. intros d Hd. inversion Hd; subst.
    + eapply Vc_SN. assert (Hc1' : Vc (F A) c1') by (eapply Vc_step; [exact Hc1|exact H2]).
      apply (IH1 c1' H2 Hc1' c20 Hsn2' Hstab).
    + eapply Vc_SN. apply (IH2 c2' H2 (@SN_inv (comp (S n)) sstep c20 Hsn2' c2' H2)). intros vv Hv.
      eapply Vc_star. apply (Hstab vv Hv). exact (star_sstep_subst (@starStep (comp (S n)) sstep c20 c2' c2' H2 (@starRefl (comp (S n)) sstep c2')) (vv..)).
    + match goal with Hp : @pstep ?a ?b ?c |- _ => inversion Hp; subst end.
      match goal with H : Vc (F A) (ret ?w) |- _ =>
        cbn in H; eapply Vc_SN; apply (Hstab w (proj2 H w (@starRefl (comp n) sstep (ret w)))) end.
  - intros d Hd. inversion Hd; subst.
    + assert (Hc1' : Vc (F A) c1') by (eapply Vc_step; [exact Hc1|exact H2]).
      apply (IH1 c1' H2 Hc1' c20 Hsn2' Hstab).
    + apply (IH2 c2' H2 (@SN_inv (comp (S n)) sstep c20 Hsn2' c2' H2)). intros vv Hv.
      eapply Vc_star. apply (Hstab vv Hv). exact (star_sstep_subst (@starStep (comp (S n)) sstep c20 c2' c2' H2 (@starRefl (comp (S n)) sstep c2')) (vv..)).
    + match goal with Hp : @pstep ?a ?b ?c |- _ => inversion Hp; subst end.
      match goal with H : Vc (F A) (ret ?w) |- _ =>
        cbn in H; apply (Hstab w (proj2 H w (@starRefl (comp n) sstep (ret w)))) end.
  - destruct B; cbn; intros; try exact I; discriminate.
Qed.

Lemma Vc_caseS n (A1 A2:valtype) (C:comptype) (v:value n) (c1 c2:comp (S n)) :
  Vv (Sigma A1 A2) v ->
  SN sstep c1 -> (forall (w:value n), Vv A1 w -> Vc C (c1[w..])) ->
  SN sstep c2 -> (forall (w:value n), Vv A2 w -> Vc C (c2[w..])) ->
  Vc C (caseS v c1 c2).
Proof.
  intros Hv Hsn1 Hstab1 Hsn2 Hstab2.
  pose proof (@Vv_SN n (Sigma A1 A2) v Hv) as Hsv.
  revert Hv c1 Hsn1 Hstab1 c2 Hsn2 Hstab2.
  induction Hsv as [v0 Hf IH]; intros Hv c1 Hsn1 Hstab1 c2 Hsn2 Hstab2.
  revert Hstab1 c2 Hsn2 Hstab2.
  induction Hsn1 as [c10 Hf1 IH1']; intros Hstab1 c2 Hsn2 Hstab2.
  revert Hstab2.
  induction Hsn2 as [c20 Hf2 IH3]; intros Hstab2.
  assert (Hs10 : SN sstep c10) by exact (@SNC (comp (S n)) sstep c10 Hf1).
  assert (Hs20 : SN sstep c20) by exact (@SNC (comp (S n)) sstep c20 Hf2).
  apply Vc_intro_noncanon.
  - apply SNC. intros d Hd. inversion Hd; subst.
    + eapply Vc_SN. eapply IH.
      * eassumption.
      * eapply Vv_step. exact Hv. eassumption.
      * exact Hs10. * exact Hstab1. * exact Hs20. * exact Hstab2.
    + assert (Hstab1' : forall w, Vv A1 w -> Vc C (c1'[w..])).
      { intros w Hw. eapply Vc_star. apply (Hstab1 w Hw).
        exact (star_sstep_subst (@starStep (comp (S n)) sstep c10 c1' c1' H3 (@starRefl (comp (S n)) sstep c1')) (w..)). }
      eapply Vc_SN. eapply IH1'. eassumption. exact Hstab1'. exact Hs20. exact Hstab2.
    + assert (Hstab2' : forall w, Vv A2 w -> Vc C (c2'[w..])).
      { intros w Hw. eapply Vc_star. apply (Hstab2 w Hw).
        exact (star_sstep_subst (@starStep (comp (S n)) sstep c20 c2' c2' H3 (@starRefl (comp (S n)) sstep c2')) (w..)). }
      eapply Vc_SN. eapply IH3. eassumption. exact Hstab2'.
    + match goal with Hp : @pstep ?a ?b ?c |- _ => inversion Hp; subst end.
      cbn in Hv. destruct b.
      * eapply Vc_SN. apply (Hstab1 v (proj2 Hv)).
      * eapply Vc_SN. apply (Hstab2 v (proj2 Hv)).
  - intros d Hd. inversion Hd; subst.
    + eapply IH.
      * eassumption.
      * eapply Vv_step. exact Hv. eassumption.
      * exact Hs10. * exact Hstab1. * exact Hs20. * exact Hstab2.
    + assert (Hstab1' : forall w, Vv A1 w -> Vc C (c1'[w..])).
      { intros w Hw. eapply Vc_star. apply (Hstab1 w Hw).
        exact (star_sstep_subst (@starStep (comp (S n)) sstep c10 c1' c1' H3 (@starRefl (comp (S n)) sstep c1')) (w..)). }
      eapply IH1'. eassumption. exact Hstab1'. exact Hs20. exact Hstab2.
    + assert (Hstab2' : forall w, Vv A2 w -> Vc C (c2'[w..])).
      { intros w Hw. eapply Vc_star. apply (Hstab2 w Hw).
        exact (star_sstep_subst (@starStep (comp (S n)) sstep c20 c2' c2' H3 (@starRefl (comp (S n)) sstep c2')) (w..)). }
      eapply IH3. eassumption. exact Hstab2'.
    + match goal with Hp : @pstep ?a ?b ?c |- _ => inversion Hp; subst end.
      cbn in Hv. destruct b.
      * apply (Hstab1 v (proj2 Hv)).
      * apply (Hstab2 v (proj2 Hv)).
  - destruct C; cbn; intros; try exact I; discriminate.
Qed.


Lemma Vc_caseP n (A1 A2:valtype) (C:comptype) (v:value n) (c:comp (S (S n))) :
  Vv (cross A1 A2) v ->
  SN sstep c ->
  (forall (w2:value n), Vv A2 w2 -> forall (w1:value n), Vv A1 w1 -> Vc C (c[w2,w1..])) ->
  Vc C (caseP v c).
Proof.
  intros Hv Hsn Hstab.
  pose proof (@Vv_SN n (cross A1 A2) v Hv) as Hsv.
  revert Hv c Hsn Hstab.
  induction Hsv as [v0 Hf IH]; intros Hv c Hsn Hstab.
  revert Hstab. induction Hsn as [c0 Hf1 IH1]; intros Hstab.
  assert (Hsc : SN sstep c0) by exact (@SNC (comp (S (S n))) sstep c0 Hf1).
  apply Vc_intro_noncanon.
  - apply SNC. intros d Hd. inversion Hd; subst.
    + eapply Vc_SN. eapply IH.
      * eassumption.
      * eapply Vv_step. exact Hv. eassumption.
      * exact Hsc. * exact Hstab.
    + assert (Hstab' : forall w2, Vv A2 w2 -> forall w1, Vv A1 w1 -> Vc C (c'[w2,w1..])).
      { intros w2 HV2 w1 HV1. eapply Vc_star. apply (Hstab w2 HV2 w1 HV1).
        exact (star_sstep_subst (@starStep (comp (S (S n))) sstep c0 c' c' H2 (@starRefl (comp (S (S n))) sstep c')) (w2,w1..)). }
      eapply Vc_SN. eapply IH1. eassumption. exact Hstab'.
    + match goal with Hp : @pstep ?a ?b ?c |- _ => inversion Hp; subst end.
      cbn in Hv. destruct Hv as [Hv21 Hv22]. destruct Hv22 as [HV1 HV2].
      eapply Vc_SN. apply (Hstab v2 HV2 v1 HV1).
  - intros d Hd. inversion Hd; subst.
    + eapply IH.
      * eassumption.
      * eapply Vv_step. exact Hv. eassumption.
      * exact Hsc. * exact Hstab.
    + assert (Hstab' : forall w2, Vv A2 w2 -> forall w1, Vv A1 w1 -> Vc C (c'[w2,w1..])).
      { intros w2 HV2 w1 HV1. eapply Vc_star. apply (Hstab w2 HV2 w1 HV1).
        exact (star_sstep_subst (@starStep (comp (S (S n))) sstep c0 c' c' H2 (@starRefl (comp (S (S n))) sstep c')) (w2,w1..)). }
      eapply IH1. eassumption. exact Hstab'.
    + match goal with Hp : @pstep ?a ?b ?c |- _ => inversion Hp; subst end.
      cbn in Hv. destruct Hv as [Hv21 Hv22]. destruct Hv22 as [HV1 HV2].
      apply (Hstab v2 HV2 v1 HV1).
  - destruct C; cbn; intros; try exact I; discriminate.
Qed.

Lemma Vc_cu n : Vc cone (@cu n).
Proof. cbn. apply SNc_cu. Qed.

Definition GSubst {m} (Gamma: ctx m) {n} (sigma: fin m -> value n) : Prop :=
  forall i, Vv (Gamma i) (sigma i).

Lemma rscomp_shift_scomp m k (xi: ren m k) (v:value k) (l:fin m) :
  rscomp (@shift m) (scomp (renv (up_ren xi)) (v..)) l = renv xi l.
Proof.
  destruct m as [|m'].
  - destruct l.
  - unfold rscomp, scomp, renv, up_ren, scons, funcomp, shift. cbn.
    destruct l as [l'|]; cbn; reflexivity.
Qed.

Lemma val_shift_up m k (x:value m) (xi: ren m k) (v:value k) :
  (x⟨shift⟩)[scomp (renv (up_ren xi)) (v..)] = x⟨xi⟩.
Proof.
  rewrite (proj1 (ren_subst m) x (S m) shift k (scomp (renv (up_ren xi)) (v..))).
  rewrite (proj1 (ren_is_subst m) x k xi).
  apply (proj1 (subst_ext m)). intros l.
  apply rscomp_shift_scomp.
Qed.

Lemma subst_ren_subst_comp n (c:comp n) m (sigma: fin n -> value m) k (xi: ren m k) l (tau: fin k -> value l) :
  ((c[sigma])⟨xi⟩)[tau] = c[scomp sigma (scomp (renv xi) tau)].
Proof.
  rewrite (proj2 (ren_is_subst m) (c[sigma]) k xi).
  rewrite (proj2 (subst_subst m) (c[sigma]) k (renv xi) l tau).
  rewrite (proj2 (subst_subst n) c m sigma l (scomp (renv xi) tau)).
  reflexivity.
Qed.

Lemma subst_shift_id m (x:value m) (v:value m) : (x⟨shift⟩)[v..] = x.
Proof.
  rewrite (proj1 (ren_subst m) x (S m) shift m (v..)).
  transitivity (x[@idsv m]).
  - apply (proj1 (subst_ext m)). intros l. unfold rscomp, scons, idsv. cbn. reflexivity.
  - apply (proj1 (subst_ids m)).
Qed.

Lemma subst_shift2_id m (x:value m) (w1 w2:value m) : ((x⟨shift⟩)⟨shift⟩)[w2,w1..] = x.
Proof.
  rewrite (proj1 (ren_subst (S m)) (x⟨shift⟩) (S (S m)) shift m (scons w2 (scons w1 idsv))).
  rewrite (proj1 (ren_subst m) x (S m) shift m (rscomp shift (scons w2 (scons w1 idsv)))).
  rewrite <- (proj1 (subst_ids m) x) at 2.
  apply (proj1 (subst_ext m)). intros l.
  unfold rscomp, scons, idsv. cbn. reflexivity.
Qed.

Lemma FUND : forall m (Gamma:ctx m),
  (forall (v:value m) (A:valtype), Gamma ⊩ v : A ->
     forall n (sigma: fin m -> value n), GSubst Gamma sigma -> Vv A (v[sigma])) /\
  (forall (c:comp m) (B:comptype), Gamma ⊢ c : B ->
     forall n (sigma: fin m -> value n), GSubst Gamma sigma -> Vc B (c[sigma])).
Proof.
  intros m Gamma.
  apply (mutindt_value_computation_typing
    (fun m Gamma v A _ => forall n sigma, GSubst Gamma sigma -> Vv A (v[sigma]))
    (fun m Gamma c B _ => forall n sigma, GSubst Gamma sigma -> Vc B (c[sigma]))).
  - (* typeVar *) intros m0 G i n sigma GS. cbn. apply GS.
  - (* typeUnit *) intros m0 G n sigma GS. cbn. apply Vv_u.
  - (* typePair *) intros m0 G v1 v2 A1 A2 H1 IH1 H2 IH2 n sigma GS. cbn.
    apply Vv_pair. + apply (IH1 n sigma GS). + apply (IH2 n sigma GS).
  - (* typeSum *) intros m0 G A1 A2 b v H IH n sigma GS. cbn.
    apply Vv_inj. apply (IH n sigma GS).
  - (* typeThunk *) intros m0 G c A H IH n sigma GS. cbn.
    apply Vv_thunk. apply (IH n sigma GS).
  - (* typeCone *) intros m0 G n sigma GS. cbn. apply Vc_cu.
  - (* typeLambda *) intros m0 G c A B H IH n sigma GS. cbn.
    apply (@Vc_lambda A B n (c[up_value_value sigma])).
    + eapply Vc_SN. apply (IH (S n) (up_value_value sigma)).
      intros [i|]; cbn.
      * change (Vv (G i) ((sigma i)⟨shift⟩)). apply (proj1 V_ren). exact (GS i).
      * apply (Vv_var A (S n) var_zero).
    + intros k xi vv Hv.
      rewrite (@subst_ren_subst_comp (S m0) c (S n) (up_value_value sigma) (S k) (up_ren xi) k (vv..)).
      apply (IH k (scomp (up_value_value sigma) (scomp (renv (up_ren xi)) (vv..)))).
      intros [i|]; cbn.
      * change (Vv (G i) (((sigma i)⟨shift⟩)[scomp (renv (up_ren xi)) (vv..)])).
        rewrite (@val_shift_up n k (sigma i) xi vv).
        apply (proj1 V_ren). exact (GS i).
      * exact Hv.
  - (* typeLetin *) intros m0 G c1 c2 A B H1 IH1 H2 IH2 n sigma GS. cbn.
    eapply Vc_letin.
    + apply (IH1 n sigma GS).
    + eapply Vc_SN. apply (IH2 (S n) (up_value_value sigma)).
      intros [i|]; cbn.
      * change (Vv (G i) ((sigma i)⟨shift⟩)). apply (proj1 V_ren). exact (GS i).
      * apply (Vv_var A (S n) var_zero).
    + intros vv Hv.
      rewrite (proj2 (subst_subst (S m0)) c2 (S n) (up_value_value sigma) n (vv..)).
      apply (IH2 n (scomp (up_value_value sigma) (vv..))).
      intros [i|]; cbn.
      * change (Vv (G i) (((sigma i)⟨shift⟩)[vv..])).
        rewrite (@subst_shift_id n (sigma i) vv). apply GS.
      * exact Hv.
  - (* typeRet *) intros m0 G v A H IH n sigma GS. cbn.
    apply Vc_ret. apply (IH n sigma GS).
  - (* typeApp *) intros m0 G c v A B H1 IH1 H2 IH2 n sigma GS. cbn.
    eapply Vc_app. + apply (IH1 n sigma GS). + apply (IH2 n sigma GS).
  - (* typeTuple *) intros m0 G c1 c2 B1 B2 H1 IH1 H2 IH2 n sigma GS. cbn.
    apply Vc_tuple. + apply (IH1 n sigma GS). + apply (IH2 n sigma GS).
  - (* typeProj *) intros m0 G b c B1 B2 H IH n sigma GS. cbn.
    apply Vc_proj. apply (IH n sigma GS).
  - (* typeForce *) intros m0 G v A H IH n sigma GS. cbn.
    pose proof (IH n sigma GS) as Hv. cbn in Hv. exact (proj2 Hv).
  - (* typeCaseZ *) intros m0 G v A H IH n sigma GS. cbn.
    apply Vc_caseZ. apply (IH n sigma GS).
  - (* typeCaseS *) intros m0 G v c1 c2 A1 A2 C Hv IHv H1 IH1 H2 IH2 n sigma GS. cbn.
    eapply Vc_caseS.
    + apply (IHv n sigma GS).
    + eapply Vc_SN. apply (IH1 (S n) (up_value_value sigma)).
      intros [i|]; cbn.
      * change (Vv (G i) ((sigma i)⟨shift⟩)). apply (proj1 V_ren). exact (GS i).
      * apply (Vv_var A1 (S n) var_zero).
    + intros w Hw.
      rewrite (proj2 (subst_subst (S m0)) c1 (S n) (up_value_value sigma) n (w..)).
      apply (IH1 n (scomp (up_value_value sigma) (w..))).
      intros [i|]; cbn.
      * change (Vv (G i) (((sigma i)⟨shift⟩)[w..])).
        rewrite (@subst_shift_id n (sigma i) w). apply GS.
      * exact Hw.
    + eapply Vc_SN. apply (IH2 (S n) (up_value_value sigma)).
      intros [i|]; cbn.
      * change (Vv (G i) ((sigma i)⟨shift⟩)). apply (proj1 V_ren). exact (GS i).
      * apply (Vv_var A2 (S n) var_zero).
    + intros w Hw.
      rewrite (proj2 (subst_subst (S m0)) c2 (S n) (up_value_value sigma) n (w..)).
      apply (IH2 n (scomp (up_value_value sigma) (w..))).
      intros [i|]; cbn.
      * change (Vv (G i) (((sigma i)⟨shift⟩)[w..])).
        rewrite (@subst_shift_id n (sigma i) w). apply GS.
      * exact Hw.
  - (* typeCaseP *) intros m0 G v c A B C Hv IHv H1 IH1 n sigma GS. cbn.
    eapply Vc_caseP.
    + apply (IHv n sigma GS).
    + eapply Vc_SN. apply (IH1 (S (S n)) (up_value_value (up_value_value sigma))).
      intros i0. destruct i0 as [i0|].
      * destruct i0 as [i|]; cbn.
        -- change (Vv (G i) (((sigma i)⟨shift⟩)⟨shift⟩)). apply (proj1 V_ren). apply (proj1 V_ren). exact (GS i).
        -- apply (Vv_var A (S (S n)) (Some None)).
      * cbn. apply (Vv_var B (S (S n)) var_zero).
    + intros w2 Hv2 w1 Hv1.
      rewrite (proj2 (subst_subst (S (S m0))) c (S (S n)) (up_value_value (up_value_value sigma)) n (w2,w1..)).
      apply (IH1 n (scomp (up_value_value (up_value_value sigma)) (w2,w1..))).
      intros i0. destruct i0 as [i0|].
      * destruct i0 as [i|]; cbn.
        -- change (Vv (G i) ((((sigma i)⟨shift⟩)⟨shift⟩)[w2,w1..])).
           rewrite (@subst_shift2_id n (sigma i) w1 w2). apply GS.
        -- exact Hv1.
      * cbn. exact Hv2.
Qed.

Theorem strong_normalisation_cbpv n (Gamma: ctx n) P B:
  Gamma ⊢ P : B -> SN sstep P.
Proof.
  intros H.
  assert (GS : GSubst Gamma (@idsv n)).
  { intros i. apply Vv_var. }
  pose proof (proj2 (FUND Gamma) P B H n (@idsv n) GS) as Hc.
  rewrite (proj2 (subst_ids n) P) in Hc.
  exact (@Vc_SN n B P Hc).
Qed.
