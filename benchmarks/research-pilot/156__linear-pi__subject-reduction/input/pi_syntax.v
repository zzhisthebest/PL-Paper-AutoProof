Require Import Bool List Lia PeanoNat header operations.

Notation name  := nat.

Section ProcessDefinitions.

Inductive dproc : Set :=
  | dZero : dproc
  | dBang : name -> name -> name -> name ->dproc -> dproc
  | dPar : dproc -> dproc -> dproc
  | dNu : name -> name -> dproc -> dproc
  | dInp : name -> name -> name -> name -> dproc -> dproc
  | dOut : name -> name -> name -> name -> dproc -> dproc.

Fixpoint secLabs (p : dproc)  :=
    match p with
    | dZero  => nil
    | dBang _ _ _ _ p | dInp _ _ _ _ p | dOut _ _ _ _ p => secLabs p
    | dPar p q => secLabs q ++ secLabs p
    | dNu h i  p =>  secLabs p ++ (h, i) :: nil
    end.

Fixpoint fn (p : dproc) : list (nat * nat) :=
    match p with
    | dZero  => nil
    | dBang x1 x2 y1 y2 p
    | dInp x1 x2 y1 y2  p =>
      List.remove nat_pair_eq_dec (y1, y2) ((x1, x2) :: fn p)
    | dPar p1 p2 =>
      fn p1 ++  fn p2
    | dNu a1 a2 p =>
      List.remove nat_pair_eq_dec (a1, a2) (fn p)
    | dOut x1 x2 y1 y2 p =>
      (x1, x2) :: (y1, y2) :: fn p
    end.

Fixpoint bv (p : dproc) : list (nat * nat) :=
    match p with
    | dZero  =>
      nil
    | dBang x1 x2 y1 y2 p
    | dInp x1 x2 y1 y2  p =>
      (y1, y2) :: bv p
    | dPar p1 p2 =>
      bv p1 ++  bv p2
    | dNu a1 a2 p =>
      bv p
    | dOut x1 x2 y1 y2 p =>
      bv p
    end.

Definition wf (p : dproc) : Prop :=
    NoDup (secLabs p) /\ disjoint (fn p) (secLabs p).

Definition pos l := forall x1 x2 : nat,
      In (x1, x2) l-> x2 > 0.

Definition sl_pos p := pos (secLabs p).

Definition mv (py pz pv : name * name)  :=
    let (y1, y2) := (fst py, snd py) in
    let (z1, z2) := (fst pz, snd pz) in
    let (v1, v2) := (fst pv, snd pv) in
    if (y1 =? z1) && (y2 =? z2)
    then (v1, v2)
    else (y1, y2).

Fixpoint pmap p z1 z2 v1 v2 :=
    match p with
    | dZero  =>  p
    | dBang x1 x2 y1 y2 q =>
      let r := mv (x1, x2) (z1, z2) (v1, v2) in
      dBang (fst r) (snd r) y1 y2 (pmap q z1 z2 v1 v2)
    | dInp x1 x2 y1 y2  q =>
      let r := mv (x1, x2) (z1, z2) (v1, v2) in
      dInp (fst r) (snd r) y1 y2  (pmap q z1 z2 v1 v2)
    | dOut x1 x2 y1 y2 p =>
      let r1 := mv (x1, x2) (z1, z2) (v1, v2) in
      let r2 := mv (y1, y2) (z1, z2) (v1, v2) in
      dOut  (fst r1) (snd r1) (fst r2) (snd r2) (pmap p z1 z2 v1 v2)
    | dPar p q =>
      dPar (pmap p z1 z2 v1 v2) (pmap q z1 z2 v1 v2)
    | dNu h i q =>
      dNu h i (pmap q z1 z2 v1 v2)
    end.

Definition map_nat_nat := list (nat * nat).

Fixpoint  domain_projection (m : map_nat_nat) :=
    match m with
    | nil => nil
    | (k, _) :: t => k :: (domain_projection t)
    end.

Fixpoint  codomain_projection (m : map_nat_nat) :=
    match m with
    | nil => nil
    | (_, v) :: t => v :: (codomain_projection t)
    end.

Definition structure_is_map (m : map_nat_nat) :=
    NoDup (domain_projection m).

Fixpoint max (l :list (nat*nat)) : nat :=
    match l with
    | nil => 0
    | (_, x) :: t => let m := max t in
                     if x <? m then m else x
    end.

Notation dp := domain_projection.

Notation cp := codomain_projection.

Local Definition no_dup_cont (h : nat * nat) (t : list (nat * nat))
    (pf : NoDup (h :: t)) : NoDup t := ltac:(inversion pf; assumption).

Local Opaque no_dup_cont.

Fixpoint dep_map_gen_r (l :list (name * name)) (m : nat) : NoDup l -> map_nat_nat :=
    match l with
    | nil => fun _ => nil
    | h :: t =>
      fun pf : NoDup (h :: t)  =>
        (fst h, snd h + m) :: (dep_map_gen_r t m (no_dup_cont h t pf))
    end.

Definition dep_map_gen (l :list (name * name)) : NoDup l -> map_nat_nat :=
    dep_map_gen_r l (max l).

Fixpoint dep_relabel (p : dproc) (s : list (name*name)) : NoDup s -> dproc :=
    match p with
    | dZero   => fun _  => p
    | dBang x1 x2 y1 y2 p  =>
      fun pf : NoDup s => dBang  x1 x2 y1 y2 (dep_relabel p s pf)
    | dInp x1 x2 y1 y2 p =>
      fun pf : NoDup  s => dInp  x1 x2 y1 y2 (dep_relabel p s pf)
    | dOut x1 x2 y1 y2 p  =>
      fun pf : NoDup s => dOut x1 x2 y1 y2  (dep_relabel p s pf )
    | dPar p q =>
      fun pf : NoDup s =>
        dPar (dep_relabel p s pf) (dep_relabel q s pf)
    | dNu h i p =>
      fun pf : NoDup s =>
        dNu h (i + max s) (pmap (dep_relabel p s pf) h i h (i + max s))
    end.

End ProcessDefinitions.

Section Facts.

End Facts.
