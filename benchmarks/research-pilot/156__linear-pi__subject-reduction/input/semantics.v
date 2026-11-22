Require Import Bool List Lia PeanoNat header operations pi_syntax pairEq type_system.

Section Semantics.

Inductive action : Set :=
  | aIn : nat -> nat -> nat -> nat -> action
  | aOut : nat -> nat -> nat -> nat -> action
  | aTau : nat -> nat -> action.

Fixpoint InB a g : ((flag * piType) * bool) :=
    match g with
    | nil => ((ill, Top), false)
    | (b, f, t) :: m =>
      if pair_eq a b then ((f, t), true) else InB a m
    end.

Fixpoint newEntries (g : typeEnv) (l : list (name * name)) (max : nat) : typeEnv :=
    match l with
    | (a1, a2) :: tail =>
      let (_, notNew) := InB (a1, a2) g in
      if notNew
      then newEntries g tail max
      else
        let (pair, _) := InB (a1, a2 - max) g in
        ((a1, a2), fst pair, snd pair) :: newEntries g tail max
    | nil => nil
    end.

Definition notHidden c1 c2 act :=
    match act with
    | aIn a1 a2 b1 b2
    | aOut a1 a2 b1 b2 =>
      (a1, a2)<> (c1, c2) /\ (b1, b2) <> (c1, c2)
    | aTau _ _ => True
    end.

Inductive lts (g : typeEnv) :
    dproc ->  action -> typeEnv -> dproc -> NoDup (domain g) -> Prop :=
  | parL : forall p1 a g' q p2 pf,
      lts g p1 a g' p2 pf ->
      lts g (dPar p1 q) a g' (dPar p2 q) pf
  | lOut : forall p a1 a2 b1 b2 pf t t1 t2,
      type_remove t1 t t2 ->
      In ((a1, a2), vis, Chan lin out t) g ->
      In ((b1, b2), vis, t1) g ->
      lts g (dOut a1 a2 b1 b2 p) (aOut a1 a2 b1 b2)
          (((a1, a2), vis, Chan lin empty t)
             :: ((b1, b2), vis, t2)
             :: (removeEntry (a1, a2) (removeEntry (b1, b2) g))) p pf
  | uOut : forall pol p a1 a2 b1 b2 pf t t1 t2,
      pol = out \/ pol = io ->
      type_remove t1 t t2 ->
      In ((a1, a2), vis, Chan un pol t) g ->
      In ((b1, b2), vis, t1) g ->
      lts g (dOut a1 a2 b1 b2 p) (aOut a1 a2 b1 b2)
          (((b1, b2), vis, t2) :: removeEntry (b1, b2) g) p pf
  | lIn : forall p a1 a2 x1 x2 b1 b2 pf f t t1 t2,
      type_plus t1 t t2->
      f <> hid ->
      In ((a1, a2), vis, Chan lin inp t) g ->
      In ((b1, b2), f, t1) g ->
      lts g (dInp a1 a2 x1 x2 p) (aIn a1 a2 b1 b2)
          (((a1, a2), vis, Chan lin empty t)
             :: ((b1, b2), vis, t2)
             :: (removeEntry (a1, a2) (removeEntry (b1, b2) g)))
          (pmap p x1 x2 b1 b2) pf
  | uIn : forall pol p a1 a2 x1 x2 b1 b2 pf f t t1 t2,
      pol = inp \/ pol = io ->
      type_plus t1 t t2 ->
      f <> hid ->
      In ((a1, a2), vis, Chan un pol t) g ->
      In ((b1, b2), f, t1) g ->
      lts g (dInp a1 a2 x1 x2 p) (aIn a1 a2 b1 b2)
          (((b1, b2), vis, t2) :: removeEntry (b1, b2) g)
          (pmap p x1 x2 b1 b2) pf
  | uRin : forall pol p a1 a2 x1 x2 b1 b2 pf f t t1 t2,
      pol = inp \/ pol = io ->
      type_plus t1 t t2 ->
      f <> hid ->
      In ((a1, a2), vis, Chan un pol t) g ->
      In ((b1, b2), f, t1) g ->
      let q := dep_relabel p (domain g) pf in
      lts g (dBang a1 a2 x1 x2 p) (aIn a1 a2 b1 b2)
          ((newEntries g (secLabs q) (max (domain g)))
             ++ (((b1, b2), vis, t2) :: removeEntry (b1, b2) g))
          (dPar (pmap p x1 x2 b1 b2) (dBang a1 a2 x1 x2 q)) pf
  | lcomL : forall p1 p2 q1 q2 a1 a2 b1 b2 s s1 t
                   pf pf1 pf2,
      let g0 := removeEntry (a1, a2) (removeEntry (b1, b2) g) in
      type_remove s t s1 ->
      In ((a1, a2), vis, Chan lin io t) g ->
      In ((b1, b2), vis, s) g ->
      lts
        (((a1, a2), vis, Chan lin out t)
           :: ((b1, b2), vis, s)
           :: g0)
        p1
        (aOut a1 a2 b1 b2)
        (((a1, a2), vis, Chan lin empty t)
           :: ((b1, b2), vis, s1)
           :: g0)
        p2
        pf1 ->
      lts
        (((a1, a2), vis, Chan lin inp t)
           :: ((b1, b2), vis, s1)
           :: g0)
        q1
        (aIn a1 a2 b1 b2)
        (((a1, a2), vis, Chan lin empty t)
           :: ((b1, b2), vis, s)
           :: g0)
        q2
        pf2 ->
      lts g (dPar p1 q1) (aTau a1 a2)
          (((a1, a2), vis, Chan lin empty t)
             :: ((b1, b2), vis, s)
             :: g0) (dPar p2 q2) pf
  | lclsL : forall p1 p2 q1 q2 a1 a2 b1 b2 s s1 t
                   pf pf1 pf2,
      let g0 := removeEntry (a1, a2) (removeEntry (b1, b2) g) in
      let g3 := (((a1, a2), vis, Chan lin empty t)
                   :: ((b1, b2), hid, s)
                   :: g0) in
      type_remove s t s1 ->
      In ((a1, a2), vis, Chan lin io t) g ->
      In ((b1, b2), hid, s) g ->
      lts
        (((a1, a2), vis, Chan lin out t)
           :: ((b1, b2), hid, s)
           :: g0)
        p1
        (aOut a1 a2 b1 b2)
        (((a1, a2), vis, Chan lin empty t)
           :: ((b1, b2), vis, s1)
           :: g0)
        p2
        pf1 ->
      lts
        (((a1, a2), vis, Chan lin inp t)
           :: ((b1, b2), ill, s1)
           :: g0)
        q1
        (aIn a1 a2 b1 b2)
        (((a1, a2), vis, Chan lin empty t)
           :: ((b1, b2), vis, s)
           :: g0)
        q2
        pf2 ->
      lts g (dPar p1 q1) (aTau a1 a2) g3 (dNu b1 b2 (dPar p2 q2)) pf
  | ucomL : forall g3 p1 p2 q1 q2 a1 a2 b1 b2 s s1 t
                   pf pf1 pf2,
      let g0 := removeEntry (b1, b2) g in
      let g' := ((b1, b2), vis, s1) :: g0 in
      type_remove s t s1 ->
      In ((a1, a2), vis, Chan un io t) g ->
      In ((b1, b2), vis, s) g ->
      lts
        g
        p1
        (aOut a1 a2 b1 b2)
        (((b1, b2), vis, s1) :: g0)
        p2
        pf1 ->
      lts
        g'
        q1
        (aIn a1 a2 b1 b2)
        g3
        q2
        pf2 ->
      In ((a1, a2), vis, Chan un io t) g3 ->
      In ((b1, b2), vis, s) g3 ->
      lts g (dPar p1 q1) (aTau a1 a2) g3 (dPar p2 q2) pf
  | uclsL : forall g3 p1 p2 q1 q2 a1 a2 b1 b2 s s1 t
                   pf pf1 pf2,
      let g0 := removeEntry (b1, b2) g in
      let g' := ((b1, b2), ill, s1) :: g0 in
      type_remove s t s1 ->
      In ((a1, a2), vis, Chan un io t) g ->
      In ((b1, b2), hid, s) g ->
      lts
        g
        p1
        (aOut a1 a2 b1 b2)
        (((b1, b2), vis, s1) :: g0)
        p2
        pf1 ->
      lts
        g'
        q1
        (aIn a1 a2 b1 b2)
        g3
        q2
        pf2 ->
      In ((a1, a2), vis, Chan un io t) g3 ->
      In ((b1, b2), vis, s) g3 ->
      lts g (dPar p1 q1) (aTau a1 a2)
          (((b1, b2), hid, s) :: removeEntry (b1, b2) g3)
          (dNu b1 b2 (dPar p2 q2)) pf
  | open : forall p a1 a2 b1 b2 g' p' t pf pf1,
      In ((b1, b2), hid, t) g ->
      lts (((b1, b2), vis, t) :: removeEntry (b1, b2) g)
          p (aOut a1 a2 b1 b2)
          g' p' pf1 ->
      lts g (dNu b1 b2 p)
          (aOut a1 a2 b1 b2)
          g' p' pf
  | hide : forall b1 b2 t p a  h1 h2 h' h'' t' p' pf pf1,
      lts (h1 ++ (b1, b2, vis, t) :: h2) p a
          (h' ++ (b1, b2, vis, t') :: h'') p' pf1 ->
      notHidden b1 b2 a ->
      g = h1 ++ (b1, b2, hid, t) :: h2 ->
      lts g (dNu b1 b2 p) a (h' ++ (b1, b2, hid, t') :: h'') (dNu b1 b2 p') pf
  | parR : forall p1 a g' q p2 pf,
      lts g p1 a g' p2 pf ->
      lts g (dPar q p1) a g' (dPar q p2) pf
  | lcomR : forall p1 p2 q1 q2 a1 a2 b1 b2 s s1 t
                   pf pf1 pf2,
      let g0 := removeEntry (a1, a2) (removeEntry (b1, b2) g) in
      type_remove s t s1 ->
      In ((a1, a2), vis, Chan lin io t) g ->
      In ((b1, b2), vis, s) g ->
      lts
        (((a1, a2), vis, Chan lin out t)
           :: ((b1, b2), vis, s)
           :: g0)
        p1
        (aOut a1 a2 b1 b2)
        (((a1, a2), vis, Chan lin empty t)
           :: ((b1, b2), vis, s1)
           :: g0)
        p2
        pf1 ->
      lts
        (((a1, a2), vis, Chan lin inp t)
           :: ((b1, b2), vis, s1)
           :: g0)
        q1
        (aIn a1 a2 b1 b2)
        (((a1, a2), vis, Chan lin empty t)
           :: ((b1, b2), vis, s)
           :: g0)
        q2
        pf2 ->
      lts g (dPar q1 p1) (aTau a1 a2)
          (((a1, a2), vis, Chan lin empty t)
             :: ((b1, b2), vis, s)
             :: g0) (dPar q2 p2) pf
  | lclsR : forall p1 p2 q1 q2 a1 a2 b1 b2 s s1 t
                   pf pf1 pf2,
      let g0 := removeEntry (a1, a2) (removeEntry (b1, b2) g) in
      let g3 := (((a1, a2), vis, Chan lin empty t)
                   :: ((b1, b2), hid, s)
                   :: g0) in
      type_remove s t s1 ->
      In ((a1, a2), vis, Chan lin io t) g ->
      In ((b1, b2), hid, s) g ->
      lts
        (((a1, a2), vis, Chan lin out t)
           :: ((b1, b2), hid, s)
           :: g0)
        p1
        (aOut a1 a2 b1 b2)
        (((a1, a2), vis, Chan lin empty t)
           :: ((b1, b2), vis, s1)
           :: g0)
        p2
        pf1 ->
      lts
        (((a1, a2), vis, Chan lin inp t)
           :: ((b1, b2), ill, s1)
           :: g0)
        q1
        (aIn a1 a2 b1 b2)
        (((a1, a2), vis, Chan lin empty t)
           :: ((b1, b2), vis, s)
           :: g0)
        q2
        pf2 ->
      lts g (dPar q1 p1) (aTau a1 a2) g3 (dNu b1 b2 (dPar q2 p2)) pf
  | ucomR : forall g3 p1 p2 q1 q2 a1 a2 b1 b2 s s1 t
                   pf pf1 pf2,
      let g0 := removeEntry (b1, b2) g in
      let g' := ((b1, b2), vis, s1) :: g0 in
      type_remove s t s1 ->
      In ((a1, a2), vis, Chan un io t) g ->
      In ((b1, b2), vis, s) g ->
      lts
        g
        p1
        (aOut a1 a2 b1 b2)
        (((b1, b2), vis, s1) :: g0)
        p2
        pf1 ->
      lts
        g'
        q1
        (aIn a1 a2 b1 b2)
        g3
        q2
        pf2 ->
      In ((a1, a2), vis, Chan un io t) g3 ->
      In ((b1, b2), vis, s) g3 ->
      lts g (dPar q1 p1) (aTau a1 a2) g3 (dPar q2 p2) pf
  | uclsR : forall g3 p1 p2 q1 q2 a1 a2 b1 b2 s s1 t
                   pf pf1 pf2,
      let g0 := removeEntry (b1, b2) g in
      let g' := ((b1, b2), ill, s1) :: g0 in
      type_remove s t s1 ->
      In ((a1, a2), vis, Chan un io t) g ->
      In ((b1, b2), hid, s) g ->
      lts
        g
        p1
        (aOut a1 a2 b1 b2)
        (((b1, b2), vis, s1) :: g0)
        p2
        pf1 ->
      lts
        g'
        q1
        (aIn a1 a2 b1 b2)
        g3
        q2
        pf2 ->
      In ((a1, a2), vis, Chan un io t) g3 ->
      In ((b1, b2), vis, s) g3 ->
      lts g (dPar q1 p1) (aTau a1 a2)
          (((b1, b2), hid, s) :: removeEntry (b1, b2) g3)
          (dNu b1 b2 (dPar q2 p2)) pf.

End Semantics.
