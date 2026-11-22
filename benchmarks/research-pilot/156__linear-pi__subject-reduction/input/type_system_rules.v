Require Import Bool Arith ZArith List Eqdep Lia PeanoNat Relations EquivDec Program.Equality String operations pi_syntax pairEq type_system.

Section TypeSystemRules.

Inductive cons (g : typeEnv) (pf : isMap g) : Prop :=
  | Co_nil : g = nil -> cons g pf
  | Co_top : forall n pf',
      typeOf g n Top ->
      cons (removeEntry n g) pf' ->
      cons g pf
  | Co_un : forall n p t pf',
      typeOf g n (Chan un p t) ->
      cons (removeEntry n g) pf' ->
      cons g pf
  | Co_lin : forall n t pf',
      typeOf g n (Chan lin empty t) ->
      cons (removeEntry n g) pf' ->
      cons g pf.

Inductive typeCheck (g : typeEnv) (pf : isMap g) : dproc -> Prop :=
  | TNil :  cons g pf -> typeCheck g pf dZero
  | TNew : forall p n t pf1,
      In (n, hid, t) g ->
      typeCheck ((n, vis, t) :: (removeEntry n g)) pf1 p ->
      typeCheck g  pf (dNu (fst n) (snd n) p)
  | TPar : forall g1 g2 p1 p2 pf1 pf2,
      tEnv_split g1 g2 g pf1 pf2 pf ->
      typeCheck g1 pf1 p1 ->
      typeCheck g2 pf2 p2 ->
      typeCheck g pf (dPar p1 p2)
  | TOutL : forall u p t v t' q t1 t2 pf1,
      type_remove (Chan lin p t) (Chan lin out t) t1 ->
      type_remove t' t t2 ->
      In (u, vis, Chan lin p t) g ->
      In (v, vis, t') g ->
      typeCheck
        ((u, vis, t1) :: (v, vis, t2) :: (removeEntry v (removeEntry u g))) pf1 q ->
      typeCheck
        g pf (dOut (fst u) (snd u) (fst v) (snd v) q)
  | TOutUn : forall u p t v t' q t2 pf1,
      (p = io \/ p = out) ->
      type_remove t' t t2 ->
      In (u, vis, Chan un p t) g ->
      In (v, vis, t') g ->
      typeCheck
        ((v, vis, t2) :: (removeEntry v g)) pf1 q ->
      typeCheck
        g pf (dOut (fst u) (snd u) (fst v) (snd v) q)
  | TInL : forall u p t x q t1 pf1,
      type_remove (Chan lin p t) (Chan lin inp t) t1 ->
      In (u, vis, Chan lin p t) g ->
      ~In x (domain g) ->
      snd x < max (domain g) ->
      typeCheck
        ((u, vis, t1) :: (x, vis, t) :: removeEntry u g) pf1 q ->
      typeCheck
        g pf (dInp (fst u) (snd u) (fst x) (snd x) q)
  | TInUn : forall u p t x q pf1,
      (p = io \/ p = inp) ->
      In (u, vis, Chan un p t) g ->
      ~In x (domain g) ->
      snd x < max (domain g) ->
      typeCheck ((x, vis, t) ::  g) pf1 q ->
      typeCheck
        g pf (dInp (fst u) (snd u) (fst x) (snd x) q)
  | TInU : forall u p t x q pf1 pf2,
      (p = io \/ p = inp) ->
      In (u, vis, Chan un p t) g ->
      ~In x (domain g) ->
      snd x < max (domain g) ->
      cons (vis_proj g ++ ill_proj g) pf2 ->
      typeCheck ( (x, vis, t) :: g) pf1 q ->
      typeCheck
        g pf (dBang (fst u) (snd u) (fst x) (snd x) q).

End TypeSystemRules.
