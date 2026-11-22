Require Import Bool List Lia PeanoNat operations pi_syntax pairEq.

Section TypeSystem.

Inductive pol : Set := empty | inp | out | io.

Inductive mode : Set := lin | un.

Inductive piType : Set :=
  | Chan : mode -> pol -> piType -> piType
  | Top : piType.

Inductive flag : Set := hid | ill | vis.

Definition isMap (l : list ((name * name) * flag * piType)) :=
    forall x f1 t1 f2 t2,
      In (x, f1, t1) l /\ In (x, f2, t2) l ->
      f1 = f2 /\ t1 = t2.

Definition typeEnv := list ((name * name) * flag * piType).

Fixpoint pol_eq (p1 p2 : pol) : bool :=
    match p1, p2 with
    | empty, empty | inp, inp | out, out | io, io => true
    | _, _  => false
    end.

Fixpoint mode_eq (m1 m2 : mode) : bool :=
    match m1, m2 with
    | lin, lin | un, un => true
    | _, _ => false
    end.

Fixpoint type_eq (t1 t2 : piType) : bool :=
    match t1, t2 with
    | Top, Top => true
    | Chan m1 p1 t1, Chan m2 p2 t2 =>
      if mode_eq m1 m2
      then (if pol_eq p1 p2 then type_eq t1 t2 else false)
      else false
    | _, _ => false
    end.

Fixpoint flag_eq (f1 f2 : flag) : bool :=
    match f1, f2 with
    | hid, hid | ill, ill | vis, vis => true
    | _, _  => false
    end.

Fixpoint removeEntry (y : (name * name)) (g : typeEnv) :=
    match g with
    | nil => nil
    | (x, f, t) :: tail =>
      if pair_eq x y
      then
        tail
      else (x, f, t) :: removeEntry y tail
    end.

Inductive typeOf : typeEnv -> (name * name) -> piType -> Prop :=
  | T_Entry : forall g n f t,
      In (n, f, t) g -> typeOf g n t.

Inductive flagOf : typeEnv -> (name * name) -> flag -> Prop :=
  | F_Entry : forall g n f t,
      In (n, f, t) g -> flagOf g n f.

Fixpoint pol_cup (p1 p2 : pol) : pol :=
    match p1, p2 with
    | empty, _ => p2
    | io, _ => io
    | _, io => io
    | out, inp => io
    | out, _ => out
    | inp, out => io
    | inp, _ => inp
    end.

Inductive pol_plus : pol -> pol -> pol -> Prop :=
  | Pp_emptyL : forall p, pol_plus empty p p
  | Pp_emptyR : forall p, pol_plus p empty p
  | Pp_inpL:  pol_plus inp out io
  | Pp_inpR:  pol_plus out inp io.

Inductive type_plus : piType -> piType -> piType -> Prop :=
  | Tp_Base : type_plus Top Top Top
  | Tp_LinPlus : forall p1 p2 p t,
      pol_plus p1 p2 p ->
      type_plus (Chan lin p1 t) (Chan lin p2 t) (Chan lin p t)
  | Tp_UnPlus : forall p1 p2 t,
      type_plus (Chan un p1 t) (Chan un p2 t) (Chan un (pol_cup p1 p2) t).

Definition is_linear (t : piType) :=
    exists p t', t = Chan lin p t'.

Definition is_unrestricted (t : piType) :=
    exists p t', t = Chan un p t'.

Inductive type_sub : piType -> piType -> Prop :=
  | Ts_id : forall t,
      type_sub t t
  | Ts_empty : forall m q t,
      type_sub (Chan m empty t) (Chan m q t)
  | Ts_inp : forall m t,
      type_sub (Chan m inp t) (Chan m io t)
  | Ts_out : forall m t,
      type_sub (Chan m out t) (Chan m io t).

Definition type_remove (t : piType) (s : piType) (r : piType) :=
    type_sub s t /\ type_plus s r t /\ (is_unrestricted t -> r = t).

Inductive flag_plus : flag -> flag -> flag -> Prop :=
  | Fp_hi : flag_plus hid ill hid
  | Fp_ih : flag_plus ill hid hid
  | Fp_vv : flag_plus vis vis vis
  | Fp_ii : flag_plus ill ill ill.

Inductive tEnv_split (g1 : typeEnv) (g2 : typeEnv) (g3 : typeEnv)
            (pf1 : isMap g1) (pf2 : isMap g2) (pf3 : isMap g3) : Prop :=
  | SpNil : g1 = nil -> g2 = nil -> g3 = nil ->
            tEnv_split g1 g2 g3 pf1 pf2 pf3
  | SpLin : forall n f f' g p q p' t g''' pf' pf'' pf''',
      flag_plus f g f'->
      pol_plus p q p' ->
      In (n, f, Chan lin p t) g1 ->
      In (n, g, Chan lin q t) g2 ->
      tEnv_split (removeEntry n g1) (removeEntry n g2) g''' pf' pf'' pf''' ->
      removeEntry n g3 = g''' ->
      flagOf g3 n f' ->
      typeOf g3 n (Chan lin p' t) ->
      tEnv_split g1 g2 g3 pf1 pf2 pf3
  | SpUn : forall n f f' g p t g''' pf' pf'' pf''',
      flag_plus f g f'->
      In (n, f, Chan un p t) g1 ->
      In (n, g, Chan un p t) g2 ->
      tEnv_split (removeEntry n g1) (removeEntry n g2) g''' pf' pf'' pf''' ->
      removeEntry n g3 = g''' ->
      flagOf g3 n f' ->
      typeOf g3 n (Chan un p t) ->
      tEnv_split g1 g2 g3 pf1 pf2 pf3
  | SpTop :  forall n f f' g g''' pf' pf'' pf''',
      flag_plus f g f'->
      In (n, f, Top) g1 ->
      In (n, g, Top) g2 ->
      tEnv_split (removeEntry n g1) (removeEntry n g2) g''' pf' pf'' pf''' ->
      removeEntry n g3 = g''' ->
      flagOf g3 n f' ->
      typeOf g3 n Top ->
      tEnv_split g1 g2 g3 pf1 pf2 pf3.

Fixpoint domain (g: typeEnv) : list (nat * nat) :=
    match g with
    | (x, _, _) :: t => x :: domain t
    | nil => nil
    end.

Fixpoint hid_proj (g : typeEnv) : typeEnv:=
    match g with
    | nil => nil
    | (a1, a2, hid, t) :: m =>
      (a1, a2, hid, t) :: hid_proj m
    |  (a1, a2, f, t) :: m =>
       hid_proj m
    end.

Fixpoint vis_proj (g : typeEnv) : typeEnv:=
    match g with
    | nil => nil
    | (a1, a2, vis, t) :: m =>
      (a1, a2, vis, t) :: vis_proj m
    |  (a1, a2, f, t) :: m =>
       vis_proj m
    end.

Fixpoint ill_proj (g : typeEnv) : typeEnv:=
    match g with
    | nil => nil
    | (a1, a2, ill, t) :: m =>
      (a1, a2, ill, t) :: ill_proj m
    |  (a1, a2, f, t) :: m =>
       ill_proj m
    end.

End TypeSystem.
