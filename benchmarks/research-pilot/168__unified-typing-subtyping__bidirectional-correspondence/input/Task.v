Set Implicit Arguments.

From TLC Require Import LibLN.

Require Import Main_ott Main_Infra.

Implicit Types x : var.

Implicit Types G : env.

Fixpoint remove_anno (e : trm) {struct e} : trm :=
  match e with
  | trm_var_b i        => trm_var_b i
  | trm_var_f x        => trm_var_f x
  | trm_star          => trm_star
  | trm_top           => trm_top
  | trm_app t1 t2     => trm_app (remove_anno t1) (remove_anno t2)
  | trm_abs t0 t1 t2  => trm_abs (remove_anno t0) (remove_anno t1) (remove_anno t2)
  | trm_prod t0 t1 t2 => trm_prod (remove_anno t0) (remove_anno t1) (remove_anno t2)
  | trm_castup t1 t2  => trm_castup (remove_anno t1) (remove_anno t2)
  | trm_castdn t1     => trm_castdn (remove_anno t1)
  | trm_anno t1 t2    => remove_anno t1
  end.

Notation "[# e #]" := (remove_anno e) (at level 2).

Definition rem_anno_env (p:binding) :=
  match p with
  | bind_sub e A => bind_sub (remove_anno e) (remove_anno A)
  end.

Notation "{# E #}" := (map rem_anno_env E) (at level 2).

Inductive dsub : env -> trm -> trm -> Prop :=
  | dsub_star : forall G, ok G -> dsub G trm_star trm_star
  | dsub_var_refl : forall G x e A,
      ok G -> binds x (bind_sub e A) G -> dsub G (trm_var_f x) (trm_var_f x)
  | dsub_var_trans : forall e1 A G x e2,
      binds x (bind_sub e1 A) G -> dsub G e1 e2 ->
      dsub G (trm_var_f x) e2
  | dsub_top : forall G e,
      ok G -> lc_trm e -> dsub G e trm_top
  | dsub_lam : forall L G e1 e2 e3 A,
      ok G ->
      (forall x, x \notin L -> dsub (G & x ~ bind_sub [#e3#] [#A#]) (e1 ^ x) (e2 ^ x)) ->
      dsub G (trm_abs e3 A e1) (trm_abs e3 A e2)
  | dsub_app : forall G e1 e2 A,
      lc_trm A ->
      dsub G e1 e2 -> dsub G (trm_app e1 A) (trm_app e2 A)
  | dsub_pi : forall L G e A B C D,
      dsub G C A ->
      (forall x, x \notin L -> dsub (G & x ~ bind_sub [#e#] [#C#]) (B ^ x) (D ^ x)) ->
      dsub G (trm_prod e A B) (trm_prod e C D)
  | dsub_castup : forall G A e1 e2,
      lc_trm A -> dsub G e1 e2 -> dsub G (trm_castup A e1) (trm_castup A e2)
  | dsub_castdn : forall G e1 e2,
      dsub G e1 e2 -> dsub G (trm_castdn e1) (trm_castdn e2).

Inductive dir := inf | chk.

Inductive dtyping : dir -> env -> trm -> trm -> Prop :=
  | dtyping_star : forall G,
      dwf G -> dtyping inf G trm_star trm_star
  | dtyping_var : forall e G x A,
      dwf G -> binds x (bind_sub e A) G -> dtyping inf G (trm_var_f x) A
  | dtyping_top : forall G A,
      dtyping chk G A trm_star -> dtyping chk G trm_top A
  | dtyping_lam : forall L G e1 e2 A B,
      dtyping chk G e1 [#A#] ->
      dtyping chk G A trm_star ->
      (forall x, x \notin L ->
                 dtyping inf (G & x ~ bind_sub [#e1#] [#A#]) (e2 ^ x) (B ^ x)) ->
      dtyping inf G (trm_abs e1 A e2) (trm_prod [#e1#] [#A#] B)
  | dtyping_app : forall e3 G e A B C,
      dtyping chk G A B ->
      dsub G [#A#] e3 ->
      dtyping inf G e (trm_prod e3 B C) ->
      dtyping inf G (trm_app e A) (C ^^ [#A#])
  | dtyping_pi : forall L G e A B,
      dtyping chk G e [#A#] ->
      dtyping chk G A trm_star ->
      (forall x, x \notin L ->
        dtyping chk (G & x ~ bind_sub [#e#] [#A#]) (B ^ x) trm_star) ->
      dtyping inf G (trm_prod e A B) trm_star
  | dtyping_castup : forall G e A B,
      dtyping chk G B trm_star ->
      dtyping inf G e A ->
      reduct [#B#] [#A#] ->
      dtyping inf G (trm_castup B e) [#B#]
  | dtyping_castdn : forall G e A B,
      dtyping chk G B trm_star ->
      dtyping inf G e A ->
      reduct [#A#] [#B#] ->
      dtyping chk G (trm_castdn e) B
  | dtyping_anno : forall G e A,
      dtyping chk G e A ->
      dtyping chk G A trm_star ->
      dtyping inf G (trm_anno e A) [#A#]
  | dtyping_sub : forall A G e B,
      dtyping inf G e A ->
      dsub G A [#B#] ->
      dtyping chk G B trm_star ->
      dtyping chk G e B
  | dtyping_chk : forall G e A,
      dtyping inf G e A ->
      dtyping chk G e A

with dwf : env -> Prop :=
  | dwf_nil : dwf empty
  | dwf_cons : forall G x e A,
      x # G ->
      dtyping chk G e [#A#] ->
      dtyping chk G A trm_star ->
      dwf (G & x ~ bind_sub [#e#] [#A#]).

Theorem sub_to_bidir : forall G e1 e2 A,
  sub G e1 e2 A ->
  dsub G e1 e2 /\
  exists e1' e2',
    dtyping inf G e1' A /\ dtyping inf G e2' A /\
    [#e1'#] = e1 /\ [#e2'#] = e2.

Theorem bidir_to_sub : forall G d e1 e2 A,
  dtyping d G e1 A ->
  dtyping d G e2 A ->
  dsub G e1 e2 ->
  sub {#G#} [#e1#] [#e2#] [#A#].
