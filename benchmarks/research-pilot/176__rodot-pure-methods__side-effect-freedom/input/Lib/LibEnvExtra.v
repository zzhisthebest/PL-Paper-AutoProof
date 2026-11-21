Set Implicit Arguments.

From TLC Require Import LibEnv LibVar LibLN LibTactics.

Require Import LibVarExtra LibListExtra LibSetExtra LibFreshExtra.

Class EnvConjunctive (A: Type) (P: env A -> Prop) (Q: var -> A -> Prop) := {

  env_conj_empty: (P empty) ;
  env_conj_push E x v: (P E) -> (Q x v) -> (P (E & x ~ v)) ;

  env_conj_push_item E x v: (P (E & x ~ v)) -> (Q x v) ;
  env_conj_push_inv E x v: (P (E & x ~ v)) -> (P E)
}.
