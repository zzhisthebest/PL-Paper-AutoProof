Set Implicit Arguments.

Require Import LibExtra SyntaxClasses.

Require Import AbstractSyntax.

Class DefsConjunctive (P: defs -> Prop) (Q: def -> Prop) := {

  defs_conj_nil: (P defs_nil) ;
  defs_conj_cons ds d: (P ds) -> (Q d) -> (P (defs_cons ds d)) ;

  defs_conj_cons_def ds d: (P (defs_cons ds d)) -> (Q d) ;
  defs_conj_cons_inv ds d: (P (defs_cons ds d)) -> (P ds)
}.
