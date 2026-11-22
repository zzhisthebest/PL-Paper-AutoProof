Set Implicit Arguments.

Require Import Coq.Init.Datatypes.

Require Import LibExtra DotTactics.

Require Import Coq.Program.Equality.

Require Import AbstractSyntax GeneralTyping Similarity SyntaxSimilarity OperationalSemantics HeapUpdate Deref Defs ConfigValid.

Require Import HeapCorrespondence EnvCorrespondence.

Require Import ConfigTyping ConfigVarkinds TFree.

Require Import Safety.

Instance similar_conf: Similar config := {
  similar xs1 xs2 c1 c2 :=
    match (c1, c2) with
    | ((t1 ; s1 ; S1 ; e1 ; Lv1), (t2 ; s2 ; S2 ; e2 ; Lv2)) =>
      similar xs1 xs2 t1 t2 /\
      similar xs1 xs2 s1 s2 /\
      similar xs1 xs2 S1 S2 /\
      similar xs1 xs2 e1 e2
    end
}.

Definition similar_conf_any C1 C2 :=
  exists xs1 xs2, length xs1 = length xs2 /\ similar xs1 xs2 C1 C2.

Definition similar_conf_1to1 C1 C2 :=
  exists xs1 xs2, vars_conf_unique xs1 C1 /\ vars_conf_unique xs2 C2 /\ length xs1 = length xs2 /\ similar xs1 xs2 C1 C2.

Section SimilarOut.

Context {A: Set} {AS: Similar A} {AF: FreeVar A} {ASC: SimilarCommon AS} {ASO: SimilarOut AS}.

Let SW: SimilarWith (env A) := similar_env_with AS.

End SimilarOut.
