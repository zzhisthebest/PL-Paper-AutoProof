Require Import Definitions.Syntax Definitions.Semantics Definitions.Typing
  Definitions.CTSanity.

Theorem type_soundness : forall (e e':expr) (t:type),
    EvalsTo e e' -> Hastype Empty e t -> isValue e' \/  exists e'', Step e' e''.
