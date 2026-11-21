Require Import Definitions.Syntax Definitions.Semantics Definitions.Typing
  Definitions.CTSanity Definitions.SubDenotation.

Theorem logical_soundness: forall (e e':expr) (t:type) g b ps,
  Hastype g e (TRefn b ps) -> WFEnv g -> Terminating g e -> LEntails g (psubBV e ps).
