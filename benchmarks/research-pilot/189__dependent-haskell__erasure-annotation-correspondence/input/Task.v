Require Import Language.

Theorem erase_mutual :
  (forall G a A, AnnTyping G a A ->
          Typing (erase_context G) (erase_tm a) (erase_tm A)) /\
  (forall G phi, AnnPropWff G phi ->
          PropWff (erase_context G) (erase_constraint phi)) /\
  (forall G D g p1 p2, AnnIso G D g p1 p2 ->
          Iso (erase_context G) D
              (erase_constraint p1) (erase_constraint p2)) /\
  (forall G D g a b,
      AnnDefEq G D g a b ->
      forall A, AnnTyping G a A ->
             DefEq (erase_context G) D (erase_tm a) (erase_tm b) (erase_tm A)) /\
  (forall G, AnnCtx G -> Ctx (erase_context G) /\
    forall c t, binds c t G -> binds c (erase_sort t) (erase_context G)).

Theorem annotation_mutual :
  (forall G a A, Typing G a A ->
     forall G0, erase_context G0 = G -> AnnCtx G0 ->
     exists a0 A0,
         (erase_tm a0) = a /\
         (erase_tm A0) = A /\
         AnnTyping G0 a0 A0) /\
  (forall G phi, PropWff G phi ->
     forall G0, erase_context G0 = G -> AnnCtx G0 ->
     exists phi0,
          erase_constraint phi0 = phi /\
          AnnPropWff G0 phi0) /\
  (forall G D p1 p2, Iso G D p1 p2 ->
     forall G0, erase_context G0 = G -> AnnCtx G0 ->
     exists g0 p1' p2',
       (erase_constraint p1') = p1 /\
       (erase_constraint p2') = p2 /\
       AnnIso G0 D g0 p1' p2') /\
  (forall G D a b A, DefEq G D a b A ->
     forall G0, erase_context G0 = G -> AnnCtx G0 ->
     exists g a0 b0 A0,
       (erase_tm a0) = a /\
       (erase_tm b0) = b /\
       (erase_tm A0) = A /\
       AnnDefEq G0 D g a0 b0 /\ AnnTyping G0 a0 A0 /\ AnnTyping G0 b0 A0) /\
  (forall G, Ctx G -> True).
