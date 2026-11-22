Set Implicit Arguments.

Require Import LibExtra DotTactics.

Require Import Coq.Program.Equality.

Require Import AbstractSyntax TypingMode GeneralTyping RecordTypes InertContext Narrowing Indep.

Section WithTypingMode.

Context (typing_mode: Mode).

Reserved Notation "G '⊢!' x '∶' T '⪼' U" (at level 40, x at level 59).

Inductive precise_flow : var -> ctx -> typ -> typ -> Prop :=





  | pf_bind : forall x G T,
      ctx_binds x T G ->
      G ⊢! x ∶ T ⪼ T




  | pf_open : forall x G T U,
      G ⊢! x ∶ T ⪼ typ_bnd U ->
      G ⊢! x ∶ T ⪼ open x U




  | pf_and1 : forall x G T U1 U2,
      G ⊢! x ∶ T ⪼ typ_and U1 U2 ->
      G ⊢! x ∶ T ⪼ U1




  | pf_and2 : forall x G T U1 U2,
      G ⊢! x ∶ T ⪼ typ_and U1 U2 ->
      G ⊢! x ∶ T ⪼ U2

where "G '⊢!' x '∶' T '⪼' U" := (precise_flow x G T U).

End WithTypingMode.

Notation "G '⊢!' x '∶' T '⪼' U" := (precise_flow x G T U) (at level 40, x at level 59).

Section WithTypingMode.

Context (typing_mode : Mode).

Inductive open_proj (x : var) (T : typ) : typ -> Prop :=
| open_proj_refl : open_proj x T T
| open_proj_open : forall U, open_proj x T (typ_bnd U) ->
                        open_proj x T (open x U)
| open_proj1 : forall U1 U2, open_proj x T (typ_and U1 U2) ->
                        open_proj x T U1
| open_proj2 : forall U1 U2, open_proj x T (typ_and U1 U2) ->
                        open_proj x T U2.

End WithTypingMode.
