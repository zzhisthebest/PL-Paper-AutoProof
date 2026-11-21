Set Implicit Arguments.

Require Import Coq.Program.Equality.

Require Import Definitions Binding.

Definition is_sngl T := exists p, T = {{ p }}.

Definition inert_sngl T := inert_typ T \/ is_sngl T.
