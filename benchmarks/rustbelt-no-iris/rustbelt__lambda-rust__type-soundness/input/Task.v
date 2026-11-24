Require Import Typing.
Local Open Scope string_scope.

Definition empty_scope := Scope [] [] [].
Definition main_type := TyFn 0 [] [] unit_type.
Definition exit_cont := Rec BAnon [BAnon] poison.

(* The operational conclusion of type_soundness_closed. Its original
   Iris-typed premise is replaced by the closed syntactic main interface. *)
Theorem type_soundness_closed : forall main threads heap,
  typed_instruction empty_scope [] [] [] main "main" [named "main" main_type] ->
  rtc pool_step ([App (erase_instruction main) [exit_cont]], (∅ : state))
                (threads, heap) ->
  nonracing_threadpool threads heap /\
  (forall e, e ∈ threads -> is_Some (to_val e) \/ reducible e heap).
