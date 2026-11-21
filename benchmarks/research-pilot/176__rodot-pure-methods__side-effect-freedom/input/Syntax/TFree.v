Set Implicit Arguments.

Require Import LibExtra SyntaxClasses.

Require Import AbstractSyntax Context Defs Heap.

Class TFree(A : Set) := tfree: var -> A -> Prop.

Inductive tfree_trm: TFree trm :=

| tfree_trm_var v:
  tfree_trm v (trm_var (avar_f v))

| tfree_trm_read v1 l:
  tfree_trm v1 (trm_read (avar_f v1) l)

| tfree_trm_apply_l v1 a2:
  tfree_trm v1 (trm_apply (avar_f v1) a2)
| tfree_trm_apply_r a1 v2:
  tfree_trm v2 (trm_apply a1 (avar_f v2))

| tfree_trm_let_l v t1 t2:
  tfree_trm v t1 ->
  tfree_trm v (trm_let t1 t2)
| tfree_trm_let_r v t1 t2:
  tfree_trm v t2 ->
  tfree_trm v (trm_let t1 t2)

| tfree_trm_lit_l v t1 t2:
  tfree_lit v t1 ->
  tfree_trm v (trm_lit t1 t2)
| tfree_trm_lit_r v t1 t2:
  tfree_trm v t2 ->
  tfree_trm v (trm_lit t1 t2)

| tfree_trm_write_l v1 a2 l:
  tfree_trm v1 (trm_write (avar_f v1) l a2)
| tfree_trm_write_r a1 v2 l:
  tfree_trm v2 (trm_write a1 l (avar_f v2))

| tfree_trm_call_l v1 a2 l:
  tfree_trm v1 (trm_call (avar_f v1) l a2)
| tfree_trm_call_r a1 v2 l:
  tfree_trm v2 (trm_call a1 l (avar_f v2))

with tfree_lit: TFree lit :=

| tfree_lit_fun v t T:
  tfree_trm v t ->
  tfree_lit v (lit_fun T t)
| tfree_lit_obj v t T:
  tfree_defs v t ->
  tfree_lit v (lit_obj T t)

with tfree_def: TFree def :=

| tfree_def_trm v l:
  tfree_def v (def_fld l (avar_f v))

| tfree_def_met v t l:
  tfree_trm v t ->
  tfree_def v (def_met l t)

with tfree_defs: TFree defs :=

| tfree_defs_cons_l v d ds:
  tfree_defs v ds ->
  tfree_defs v (defs_cons ds d)
| tfree_defs_cons_r v d ds:
  tfree_def v d ->
  tfree_defs v (defs_cons ds d)
.

Scheme tfree_trm_mut    := Induction for tfree_trm Sort Prop
with   tfree_lit_mut    := Induction for tfree_lit Sort Prop
with   tfree_def_mut    := Induction for tfree_def Sort Prop
with   tfree_defs_mut   := Induction for tfree_defs Sort Prop.

Combined Scheme tfree_mutind from tfree_trm_mut, tfree_lit_mut,
tfree_def_mut, tfree_defs_mut.

Inductive tfree_stack: TFree stack :=

| tfree_stack_cons_l v t st:
  tfree_trm v t ->
  tfree_stack v (stack_cons (frame_let t) st)
| tfree_stack_cons_r v f st:
  tfree_stack v st ->
  tfree_stack v (stack_cons f st)
.

Existing Instance tfree_trm.

Existing Instance tfree_lit.

Existing Instance tfree_def.

Existing Instance tfree_defs.

Existing Instance tfree_stack.

Definition all_tfree_k {A: Set} {AT: TFree A} G (t:A) vk :=
  forall v, tfree v t -> ctx_k G v vk.

Notation all_tfree_k_trm := (@all_tfree_k trm _).

Notation all_tfree_k_def := (@all_tfree_k def _).

Notation all_tfree_k_defs := (@all_tfree_k defs _).

Notation all_tfree_k_stack := (@all_tfree_k stack _).

Definition TFreeInFV (A: Set) (AT: TFree A) {AF: FreeVar A} :=
  forall v t,
    tfree v t ->
    v \in fv t.

Local Definition TFreeOpenInvInd (A: Set) (AT: TFree A) {AO: Openable A} :=
  forall v t,
    tfree v t ->
    forall k x tR,
      t = (open_rec k x tR) ->
      tfree v tR \/ v = x.

Class TFreeOpenInv(A : Set)(AT: TFree A){AO: Openable A} :=
  tfree_open_inv v x (t:A) n:
    tfree v (open_rec n x t) ->
    tfree v t \/ v = x
.

Local Definition TFreeOpenInd (A: Set) (AT: TFree A) {AO: Openable A} :=
  forall v t,
    tfree v t ->
    forall k x,
    tfree v (open_rec k x t).

Class TFreeOpen(A : Set)(AT: TFree A){AO: Openable A} :=
  tfree_open v x (t:A) n:
    tfree v t ->
    tfree v (open_rec n x t).

Section TFreeOpenLemmata.

Context (A: Set) {AT: TFree A} {AO: Openable A} {ATO: TFreeOpenInv AT}.

End TFreeOpenLemmata.
