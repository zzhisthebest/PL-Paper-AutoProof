Set Implicit Arguments.

Require Import LibExtra SyntaxClasses AbstractSyntax.

Require Import Vars Types Context Env Equivalence.

Require Import Coq.Program.Equality.

Inductive typ_indep: avar -> typ -> Prop :=
| typ_indep_nulary v T:
  typ_nulary T -> typ_indep v T

| typ_indep_and v t1 t2:
    typ_indep v t1->
    typ_indep v t2->
    typ_indep v (typ_and t1 t2)
| typ_indep_or v t1 t2:
    typ_indep v t1->
    typ_indep v t2->
    typ_indep v (typ_or t1 t2)
| typ_indep_fld v a t1 t2:
    typ_indep v t1->
    typ_indep v t2->
    typ_indep v (typ_rcd (dec_fld a t1 t2))
| typ_indep_typ_f v a t1 t2:
    typ_indep (avar_f v) t1->
    typ_indep (avar_f v) t2->
    typ_indep (avar_f v) (typ_rcd (dec_typ a t1 t2))
| typ_indep_typ_b n a t1 t2:
    typ_indep (avar_b (S n)) t1->
    typ_indep (avar_b (S n)) t2->
    typ_indep (avar_b n) (typ_rcd (dec_typ a t1 t2))
| typ_indep_fun_f v t1 t2:
    typ_indep (avar_f v) t1 ->
    typ_indep (avar_f v) t2 ->
    typ_indep (avar_f v) (typ_fun t1 t2)
| typ_indep_fun_b n t1 t2:
    typ_indep (avar_b n) t1 ->
    typ_indep (avar_b (S n)) t2 ->
    typ_indep (avar_b n) (typ_fun t1 t2)
| typ_indep_sel(v v1 v2: avar)(l: typ_label):
    v <> v1 ->
    v <> v2 ->
    typ_indep v (typ_sel v1 l v2)
| typ_indep_sel_normal(v v1 v2: avar)(l: typ_normal_label):
    v <> v2 ->
    typ_indep v (typ_sel v1 (typ_label_normal l) v2)
| typ_indep_bnd_f v t:
    typ_indep (avar_f v) t ->
    typ_indep (avar_f v) (typ_bnd t)
| typ_indep_bnd_b n t:
    typ_indep (avar_b (S n)) t ->
    typ_indep (avar_b n) (typ_bnd t)
| typ_indep_met_f v t1 t2 t3 l:
    typ_indep (avar_f v) t1 ->
    typ_indep (avar_f v) t2 ->
    typ_indep (avar_f v) t3 ->
    typ_indep (avar_f v) (typ_rcd (dec_met l t1 t2 t3))
| typ_indep_met_b n t1 t2 t3 l:
    typ_indep (avar_b (S n)) t1 ->
    typ_indep (avar_b n) t2 ->
    typ_indep (avar_b (S (S n))) t3 ->
    typ_indep (avar_b n) (typ_rcd (dec_met l t1 t2 t3))
.

Notation typ_indep_f v T := (typ_indep (avar_f v) T).

Notation typ_indep_b n T := (typ_indep (avar_b n) T).
