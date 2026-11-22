Require Import Program.Equality.

Require Import Lia.

Inductive typ :=
  | int : typ
  | top : typ
  | and : typ -> typ -> typ
  | rcd : nat -> typ -> typ
  | arr : typ -> typ -> typ.

Inductive mode := inf | chk.

Inductive fmode := bl | wh.

Inductive exp :=
  | lit : nat -> exp
  | unit : exp
  | ctx : exp
  | merge : exp -> exp -> exp
  | ann : exp -> typ -> exp
  | rec : nat -> exp -> exp
  | proj : exp -> nat -> exp
  | lam : fmode -> exp -> exp
  | app : exp -> exp -> exp
  | box : exp -> exp -> exp.

Inductive sub : typ -> typ -> Prop :=
  | sint  : sub int int
  | stop  : forall A, sub A top
  | sand  : forall A B C, sub A B -> sub A C -> sub A (and B C)
  | sandl : forall A B C, sub A C -> sub (and A B) C
  | sandr : forall A B C, sub B C -> sub (and A B) C
  | srcd  : forall x A B, sub A B -> sub (rcd x A) (rcd x B)
  | sarr  : forall A B C D, sub C A -> sub B D -> sub (arr A B) (arr C D).

Inductive gord : typ -> Prop :=
  | GO_int :
      gord int
  | GO_arrow : forall A B,
      gord B ->
      gord (arr A B)
  | GO_rcd : forall x B,
      gord B ->
      gord (rcd x B).

Definition cost_spec A B := exists C, gord C /\ sub A C /\ sub B C.

Definition disjoint A B := ~ (cost_spec A B).

Inductive value : exp -> Prop :=
  | vlit : forall i, value (lit i)
  | vunit : value unit
  | vmrg : forall e1 e2, value e1 -> value e2 -> value (merge e1 e2)
  | vrec : forall x e, value e -> value (rec x e)
  | vclos : forall e1 e A B, value e1 -> value (box e1 (ann (lam bl e) (arr A B)))
  | vsclos : forall e1 e A B l, value e1 -> value (box e1 (ann (lam wh e) (arr (rcd l A) B))).

Inductive genv : typ -> exp -> Prop :=
  | genv_top : genv top unit
  | genv_arr : forall A B v,
      genv B v ->
      genv (arr A B) (box unit (ann (lam bl v) (arr A B)))
  | genv_and : forall A B v1 v2, genv A v1 -> genv B v2 -> genv (and A B) (merge v1 v2)
  | genv_rcd : forall A l v, genv A v -> genv (rcd l A) (rec l v).

Inductive ord : typ -> Prop :=
  | O_int :
      ord int
  | O_arrow : forall A B,
      ord (arr A B)
  | O_rcd : forall x B,
      ord (rcd x B).

Inductive toplike : typ -> Prop :=
  | TL_top :
      toplike top
  | TL_and : forall A B,
      toplike A ->
      toplike B ->
      toplike (and A B)
  | TL_arr : forall (A B:typ),
      toplike B ->
      toplike (arr A B)
  | TL_rcd : forall x (B:typ),
      toplike B ->
      toplike (rcd x B).

Inductive ext : typ -> fmode -> typ -> Prop :=
  | ext_bl: forall A, ext A bl A
  | ext_wh: forall x A, ext (rcd x A) wh A.

Inductive casting : exp -> typ -> exp -> Prop :=
  | cast_top  : forall v, casting v top unit
  | cast_int  : forall i, casting (lit i) int (lit i)
  | cast_mrgl : forall v1 v2 A v1',
      casting v1 A v1' ->
      ord A ->
      casting (merge v1 v2) A v1'
  | cast_mrgr : forall v1 v2 A v2',
      casting v2 A v2' ->
      ord A ->
      casting (merge v1 v2) A v2'
  | cast_and : forall v v1 v2 A B,
      casting v A v1 ->
      casting v B v2 ->
      casting v (and A B) (merge v1 v2)
  | cast_rcd : forall v A v' x,
      casting v A v' ->
      casting (rec x v) (rcd x A) (rec x v')
  | cast_arr : forall e v A B C D A' fm,
      value v ->
      ~ toplike D ->
      ext A fm A' ->
      sub C A' ->
      sub B D ->
      casting (box v (ann (lam fm e) (arr A B))) (arr C D) (box v (ann (lam fm e) (arr A D)))
  | cast_arr_tl : forall e v A B C D v' fm A',
      value v ->
      toplike D ->
      ext A fm A' ->
      sub C A' ->
      sub B D ->
      genv (arr C D) v' ->
      casting (box v (ann (lam fm e) (arr A B))) (arr C D) v'.

Definition consistencySpec v1 v2 :=
  forall A v1' v2', casting v1 A v1' -> casting v2 A v2' -> v1' = v2'.

Inductive has_type : typ -> exp -> mode -> typ -> Prop :=
  | tlit : forall G i, has_type G (lit i) inf int
  | tunit : forall G, has_type G unit inf top
  | tctx : forall G, has_type G ctx inf G
  | tmrg : forall G e1 e2 A B,
      has_type G e1 inf A ->
      has_type (and G A) e2 inf B ->
      disjoint A B ->
      disjoint G A ->
      has_type G (merge e1 e2) inf (and A B)
  | tcon : forall G v1 v2 A B,
      has_type G v1 inf A ->
      has_type G v2 inf B ->
      value v1 ->
      value v2 ->
      consistencySpec v1 v2->
      has_type G (merge v1 v2) inf (and A B)
  | tann : forall G e A,
      has_type G e chk A ->
      has_type G (ann e A) inf A
  | tlam : forall A e B G C fm A',
      disjoint G A ->
      ext A fm A' ->
      sub C A' ->
      has_type (and G A) e chk B ->
      has_type G (ann (lam fm e) (arr A B)) inf (arr C B)
  | tapp : forall G e1 e2 A B,
      has_type G e1 inf (arr A B) ->
      has_type G e2 chk A ->
      has_type G (app e1 e2) inf B
  | tbox : forall e1 e2 A B G,
      has_type G e1 inf B ->
      has_type B e2 inf A ->
      has_type G (box e1 e2) inf A
  | tsub : forall G e A B,
      has_type G e inf A ->
      sub A B ->
      has_type G e chk B
  | trec : forall G e x A,
      has_type G e inf A ->
      has_type G (rec x e) inf (rcd x A)
  | tproj : forall G e x A,
      has_type G e inf (rcd x A) ->
      has_type G (proj e x) inf A.

Inductive constr : typ -> exp -> fmode -> exp -> Prop :=
  | constr_bl: forall A v, constr A v bl v
  | constr_wh: forall x A v, constr (rcd x A) v wh (rec x v).

Inductive step : exp -> exp -> exp -> Prop :=
  | step_ctx : forall v, value v -> step v ctx v
  | step_annv : forall v v1 A v1', value v -> casting v1 A v1' -> value v1 -> step v (ann v1 A) v1'
  | step_anne : forall v e e' A, step v e e' -> step v (ann e A) (ann e' A)
  | step_mrgr : forall v e e' v1, step (merge v v1)  e e' -> value v1 -> step v (merge v1 e) (merge v1 e')
  | step_mrgl : forall v e1 e1' e2, step v e1 e1' -> step v (merge e1 e2) (merge e1' e2)
  | step_rcde : forall v e' e x, step v e e' -> step v (rec x e) (rec x e')
  | step_projv : forall v v1 x, value v -> value v1 -> step v (proj (rec x v1) x) v1
  | step_proje : forall v e' e x, step v e e' -> step v (proj e x) (proj e' x)
  | step_switch : forall v e A B fm,
      value v ->
      step v (ann (lam fm e) (arr A B)) (box v (ann (lam fm e) (arr A B)))
  | step_beta : forall v v1 A B v1' e v2 A' fm v3,
      ext A fm A' ->
      casting v1 A' v1' ->
      value v ->
      value v1 ->
      value v2 ->
      constr A v1' fm v3 ->
      step v (app (box v2 (ann (lam fm e) (arr A B))) v1) (box (merge v2 v3) (ann e B))
  | step_appl : forall v e1 e1' e2, step v e1 e1' -> step v (app e1 e2) (app e1' e2)
  | step_appr : forall v v1 e2 e2', step v e2 e2' -> value v1 -> step v (app v1 e2) (app v1 e2')
  | step_boxv : forall v v1 v2, value v -> value v1 -> value v2 -> step v (box v1 v2) v2
  | step_boxe : forall e e' v v1,
      step v1 e e' ->
      value v ->
      ~ value (box v1 e) ->
      step v (box v1 e) (box v1 e')
  | step_boxc : forall e1 e2 v e,
      step v e1 e2 ->
      value v ->
      step v (box e1 e) (box e2 e).
