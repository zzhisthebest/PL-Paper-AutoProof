Require Import Syntax.

Definition vpa_mutability_qq_abstract_state (q1: q)(q2 : q) : q :=
  match q1, q2 with
    | RO, RDM => Lost
    | q1, RDM => q1
    | _, q2 => q2
  end.

Definition vpa_mutability_tt_abstract_state (t1: qualified_type)(t2 : qualified_type) : qualified_type :=
  Build_qualified_type
    (vpa_mutability_qq_abstract_state (sqtype t1) (sqtype t2))
    (sctype t2).

Definition vpa_mutability_stype_fld_abstract_state (q1: q)(q2 : q_f) : q :=
  match q1, q2 with
    | RO, RDM_f => Lost
    | q1, RDM_f => q1
    | _, Imm_f => Imm
    | _, Mut_f => Mut
    | _, RO_f => RO
    end.

Definition vpa_mutability_qq_readonly_state (q1: q)(q2 : q) : q :=
  match q1, q2 with
    | RO, RDM => Lost
    | q1, RDM => q1
    | Mut, Mut => Mut
    | _, Mut => Lost
    | _, q2 => q2
  end.

Definition vpa_mutability_tt_readonly_state (t1: qualified_type)(t2 : qualified_type) : qualified_type :=
  Build_qualified_type
    (vpa_mutability_qq_readonly_state (sqtype t1) (sqtype t2))
    (sctype t2).

Definition vpa_mutability_stype_fld_readonly_state (q1: q)(q2 : q_f) : q :=
  match q1, q2 with






    | RO, RDM_f => Lost
    | q1, RDM_f => q1
    | _, Imm_f => Imm
    | Mut, Mut_f => Mut
    | _, Mut_f => Lost
    | _, RO_f => RO
    end.

Definition vpa_assignability (q1: q) (a1: a) : a :=
  match q1, a1 with
    | Mut, RDA => Assignable
    | _, Assignable => Assignable
    | _, _ => Final
  end.

Definition vpa_assignability_cs_ts (q1: q) (a1: a) : a :=
  match q1, a1 with
    | Mut, RDA => Assignable
    | Mut, Assignable => Assignable
    | _, _ => Final
  end.

Definition vpa_mutability_bound (q1: q)(q2 : q_c) : q :=
  match q1, q2 with
    | RO, RDM_c => Lost
    | q1, RDM_c => q1
    | _, Imm_c => Imm
    | _, Mut_c => Mut
    end.

Definition vpa_mutability_constructor_fld (q1: q_c)(q2 : q_f) : q :=
  match q1, q2 with
    | Imm_c, RDM_f => Imm
    | Mut_c, RDM_f => Mut
    | RDM_c, RDM_f => RDM
    | _, Imm_f => Imm
    | _, Mut_f => Mut
    | _, RO_f => RO
    end.

Definition vpa_mutability_rec_fld (q1: q_r)(q2 : q_f) : q :=
  match q1, q2 with
    | Imm_r, RDM_f => Imm
    | Mut_r, RDM_f => Mut
    | _, Imm_f => Imm
    | _, Mut_f => Mut
    | _, RO_f => RO
    end.

Definition vpa_mutability_runtime (q1: q_r)(q2 : q) : q :=
  match q1, q2 with
    | Imm_r, RDM => Imm
    | Mut_r, RDM => Mut
    | _, q2 => q2
  end.

Definition vpa_mutability_object_creation (q1: q_r)(q2 : q_c) : q_r :=
  match q1, q2 with
    | Imm_r, RDM_c => Imm_r
    | Mut_r, RDM_c => Mut_r
    | _, Imm_c => Imm_r
    | _, Mut_c => Mut_r
    end.
