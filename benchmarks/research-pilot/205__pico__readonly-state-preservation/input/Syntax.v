From Stdlib Require List.

Require Import Stdlib.Sets.Ensembles.

Definition var : Type := nat.

Definition method_name : Type := nat.

Definition class_name : Type := nat.

Inductive q : Type :=

  | Mut
  | Imm
  | RDM

  | RO

  | Lost
  | Bot.

Inductive q_f : Type :=

  | Mut_f
  | Imm_f
  | RDM_f

  | RO_f.

Inductive q_c : Type :=

  | Mut_c
  | Imm_c
  | RDM_c.

Inductive a : Type :=
  | Assignable
  | Final
  | RDA.

Record qualified_type := {
  sqtype: q;
  sctype: class_name;
}.

Definition s_env := list qualified_type.

Inductive expr : Type :=
  | ENull : expr
  | EVar : var -> expr
  | EField : var -> var -> expr.

Inductive stmt: Type :=
  | SSkip: stmt
  | SLocal: qualified_type -> var -> stmt
  | SVarAss: var -> expr -> stmt
  | SFldWrite: var -> var -> var -> stmt
  | SNew: var -> q_c -> class_name -> list var -> stmt
  | SCall: var -> var -> method_name -> list var -> stmt

  | SSeq: stmt -> stmt -> stmt.

Record field_type := {
  assignability: a;
  mutability: q_f;
  f_base_type : class_name;
}.

Record field_def := {
  ftype : field_type;
  fname : var;
}.

Record constructor_body :={
  assignments: list (var * var);
}.

Record constructor_sig := {
  cqualifier: q_c;
  cparams : list qualified_type;
}.

Record constructor_def := {
  csignature : constructor_sig;

}.

Record method_body := {
  mbody_stmt: stmt;
  mreturn: var;
}.

Inductive method_scope : Type :=
  | AbstractState
  | ConcreteState
  | ReadonlyState
  | TransitiveState.

Definition readonly_state_method_scope (mt : method_scope) : Prop :=
  mt = ReadonlyState \/ mt = TransitiveState.

Definition strict_assignability_method_scope (mt : method_scope) : Prop :=
  mt = ConcreteState \/ mt = TransitiveState.

Record method_sig := {
  mscope: method_scope;
  mret : qualified_type;
  mname : method_name;
  mreceiver: qualified_type;
  mparams : list qualified_type;
}.

Record method_def := {
  msignature : method_sig;
  mbody : method_body;
}.

Record class_body := {
  fields : list field_def;
  constructor: constructor_def;
  methods : list method_def;
}.

Record class_sig := {
  class_qualifier : q_c;
  cname : class_name;
  super : option class_name;
}.

Record class_def := {
  signature : class_sig;
  body : class_body;
}.

Record program_def := {
  classes: list class_def;
  main_statement: stmt;
}.

Definition class_table := list class_def.

Inductive q_r : Type :=
  | Mut_r
  | Imm_r
  .

Record runtime_type := mkruntime_type {
  rqtype: q_r;
  rctype: class_name;
}.

Definition Loc : Type := nat.

Inductive value : Type :=
  | Null_a : value
  | Iot: Loc -> value.

Definition var_mapping   := list value.

Record r_env := mkr_env {
  vars: var_mapping;
}.

Definition set_vars (_ : r_env) (vars' : var_mapping) : r_env :=
  mkr_env vars'.

Definition fields_mapping := list value.

Record Obj := mkObj {
  rt_type: runtime_type;
  fields_map: fields_mapping;
}.

Definition set_fields_map (o : Obj) (fields' : fields_mapping) : Obj :=
  mkObj (rt_type o) fields'.

Definition heap          := list Obj.
