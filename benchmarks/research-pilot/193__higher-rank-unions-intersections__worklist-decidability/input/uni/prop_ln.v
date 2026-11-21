Require Import Coq.Arith.Wf_nat.

Require Import Coq.Logic.FunctionalExtensionality.

Require Import Coq.Program.Equality.

Require Export Metalib.Metatheory.

Require Export Metalib.LibLNgen.

Require Export uni.def_ott.

Scheme typ_ind' := Induction for typ Sort Prop.

Combined Scheme typ_mutind from typ_ind'.

Scheme typ_rec' := Induction for typ Sort Set.

Combined Scheme typ_mutrec from typ_rec'.

Scheme abind_ind' := Induction for abind Sort Prop.

Combined Scheme abind_mutind from abind_ind'.

Scheme abind_rec' := Induction for abind Sort Set.

Combined Scheme abind_mutrec from abind_rec'.

Scheme exp_ind' := Induction for exp Sort Prop.

Combined Scheme exp_mutind from exp_ind'.

Scheme exp_rec' := Induction for exp Sort Set.

Combined Scheme exp_mutrec from exp_rec'.

Scheme contd_ind' := Induction for contd Sort Prop
  with conts_ind' := Induction for conts Sort Prop.

Combined Scheme contd_conts_mutind from contd_ind',conts_ind'.

Scheme contd_rec' := Induction for contd Sort Set
  with conts_rec' := Induction for conts Sort Set.

Combined Scheme contd_conts_mutrec from contd_rec',conts_rec'.

Scheme dbind_ind' := Induction for dbind Sort Prop.

Combined Scheme dbind_mutind from dbind_ind'.

Scheme dbind_rec' := Induction for dbind Sort Set.

Combined Scheme dbind_mutrec from dbind_rec'.

Scheme work_ind' := Induction for work Sort Prop.

Combined Scheme work_mutind from work_ind'.

Scheme work_rec' := Induction for work Sort Set.

Combined Scheme work_mutrec from work_rec'.

Fixpoint size_typ (A1 : typ) {struct A1} : nat :=
  match A1 with
    | typ_unit => 1
    | typ_top => 1
    | typ_bot => 1
    | typ_var_f X1 => 1
    | typ_var_b n1 => 1
    | typ_arrow A2 A3 => 1 + (size_typ A2) + (size_typ A3)
    | typ_all A2 => 1 + (size_typ A2)
    | typ_union A2 A3 => 1 + (size_typ A2) + (size_typ A3)
    | typ_intersection A2 A3 => 1 + (size_typ A2) + (size_typ A3)
  end.

Fixpoint size_abind (ab1 : abind) {struct ab1} : nat :=
  match ab1 with
    | abind_tvar_empty => 1
    | abind_stvar_empty => 1
    | abind_etvar_empty => 1
    | abind_var_typ A1 => 1 + (size_typ A1)
  end.

Fixpoint size_exp (e1 : exp) {struct e1} : nat :=
  match e1 with
    | exp_unit => 1
    | exp_var_f x1 => 1
    | exp_var_b n1 => 1
    | exp_abs e2 => 1 + (size_exp e2)
    | exp_app e2 e3 => 1 + (size_exp e2) + (size_exp e3)
    | exp_tabs e2 => 1 + (size_exp e2)
    | exp_tapp e2 A1 => 1 + (size_exp e2) + (size_typ A1)
    | exp_anno e2 A1 => 1 + (size_exp e2) + (size_typ A1)
  end.

Fixpoint size_contd (cd1 : contd) {struct cd1} : nat :=
  match cd1 with
    | contd_infabsunion A1 cd2 => 1 + (size_typ A1) + (size_contd cd2)
    | contd_infapp e1 cs1 => 1 + (size_exp e1) + (size_conts cs1)
    | contd_unioninfabs A1 B1 cd2 => 1 + (size_typ A1) + (size_typ B1) + (size_contd cd2)
  end

with size_conts (cs1 : conts) {struct cs1} : nat :=
  match cs1 with
    | conts_infabs cd1 => 1 + (size_contd cd1)
    | conts_inftapp A1 cs2 => 1 + (size_typ A1) + (size_conts cs2)
    | conts_inftappunion A1 A2 cs2 => 1 + (size_typ A1) + (size_typ A2) + (size_conts cs2)
    | conts_unioninftapp A1 cs2 => 1 + (size_typ A1) + (size_conts cs2)
    | conts_sub A1 => 1 + (size_typ A1)
  end.

Fixpoint size_dbind (db1 : dbind) {struct db1} : nat :=
  match db1 with
    | dbind_tvar_empty => 1
    | dbind_stvar_empty => 1
    | dbind_typ A1 => 1 + (size_typ A1)
  end.

Fixpoint size_work (w1 : work) {struct w1} : nat :=
  match w1 with
    | work_infer e1 cs1 => 1 + (size_exp e1) + (size_conts cs1)
    | work_check e1 A1 => 1 + (size_exp e1) + (size_typ A1)
    | work_infabs A1 cd1 => 1 + (size_typ A1) + (size_contd cd1)
    | work_infabsunion A1 B1 A2 cd1 => 1 + (size_typ A1) + (size_typ B1) + (size_typ A2) + (size_contd cd1)
    | work_infapp A1 B1 e1 cs1 => 1 + (size_typ A1) + (size_typ B1) + (size_exp e1) + (size_conts cs1)
    | work_inftapp A1 A2 cs1 => 1 + (size_typ A1) + (size_typ A2) + (size_conts cs1)
    | work_sub A1 A2 => 1 + (size_typ A1) + (size_typ A2)
    | work_inftappunion A1 A2 B1 cs1 => 1 + (size_typ A1) + (size_typ A2) + (size_typ B1) + (size_conts cs1)
    | work_unioninftapp A1 A2 cs1 => 1 + (size_typ A1) + (size_typ A2) + (size_conts cs1)
    | work_unioninfabs A1 B1 A2 B2 cd1 => 1 + (size_typ A1) + (size_typ B1) + (size_typ A2) + (size_typ B2) + (size_contd cd1)
    | work_applys cs1 A1 => 1 + (size_conts cs1) + (size_typ A1)
    | work_applyd cd1 A1 B1 => 1 + (size_contd cd1) + (size_typ A1) + (size_typ B1)
  end.

Inductive degree_typ_wrt_typ : nat -> typ -> Prop :=
  | degree_wrt_typ_typ_unit : forall n1,
    degree_typ_wrt_typ n1 (typ_unit)
  | degree_wrt_typ_typ_top : forall n1,
    degree_typ_wrt_typ n1 (typ_top)
  | degree_wrt_typ_typ_bot : forall n1,
    degree_typ_wrt_typ n1 (typ_bot)
  | degree_wrt_typ_typ_var_f : forall n1 X1,
    degree_typ_wrt_typ n1 (typ_var_f X1)
  | degree_wrt_typ_typ_var_b : forall n1 n2,
    lt n2 n1 ->
    degree_typ_wrt_typ n1 (typ_var_b n2)
  | degree_wrt_typ_typ_arrow : forall n1 A1 A2,
    degree_typ_wrt_typ n1 A1 ->
    degree_typ_wrt_typ n1 A2 ->
    degree_typ_wrt_typ n1 (typ_arrow A1 A2)
  | degree_wrt_typ_typ_all : forall n1 A1,
    degree_typ_wrt_typ (S n1) A1 ->
    degree_typ_wrt_typ n1 (typ_all A1)
  | degree_wrt_typ_typ_union : forall n1 A1 A2,
    degree_typ_wrt_typ n1 A1 ->
    degree_typ_wrt_typ n1 A2 ->
    degree_typ_wrt_typ n1 (typ_union A1 A2)
  | degree_wrt_typ_typ_intersection : forall n1 A1 A2,
    degree_typ_wrt_typ n1 A1 ->
    degree_typ_wrt_typ n1 A2 ->
    degree_typ_wrt_typ n1 (typ_intersection A1 A2).

Scheme degree_typ_wrt_typ_ind' := Induction for degree_typ_wrt_typ Sort Prop.

Combined Scheme degree_typ_wrt_typ_mutind from degree_typ_wrt_typ_ind'.

Inductive degree_abind_wrt_typ : nat -> abind -> Prop :=
  | degree_wrt_typ_abind_tvar_empty : forall n1,
    degree_abind_wrt_typ n1 (abind_tvar_empty)
  | degree_wrt_typ_abind_stvar_empty : forall n1,
    degree_abind_wrt_typ n1 (abind_stvar_empty)
  | degree_wrt_typ_abind_etvar_empty : forall n1,
    degree_abind_wrt_typ n1 (abind_etvar_empty)
  | degree_wrt_typ_abind_var_typ : forall n1 A1,
    degree_typ_wrt_typ n1 A1 ->
    degree_abind_wrt_typ n1 (abind_var_typ A1).

Scheme degree_abind_wrt_typ_ind' := Induction for degree_abind_wrt_typ Sort Prop.

Combined Scheme degree_abind_wrt_typ_mutind from degree_abind_wrt_typ_ind'.

Inductive degree_exp_wrt_typ : nat -> exp -> Prop :=
  | degree_wrt_typ_exp_unit : forall n1,
    degree_exp_wrt_typ n1 (exp_unit)
  | degree_wrt_typ_exp_var_f : forall n1 x1,
    degree_exp_wrt_typ n1 (exp_var_f x1)
  | degree_wrt_typ_exp_var_b : forall n1 n2,
    degree_exp_wrt_typ n1 (exp_var_b n2)
  | degree_wrt_typ_exp_abs : forall n1 e1,
    degree_exp_wrt_typ n1 e1 ->
    degree_exp_wrt_typ n1 (exp_abs e1)
  | degree_wrt_typ_exp_app : forall n1 e1 e2,
    degree_exp_wrt_typ n1 e1 ->
    degree_exp_wrt_typ n1 e2 ->
    degree_exp_wrt_typ n1 (exp_app e1 e2)
  | degree_wrt_typ_exp_tabs : forall n1 e1,
    degree_exp_wrt_typ (S n1) e1 ->
    degree_exp_wrt_typ n1 (exp_tabs e1)
  | degree_wrt_typ_exp_tapp : forall n1 e1 A1,
    degree_exp_wrt_typ n1 e1 ->
    degree_typ_wrt_typ n1 A1 ->
    degree_exp_wrt_typ n1 (exp_tapp e1 A1)
  | degree_wrt_typ_exp_anno : forall n1 e1 A1,
    degree_exp_wrt_typ n1 e1 ->
    degree_typ_wrt_typ n1 A1 ->
    degree_exp_wrt_typ n1 (exp_anno e1 A1).

Inductive degree_exp_wrt_exp : nat -> exp -> Prop :=
  | degree_wrt_exp_exp_unit : forall n1,
    degree_exp_wrt_exp n1 (exp_unit)
  | degree_wrt_exp_exp_var_f : forall n1 x1,
    degree_exp_wrt_exp n1 (exp_var_f x1)
  | degree_wrt_exp_exp_var_b : forall n1 n2,
    lt n2 n1 ->
    degree_exp_wrt_exp n1 (exp_var_b n2)
  | degree_wrt_exp_exp_abs : forall n1 e1,
    degree_exp_wrt_exp (S n1) e1 ->
    degree_exp_wrt_exp n1 (exp_abs e1)
  | degree_wrt_exp_exp_app : forall n1 e1 e2,
    degree_exp_wrt_exp n1 e1 ->
    degree_exp_wrt_exp n1 e2 ->
    degree_exp_wrt_exp n1 (exp_app e1 e2)
  | degree_wrt_exp_exp_tabs : forall n1 e1,
    degree_exp_wrt_exp n1 e1 ->
    degree_exp_wrt_exp n1 (exp_tabs e1)
  | degree_wrt_exp_exp_tapp : forall n1 e1 A1,
    degree_exp_wrt_exp n1 e1 ->
    degree_exp_wrt_exp n1 (exp_tapp e1 A1)
  | degree_wrt_exp_exp_anno : forall n1 e1 A1,
    degree_exp_wrt_exp n1 e1 ->
    degree_exp_wrt_exp n1 (exp_anno e1 A1).

Scheme degree_exp_wrt_typ_ind' := Induction for degree_exp_wrt_typ Sort Prop.

Combined Scheme degree_exp_wrt_typ_mutind from degree_exp_wrt_typ_ind'.

Scheme degree_exp_wrt_exp_ind' := Induction for degree_exp_wrt_exp Sort Prop.

Combined Scheme degree_exp_wrt_exp_mutind from degree_exp_wrt_exp_ind'.

Inductive degree_contd_wrt_typ : nat -> contd -> Prop :=
  | degree_wrt_typ_contd_infabsunion : forall n1 A1 cd1,
    degree_typ_wrt_typ n1 A1 ->
    degree_contd_wrt_typ n1 cd1 ->
    degree_contd_wrt_typ n1 (contd_infabsunion A1 cd1)
  | degree_wrt_typ_contd_infapp : forall n1 e1 cs1,
    degree_exp_wrt_typ n1 e1 ->
    degree_conts_wrt_typ n1 cs1 ->
    degree_contd_wrt_typ n1 (contd_infapp e1 cs1)
  | degree_wrt_typ_contd_unioninfabs : forall n1 A1 B1 cd1,
    degree_typ_wrt_typ n1 A1 ->
    degree_typ_wrt_typ n1 B1 ->
    degree_contd_wrt_typ n1 cd1 ->
    degree_contd_wrt_typ n1 (contd_unioninfabs A1 B1 cd1)

with degree_conts_wrt_typ : nat -> conts -> Prop :=
  | degree_wrt_typ_conts_infabs : forall n1 cd1,
    degree_contd_wrt_typ n1 cd1 ->
    degree_conts_wrt_typ n1 (conts_infabs cd1)
  | degree_wrt_typ_conts_inftapp : forall n1 A1 cs1,
    degree_typ_wrt_typ n1 A1 ->
    degree_conts_wrt_typ n1 cs1 ->
    degree_conts_wrt_typ n1 (conts_inftapp A1 cs1)
  | degree_wrt_typ_conts_inftappunion : forall n1 A1 A2 cs1,
    degree_typ_wrt_typ n1 A1 ->
    degree_typ_wrt_typ n1 A2 ->
    degree_conts_wrt_typ n1 cs1 ->
    degree_conts_wrt_typ n1 (conts_inftappunion A1 A2 cs1)
  | degree_wrt_typ_conts_unioninftapp : forall n1 A1 cs1,
    degree_typ_wrt_typ n1 A1 ->
    degree_conts_wrt_typ n1 cs1 ->
    degree_conts_wrt_typ n1 (conts_unioninftapp A1 cs1)
  | degree_wrt_typ_conts_sub : forall n1 A1,
    degree_typ_wrt_typ n1 A1 ->
    degree_conts_wrt_typ n1 (conts_sub A1).

Inductive degree_contd_wrt_exp : nat -> contd -> Prop :=
  | degree_wrt_exp_contd_infabsunion : forall n1 A1 cd1,
    degree_contd_wrt_exp n1 cd1 ->
    degree_contd_wrt_exp n1 (contd_infabsunion A1 cd1)
  | degree_wrt_exp_contd_infapp : forall n1 e1 cs1,
    degree_exp_wrt_exp n1 e1 ->
    degree_conts_wrt_exp n1 cs1 ->
    degree_contd_wrt_exp n1 (contd_infapp e1 cs1)
  | degree_wrt_exp_contd_unioninfabs : forall n1 A1 B1 cd1,
    degree_contd_wrt_exp n1 cd1 ->
    degree_contd_wrt_exp n1 (contd_unioninfabs A1 B1 cd1)

with degree_conts_wrt_exp : nat -> conts -> Prop :=
  | degree_wrt_exp_conts_infabs : forall n1 cd1,
    degree_contd_wrt_exp n1 cd1 ->
    degree_conts_wrt_exp n1 (conts_infabs cd1)
  | degree_wrt_exp_conts_inftapp : forall n1 A1 cs1,
    degree_conts_wrt_exp n1 cs1 ->
    degree_conts_wrt_exp n1 (conts_inftapp A1 cs1)
  | degree_wrt_exp_conts_inftappunion : forall n1 A1 A2 cs1,
    degree_conts_wrt_exp n1 cs1 ->
    degree_conts_wrt_exp n1 (conts_inftappunion A1 A2 cs1)
  | degree_wrt_exp_conts_unioninftapp : forall n1 A1 cs1,
    degree_conts_wrt_exp n1 cs1 ->
    degree_conts_wrt_exp n1 (conts_unioninftapp A1 cs1)
  | degree_wrt_exp_conts_sub : forall n1 A1,
    degree_conts_wrt_exp n1 (conts_sub A1).

Scheme degree_contd_wrt_typ_ind' := Induction for degree_contd_wrt_typ Sort Prop
  with degree_conts_wrt_typ_ind' := Induction for degree_conts_wrt_typ Sort Prop.

Combined Scheme degree_contd_wrt_typ_degree_conts_wrt_typ_mutind from degree_contd_wrt_typ_ind',degree_conts_wrt_typ_ind'.

Scheme degree_contd_wrt_exp_ind' := Induction for degree_contd_wrt_exp Sort Prop
  with degree_conts_wrt_exp_ind' := Induction for degree_conts_wrt_exp Sort Prop.

Combined Scheme degree_contd_wrt_exp_degree_conts_wrt_exp_mutind from degree_contd_wrt_exp_ind',degree_conts_wrt_exp_ind'.

Inductive degree_dbind_wrt_typ : nat -> dbind -> Prop :=
  | degree_wrt_typ_dbind_tvar_empty : forall n1,
    degree_dbind_wrt_typ n1 (dbind_tvar_empty)
  | degree_wrt_typ_dbind_stvar_empty : forall n1,
    degree_dbind_wrt_typ n1 (dbind_stvar_empty)
  | degree_wrt_typ_dbind_typ : forall n1 A1,
    degree_typ_wrt_typ n1 A1 ->
    degree_dbind_wrt_typ n1 (dbind_typ A1).

Scheme degree_dbind_wrt_typ_ind' := Induction for degree_dbind_wrt_typ Sort Prop.

Combined Scheme degree_dbind_wrt_typ_mutind from degree_dbind_wrt_typ_ind'.

Inductive degree_work_wrt_typ : nat -> work -> Prop :=
  | degree_wrt_typ_work_infer : forall n1 e1 cs1,
    degree_exp_wrt_typ n1 e1 ->
    degree_conts_wrt_typ n1 cs1 ->
    degree_work_wrt_typ n1 (work_infer e1 cs1)
  | degree_wrt_typ_work_check : forall n1 e1 A1,
    degree_exp_wrt_typ n1 e1 ->
    degree_typ_wrt_typ n1 A1 ->
    degree_work_wrt_typ n1 (work_check e1 A1)
  | degree_wrt_typ_work_infabs : forall n1 A1 cd1,
    degree_typ_wrt_typ n1 A1 ->
    degree_contd_wrt_typ n1 cd1 ->
    degree_work_wrt_typ n1 (work_infabs A1 cd1)
  | degree_wrt_typ_work_infabsunion : forall n1 A1 B1 A2 cd1,
    degree_typ_wrt_typ n1 A1 ->
    degree_typ_wrt_typ n1 B1 ->
    degree_typ_wrt_typ n1 A2 ->
    degree_contd_wrt_typ n1 cd1 ->
    degree_work_wrt_typ n1 (work_infabsunion A1 B1 A2 cd1)
  | degree_wrt_typ_work_infapp : forall n1 A1 B1 e1 cs1,
    degree_typ_wrt_typ n1 A1 ->
    degree_typ_wrt_typ n1 B1 ->
    degree_exp_wrt_typ n1 e1 ->
    degree_conts_wrt_typ n1 cs1 ->
    degree_work_wrt_typ n1 (work_infapp A1 B1 e1 cs1)
  | degree_wrt_typ_work_inftapp : forall n1 A1 A2 cs1,
    degree_typ_wrt_typ n1 A1 ->
    degree_typ_wrt_typ n1 A2 ->
    degree_conts_wrt_typ n1 cs1 ->
    degree_work_wrt_typ n1 (work_inftapp A1 A2 cs1)
  | degree_wrt_typ_work_sub : forall n1 A1 A2,
    degree_typ_wrt_typ n1 A1 ->
    degree_typ_wrt_typ n1 A2 ->
    degree_work_wrt_typ n1 (work_sub A1 A2)
  | degree_wrt_typ_work_inftappunion : forall n1 A1 A2 B1 cs1,
    degree_typ_wrt_typ n1 A1 ->
    degree_typ_wrt_typ n1 A2 ->
    degree_typ_wrt_typ n1 B1 ->
    degree_conts_wrt_typ n1 cs1 ->
    degree_work_wrt_typ n1 (work_inftappunion A1 A2 B1 cs1)
  | degree_wrt_typ_work_unioninftapp : forall n1 A1 A2 cs1,
    degree_typ_wrt_typ n1 A1 ->
    degree_typ_wrt_typ n1 A2 ->
    degree_conts_wrt_typ n1 cs1 ->
    degree_work_wrt_typ n1 (work_unioninftapp A1 A2 cs1)
  | degree_wrt_typ_work_unioninfabs : forall n1 A1 B1 A2 B2 cd1,
    degree_typ_wrt_typ n1 A1 ->
    degree_typ_wrt_typ n1 B1 ->
    degree_typ_wrt_typ n1 A2 ->
    degree_typ_wrt_typ n1 B2 ->
    degree_contd_wrt_typ n1 cd1 ->
    degree_work_wrt_typ n1 (work_unioninfabs A1 B1 A2 B2 cd1)
  | degree_wrt_typ_work_applys : forall n1 cs1 A1,
    degree_conts_wrt_typ n1 cs1 ->
    degree_typ_wrt_typ n1 A1 ->
    degree_work_wrt_typ n1 (work_applys cs1 A1)
  | degree_wrt_typ_work_applyd : forall n1 cd1 A1 B1,
    degree_contd_wrt_typ n1 cd1 ->
    degree_typ_wrt_typ n1 A1 ->
    degree_typ_wrt_typ n1 B1 ->
    degree_work_wrt_typ n1 (work_applyd cd1 A1 B1).

Inductive degree_work_wrt_exp : nat -> work -> Prop :=
  | degree_wrt_exp_work_infer : forall n1 e1 cs1,
    degree_exp_wrt_exp n1 e1 ->
    degree_conts_wrt_exp n1 cs1 ->
    degree_work_wrt_exp n1 (work_infer e1 cs1)
  | degree_wrt_exp_work_check : forall n1 e1 A1,
    degree_exp_wrt_exp n1 e1 ->
    degree_work_wrt_exp n1 (work_check e1 A1)
  | degree_wrt_exp_work_infabs : forall n1 A1 cd1,
    degree_contd_wrt_exp n1 cd1 ->
    degree_work_wrt_exp n1 (work_infabs A1 cd1)
  | degree_wrt_exp_work_infabsunion : forall n1 A1 B1 A2 cd1,
    degree_contd_wrt_exp n1 cd1 ->
    degree_work_wrt_exp n1 (work_infabsunion A1 B1 A2 cd1)
  | degree_wrt_exp_work_infapp : forall n1 A1 B1 e1 cs1,
    degree_exp_wrt_exp n1 e1 ->
    degree_conts_wrt_exp n1 cs1 ->
    degree_work_wrt_exp n1 (work_infapp A1 B1 e1 cs1)
  | degree_wrt_exp_work_inftapp : forall n1 A1 A2 cs1,
    degree_conts_wrt_exp n1 cs1 ->
    degree_work_wrt_exp n1 (work_inftapp A1 A2 cs1)
  | degree_wrt_exp_work_sub : forall n1 A1 A2,
    degree_work_wrt_exp n1 (work_sub A1 A2)
  | degree_wrt_exp_work_inftappunion : forall n1 A1 A2 B1 cs1,
    degree_conts_wrt_exp n1 cs1 ->
    degree_work_wrt_exp n1 (work_inftappunion A1 A2 B1 cs1)
  | degree_wrt_exp_work_unioninftapp : forall n1 A1 A2 cs1,
    degree_conts_wrt_exp n1 cs1 ->
    degree_work_wrt_exp n1 (work_unioninftapp A1 A2 cs1)
  | degree_wrt_exp_work_unioninfabs : forall n1 A1 B1 A2 B2 cd1,
    degree_contd_wrt_exp n1 cd1 ->
    degree_work_wrt_exp n1 (work_unioninfabs A1 B1 A2 B2 cd1)
  | degree_wrt_exp_work_applys : forall n1 cs1 A1,
    degree_conts_wrt_exp n1 cs1 ->
    degree_work_wrt_exp n1 (work_applys cs1 A1)
  | degree_wrt_exp_work_applyd : forall n1 cd1 A1 B1,
    degree_contd_wrt_exp n1 cd1 ->
    degree_work_wrt_exp n1 (work_applyd cd1 A1 B1).

Scheme degree_work_wrt_typ_ind' := Induction for degree_work_wrt_typ Sort Prop.

Combined Scheme degree_work_wrt_typ_mutind from degree_work_wrt_typ_ind'.

Scheme degree_work_wrt_exp_ind' := Induction for degree_work_wrt_exp Sort Prop.

Combined Scheme degree_work_wrt_exp_mutind from degree_work_wrt_exp_ind'.

Inductive lc_set_typ : typ -> Set :=
  | lc_set_typ_unit :
    lc_set_typ (typ_unit)
  | lc_set_typ_top :
    lc_set_typ (typ_top)
  | lc_set_typ_bot :
    lc_set_typ (typ_bot)
  | lc_set_typ_var_f : forall X1,
    lc_set_typ (typ_var_f X1)
  | lc_set_typ_arrow : forall A1 A2,
    lc_set_typ A1 ->
    lc_set_typ A2 ->
    lc_set_typ (typ_arrow A1 A2)
  | lc_set_typ_all : forall A1,
    (forall X1 : typvar, lc_set_typ (open_typ_wrt_typ A1 (typ_var_f X1))) ->
    lc_set_typ (typ_all A1)
  | lc_set_typ_union : forall A1 A2,
    lc_set_typ A1 ->
    lc_set_typ A2 ->
    lc_set_typ (typ_union A1 A2)
  | lc_set_typ_intersection : forall A1 A2,
    lc_set_typ A1 ->
    lc_set_typ A2 ->
    lc_set_typ (typ_intersection A1 A2).

Scheme lc_typ_ind' := Induction for lc_typ Sort Prop.

Combined Scheme lc_typ_mutind from lc_typ_ind'.

Scheme lc_set_typ_ind' := Induction for lc_set_typ Sort Prop.

Combined Scheme lc_set_typ_mutind from lc_set_typ_ind'.

Scheme lc_set_typ_rec' := Induction for lc_set_typ Sort Set.

Combined Scheme lc_set_typ_mutrec from lc_set_typ_rec'.

Inductive lc_set_abind : abind -> Set :=
  | lc_set_abind_tvar_empty :
    lc_set_abind (abind_tvar_empty)
  | lc_set_abind_stvar_empty :
    lc_set_abind (abind_stvar_empty)
  | lc_set_abind_etvar_empty :
    lc_set_abind (abind_etvar_empty)
  | lc_set_abind_var_typ : forall A1,
    lc_set_typ A1 ->
    lc_set_abind (abind_var_typ A1).

Scheme lc_abind_ind' := Induction for lc_abind Sort Prop.

Combined Scheme lc_abind_mutind from lc_abind_ind'.

Scheme lc_set_abind_ind' := Induction for lc_set_abind Sort Prop.

Combined Scheme lc_set_abind_mutind from lc_set_abind_ind'.

Scheme lc_set_abind_rec' := Induction for lc_set_abind Sort Set.

Combined Scheme lc_set_abind_mutrec from lc_set_abind_rec'.

Inductive lc_set_exp : exp -> Set :=
  | lc_set_exp_unit :
    lc_set_exp (exp_unit)
  | lc_set_exp_var_f : forall x1,
    lc_set_exp (exp_var_f x1)
  | lc_set_exp_abs : forall e1,
    (forall x1 : expvar, lc_set_exp (open_exp_wrt_exp e1 (exp_var_f x1))) ->
    lc_set_exp (exp_abs e1)
  | lc_set_exp_app : forall e1 e2,
    lc_set_exp e1 ->
    lc_set_exp e2 ->
    lc_set_exp (exp_app e1 e2)
  | lc_set_exp_tabs : forall e1,
    (forall X1 : typvar, lc_set_exp (open_exp_wrt_typ e1 (typ_var_f X1))) ->
    lc_set_exp (exp_tabs e1)
  | lc_set_exp_tapp : forall e1 A1,
    lc_set_exp e1 ->
    lc_set_typ A1 ->
    lc_set_exp (exp_tapp e1 A1)
  | lc_set_exp_anno : forall e1 A1,
    lc_set_exp e1 ->
    lc_set_typ A1 ->
    lc_set_exp (exp_anno e1 A1).

Scheme lc_exp_ind' := Induction for lc_exp Sort Prop.

Combined Scheme lc_exp_mutind from lc_exp_ind'.

Scheme lc_set_exp_ind' := Induction for lc_set_exp Sort Prop.

Combined Scheme lc_set_exp_mutind from lc_set_exp_ind'.

Scheme lc_set_exp_rec' := Induction for lc_set_exp Sort Set.

Combined Scheme lc_set_exp_mutrec from lc_set_exp_rec'.

Inductive lc_set_contd : contd -> Set :=
  | lc_set_contd_infabsunion : forall A1 cd1,
    lc_set_typ A1 ->
    lc_set_contd cd1 ->
    lc_set_contd (contd_infabsunion A1 cd1)
  | lc_set_contd_infapp : forall e1 cs1,
    lc_set_exp e1 ->
    lc_set_conts cs1 ->
    lc_set_contd (contd_infapp e1 cs1)
  | lc_set_contd_unioninfabs : forall A1 B1 cd1,
    lc_set_typ A1 ->
    lc_set_typ B1 ->
    lc_set_contd cd1 ->
    lc_set_contd (contd_unioninfabs A1 B1 cd1)

with lc_set_conts : conts -> Set :=
  | lc_set_conts_infabs : forall cd1,
    lc_set_contd cd1 ->
    lc_set_conts (conts_infabs cd1)
  | lc_set_conts_inftapp : forall A1 cs1,
    lc_set_typ A1 ->
    lc_set_conts cs1 ->
    lc_set_conts (conts_inftapp A1 cs1)
  | lc_set_conts_inftappunion : forall A1 A2 cs1,
    lc_set_typ A1 ->
    lc_set_typ A2 ->
    lc_set_conts cs1 ->
    lc_set_conts (conts_inftappunion A1 A2 cs1)
  | lc_set_conts_unioninftapp : forall A1 cs1,
    lc_set_typ A1 ->
    lc_set_conts cs1 ->
    lc_set_conts (conts_unioninftapp A1 cs1)
  | lc_set_conts_sub : forall A1,
    lc_set_typ A1 ->
    lc_set_conts (conts_sub A1).

Scheme lc_contd_ind' := Induction for lc_contd Sort Prop
  with lc_conts_ind' := Induction for lc_conts Sort Prop.

Combined Scheme lc_contd_lc_conts_mutind from lc_contd_ind',lc_conts_ind'.

Scheme lc_set_contd_ind' := Induction for lc_set_contd Sort Prop
  with lc_set_conts_ind' := Induction for lc_set_conts Sort Prop.

Combined Scheme lc_set_contd_lc_set_conts_mutind from lc_set_contd_ind',lc_set_conts_ind'.

Scheme lc_set_contd_rec' := Induction for lc_set_contd Sort Set
  with lc_set_conts_rec' := Induction for lc_set_conts Sort Set.

Combined Scheme lc_set_contd_lc_set_conts_mutrec from lc_set_contd_rec',lc_set_conts_rec'.

Inductive lc_set_dbind : dbind -> Set :=
  | lc_set_dbind_tvar_empty :
    lc_set_dbind (dbind_tvar_empty)
  | lc_set_dbind_stvar_empty :
    lc_set_dbind (dbind_stvar_empty)
  | lc_set_dbind_typ : forall A1,
    lc_set_typ A1 ->
    lc_set_dbind (dbind_typ A1).

Scheme lc_dbind_ind' := Induction for lc_dbind Sort Prop.

Combined Scheme lc_dbind_mutind from lc_dbind_ind'.

Scheme lc_set_dbind_ind' := Induction for lc_set_dbind Sort Prop.

Combined Scheme lc_set_dbind_mutind from lc_set_dbind_ind'.

Scheme lc_set_dbind_rec' := Induction for lc_set_dbind Sort Set.

Combined Scheme lc_set_dbind_mutrec from lc_set_dbind_rec'.

Inductive lc_set_work : work -> Set :=
  | lc_set_work_infer : forall e1 cs1,
    lc_set_exp e1 ->
    lc_set_conts cs1 ->
    lc_set_work (work_infer e1 cs1)
  | lc_set_work_check : forall e1 A1,
    lc_set_exp e1 ->
    lc_set_typ A1 ->
    lc_set_work (work_check e1 A1)
  | lc_set_work_infabs : forall A1 cd1,
    lc_set_typ A1 ->
    lc_set_contd cd1 ->
    lc_set_work (work_infabs A1 cd1)
  | lc_set_work_infabsunion : forall A1 B1 A2 cd1,
    lc_set_typ A1 ->
    lc_set_typ B1 ->
    lc_set_typ A2 ->
    lc_set_contd cd1 ->
    lc_set_work (work_infabsunion A1 B1 A2 cd1)
  | lc_set_work_infapp : forall A1 B1 e1 cs1,
    lc_set_typ A1 ->
    lc_set_typ B1 ->
    lc_set_exp e1 ->
    lc_set_conts cs1 ->
    lc_set_work (work_infapp A1 B1 e1 cs1)
  | lc_set_work_inftapp : forall A1 A2 cs1,
    lc_set_typ A1 ->
    lc_set_typ A2 ->
    lc_set_conts cs1 ->
    lc_set_work (work_inftapp A1 A2 cs1)
  | lc_set_work_sub : forall A1 A2,
    lc_set_typ A1 ->
    lc_set_typ A2 ->
    lc_set_work (work_sub A1 A2)
  | lc_set_work_inftappunion : forall A1 A2 B1 cs1,
    lc_set_typ A1 ->
    lc_set_typ A2 ->
    lc_set_typ B1 ->
    lc_set_conts cs1 ->
    lc_set_work (work_inftappunion A1 A2 B1 cs1)
  | lc_set_work_unioninftapp : forall A1 A2 cs1,
    lc_set_typ A1 ->
    lc_set_typ A2 ->
    lc_set_conts cs1 ->
    lc_set_work (work_unioninftapp A1 A2 cs1)
  | lc_set_work_unioninfabs : forall A1 B1 A2 B2 cd1,
    lc_set_typ A1 ->
    lc_set_typ B1 ->
    lc_set_typ A2 ->
    lc_set_typ B2 ->
    lc_set_contd cd1 ->
    lc_set_work (work_unioninfabs A1 B1 A2 B2 cd1)
  | lc_set_work_applys : forall cs1 A1,
    lc_set_conts cs1 ->
    lc_set_typ A1 ->
    lc_set_work (work_applys cs1 A1)
  | lc_set_work_applyd : forall cd1 A1 B1,
    lc_set_contd cd1 ->
    lc_set_typ A1 ->
    lc_set_typ B1 ->
    lc_set_work (work_applyd cd1 A1 B1).

Scheme lc_work_ind' := Induction for lc_work Sort Prop.

Combined Scheme lc_work_mutind from lc_work_ind'.

Scheme lc_set_work_ind' := Induction for lc_set_work Sort Prop.

Combined Scheme lc_set_work_mutind from lc_set_work_ind'.

Scheme lc_set_work_rec' := Induction for lc_set_work Sort Set.

Combined Scheme lc_set_work_mutrec from lc_set_work_rec'.

Definition body_typ_wrt_typ A1 := forall X1, lc_typ (open_typ_wrt_typ A1 (typ_var_f X1)).

Definition body_abind_wrt_typ ab1 := forall X1, lc_abind (open_abind_wrt_typ ab1 (typ_var_f X1)).

Definition body_exp_wrt_typ e1 := forall X1, lc_exp (open_exp_wrt_typ e1 (typ_var_f X1)).

Definition body_exp_wrt_exp e1 := forall x1, lc_exp (open_exp_wrt_exp e1 (exp_var_f x1)).

Definition body_contd_wrt_typ cd1 := forall X1, lc_contd (open_contd_wrt_typ cd1 (typ_var_f X1)).

Definition body_conts_wrt_typ cs1 := forall X1, lc_conts (open_conts_wrt_typ cs1 (typ_var_f X1)).

Definition body_contd_wrt_exp cd1 := forall x1, lc_contd (open_contd_wrt_exp cd1 (exp_var_f x1)).

Definition body_conts_wrt_exp cs1 := forall x1, lc_conts (open_conts_wrt_exp cs1 (exp_var_f x1)).

Definition body_dbind_wrt_typ db1 := forall X1, lc_dbind (open_dbind_wrt_typ db1 (typ_var_f X1)).

Definition body_work_wrt_typ w1 := forall X1, lc_work (open_work_wrt_typ w1 (typ_var_f X1)).

Definition body_work_wrt_exp w1 := forall x1, lc_work (open_work_wrt_exp w1 (exp_var_f x1)).
