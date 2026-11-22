Set Implicit Arguments.

Require Import LibExtra DotTactics.

Require Import Coq.Program.Equality.

Require Import AbstractSyntax TypingMode Equivalence GeneralTyping.

Require Import PreciseTyping RecordTypes InertContext TightTyping Subenvironments Narrowing InertTightSubtyping EnvCorrespondence Indep Weakening Orctx Logctx Logpath LogpathOrder OrctxLogctx.

Require Import TypeInduction TypLogicInduction TypeBndSel.

Require Import LayeredCommon LayeredSubtypingAtomic.

Require Import LayeredCapabilityBasic LayeredCapabilityBasicClosure LayeredCapabilityLogic.

Require Import LayeredTypingAtomic LayeredTypingBasic LayeredTypingBasicClosure LayeredTypingLogic LayeredTypingMain.

Section WithTypingMode.

Context {typing_mode: Mode}.

Inductive ty_main_tree: Set :=
| ty_main_tree_atomic (T: typ): ty_main_tree
| ty_main_tree_or (trl trr: ty_main_tree): ty_main_tree
| ty_main_tree_and (trl trr: ty_main_tree): ty_main_tree
| ty_main_tree_bnd (tr trn: ty_main_tree): ty_main_tree
| ty_main_tree_nocap_bnd (T: typ): ty_main_tree
| ty_main_tree_sel (tr: ty_main_tree) (y: var) (A: typ_label) (z: var): ty_main_tree
.

Inductive ty_main_tree_sub (G: ctx) (e: renv) (x: var): ty_main_tree -> typ -> typ -> Prop :=
| ty_main_tree_sub_atomic T:
  typ_notlog T ->
  ty_main_tree_sub G e x (ty_main_tree_atomic T) T T

| ty_main_tree_sub_or trl trr Tl Tr Ul Ur:
  ty_main_tree_sub G e x trl Tl Ul ->
  ty_main_tree_sub G e x trr Tr Ur ->
  ty_main_tree_sub G e x (ty_main_tree_or trl trr) (typ_or Tl Tr) (typ_or Ul Ur)

| ty_main_tree_sub_and trl trr Tl Tr Ul Ur:
  ty_main_tree_sub G e x trl Tl Ul ->
  ty_main_tree_sub G e x trr Tr Ur ->
  ty_main_tree_sub G e x (ty_main_tree_and trl trr) (typ_and Tl Tr) (typ_and Ul Ur)

| ty_main_tree_sub_bnd tr T U trn Un:
  ty_main_tree_sub G e x tr T (open x U) ->
  ((mode_has_incap typing_mode) ->
    (ty_has_N_logic G e Un /\ ty_main_tree_sub G e x trn Un (open x U) ) ) ->
  typ_indep_b 0 U ->
  ty_main_tree_sub G e x (ty_main_tree_bnd tr trn) T (typ_bnd U)

| ty_main_tree_sub_nocap_bnd T:
  ty_main_tree_sub G e x (ty_main_tree_nocap_bnd T) typ_nocap (typ_bnd T)

| ty_main_tree_sub_sel tr T y A z U S1 S2:
  ty_main_tree_sub G e x tr T (open z S1) ->
  G ⊢! y ∶ U ⪼ typ_rcd (dec_typ A S1 S2) ->
  ty_main_tree_sub G e x (ty_main_tree_sel tr y A z) T  (typ_sel (avar_f y) A (avar_f z))
.

Inductive ty_main_tree_linear_sub (G: ctx) (e: renv) (x: var): ty_main_tree -> typ -> typ -> Prop :=
| ty_main_tree_linear_sub_atomic T:
  typ_notlog T ->
  ty_main_tree_linear_sub G e x (ty_main_tree_atomic T) T T

| ty_main_tree_linear_sub_or trl trr Tl Tr Ul Ur:
  ty_main_tree_linear_sub G e x trl Tl Ul ->
  ty_main_tree_linear_sub G e x trr Tr Ur ->
  ty_main_tree_linear_sub G e x (ty_main_tree_or trl trr) (typ_or Tl Tr) (typ_or Ul Ur)

| ty_main_tree_linear_sub_and trl trr Tl Tr Ul Ur:
  ty_main_tree_linear_sub G e x trl Tl Ul ->
  ty_main_tree_linear_sub G e x trr Tr Ur ->
  ty_main_tree_linear_sub G e x (ty_main_tree_and trl trr) (typ_and Tl Tr) (typ_and Ul Ur)

| ty_main_tree_linear_sub_bnd tr T U:
  ty_main_tree_linear_sub G e x tr T (open x U) ->
  ((mode_has_incap typing_mode) -> ty_has_N_logic G e T) ->
  typ_indep_b 0 U ->
  ty_main_tree_linear_sub G e x (ty_main_tree_bnd tr (ty_main_tree_atomic typ_top)) T (typ_bnd U)

| ty_main_tree_linear_sub_nocap_bnd T:
  ty_main_tree_linear_sub G e x (ty_main_tree_nocap_bnd T) typ_nocap (typ_bnd T)

| ty_main_tree_linear_sub_sel tr T y A z U S1 S2:
  ty_main_tree_linear_sub G e x tr T (open z S1) ->
  G ⊢! y ∶ U ⪼ typ_rcd (dec_typ A S1 S2) ->
  ty_main_tree_linear_sub G e x (ty_main_tree_sel tr y A z) T  (typ_sel (avar_f y) A (avar_f z))
.

Fixpoint ty_main_tree_folds (tr: ty_main_tree): nat :=
match tr with
| ty_main_tree_atomic T => 0
| ty_main_tree_or trl trr => (ty_main_tree_folds trl) + (ty_main_tree_folds trr)
| ty_main_tree_and trl trr => (ty_main_tree_folds trl) + (ty_main_tree_folds trr)
| ty_main_tree_bnd tr trn => S ((ty_main_tree_folds tr) + (ty_main_tree_folds trn))
| ty_main_tree_nocap_bnd T => 1
| ty_main_tree_sel tr y A z => S (ty_main_tree_folds tr)
end.

Fixpoint ty_main_tree_bndfolds (tr: ty_main_tree): nat :=
match tr with
| ty_main_tree_atomic T => 0
| ty_main_tree_or trl trr => (ty_main_tree_bndfolds trl) + (ty_main_tree_bndfolds trr)
| ty_main_tree_and trl trr => (ty_main_tree_bndfolds trl) + (ty_main_tree_bndfolds trr)
| ty_main_tree_bnd tr trn => S (ty_main_tree_bndfolds tr)
| ty_main_tree_nocap_bnd T => 0
| ty_main_tree_sel tr y A z => (ty_main_tree_bndfolds tr)
end.

Fixpoint ty_main_tree_under_lc (tr: ty_main_tree) oc {struct oc}: ty_main_tree :=
match oc, tr with
| logpath_nil, _ => tr
| logpath_orl ocp, ty_main_tree_or trl trr => ty_main_tree_under_lc trl ocp
| logpath_orl ocp, _ => tr
| logpath_orr ocp, ty_main_tree_or trl trr => ty_main_tree_under_lc trr ocp
| logpath_orr ocp, _ => tr
| logpath_andl ocp, ty_main_tree_and trl trr => ty_main_tree_under_lc trl ocp
| logpath_andl ocp, _ => tr
| logpath_andr ocp, ty_main_tree_and trl trr => ty_main_tree_under_lc trr ocp
| logpath_andr ocp, _ => tr
end.

Fixpoint ty_main_tree_set_under_lc (tr tr2: ty_main_tree) oc {struct oc}: ty_main_tree :=
match oc, tr with
| logpath_nil, _ => tr2
| logpath_orl ocp, ty_main_tree_or trl trr => ty_main_tree_or (ty_main_tree_set_under_lc trl tr2 ocp) trr
| logpath_orl ocp, _ => tr2
| logpath_orr ocp, ty_main_tree_or trl trr => ty_main_tree_or trl (ty_main_tree_set_under_lc trr tr2 ocp)
| logpath_orr ocp, _ => tr2
| logpath_andl ocp, ty_main_tree_and trl trr => ty_main_tree_and (ty_main_tree_set_under_lc trl tr2 ocp) trr
| logpath_andl ocp, _ => tr2
| logpath_andr ocp, ty_main_tree_and trl trr => ty_main_tree_and trl (ty_main_tree_set_under_lc trr tr2 ocp)
| logpath_andr ocp, _ => tr2
end.

Fixpoint ty_main_tree_refl T: ty_main_tree :=
match T with
| typ_and Tl Tr => ty_main_tree_and (ty_main_tree_refl Tl) (ty_main_tree_refl Tr)
| typ_or Tl Tr => ty_main_tree_or (ty_main_tree_refl Tl) (ty_main_tree_refl Tr)
| _ => (ty_main_tree_atomic T)
end.

Fixpoint ty_main_tree_extend_lc (tr: ty_main_tree) oc {struct oc}: ty_main_tree :=
match oc with
| logctx_nil => tr
| logctx_orl ocp Tr => ty_main_tree_or (ty_main_tree_extend_lc tr ocp) (ty_main_tree_refl Tr)
| logctx_orr Tl ocp => ty_main_tree_or (ty_main_tree_refl Tl) (ty_main_tree_extend_lc tr ocp)
| logctx_andl ocp Tr => ty_main_tree_and (ty_main_tree_extend_lc tr ocp) (ty_main_tree_refl Tr)
| logctx_andr Tl ocp => ty_main_tree_and (ty_main_tree_refl Tl) (ty_main_tree_extend_lc tr ocp)
end.

Fixpoint ty_main_tree_trans (tr1 tr2: ty_main_tree) {struct tr2} :=
  match tr2, tr1 with
  | ty_main_tree_atomic tr2l, _ => tr1
  | ty_main_tree_or tr2l tr2r, ty_main_tree_or tr1l tr1r => ty_main_tree_or (ty_main_tree_trans tr1l tr2l) (ty_main_tree_trans tr1r tr2r)
  | ty_main_tree_and tr2l tr2r, ty_main_tree_and tr1l tr1r => ty_main_tree_and (ty_main_tree_trans tr1l tr2l) (ty_main_tree_trans tr1r tr2r)
  | ty_main_tree_bnd tr2l T2, _ => ty_main_tree_bnd (ty_main_tree_trans tr1 tr2l) T2
  | ty_main_tree_sel tr2l y2 A2 z2, _ => ty_main_tree_sel (ty_main_tree_trans tr1 tr2l) y2 A2 z2
  | ty_main_tree_nocap_bnd T2, _ => ty_main_tree_nocap_bnd T2
  | _,_ => tr1
  end.

Section WithContext.

Context (G: ctx) (e: renv) (x: var).

Context (Hin: inert G).

End WithContext.

End WithTypingMode.
