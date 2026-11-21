Require Import Bool.

Require Import Metalib.Metatheory.

Require Import List.

Definition typvar : Set := var.

Definition expvar : Set := var.

Inductive typ : Set :=
 | typ_unit : typ
 | typ_top : typ
 | typ_bot : typ
 | typ_var_b (_:nat)
 | typ_var_f (X:typvar)
 | typ_arrow (A1:typ) (A2:typ)
 | typ_all (A:typ)
 | typ_union (A1:typ) (A2:typ)
 | typ_intersection (A1:typ) (A2:typ).

Inductive exp : Set :=
 | exp_unit : exp
 | exp_var_b (_:nat)
 | exp_var_f (x:expvar)
 | exp_abs (e:exp)
 | exp_app (e1:exp) (e2:exp)
 | exp_tabs (e:exp)
 | exp_tapp (e:exp) (A:typ)
 | exp_anno (e:exp) (A:typ).

Inductive conts : Set :=
 | conts_infabs (cd:contd)
 | conts_inftapp (A:typ) (cs:conts)
 | conts_inftappunion (A1:typ) (A2:typ) (cs:conts)
 | conts_unioninftapp (A2:typ) (cs:conts)
 | conts_sub (A:typ)
with contd : Set :=
 | contd_infabsunion (A:typ) (cd:contd)
 | contd_infapp (e:exp) (cs:conts)
 | contd_unioninfabs (A:typ) (B:typ) (cd:contd).

Inductive dbind : Set :=
 | dbind_tvar_empty : dbind
 | dbind_stvar_empty : dbind
 | dbind_typ (A:typ).

Inductive abind : Set :=
 | abind_tvar_empty : abind
 | abind_stvar_empty : abind
 | abind_etvar_empty : abind
 | abind_var_typ (A:typ).

Inductive work : Set :=
 | work_infer (e:exp) (cs:conts)
 | work_check (e:exp) (A:typ)
 | work_infabs (A:typ) (cd:contd)
 | work_infabsunion (A1:typ) (B1:typ) (A2:typ) (cd:contd)
 | work_infapp (A:typ) (B:typ) (e:exp) (cs:conts)
 | work_inftapp (A1:typ) (A2:typ) (cs:conts)
 | work_sub (A1:typ) (A2:typ)
 | work_inftappunion (A1:typ) (A2:typ) (B:typ) (cs:conts)
 | work_unioninftapp (A1:typ) (A2:typ) (cs:conts)
 | work_unioninfabs (A1:typ) (B1:typ) (A2:typ) (B2:typ) (cd:contd)
 | work_applys (cs:conts) (A:typ)
 | work_applyd (cd:contd) (A:typ) (B:typ).

Definition denv : Set := list (atom*dbind).

Definition aenv : Set := list (atom*abind).

Inductive aworklist : Set :=
 | aworklist_empty : aworklist
 | aworklist_cons_var (Γ:aworklist) (X:typvar) (ab:abind)
 | aworklist_cons_work (Γ:aworklist) (w:work).

Inductive dworklist : Set :=
 | dworklist_empty : dworklist
 | dworklist_cons_var (Ω:dworklist) (X:typvar) (db:dbind)
 | dworklist_cons_work (Ω:dworklist) (w:work).

Fixpoint open_typ_wrt_typ_rec (k:nat) (A_5:typ) (A__6:typ) {struct A__6}: typ :=
  match A__6 with
  | typ_unit => typ_unit
  | typ_top => typ_top
  | typ_bot => typ_bot
  | (typ_var_b nat) =>
      match lt_eq_lt_dec nat k with
        | inleft (left _) => typ_var_b nat
        | inleft (right _) => A_5
        | inright _ => typ_var_b (nat - 1)
      end
  | (typ_var_f X) => typ_var_f X
  | (typ_arrow A1 A2) => typ_arrow (open_typ_wrt_typ_rec k A_5 A1) (open_typ_wrt_typ_rec k A_5 A2)
  | (typ_all A) => typ_all (open_typ_wrt_typ_rec (S k) A_5 A)
  | (typ_union A1 A2) => typ_union (open_typ_wrt_typ_rec k A_5 A1) (open_typ_wrt_typ_rec k A_5 A2)
  | (typ_intersection A1 A2) => typ_intersection (open_typ_wrt_typ_rec k A_5 A1) (open_typ_wrt_typ_rec k A_5 A2)
end.

Fixpoint open_exp_wrt_exp_rec (k:nat) (e_5:exp) (e__6:exp) {struct e__6}: exp :=
  match e__6 with
  | exp_unit => exp_unit
  | (exp_var_b nat) =>
      match lt_eq_lt_dec nat k with
        | inleft (left _) => exp_var_b nat
        | inleft (right _) => e_5
        | inright _ => exp_var_b (nat - 1)
      end
  | (exp_var_f x) => exp_var_f x
  | (exp_abs e) => exp_abs (open_exp_wrt_exp_rec (S k) e_5 e)
  | (exp_app e1 e2) => exp_app (open_exp_wrt_exp_rec k e_5 e1) (open_exp_wrt_exp_rec k e_5 e2)
  | (exp_tabs e) => exp_tabs (open_exp_wrt_exp_rec k e_5 e)
  | (exp_tapp e A) => exp_tapp (open_exp_wrt_exp_rec k e_5 e) A
  | (exp_anno e A) => exp_anno (open_exp_wrt_exp_rec k e_5 e) A
end.

Fixpoint open_exp_wrt_typ_rec (k:nat) (A_5:typ) (e_5:exp) {struct e_5}: exp :=
  match e_5 with
  | exp_unit => exp_unit
  | (exp_var_b nat) => exp_var_b nat
  | (exp_var_f x) => exp_var_f x
  | (exp_abs e) => exp_abs (open_exp_wrt_typ_rec k A_5 e)
  | (exp_app e1 e2) => exp_app (open_exp_wrt_typ_rec k A_5 e1) (open_exp_wrt_typ_rec k A_5 e2)
  | (exp_tabs e) => exp_tabs (open_exp_wrt_typ_rec (S k) A_5 e)
  | (exp_tapp e A) => exp_tapp (open_exp_wrt_typ_rec k A_5 e) (open_typ_wrt_typ_rec k A_5 A)
  | (exp_anno e A) => exp_anno (open_exp_wrt_typ_rec k A_5 e) (open_typ_wrt_typ_rec k A_5 A)
end.

Fixpoint open_contd_wrt_exp_rec (k:nat) (e5:exp) (cd5:contd) {struct cd5}: contd :=
  match cd5 with
  | (contd_infabsunion A cd) => contd_infabsunion A (open_contd_wrt_exp_rec k e5 cd)
  | (contd_infapp e cs) => contd_infapp (open_exp_wrt_exp_rec k e5 e) (open_conts_wrt_exp_rec k e5 cs)
  | (contd_unioninfabs A B cd) => contd_unioninfabs A B (open_contd_wrt_exp_rec k e5 cd)
end
with open_conts_wrt_exp_rec (k:nat) (e5:exp) (cs5:conts) {struct cs5}: conts :=
  match cs5 with
  | (conts_infabs cd) => conts_infabs (open_contd_wrt_exp_rec k e5 cd)
  | (conts_inftapp A cs) => conts_inftapp A (open_conts_wrt_exp_rec k e5 cs)
  | (conts_inftappunion A1 A2 cs) => conts_inftappunion A1 A2 (open_conts_wrt_exp_rec k e5 cs)
  | (conts_unioninftapp A2 cs) => conts_unioninftapp A2 (open_conts_wrt_exp_rec k e5 cs)
  | (conts_sub A) => conts_sub A
end.

Fixpoint open_contd_wrt_typ_rec (k:nat) (A5:typ) (cd5:contd) {struct cd5}: contd :=
  match cd5 with
  | (contd_infabsunion A cd) => contd_infabsunion (open_typ_wrt_typ_rec k A5 A) (open_contd_wrt_typ_rec k A5 cd)
  | (contd_infapp e cs) => contd_infapp (open_exp_wrt_typ_rec k A5 e) (open_conts_wrt_typ_rec k A5 cs)
  | (contd_unioninfabs A B cd) => contd_unioninfabs (open_typ_wrt_typ_rec k A5 A) (open_typ_wrt_typ_rec k A5 B) (open_contd_wrt_typ_rec k A5 cd)
end
with open_conts_wrt_typ_rec (k:nat) (A_5:typ) (cs5:conts) {struct cs5}: conts :=
  match cs5 with
  | (conts_infabs cd) => conts_infabs (open_contd_wrt_typ_rec k A_5 cd)
  | (conts_inftapp A cs) => conts_inftapp (open_typ_wrt_typ_rec k A_5 A) (open_conts_wrt_typ_rec k A_5 cs)
  | (conts_inftappunion A1 A2 cs) => conts_inftappunion (open_typ_wrt_typ_rec k A_5 A1) (open_typ_wrt_typ_rec k A_5 A2) (open_conts_wrt_typ_rec k A_5 cs)
  | (conts_unioninftapp A2 cs) => conts_unioninftapp (open_typ_wrt_typ_rec k A_5 A2) (open_conts_wrt_typ_rec k A_5 cs)
  | (conts_sub A) => conts_sub (open_typ_wrt_typ_rec k A_5 A)
end.

Definition open_work_wrt_exp_rec (k:nat) (e5:exp) (w5:work) : work :=
  match w5 with
  | (work_infer e cs) => work_infer (open_exp_wrt_exp_rec k e5 e) (open_conts_wrt_exp_rec k e5 cs)
  | (work_check e A) => work_check (open_exp_wrt_exp_rec k e5 e) A
  | (work_infabs A cd) => work_infabs A (open_contd_wrt_exp_rec k e5 cd)
  | (work_infabsunion A1 B1 A2 cd) => work_infabsunion A1 B1 A2 (open_contd_wrt_exp_rec k e5 cd)
  | (work_infapp A B e cs) => work_infapp A B (open_exp_wrt_exp_rec k e5 e) (open_conts_wrt_exp_rec k e5 cs)
  | (work_inftapp A1 A2 cs) => work_inftapp A1 A2 (open_conts_wrt_exp_rec k e5 cs)
  | (work_sub A1 A2) => work_sub A1 A2
  | (work_inftappunion A1 A2 B cs) => work_inftappunion A1 A2 B (open_conts_wrt_exp_rec k e5 cs)
  | (work_unioninftapp A1 A2 cs) => work_unioninftapp A1 A2 (open_conts_wrt_exp_rec k e5 cs)
  | (work_unioninfabs A1 B1 A2 B2 cd) => work_unioninfabs A1 B1 A2 B2 (open_contd_wrt_exp_rec k e5 cd)
  | (work_applys cs A) => work_applys (open_conts_wrt_exp_rec k e5 cs) A
  | (work_applyd cd A B) => work_applyd (open_contd_wrt_exp_rec k e5 cd) A B
end.

Definition open_work_wrt_typ_rec (k:nat) (A_5:typ) (w5:work) : work :=
  match w5 with
  | (work_infer e cs) => work_infer (open_exp_wrt_typ_rec k A_5 e) (open_conts_wrt_typ_rec k A_5 cs)
  | (work_check e A) => work_check (open_exp_wrt_typ_rec k A_5 e) (open_typ_wrt_typ_rec k A_5 A)
  | (work_infabs A cd) => work_infabs (open_typ_wrt_typ_rec k A_5 A) (open_contd_wrt_typ_rec k A_5 cd)
  | (work_infabsunion A1 B1 A2 cd) => work_infabsunion (open_typ_wrt_typ_rec k A_5 A1) (open_typ_wrt_typ_rec k A_5 B1) (open_typ_wrt_typ_rec k A_5 A2) (open_contd_wrt_typ_rec k A_5 cd)
  | (work_infapp A B e cs) => work_infapp (open_typ_wrt_typ_rec k A_5 A) (open_typ_wrt_typ_rec k A_5 B) (open_exp_wrt_typ_rec k A_5 e) (open_conts_wrt_typ_rec k A_5 cs)
  | (work_inftapp A1 A2 cs) => work_inftapp (open_typ_wrt_typ_rec k A_5 A1) (open_typ_wrt_typ_rec k A_5 A2) (open_conts_wrt_typ_rec k A_5 cs)
  | (work_sub A1 A2) => work_sub (open_typ_wrt_typ_rec k A_5 A1) (open_typ_wrt_typ_rec k A_5 A2)
  | (work_inftappunion A1 A2 B cs) => work_inftappunion (open_typ_wrt_typ_rec k A_5 A1) (open_typ_wrt_typ_rec k A_5 A2) (open_typ_wrt_typ_rec k A_5 B) (open_conts_wrt_typ_rec k A_5 cs)
  | (work_unioninftapp A1 A2 cs) => work_unioninftapp (open_typ_wrt_typ_rec k A_5 A1) (open_typ_wrt_typ_rec k A_5 A2) (open_conts_wrt_typ_rec k A_5 cs)
  | (work_unioninfabs A1 B1 A2 B2 cd) => work_unioninfabs (open_typ_wrt_typ_rec k A_5 A1) (open_typ_wrt_typ_rec k A_5 B1) (open_typ_wrt_typ_rec k A_5 A2) (open_typ_wrt_typ_rec k A_5 B2) (open_contd_wrt_typ_rec k A_5 cd)
  | (work_applys cs A) => work_applys (open_conts_wrt_typ_rec k A_5 cs) (open_typ_wrt_typ_rec k A_5 A)
  | (work_applyd cd A B) => work_applyd (open_contd_wrt_typ_rec k A_5 cd) (open_typ_wrt_typ_rec k A_5 A) (open_typ_wrt_typ_rec k A_5 B)
end.

Definition open_abind_wrt_typ_rec (k:nat) (A5:typ) (ab5:abind) : abind :=
  match ab5 with
  | abind_tvar_empty => abind_tvar_empty
  | abind_stvar_empty => abind_stvar_empty
  | abind_etvar_empty => abind_etvar_empty
  | (abind_var_typ A) => abind_var_typ (open_typ_wrt_typ_rec k A5 A)
end.

Definition open_dbind_wrt_typ_rec (k:nat) (A5:typ) (db5:dbind) : dbind :=
  match db5 with
  | dbind_tvar_empty => dbind_tvar_empty
  | dbind_stvar_empty => dbind_stvar_empty
  | (dbind_typ A) => dbind_typ (open_typ_wrt_typ_rec k A5 A)
end.

Fixpoint open_dworklist_wrt_exp_rec (k:nat) (e5:exp) (Ω5:dworklist) {struct Ω5}: dworklist :=
  match Ω5 with
  | dworklist_empty => dworklist_empty
  | (dworklist_cons_var Ω X db) => dworklist_cons_var (open_dworklist_wrt_exp_rec k e5 Ω) X db
  | (dworklist_cons_work Ω w) => dworklist_cons_work (open_dworklist_wrt_exp_rec k e5 Ω) (open_work_wrt_exp_rec k e5 w)
end.

Fixpoint open_aworklist_wrt_typ_rec (k:nat) (A5:typ) (Γ_5:aworklist) {struct Γ_5}: aworklist :=
  match Γ_5 with
  | aworklist_empty => aworklist_empty
  | (aworklist_cons_var Γ X ab) => aworklist_cons_var (open_aworklist_wrt_typ_rec k A5 Γ) X (open_abind_wrt_typ_rec k A5 ab)
  | (aworklist_cons_work Γ w) => aworklist_cons_work (open_aworklist_wrt_typ_rec k A5 Γ) (open_work_wrt_typ_rec k A5 w)
end.

Fixpoint open_aworklist_wrt_exp_rec (k:nat) (e5:exp) (Γ_5:aworklist) {struct Γ_5}: aworklist :=
  match Γ_5 with
  | aworklist_empty => aworklist_empty
  | (aworklist_cons_var Γ X ab) => aworklist_cons_var (open_aworklist_wrt_exp_rec k e5 Γ) X ab
  | (aworklist_cons_work Γ w) => aworklist_cons_work (open_aworklist_wrt_exp_rec k e5 Γ) (open_work_wrt_exp_rec k e5 w)
end.

Fixpoint open_dworklist_wrt_typ_rec (k:nat) (A5:typ) (Ω5:dworklist) {struct Ω5}: dworklist :=
  match Ω5 with
  | dworklist_empty => dworklist_empty
  | (dworklist_cons_var Ω X db) => dworklist_cons_var (open_dworklist_wrt_typ_rec k A5 Ω) X (open_dbind_wrt_typ_rec k A5 db)
  | (dworklist_cons_work Ω w) => dworklist_cons_work (open_dworklist_wrt_typ_rec k A5 Ω) (open_work_wrt_typ_rec k A5 w)
end.

Definition open_dworklist_wrt_exp e5 Ω5 := open_dworklist_wrt_exp_rec 0 Ω5 e5.

Definition open_typ_wrt_typ A_5 A__6 := open_typ_wrt_typ_rec 0 A__6 A_5.

Definition open_contd_wrt_exp e5 cd5 := open_contd_wrt_exp_rec 0 cd5 e5.

Definition open_contd_wrt_typ A5 cd5 := open_contd_wrt_typ_rec 0 cd5 A5.

Definition open_aworklist_wrt_typ A5 Γ_5 := open_aworklist_wrt_typ_rec 0 Γ_5 A5.

Definition open_dbind_wrt_typ A5 db5 := open_dbind_wrt_typ_rec 0 db5 A5.

Definition open_exp_wrt_exp e_5 e__6 := open_exp_wrt_exp_rec 0 e__6 e_5.

Definition open_aworklist_wrt_exp e5 Γ_5 := open_aworklist_wrt_exp_rec 0 Γ_5 e5.

Definition open_work_wrt_typ A_5 w5 := open_work_wrt_typ_rec 0 w5 A_5.

Definition open_work_wrt_exp e5 w5 := open_work_wrt_exp_rec 0 w5 e5.

Definition open_conts_wrt_exp e5 cs5 := open_conts_wrt_exp_rec 0 cs5 e5.

Definition open_abind_wrt_typ A5 ab5 := open_abind_wrt_typ_rec 0 ab5 A5.

Definition open_conts_wrt_typ A_5 cs5 := open_conts_wrt_typ_rec 0 cs5 A_5.

Definition open_dworklist_wrt_typ A5 Ω5 := open_dworklist_wrt_typ_rec 0 Ω5 A5.

Definition open_exp_wrt_typ A_5 e_5 := open_exp_wrt_typ_rec 0 e_5 A_5.

Fixpoint close_typ_wrt_typ_rec (k:nat) (A_5:var) (A__6:typ) {struct A__6}: typ :=
  match A__6 with
  | typ_unit => typ_unit
  | typ_top => typ_top
  | typ_bot => typ_bot
  | (typ_var_b nat) =>
       if (lt_dec nat k)
         then typ_var_b nat
         else typ_var_b (S nat)
  | (typ_var_f X) => if (A_5 === X) then (typ_var_b k) else (typ_var_f X)
  | (typ_arrow A1 A2) => typ_arrow (close_typ_wrt_typ_rec k A_5 A1) (close_typ_wrt_typ_rec k A_5 A2)
  | (typ_all A) => typ_all (close_typ_wrt_typ_rec (S k) A_5 A)
  | (typ_union A1 A2) => typ_union (close_typ_wrt_typ_rec k A_5 A1) (close_typ_wrt_typ_rec k A_5 A2)
  | (typ_intersection A1 A2) => typ_intersection (close_typ_wrt_typ_rec k A_5 A1) (close_typ_wrt_typ_rec k A_5 A2)
end.

Fixpoint close_exp_wrt_exp_rec (k:nat) (e_5:var) (e__6:exp) {struct e__6}: exp :=
  match e__6 with
  | exp_unit => exp_unit
  | (exp_var_b nat) =>
       if (lt_dec nat k)
         then exp_var_b nat
         else exp_var_b (S nat)
  | (exp_var_f x) => if (e_5 === x) then (exp_var_b k) else (exp_var_f x)
  | (exp_abs e) => exp_abs (close_exp_wrt_exp_rec (S k) e_5 e)
  | (exp_app e1 e2) => exp_app (close_exp_wrt_exp_rec k e_5 e1) (close_exp_wrt_exp_rec k e_5 e2)
  | (exp_tabs e) => exp_tabs (close_exp_wrt_exp_rec k e_5 e)
  | (exp_tapp e A) => exp_tapp (close_exp_wrt_exp_rec k e_5 e) A
  | (exp_anno e A) => exp_anno (close_exp_wrt_exp_rec k e_5 e) A
end.

Fixpoint close_exp_wrt_typ_rec (k:nat) (A_5:var) (e_5:exp) {struct e_5}: exp :=
  match e_5 with
  | exp_unit => exp_unit
  | (exp_var_b nat) => exp_var_b nat
  | (exp_var_f x) => exp_var_f x
  | (exp_abs e) => exp_abs (close_exp_wrt_typ_rec k A_5 e)
  | (exp_app e1 e2) => exp_app (close_exp_wrt_typ_rec k A_5 e1) (close_exp_wrt_typ_rec k A_5 e2)
  | (exp_tabs e) => exp_tabs (close_exp_wrt_typ_rec (S k) A_5 e)
  | (exp_tapp e A) => exp_tapp (close_exp_wrt_typ_rec k A_5 e) (close_typ_wrt_typ_rec k A_5 A)
  | (exp_anno e A) => exp_anno (close_exp_wrt_typ_rec k A_5 e) (close_typ_wrt_typ_rec k A_5 A)
end.

Fixpoint close_contd_wrt_exp_rec (k:nat) (e5:var) (cd5:contd) {struct cd5}: contd :=
  match cd5 with
  | (contd_infabsunion A cd) => contd_infabsunion A (close_contd_wrt_exp_rec k e5 cd)
  | (contd_infapp e cs) => contd_infapp (close_exp_wrt_exp_rec k e5 e) (close_conts_wrt_exp_rec k e5 cs)
  | (contd_unioninfabs A B cd) => contd_unioninfabs A B (close_contd_wrt_exp_rec k e5 cd)
end
with close_conts_wrt_exp_rec (k:nat) (e5:var) (cs5:conts) {struct cs5}: conts :=
  match cs5 with
  | (conts_infabs cd) => conts_infabs (close_contd_wrt_exp_rec k e5 cd)
  | (conts_inftapp A cs) => conts_inftapp A (close_conts_wrt_exp_rec k e5 cs)
  | (conts_inftappunion A1 A2 cs) => conts_inftappunion A1 A2 (close_conts_wrt_exp_rec k e5 cs)
  | (conts_unioninftapp A2 cs) => conts_unioninftapp A2 (close_conts_wrt_exp_rec k e5 cs)
  | (conts_sub A) => conts_sub A
end.

Fixpoint close_contd_wrt_typ_rec (k:nat) (A5:var) (cd5:contd) {struct cd5}: contd :=
  match cd5 with
  | (contd_infabsunion A cd) => contd_infabsunion (close_typ_wrt_typ_rec k A5 A) (close_contd_wrt_typ_rec k A5 cd)
  | (contd_infapp e cs) => contd_infapp (close_exp_wrt_typ_rec k A5 e) (close_conts_wrt_typ_rec k A5 cs)
  | (contd_unioninfabs A B cd) => contd_unioninfabs (close_typ_wrt_typ_rec k A5 A) (close_typ_wrt_typ_rec k A5 B) (close_contd_wrt_typ_rec k A5 cd)
end
with close_conts_wrt_typ_rec (k:nat) (A_5:var) (cs5:conts) {struct cs5}: conts :=
  match cs5 with
  | (conts_infabs cd) => conts_infabs (close_contd_wrt_typ_rec k A_5 cd)
  | (conts_inftapp A cs) => conts_inftapp (close_typ_wrt_typ_rec k A_5 A) (close_conts_wrt_typ_rec k A_5 cs)
  | (conts_inftappunion A1 A2 cs) => conts_inftappunion (close_typ_wrt_typ_rec k A_5 A1) (close_typ_wrt_typ_rec k A_5 A2) (close_conts_wrt_typ_rec k A_5 cs)
  | (conts_unioninftapp A2 cs) => conts_unioninftapp (close_typ_wrt_typ_rec k A_5 A2) (close_conts_wrt_typ_rec k A_5 cs)
  | (conts_sub A) => conts_sub (close_typ_wrt_typ_rec k A_5 A)
end.

Definition close_work_wrt_exp_rec (k:nat) (e5:var) (w5:work) : work :=
  match w5 with
  | (work_infer e cs) => work_infer (close_exp_wrt_exp_rec k e5 e) (close_conts_wrt_exp_rec k e5 cs)
  | (work_check e A) => work_check (close_exp_wrt_exp_rec k e5 e) A
  | (work_infabs A cd) => work_infabs A (close_contd_wrt_exp_rec k e5 cd)
  | (work_infabsunion A1 B1 A2 cd) => work_infabsunion A1 B1 A2 (close_contd_wrt_exp_rec k e5 cd)
  | (work_infapp A B e cs) => work_infapp A B (close_exp_wrt_exp_rec k e5 e) (close_conts_wrt_exp_rec k e5 cs)
  | (work_inftapp A1 A2 cs) => work_inftapp A1 A2 (close_conts_wrt_exp_rec k e5 cs)
  | (work_sub A1 A2) => work_sub A1 A2
  | (work_inftappunion A1 A2 B cs) => work_inftappunion A1 A2 B (close_conts_wrt_exp_rec k e5 cs)
  | (work_unioninftapp A1 A2 cs) => work_unioninftapp A1 A2 (close_conts_wrt_exp_rec k e5 cs)
  | (work_unioninfabs A1 B1 A2 B2 cd) => work_unioninfabs A1 B1 A2 B2 (close_contd_wrt_exp_rec k e5 cd)
  | (work_applys cs A) => work_applys (close_conts_wrt_exp_rec k e5 cs) A
  | (work_applyd cd A B) => work_applyd (close_contd_wrt_exp_rec k e5 cd) A B
end.

Definition close_dbind_wrt_typ_rec (k:nat) (A5:var) (db5:dbind) : dbind :=
  match db5 with
  | dbind_tvar_empty => dbind_tvar_empty
  | dbind_stvar_empty => dbind_stvar_empty
  | (dbind_typ A) => dbind_typ (close_typ_wrt_typ_rec k A5 A)
end.

Definition close_work_wrt_typ_rec (k:nat) (A_5:var) (w5:work) : work :=
  match w5 with
  | (work_infer e cs) => work_infer (close_exp_wrt_typ_rec k A_5 e) (close_conts_wrt_typ_rec k A_5 cs)
  | (work_check e A) => work_check (close_exp_wrt_typ_rec k A_5 e) (close_typ_wrt_typ_rec k A_5 A)
  | (work_infabs A cd) => work_infabs (close_typ_wrt_typ_rec k A_5 A) (close_contd_wrt_typ_rec k A_5 cd)
  | (work_infabsunion A1 B1 A2 cd) => work_infabsunion (close_typ_wrt_typ_rec k A_5 A1) (close_typ_wrt_typ_rec k A_5 B1) (close_typ_wrt_typ_rec k A_5 A2) (close_contd_wrt_typ_rec k A_5 cd)
  | (work_infapp A B e cs) => work_infapp (close_typ_wrt_typ_rec k A_5 A) (close_typ_wrt_typ_rec k A_5 B) (close_exp_wrt_typ_rec k A_5 e) (close_conts_wrt_typ_rec k A_5 cs)
  | (work_inftapp A1 A2 cs) => work_inftapp (close_typ_wrt_typ_rec k A_5 A1) (close_typ_wrt_typ_rec k A_5 A2) (close_conts_wrt_typ_rec k A_5 cs)
  | (work_sub A1 A2) => work_sub (close_typ_wrt_typ_rec k A_5 A1) (close_typ_wrt_typ_rec k A_5 A2)
  | (work_inftappunion A1 A2 B cs) => work_inftappunion (close_typ_wrt_typ_rec k A_5 A1) (close_typ_wrt_typ_rec k A_5 A2) (close_typ_wrt_typ_rec k A_5 B) (close_conts_wrt_typ_rec k A_5 cs)
  | (work_unioninftapp A1 A2 cs) => work_unioninftapp (close_typ_wrt_typ_rec k A_5 A1) (close_typ_wrt_typ_rec k A_5 A2) (close_conts_wrt_typ_rec k A_5 cs)
  | (work_unioninfabs A1 B1 A2 B2 cd) => work_unioninfabs (close_typ_wrt_typ_rec k A_5 A1) (close_typ_wrt_typ_rec k A_5 B1) (close_typ_wrt_typ_rec k A_5 A2) (close_typ_wrt_typ_rec k A_5 B2) (close_contd_wrt_typ_rec k A_5 cd)
  | (work_applys cs A) => work_applys (close_conts_wrt_typ_rec k A_5 cs) (close_typ_wrt_typ_rec k A_5 A)
  | (work_applyd cd A B) => work_applyd (close_contd_wrt_typ_rec k A_5 cd) (close_typ_wrt_typ_rec k A_5 A) (close_typ_wrt_typ_rec k A_5 B)
end.

Definition close_abind_wrt_typ_rec (k:nat) (A5:var) (ab5:abind) : abind :=
  match ab5 with
  | abind_tvar_empty => abind_tvar_empty
  | abind_stvar_empty => abind_stvar_empty
  | abind_etvar_empty => abind_etvar_empty
  | (abind_var_typ A) => abind_var_typ (close_typ_wrt_typ_rec k A5 A)
end.

Fixpoint close_aworklist_wrt_exp_rec (k:nat) (e5:var) (Γ_5:aworklist) {struct Γ_5}: aworklist :=
  match Γ_5 with
  | aworklist_empty => aworklist_empty
  | (aworklist_cons_var Γ X ab) => aworklist_cons_var (close_aworklist_wrt_exp_rec k e5 Γ) X ab
  | (aworklist_cons_work Γ w) => aworklist_cons_work (close_aworklist_wrt_exp_rec k e5 Γ) (close_work_wrt_exp_rec k e5 w)
end.

Fixpoint close_dworklist_wrt_typ_rec (k:nat) (A5:var) (Ω5:dworklist) {struct Ω5}: dworklist :=
  match Ω5 with
  | dworklist_empty => dworklist_empty
  | (dworklist_cons_var Ω X db) => dworklist_cons_var (close_dworklist_wrt_typ_rec k A5 Ω) X (close_dbind_wrt_typ_rec k A5 db)
  | (dworklist_cons_work Ω w) => dworklist_cons_work (close_dworklist_wrt_typ_rec k A5 Ω) (close_work_wrt_typ_rec k A5 w)
end.

Fixpoint close_dworklist_wrt_exp_rec (k:nat) (e5:var) (Ω5:dworklist) {struct Ω5}: dworklist :=
  match Ω5 with
  | dworklist_empty => dworklist_empty
  | (dworklist_cons_var Ω X db) => dworklist_cons_var (close_dworklist_wrt_exp_rec k e5 Ω) X db
  | (dworklist_cons_work Ω w) => dworklist_cons_work (close_dworklist_wrt_exp_rec k e5 Ω) (close_work_wrt_exp_rec k e5 w)
end.

Fixpoint close_aworklist_wrt_typ_rec (k:nat) (A5:var) (Γ_5:aworklist) {struct Γ_5}: aworklist :=
  match Γ_5 with
  | aworklist_empty => aworklist_empty
  | (aworklist_cons_var Γ X ab) => aworklist_cons_var (close_aworklist_wrt_typ_rec k A5 Γ) X (close_abind_wrt_typ_rec k A5 ab)
  | (aworklist_cons_work Γ w) => aworklist_cons_work (close_aworklist_wrt_typ_rec k A5 Γ) (close_work_wrt_typ_rec k A5 w)
end.

Definition close_dbind_wrt_typ db5 A5 := close_dbind_wrt_typ_rec 0 db5 A5.

Definition close_exp_wrt_exp e__6 e_5 := close_exp_wrt_exp_rec 0 e__6 e_5.

Definition close_aworklist_wrt_exp Γ_5 e5 := close_aworklist_wrt_exp_rec 0 Γ_5 e5.

Definition close_work_wrt_typ w5 A_5 := close_work_wrt_typ_rec 0 w5 A_5.

Definition close_work_wrt_exp w5 e5 := close_work_wrt_exp_rec 0 w5 e5.

Definition close_conts_wrt_exp cs5 e5 := close_conts_wrt_exp_rec 0 cs5 e5.

Definition close_abind_wrt_typ ab5 A5 := close_abind_wrt_typ_rec 0 ab5 A5.

Definition close_conts_wrt_typ cs5 A_5 := close_conts_wrt_typ_rec 0 cs5 A_5.

Definition close_dworklist_wrt_typ Ω5 A5 := close_dworklist_wrt_typ_rec 0 Ω5 A5.

Definition close_exp_wrt_typ e_5 A_5 := close_exp_wrt_typ_rec 0 e_5 A_5.

Definition close_dworklist_wrt_exp Ω5 e5 := close_dworklist_wrt_exp_rec 0 Ω5 e5.

Definition close_typ_wrt_typ A__6 A_5 := close_typ_wrt_typ_rec 0 A__6 A_5.

Definition close_contd_wrt_exp cd5 e5 := close_contd_wrt_exp_rec 0 cd5 e5.

Definition close_contd_wrt_typ cd5 A5 := close_contd_wrt_typ_rec 0 cd5 A5.

Definition close_aworklist_wrt_typ Γ_5 A5 := close_aworklist_wrt_typ_rec 0 Γ_5 A5.

Inductive lc_typ : typ -> Prop :=
 | lc_typ_unit :
     (lc_typ typ_unit)
 | lc_typ_top :
     (lc_typ typ_top)
 | lc_typ_bot :
     (lc_typ typ_bot)
 | lc_typ_var_f : forall (X:typvar),
     (lc_typ (typ_var_f X))
 | lc_typ_arrow : forall (A1 A2:typ),
     (lc_typ A1) ->
     (lc_typ A2) ->
     (lc_typ (typ_arrow A1 A2))
 | lc_typ_all : forall (A:typ),
      ( forall X , lc_typ  ( open_typ_wrt_typ A (typ_var_f X) )  )  ->
     (lc_typ (typ_all A))
 | lc_typ_union : forall (A1 A2:typ),
     (lc_typ A1) ->
     (lc_typ A2) ->
     (lc_typ (typ_union A1 A2))
 | lc_typ_intersection : forall (A1 A2:typ),
     (lc_typ A1) ->
     (lc_typ A2) ->
     (lc_typ (typ_intersection A1 A2)).

Inductive lc_exp : exp -> Prop :=
 | lc_exp_unit :
     (lc_exp exp_unit)
 | lc_exp_var_f : forall (x:expvar),
     (lc_exp (exp_var_f x))
 | lc_exp_abs : forall (e:exp),
      ( forall x , lc_exp  ( open_exp_wrt_exp e (exp_var_f x) )  )  ->
     (lc_exp (exp_abs e))
 | lc_exp_app : forall (e1 e2:exp),
     (lc_exp e1) ->
     (lc_exp e2) ->
     (lc_exp (exp_app e1 e2))
 | lc_exp_tabs : forall (e:exp),
      ( forall X , lc_exp  ( open_exp_wrt_typ e (typ_var_f X) )  )  ->
     (lc_exp (exp_tabs e))
 | lc_exp_tapp : forall (e:exp) (A:typ),
     (lc_exp e) ->
     (lc_typ A) ->
     (lc_exp (exp_tapp e A))
 | lc_exp_anno : forall (e:exp) (A:typ),
     (lc_exp e) ->
     (lc_typ A) ->
     (lc_exp (exp_anno e A)).

Inductive lc_contd : contd -> Prop :=
 | lc_contd_infabsunion : forall (A:typ) (cd:contd),
     (lc_typ A) ->
     (lc_contd cd) ->
     (lc_contd (contd_infabsunion A cd))
 | lc_contd_infapp : forall (e:exp) (cs:conts),
     (lc_exp e) ->
     (lc_conts cs) ->
     (lc_contd (contd_infapp e cs))
 | lc_contd_unioninfabs : forall (A B:typ) (cd:contd),
     (lc_typ A) ->
     (lc_typ B) ->
     (lc_contd cd) ->
     (lc_contd (contd_unioninfabs A B cd))
with lc_conts : conts -> Prop :=
 | lc_conts_infabs : forall (cd:contd),
     (lc_contd cd) ->
     (lc_conts (conts_infabs cd))
 | lc_conts_inftapp : forall (A:typ) (cs:conts),
     (lc_typ A) ->
     (lc_conts cs) ->
     (lc_conts (conts_inftapp A cs))
 | lc_conts_inftappunion : forall (A1 A2:typ) (cs:conts),
     (lc_typ A1) ->
     (lc_typ A2) ->
     (lc_conts cs) ->
     (lc_conts (conts_inftappunion A1 A2 cs))
 | lc_conts_unioninftapp : forall (A2:typ) (cs:conts),
     (lc_typ A2) ->
     (lc_conts cs) ->
     (lc_conts (conts_unioninftapp A2 cs))
 | lc_conts_sub : forall (A:typ),
     (lc_typ A) ->
     (lc_conts (conts_sub A)).

Inductive lc_dbind : dbind -> Prop :=
 | lc_dbind_tvar_empty :
     (lc_dbind dbind_tvar_empty)
 | lc_dbind_stvar_empty :
     (lc_dbind dbind_stvar_empty)
 | lc_dbind_typ : forall (A:typ),
     (lc_typ A) ->
     (lc_dbind (dbind_typ A)).

Inductive lc_abind : abind -> Prop :=
 | lc_abind_tvar_empty :
     (lc_abind abind_tvar_empty)
 | lc_abind_stvar_empty :
     (lc_abind abind_stvar_empty)
 | lc_abind_etvar_empty :
     (lc_abind abind_etvar_empty)
 | lc_abind_var_typ : forall (A:typ),
     (lc_typ A) ->
     (lc_abind (abind_var_typ A)).

Inductive lc_work : work -> Prop :=
 | lc_work_infer : forall (e:exp) (cs:conts),
     (lc_exp e) ->
     (lc_conts cs) ->
     (lc_work (work_infer e cs))
 | lc_work_check : forall (e:exp) (A:typ),
     (lc_exp e) ->
     (lc_typ A) ->
     (lc_work (work_check e A))
 | lc_work_infabs : forall (A:typ) (cd:contd),
     (lc_typ A) ->
     (lc_contd cd) ->
     (lc_work (work_infabs A cd))
 | lc_work_infabsunion : forall (A1 B1 A2:typ) (cd:contd),
     (lc_typ A1) ->
     (lc_typ B1) ->
     (lc_typ A2) ->
     (lc_contd cd) ->
     (lc_work (work_infabsunion A1 B1 A2 cd))
 | lc_work_infapp : forall (A B:typ) (e:exp) (cs:conts),
     (lc_typ A) ->
     (lc_typ B) ->
     (lc_exp e) ->
     (lc_conts cs) ->
     (lc_work (work_infapp A B e cs))
 | lc_work_inftapp : forall (A1 A2:typ) (cs:conts),
     (lc_typ A1) ->
     (lc_typ A2) ->
     (lc_conts cs) ->
     (lc_work (work_inftapp A1 A2 cs))
 | lc_work_sub : forall (A1 A2:typ),
     (lc_typ A1) ->
     (lc_typ A2) ->
     (lc_work (work_sub A1 A2))
 | lc_work_inftappunion : forall (A1 A2 B:typ) (cs:conts),
     (lc_typ A1) ->
     (lc_typ A2) ->
     (lc_typ B) ->
     (lc_conts cs) ->
     (lc_work (work_inftappunion A1 A2 B cs))
 | lc_work_unioninftapp : forall (A1 A2:typ) (cs:conts),
     (lc_typ A1) ->
     (lc_typ A2) ->
     (lc_conts cs) ->
     (lc_work (work_unioninftapp A1 A2 cs))
 | lc_work_unioninfabs : forall (A1 B1 A2 B2:typ) (cd:contd),
     (lc_typ A1) ->
     (lc_typ B1) ->
     (lc_typ A2) ->
     (lc_typ B2) ->
     (lc_contd cd) ->
     (lc_work (work_unioninfabs A1 B1 A2 B2 cd))
 | lc_work_applys : forall (cs:conts) (A:typ),
     (lc_conts cs) ->
     (lc_typ A) ->
     (lc_work (work_applys cs A))
 | lc_work_applyd : forall (cd:contd) (A B:typ),
     (lc_contd cd) ->
     (lc_typ A) ->
     (lc_typ B) ->
     (lc_work (work_applyd cd A B)).

Inductive lc_aworklist : aworklist -> Prop :=
 | lc_aworklist_empty :
     (lc_aworklist aworklist_empty)
 | lc_aworklist_cons_var : forall (Γ:aworklist) (X:typvar) (ab:abind),
     (lc_aworklist Γ) ->
     (lc_abind ab) ->
     (lc_aworklist (aworklist_cons_var Γ X ab))
 | lc_aworklist_cons_work : forall (Γ:aworklist) (w:work),
     (lc_aworklist Γ) ->
     (lc_work w) ->
     (lc_aworklist (aworklist_cons_work Γ w)).

Inductive lc_dworklist : dworklist -> Prop :=
 | lc_dworklist_empty :
     (lc_dworklist dworklist_empty)
 | lc_dworklist_cons_var : forall (Ω:dworklist) (X:typvar) (db:dbind),
     (lc_dworklist Ω) ->
     (lc_dbind db) ->
     (lc_dworklist (dworklist_cons_var Ω X db))
 | lc_dworklist_cons_work : forall (Ω:dworklist) (w:work),
     (lc_dworklist Ω) ->
     (lc_work w) ->
     (lc_dworklist (dworklist_cons_work Ω w)).

Fixpoint ftvar_in_typ (A_5:typ) : vars :=
  match A_5 with
  | typ_unit => {}
  | typ_top => {}
  | typ_bot => {}
  | (typ_var_b nat) => {}
  | (typ_var_f X) => {{X}}
  | (typ_arrow A1 A2) => (ftvar_in_typ A1) \u (ftvar_in_typ A2)
  | (typ_all A) => (ftvar_in_typ A)
  | (typ_union A1 A2) => (ftvar_in_typ A1) \u (ftvar_in_typ A2)
  | (typ_intersection A1 A2) => (ftvar_in_typ A1) \u (ftvar_in_typ A2)
end.

Fixpoint ftvar_in_exp (e_5:exp) : vars :=
  match e_5 with
  | exp_unit => {}
  | (exp_var_b nat) => {}
  | (exp_var_f x) => {}
  | (exp_abs e) => (ftvar_in_exp e)
  | (exp_app e1 e2) => (ftvar_in_exp e1) \u (ftvar_in_exp e2)
  | (exp_tabs e) => (ftvar_in_exp e)
  | (exp_tapp e A) => (ftvar_in_exp e) \u (ftvar_in_typ A)
  | (exp_anno e A) => (ftvar_in_exp e) \u (ftvar_in_typ A)
end.

Fixpoint fvar_in_exp (e_5:exp) : vars :=
  match e_5 with
  | exp_unit => {}
  | (exp_var_b nat) => {}
  | (exp_var_f x) => {{x}}
  | (exp_abs e) => (fvar_in_exp e)
  | (exp_app e1 e2) => (fvar_in_exp e1) \u (fvar_in_exp e2)
  | (exp_tabs e) => (fvar_in_exp e)
  | (exp_tapp e A) => (fvar_in_exp e)
  | (exp_anno e A) => (fvar_in_exp e)
end.

Fixpoint ftvar_in_contd (cd5:contd) : vars :=
  match cd5 with
  | (contd_infabsunion A cd) => (ftvar_in_typ A) \u (ftvar_in_contd cd)
  | (contd_infapp e cs) => (ftvar_in_exp e) \u (ftvar_in_conts cs)
  | (contd_unioninfabs A B cd) => (ftvar_in_typ A) \u (ftvar_in_typ B) \u (ftvar_in_contd cd)
end
with ftvar_in_conts (cs5:conts) : vars :=
  match cs5 with
  | (conts_infabs cd) => (ftvar_in_contd cd)
  | (conts_inftapp A cs) => (ftvar_in_typ A) \u (ftvar_in_conts cs)
  | (conts_inftappunion A1 A2 cs) => (ftvar_in_typ A1) \u (ftvar_in_typ A2) \u (ftvar_in_conts cs)
  | (conts_unioninftapp A2 cs) => (ftvar_in_typ A2) \u (ftvar_in_conts cs)
  | (conts_sub A) => (ftvar_in_typ A)
end.

Fixpoint fvar_in_contd (cd5:contd) : vars :=
  match cd5 with
  | (contd_infabsunion A cd) => (fvar_in_contd cd)
  | (contd_infapp e cs) => (fvar_in_exp e) \u (fvar_in_conts cs)
  | (contd_unioninfabs A B cd) => (fvar_in_contd cd)
end
with fvar_in_conts (cs5:conts) : vars :=
  match cs5 with
  | (conts_infabs cd) => (fvar_in_contd cd)
  | (conts_inftapp A cs) => (fvar_in_conts cs)
  | (conts_inftappunion A1 A2 cs) => (fvar_in_conts cs)
  | (conts_unioninftapp A2 cs) => (fvar_in_conts cs)
  | (conts_sub A) => {}
end.

Definition ftvar_in_dbind (db5:dbind) : vars :=
  match db5 with
  | dbind_tvar_empty => {}
  | dbind_stvar_empty => {}
  | (dbind_typ A) => (ftvar_in_typ A)
end.

Definition ftvar_in_work (w5:work) : vars :=
  match w5 with
  | (work_infer e cs) => (ftvar_in_exp e) \u (ftvar_in_conts cs)
  | (work_check e A) => (ftvar_in_exp e) \u (ftvar_in_typ A)
  | (work_infabs A cd) => (ftvar_in_typ A) \u (ftvar_in_contd cd)
  | (work_infabsunion A1 B1 A2 cd) => (ftvar_in_typ A1) \u (ftvar_in_typ B1) \u (ftvar_in_typ A2) \u (ftvar_in_contd cd)
  | (work_infapp A B e cs) => (ftvar_in_typ A) \u (ftvar_in_typ B) \u (ftvar_in_exp e) \u (ftvar_in_conts cs)
  | (work_inftapp A1 A2 cs) => (ftvar_in_typ A1) \u (ftvar_in_typ A2) \u (ftvar_in_conts cs)
  | (work_sub A1 A2) => (ftvar_in_typ A1) \u (ftvar_in_typ A2)
  | (work_inftappunion A1 A2 B cs) => (ftvar_in_typ A1) \u (ftvar_in_typ A2) \u (ftvar_in_typ B) \u (ftvar_in_conts cs)
  | (work_unioninftapp A1 A2 cs) => (ftvar_in_typ A1) \u (ftvar_in_typ A2) \u (ftvar_in_conts cs)
  | (work_unioninfabs A1 B1 A2 B2 cd) => (ftvar_in_typ A1) \u (ftvar_in_typ B1) \u (ftvar_in_typ A2) \u (ftvar_in_typ B2) \u (ftvar_in_contd cd)
  | (work_applys cs A) => (ftvar_in_conts cs) \u (ftvar_in_typ A)
  | (work_applyd cd A B) => (ftvar_in_contd cd) \u (ftvar_in_typ A) \u (ftvar_in_typ B)
end.

Definition fvar_in_work (w5:work) : vars :=
  match w5 with
  | (work_infer e cs) => (fvar_in_exp e) \u (fvar_in_conts cs)
  | (work_check e A) => (fvar_in_exp e)
  | (work_infabs A cd) => (fvar_in_contd cd)
  | (work_infabsunion A1 B1 A2 cd) => (fvar_in_contd cd)
  | (work_infapp A B e cs) => (fvar_in_exp e) \u (fvar_in_conts cs)
  | (work_inftapp A1 A2 cs) => (fvar_in_conts cs)
  | (work_sub A1 A2) => {}
  | (work_inftappunion A1 A2 B cs) => (fvar_in_conts cs)
  | (work_unioninftapp A1 A2 cs) => (fvar_in_conts cs)
  | (work_unioninfabs A1 B1 A2 B2 cd) => (fvar_in_contd cd)
  | (work_applys cs A) => (fvar_in_conts cs)
  | (work_applyd cd A B) => (fvar_in_contd cd)
end.

Definition ftvar_in_abind (ab5:abind) : vars :=
  match ab5 with
  | abind_tvar_empty => {}
  | abind_stvar_empty => {}
  | abind_etvar_empty => {}
  | (abind_var_typ A) => (ftvar_in_typ A)
end.

Fixpoint ftvar_in_dworklist (Ω5:dworklist) : vars :=
  match Ω5 with
  | dworklist_empty => {}
  | (dworklist_cons_var Ω X db) => (ftvar_in_dworklist Ω) \u (ftvar_in_dbind db)
  | (dworklist_cons_work Ω w) => (ftvar_in_dworklist Ω) \u (ftvar_in_work w)
end.

Fixpoint fvar_in_dworklist (Ω5:dworklist) : vars :=
  match Ω5 with
  | dworklist_empty => {}
  | (dworklist_cons_var Ω X db) => (fvar_in_dworklist Ω)
  | (dworklist_cons_work Ω w) => (fvar_in_dworklist Ω) \u (fvar_in_work w)
end.

Fixpoint ftvar_in_aworklist (Γ_5:aworklist) : vars :=
  match Γ_5 with
  | aworklist_empty => {}
  | (aworklist_cons_var Γ X ab) => (ftvar_in_aworklist Γ) \u (ftvar_in_abind ab)
  | (aworklist_cons_work Γ w) => (ftvar_in_aworklist Γ) \u (ftvar_in_work w)
end.

Fixpoint fvar_in_aworklist (Γ_5:aworklist) : vars :=
  match Γ_5 with
  | aworklist_empty => {}
  | (aworklist_cons_var Γ X ab) => (fvar_in_aworklist Γ)
  | (aworklist_cons_work Γ w) => (fvar_in_aworklist Γ) \u (fvar_in_work w)
end.

Fixpoint subst_typ_in_typ (A_5:typ) (X5:typvar) (A__6:typ) {struct A__6} : typ :=
  match A__6 with
  | typ_unit => typ_unit
  | typ_top => typ_top
  | typ_bot => typ_bot
  | (typ_var_b nat) => typ_var_b nat
  | (typ_var_f X) => (if eq_var X X5 then A_5 else (typ_var_f X))
  | (typ_arrow A1 A2) => typ_arrow (subst_typ_in_typ A_5 X5 A1) (subst_typ_in_typ A_5 X5 A2)
  | (typ_all A) => typ_all (subst_typ_in_typ A_5 X5 A)
  | (typ_union A1 A2) => typ_union (subst_typ_in_typ A_5 X5 A1) (subst_typ_in_typ A_5 X5 A2)
  | (typ_intersection A1 A2) => typ_intersection (subst_typ_in_typ A_5 X5 A1) (subst_typ_in_typ A_5 X5 A2)
end.

Fixpoint subst_typ_in_exp (A_5:typ) (X5:typvar) (e_5:exp) {struct e_5} : exp :=
  match e_5 with
  | exp_unit => exp_unit
  | (exp_var_b nat) => exp_var_b nat
  | (exp_var_f x) => exp_var_f x
  | (exp_abs e) => exp_abs (subst_typ_in_exp A_5 X5 e)
  | (exp_app e1 e2) => exp_app (subst_typ_in_exp A_5 X5 e1) (subst_typ_in_exp A_5 X5 e2)
  | (exp_tabs e) => exp_tabs (subst_typ_in_exp A_5 X5 e)
  | (exp_tapp e A) => exp_tapp (subst_typ_in_exp A_5 X5 e) (subst_typ_in_typ A_5 X5 A)
  | (exp_anno e A) => exp_anno (subst_typ_in_exp A_5 X5 e) (subst_typ_in_typ A_5 X5 A)
end.

Fixpoint subst_exp_in_exp (e_5:exp) (x5:expvar) (e__6:exp) {struct e__6} : exp :=
  match e__6 with
  | exp_unit => exp_unit
  | (exp_var_b nat) => exp_var_b nat
  | (exp_var_f x) => (if eq_var x x5 then e_5 else (exp_var_f x))
  | (exp_abs e) => exp_abs (subst_exp_in_exp e_5 x5 e)
  | (exp_app e1 e2) => exp_app (subst_exp_in_exp e_5 x5 e1) (subst_exp_in_exp e_5 x5 e2)
  | (exp_tabs e) => exp_tabs (subst_exp_in_exp e_5 x5 e)
  | (exp_tapp e A) => exp_tapp (subst_exp_in_exp e_5 x5 e) A
  | (exp_anno e A) => exp_anno (subst_exp_in_exp e_5 x5 e) A
end.

Fixpoint subst_typ_in_contd (A5:typ) (X5:typvar) (cd5:contd) {struct cd5} : contd :=
  match cd5 with
  | (contd_infabsunion A cd) => contd_infabsunion (subst_typ_in_typ A5 X5 A) (subst_typ_in_contd A5 X5 cd)
  | (contd_infapp e cs) => contd_infapp (subst_typ_in_exp A5 X5 e) (subst_typ_in_conts A5 X5 cs)
  | (contd_unioninfabs A B cd) => contd_unioninfabs (subst_typ_in_typ A5 X5 A) (subst_typ_in_typ A5 X5 B) (subst_typ_in_contd A5 X5 cd)
end
with subst_typ_in_conts (A_5:typ) (X5:typvar) (cs5:conts) {struct cs5} : conts :=
  match cs5 with
  | (conts_infabs cd) => conts_infabs (subst_typ_in_contd A_5 X5 cd)
  | (conts_inftapp A cs) => conts_inftapp (subst_typ_in_typ A_5 X5 A) (subst_typ_in_conts A_5 X5 cs)
  | (conts_inftappunion A1 A2 cs) => conts_inftappunion (subst_typ_in_typ A_5 X5 A1) (subst_typ_in_typ A_5 X5 A2) (subst_typ_in_conts A_5 X5 cs)
  | (conts_unioninftapp A2 cs) => conts_unioninftapp (subst_typ_in_typ A_5 X5 A2) (subst_typ_in_conts A_5 X5 cs)
  | (conts_sub A) => conts_sub (subst_typ_in_typ A_5 X5 A)
end.

Fixpoint subst_exp_in_contd (e5:exp) (x5:expvar) (cd5:contd) {struct cd5} : contd :=
  match cd5 with
  | (contd_infabsunion A cd) => contd_infabsunion A (subst_exp_in_contd e5 x5 cd)
  | (contd_infapp e cs) => contd_infapp (subst_exp_in_exp e5 x5 e) (subst_exp_in_conts e5 x5 cs)
  | (contd_unioninfabs A B cd) => contd_unioninfabs A B (subst_exp_in_contd e5 x5 cd)
end
with subst_exp_in_conts (e5:exp) (x5:expvar) (cs5:conts) {struct cs5} : conts :=
  match cs5 with
  | (conts_infabs cd) => conts_infabs (subst_exp_in_contd e5 x5 cd)
  | (conts_inftapp A cs) => conts_inftapp A (subst_exp_in_conts e5 x5 cs)
  | (conts_inftappunion A1 A2 cs) => conts_inftappunion A1 A2 (subst_exp_in_conts e5 x5 cs)
  | (conts_unioninftapp A2 cs) => conts_unioninftapp A2 (subst_exp_in_conts e5 x5 cs)
  | (conts_sub A) => conts_sub A
end.

Definition subst_typ_in_work (A_5:typ) (X5:typvar) (w5:work) : work :=
  match w5 with
  | (work_infer e cs) => work_infer (subst_typ_in_exp A_5 X5 e) (subst_typ_in_conts A_5 X5 cs)
  | (work_check e A) => work_check (subst_typ_in_exp A_5 X5 e) (subst_typ_in_typ A_5 X5 A)
  | (work_infabs A cd) => work_infabs (subst_typ_in_typ A_5 X5 A) (subst_typ_in_contd A_5 X5 cd)
  | (work_infabsunion A1 B1 A2 cd) => work_infabsunion (subst_typ_in_typ A_5 X5 A1) (subst_typ_in_typ A_5 X5 B1) (subst_typ_in_typ A_5 X5 A2) (subst_typ_in_contd A_5 X5 cd)
  | (work_infapp A B e cs) => work_infapp (subst_typ_in_typ A_5 X5 A) (subst_typ_in_typ A_5 X5 B) (subst_typ_in_exp A_5 X5 e) (subst_typ_in_conts A_5 X5 cs)
  | (work_inftapp A1 A2 cs) => work_inftapp (subst_typ_in_typ A_5 X5 A1) (subst_typ_in_typ A_5 X5 A2) (subst_typ_in_conts A_5 X5 cs)
  | (work_sub A1 A2) => work_sub (subst_typ_in_typ A_5 X5 A1) (subst_typ_in_typ A_5 X5 A2)
  | (work_inftappunion A1 A2 B cs) => work_inftappunion (subst_typ_in_typ A_5 X5 A1) (subst_typ_in_typ A_5 X5 A2) (subst_typ_in_typ A_5 X5 B) (subst_typ_in_conts A_5 X5 cs)
  | (work_unioninftapp A1 A2 cs) => work_unioninftapp (subst_typ_in_typ A_5 X5 A1) (subst_typ_in_typ A_5 X5 A2) (subst_typ_in_conts A_5 X5 cs)
  | (work_unioninfabs A1 B1 A2 B2 cd) => work_unioninfabs (subst_typ_in_typ A_5 X5 A1) (subst_typ_in_typ A_5 X5 B1) (subst_typ_in_typ A_5 X5 A2) (subst_typ_in_typ A_5 X5 B2) (subst_typ_in_contd A_5 X5 cd)
  | (work_applys cs A) => work_applys (subst_typ_in_conts A_5 X5 cs) (subst_typ_in_typ A_5 X5 A)
  | (work_applyd cd A B) => work_applyd (subst_typ_in_contd A_5 X5 cd) (subst_typ_in_typ A_5 X5 A) (subst_typ_in_typ A_5 X5 B)
end.

Definition subst_typ_in_abind (A5:typ) (X5:typvar) (ab5:abind) : abind :=
  match ab5 with
  | abind_tvar_empty => abind_tvar_empty
  | abind_stvar_empty => abind_stvar_empty
  | abind_etvar_empty => abind_etvar_empty
  | (abind_var_typ A) => abind_var_typ (subst_typ_in_typ A5 X5 A)
end.

Definition subst_typ_in_dbind (A5:typ) (X5:typvar) (db5:dbind) : dbind :=
  match db5 with
  | dbind_tvar_empty => dbind_tvar_empty
  | dbind_stvar_empty => dbind_stvar_empty
  | (dbind_typ A) => dbind_typ (subst_typ_in_typ A5 X5 A)
end.

Definition subst_exp_in_work (e5:exp) (x5:expvar) (w5:work) : work :=
  match w5 with
  | (work_infer e cs) => work_infer (subst_exp_in_exp e5 x5 e) (subst_exp_in_conts e5 x5 cs)
  | (work_check e A) => work_check (subst_exp_in_exp e5 x5 e) A
  | (work_infabs A cd) => work_infabs A (subst_exp_in_contd e5 x5 cd)
  | (work_infabsunion A1 B1 A2 cd) => work_infabsunion A1 B1 A2 (subst_exp_in_contd e5 x5 cd)
  | (work_infapp A B e cs) => work_infapp A B (subst_exp_in_exp e5 x5 e) (subst_exp_in_conts e5 x5 cs)
  | (work_inftapp A1 A2 cs) => work_inftapp A1 A2 (subst_exp_in_conts e5 x5 cs)
  | (work_sub A1 A2) => work_sub A1 A2
  | (work_inftappunion A1 A2 B cs) => work_inftappunion A1 A2 B (subst_exp_in_conts e5 x5 cs)
  | (work_unioninftapp A1 A2 cs) => work_unioninftapp A1 A2 (subst_exp_in_conts e5 x5 cs)
  | (work_unioninfabs A1 B1 A2 B2 cd) => work_unioninfabs A1 B1 A2 B2 (subst_exp_in_contd e5 x5 cd)
  | (work_applys cs A) => work_applys (subst_exp_in_conts e5 x5 cs) A
  | (work_applyd cd A B) => work_applyd (subst_exp_in_contd e5 x5 cd) A B
end.

Fixpoint subst_typ_in_aworklist (A5:typ) (X5:typvar) (Γ_5:aworklist) {struct Γ_5} : aworklist :=
  match Γ_5 with
  | aworklist_empty => aworklist_empty
  | (aworklist_cons_var Γ X ab) => aworklist_cons_var (subst_typ_in_aworklist A5 X5 Γ) X (subst_typ_in_abind A5 X5 ab)
  | (aworklist_cons_work Γ w) => aworklist_cons_work (subst_typ_in_aworklist A5 X5 Γ) (subst_typ_in_work A5 X5 w)
end.

Fixpoint subst_typ_in_dworklist (A5:typ) (X5:typvar) (Ω5:dworklist) {struct Ω5} : dworklist :=
  match Ω5 with
  | dworklist_empty => dworklist_empty
  | (dworklist_cons_var Ω X db) => dworklist_cons_var (subst_typ_in_dworklist A5 X5 Ω) X (subst_typ_in_dbind A5 X5 db)
  | (dworklist_cons_work Ω w) => dworklist_cons_work (subst_typ_in_dworklist A5 X5 Ω) (subst_typ_in_work A5 X5 w)
end.

Fixpoint subst_exp_in_dworklist (e5:exp) (x5:expvar) (Ω5:dworklist) {struct Ω5} : dworklist :=
  match Ω5 with
  | dworklist_empty => dworklist_empty
  | (dworklist_cons_var Ω X db) => dworklist_cons_var (subst_exp_in_dworklist e5 x5 Ω) X db
  | (dworklist_cons_work Ω w) => dworklist_cons_work (subst_exp_in_dworklist e5 x5 Ω) (subst_exp_in_work e5 x5 w)
end.

Fixpoint subst_exp_in_aworklist (e5:exp) (x5:expvar) (Γ_5:aworklist) {struct Γ_5} : aworklist :=
  match Γ_5 with
  | aworklist_empty => aworklist_empty
  | (aworklist_cons_var Γ X ab) => aworklist_cons_var (subst_exp_in_aworklist e5 x5 Γ) X ab
  | (aworklist_cons_work Γ w) => aworklist_cons_work (subst_exp_in_aworklist e5 x5 Γ) (subst_exp_in_work e5 x5 w)
end.

Fixpoint dwl_to_denv (Ω : dworklist) : denv :=
  match Ω with
  | dworklist_empty => nil
  | dworklist_cons_work Ω' _ => dwl_to_denv Ω'
  | dworklist_cons_var Ω' x b => x ~ b ++ dwl_to_denv Ω'
  end.

Fixpoint awl_to_aenv (Γ : aworklist) : aenv :=
  match Γ with
  | aworklist_empty => nil
  | aworklist_cons_work Γ' _ => awl_to_aenv Γ'
  | aworklist_cons_var Γ' x b => x ~ b ++ awl_to_aenv Γ'
  end.

Inductive s_in : typvar -> typ -> Prop :=
 | s_in__var : forall (X:typvar),
     s_in X (typ_var_f X)
 | s_in__arrow1 : forall (X:typvar) (A1 A2:typ),
     lc_typ A2 ->
     s_in X A1 ->
     s_in X (typ_arrow A1 A2)
 | s_in__arrow2 : forall (X:typvar) (A1 A2:typ),
     lc_typ A1 ->
     s_in X A2 ->
     s_in X (typ_arrow A1 A2)
 | s_in__all : forall (L:vars) (X:typvar) (A:typ),
      ( forall Y , Y \notin  L  -> s_in X  ( open_typ_wrt_typ A (typ_var_f Y) )  )  ->
     s_in X (typ_all A)
 | s_in__union : forall (X:typvar) (A1 A2:typ),
     s_in X A1 ->
     s_in X A2 ->
     s_in X (typ_union A1 A2)
 | s_in__intersection : forall (X:typvar) (A1 A2:typ),
     s_in X A1 ->
     s_in X A2 ->
     s_in X (typ_intersection A1 A2).

Inductive neq_abs : exp -> Prop :=
 | neq_abs__unit :
     neq_abs exp_unit
 | neq_abs__var : forall (x:expvar),
     neq_abs (exp_var_f x)
 | neq_abs__app : forall (e1 e2:exp),
     lc_exp e1 ->
     lc_exp e2 ->
     neq_abs (exp_app e1 e2)
 | neq_abs__tabs : forall (e:exp),
     lc_exp (exp_tabs e) ->
     neq_abs (exp_tabs e)
 | neq_abs__tapp : forall (e:exp) (A:typ),
     lc_exp e ->
     lc_typ A ->
     neq_abs (exp_tapp e A)
 | neq_abs__anno : forall (e:exp) (A:typ),
     lc_exp e ->
     lc_typ A ->
     neq_abs (exp_anno e A).

Inductive neq_all : typ -> Prop :=
 | neq_all__unit :
     neq_all typ_unit
 | neq_all__top :
     neq_all typ_top
 | neq_all__bot :
     neq_all typ_bot
 | neq_all__var : forall (X:typvar),
     neq_all (typ_var_f X)
 | neq_all__arrow : forall (A1 A2:typ),
     lc_typ A1 ->
     lc_typ A2 ->
     neq_all (typ_arrow A1 A2)
 | neq_all__union : forall (A1 A2:typ),
     lc_typ A1 ->
     lc_typ A2 ->
     neq_all (typ_union A1 A2)
 | neq_all__intersection : forall (A1 A2:typ),
     lc_typ A1 ->
     lc_typ A2 ->
     neq_all (typ_intersection A1 A2).

Inductive neq_intersection : typ -> Prop :=
 | neq_intersection__unit :
     neq_intersection typ_unit
 | neq_intersection__top :
     neq_intersection typ_top
 | neq_intersection__bot :
     neq_intersection typ_bot
 | neq_intersection__var : forall (X:typvar),
     neq_intersection (typ_var_f X)
 | neq_intersection__arrow : forall (A1 A2:typ),
     lc_typ A1 ->
     lc_typ A2 ->
     neq_intersection (typ_arrow A1 A2)
 | neq_intersection__all : forall (A:typ),
     lc_typ (typ_all A) ->
     neq_intersection (typ_all A)
 | neq_intersection__union : forall (A1 A2:typ),
     lc_typ A1 ->
     lc_typ A2 ->
     neq_intersection (typ_union A1 A2).

Inductive neq_union : typ -> Prop :=
 | neq_union__unit :
     neq_union typ_unit
 | neq_union__top :
     neq_union typ_top
 | neq_union__bot :
     neq_union typ_bot
 | neq_union__var : forall (X:typvar),
     neq_union (typ_var_f X)
 | neq_union__arrow : forall (A1 A2:typ),
     lc_typ A1 ->
     lc_typ A2 ->
     neq_union (typ_arrow A1 A2)
 | neq_union__all : forall (A:typ),
     lc_typ (typ_all A) ->
     neq_union (typ_all A)
 | neq_union__intersection : forall (A1 A2:typ),
     lc_typ A1 ->
     lc_typ A2 ->
     neq_union (typ_intersection A1 A2).

Inductive neq_bot : typ -> Prop :=
 | neq_bot__unit :
     neq_bot typ_unit
 | neq_bot__top :
     neq_bot typ_top
 | neq_bot__var : forall (X:typvar),
     neq_bot (typ_var_f X)
 | neq_bot__arrow : forall (A1 A2:typ),
     lc_typ A1 ->
     lc_typ A2 ->
     neq_bot (typ_arrow A1 A2)
 | neq_bot__union : forall (A1 A2:typ),
     lc_typ A1 ->
     lc_typ A2 ->
     neq_bot (typ_union A1 A2)
 | neq_bot__intersection : forall (A1 A2:typ),
     lc_typ A1 ->
     lc_typ A2 ->
     neq_bot (typ_intersection A1 A2)
 | neq_bot__all : forall (A:typ),
     lc_typ (typ_all A) ->
     neq_bot (typ_all A).

Inductive d_wneq_all : denv -> typ -> Prop :=
 | d_wneq_all__unit : forall (Ψ:denv),
     d_wneq_all Ψ typ_unit
 | d_wneq_all__top : forall (Ψ:denv),
     d_wneq_all Ψ typ_top
 | d_wneq_all__tvar : forall (Ψ:denv) (X:typvar),
      binds ( X )  ( dbind_tvar_empty ) ( Ψ )  ->
     d_wneq_all Ψ (typ_var_f X)
 | d_wneq_all__arrow : forall (Ψ:denv) (A1 A2:typ),
     lc_typ A1 ->
     lc_typ A2 ->
     d_wneq_all Ψ (typ_arrow A1 A2)
 | d_wneq_all__union1 : forall (Ψ:denv) (A1 A2:typ),
     lc_typ A2 ->
     d_wneq_all Ψ A1 ->
     d_wneq_all Ψ (typ_union A1 A2)
 | d_wneq_all__union2 : forall (Ψ:denv) (A1 A2:typ),
     lc_typ A1 ->
     d_wneq_all Ψ A2 ->
     d_wneq_all Ψ (typ_union A1 A2)
 | d_wneq_all__intersection2 : forall (Ψ:denv) (A1 A2:typ),
     d_wneq_all Ψ A1 ->
     d_wneq_all Ψ A2 ->
     d_wneq_all Ψ (typ_intersection A1 A2).

Inductive d_wf_typ : denv -> typ -> Prop :=
 | d_wf_typ__unit : forall (Ψ:denv),
     d_wf_typ Ψ typ_unit
 | d_wf_typ__bot : forall (Ψ:denv),
     d_wf_typ Ψ typ_bot
 | d_wf_typ__top : forall (Ψ:denv),
     d_wf_typ Ψ typ_top
 | d_wf_typ__tvar : forall (Ψ:denv) (X:typvar),
      binds ( X )  ( dbind_tvar_empty ) ( Ψ )  ->
     d_wf_typ Ψ (typ_var_f X)
 | d_wf_typ__stvar : forall (Ψ:denv) (X:typvar),
      binds ( X )  ( dbind_stvar_empty ) ( Ψ )  ->
     d_wf_typ Ψ (typ_var_f X)
 | d_wf_typ__arrow : forall (Ψ:denv) (A1 A2:typ),
     d_wf_typ Ψ A1 ->
     d_wf_typ Ψ A2 ->
     d_wf_typ Ψ (typ_arrow A1 A2)
 | d_wf_typ__all : forall (L:vars) (Ψ:denv) (A:typ),
      ( forall X , X \notin  L  -> s_in X  ( open_typ_wrt_typ A (typ_var_f X) )  )  ->
      ( forall X , X \notin  L  -> d_wf_typ  ( X ~ dbind_tvar_empty  ++  Ψ )   ( open_typ_wrt_typ A (typ_var_f X) )  )  ->
     d_wf_typ Ψ (typ_all A)
 | d_wf_typ__union : forall (Ψ:denv) (A1 A2:typ),
     d_wf_typ Ψ A1 ->
     d_wf_typ Ψ A2 ->
     d_wf_typ Ψ (typ_union A1 A2)
 | d_wf_typ__intersection : forall (Ψ:denv) (A1 A2:typ),
     d_wf_typ Ψ A1 ->
     d_wf_typ Ψ A2 ->
     d_wf_typ Ψ (typ_intersection A1 A2).

Inductive d_wf_exp : denv -> exp -> Prop :=
 | d_wf_exp__unit : forall (Ψ:denv),
     d_wf_exp Ψ exp_unit
 | d_wf_exp__var : forall (Ψ:denv) (x:expvar) (A:typ),
      binds ( x )  ( (dbind_typ A) ) ( Ψ )  ->
     d_wf_exp Ψ (exp_var_f x)
 | d_wf_exp__abs : forall (L:vars) (Ψ:denv) (e:exp) (T:typ),
     d_wf_typ Ψ T ->
      ( forall x , x \notin  L  -> d_wf_exp  ( x ~ (dbind_typ T)  ++  Ψ )   ( open_exp_wrt_exp e (exp_var_f x) )  )  ->
     d_wf_exp Ψ (exp_abs e)
 | d_wf_exp__app : forall (Ψ:denv) (e1 e2:exp),
     d_wf_exp Ψ e1 ->
     d_wf_exp Ψ e2 ->
     d_wf_exp Ψ (exp_app e1 e2)
 | d_wf_exp__tabs : forall (L:vars) (Ψ:denv) (e:exp) (A:typ),
      ( forall X , X \notin  L  -> s_in X  ( open_typ_wrt_typ A (typ_var_f X) )  )  ->
      ( forall X , X \notin  L  -> d_wf_exp  ( X ~ dbind_tvar_empty  ++  Ψ )  (exp_anno  ( open_exp_wrt_typ e (typ_var_f X) )   ( open_typ_wrt_typ A (typ_var_f X) ) ) )  ->
     d_wf_exp Ψ (exp_tabs  ( (exp_anno e A) ) )
 | d_wf_exp__tapp : forall (Ψ:denv) (e:exp) (A:typ),
     d_wf_typ Ψ A ->
     d_wf_exp Ψ e ->
     d_wf_exp Ψ (exp_tapp e A)
 | d_wf_exp__anno : forall (Ψ:denv) (e:exp) (A:typ),
     d_wf_typ Ψ A ->
     d_wf_exp Ψ e ->
     d_wf_exp Ψ (exp_anno e A).

Inductive d_wf_tenv : denv -> Prop :=
 | d_wf_tenv__empty :
     d_wf_tenv  nil
 | d_wf_tenv__tvar : forall (Ψ:denv) (X:typvar),
     d_wf_tenv Ψ ->
      ( X   `notin` dom ( Ψ ))  ->
     d_wf_tenv  ( X ~ dbind_tvar_empty  ++  Ψ )
 | d_wf_tenv__typ : forall (Ψ:denv) (x:expvar) (A:typ),
     d_wf_tenv Ψ ->
     d_wf_typ Ψ A ->
      ( x   `notin` dom ( Ψ ))  ->
     d_wf_tenv  ( x ~ (dbind_typ A)  ++  Ψ ) .

Inductive d_wf_env : denv -> Prop :=
 | d_wf_env__empty : forall (Ψ:denv),
     d_wf_tenv Ψ ->
     d_wf_env Ψ
 | d_wf_env__stvar : forall (Ψ:denv) (X:typvar),
     d_wf_env Ψ ->
      ( X   `notin` dom ( Ψ ))  ->
     d_wf_env  ( X ~ dbind_stvar_empty  ++  Ψ ) .

Inductive d_mono_typ : denv -> typ -> Prop :=
 | d_mono_typ__unit : forall (Ψ:denv),
     d_mono_typ Ψ typ_unit
 | d_mono_typ__tvar : forall (Ψ:denv) (X:typvar),
      binds ( X )  ( dbind_tvar_empty ) ( Ψ )  ->
     d_mono_typ Ψ (typ_var_f X)
 | d_mono_typ__arrow : forall (Ψ:denv) (A1 A2:typ),
     d_mono_typ Ψ A1 ->
     d_mono_typ Ψ A2 ->
     d_mono_typ Ψ (typ_arrow A1 A2).

Inductive d_wf_conts : denv -> conts -> Prop :=
 | d_wf_conts__infabs : forall (Ψ:denv) (cd:contd),
     d_wf_contd Ψ cd ->
     d_wf_conts Ψ (conts_infabs cd)
 | d_wf_conts__inftapp : forall (Ψ:denv) (A:typ) (cs:conts),
     d_wf_typ Ψ A ->
     d_wf_conts Ψ cs ->
     d_wf_conts Ψ (conts_inftapp A cs)
 | d_wf_conts__inftappunion : forall (Ψ:denv) (A1 A2:typ) (cs:conts),
     d_wf_typ Ψ A1 ->
     d_wf_typ Ψ A2 ->
     d_wf_conts Ψ cs ->
     d_wf_conts Ψ (conts_inftappunion A1 A2 cs)
 | d_wf_conts__unioninftapp : forall (Ψ:denv) (A:typ) (cs:conts),
     d_wf_typ Ψ A ->
     d_wf_conts Ψ cs ->
     d_wf_conts Ψ (conts_unioninftapp A cs)
 | d_wf_conts__sub : forall (Ψ:denv) (A:typ),
     d_wf_typ Ψ A ->
     d_wf_conts Ψ (conts_sub A)
with d_wf_contd : denv -> contd -> Prop :=
 | d_wf_contd__infabsunion : forall (Ψ:denv) (A:typ) (cd:contd),
     d_wf_typ Ψ A ->
     d_wf_contd Ψ cd ->
     d_wf_contd Ψ (contd_infabsunion A cd)
 | d_wf_contd__infapp : forall (Ψ:denv) (e:exp) (cs:conts),
     d_wf_exp Ψ e ->
     d_wf_conts Ψ cs ->
     d_wf_contd Ψ (contd_infapp e cs)
 | d_wf_contd__unioninfabs : forall (Ψ:denv) (A B:typ) (cd:contd),
     d_wf_typ Ψ (typ_arrow A B) ->
     d_wf_contd Ψ cd ->
     d_wf_contd Ψ (contd_unioninfabs A B cd).

Inductive d_wf_work : denv -> work -> Prop :=
 | d_wf_work__infer : forall (Ψ:denv) (e:exp) (cs:conts),
     d_wf_exp Ψ e ->
     d_wf_conts Ψ cs ->
     d_wf_work Ψ (work_infer e cs)
 | d_wf_work__check : forall (Ψ:denv) (e:exp) (A:typ),
     d_wf_exp Ψ e ->
     d_wf_typ Ψ A ->
     d_wf_work Ψ (work_check e A)
 | d_wf_work__infabs : forall (Ψ:denv) (A:typ) (cd:contd),
     d_wf_typ Ψ A ->
     d_wf_contd Ψ cd ->
     d_wf_work Ψ (work_infabs A cd)
 | d_wf_work__infabsunion : forall (Ψ:denv) (A1 B1 A2:typ) (cd:contd),
     d_wf_typ Ψ (typ_arrow A1 B1) ->
     d_wf_typ Ψ A2 ->
     d_wf_contd Ψ cd ->
     d_wf_work Ψ (work_infabsunion A1 B1 A2 cd)
 | d_wf_work__infapp : forall (Ψ:denv) (A B:typ) (e:exp) (cs:conts),
     d_wf_typ Ψ (typ_arrow A B) ->
     d_wf_exp Ψ e ->
     d_wf_conts Ψ cs ->
     d_wf_work Ψ (work_infapp A B e cs)
 | d_wf_work__inftapp : forall (Ψ:denv) (A1 A2:typ) (cs:conts),
     d_wf_typ Ψ A1 ->
     d_wf_typ Ψ A2 ->
     d_wf_conts Ψ cs ->
     d_wf_work Ψ (work_inftapp A1 A2 cs)
 | d_wf_work__inftappunion : forall (Ψ:denv) (A1 A2 B:typ) (cs:conts),
     d_wf_typ Ψ A1 ->
     d_wf_typ Ψ A2 ->
     d_wf_typ Ψ B ->
     d_wf_conts Ψ cs ->
     d_wf_work Ψ (work_inftappunion A1 A2 B cs)
 | d_wf_work__unioninftapp : forall (Ψ:denv) (A1 A2:typ) (cs:conts),
     d_wf_typ Ψ A1 ->
     d_wf_typ Ψ A2 ->
     d_wf_conts Ψ cs ->
     d_wf_work Ψ (work_unioninftapp A1 A2 cs)
 | d_wf_work__unioninfabs : forall (Ψ:denv) (A1 B1 A2 B2:typ) (cd:contd),
     d_wf_typ Ψ (typ_arrow A1 B1) ->
     d_wf_typ Ψ (typ_arrow A2 B2) ->
     d_wf_contd Ψ cd ->
     d_wf_work Ψ (work_unioninfabs A1 B1 A2 B2 cd)
 | d_wf_work__sub : forall (Ψ:denv) (A B:typ),
     d_wf_typ Ψ A ->
     d_wf_typ Ψ B ->
     d_wf_work Ψ (work_sub A B)
 | d_wf_work__apply : forall (Ψ:denv) (cs:conts) (A:typ),
     d_wf_typ Ψ A ->
     d_wf_conts Ψ cs ->
     d_wf_work Ψ (work_applys cs A)
 | d_wf_work__apply2 : forall (Ψ:denv) (cd:contd) (A B:typ),
     d_wf_typ Ψ A ->
     d_wf_typ Ψ B ->
     d_wf_contd Ψ cd ->
     d_wf_work Ψ (work_applyd cd A B).

Inductive d_wf_twl : dworklist -> Prop :=
 | d_wf_twl__empty :
     d_wf_twl dworklist_empty
 | d_wf_twl__consvar : forall (Ω:dworklist) (x:expvar) (A:typ),
      ( x   `notin` dom (  ( dwl_to_denv  Ω  )  ))  ->
     d_wf_typ  ( dwl_to_denv  Ω  )  A ->
     d_wf_twl Ω ->
     d_wf_twl  ( dworklist_cons_var  Ω   x   (dbind_typ A)  )
 | d_wf_twl__constvar : forall (Ω:dworklist) (X:typvar),
      ( X   `notin` dom (  ( dwl_to_denv  Ω  )  ))  ->
     d_wf_twl Ω ->
     d_wf_twl (dworklist_cons_var Ω X dbind_tvar_empty)
 | d_wf_twl__conswork : forall (Ω:dworklist) (w:work),
     d_wf_work  ( dwl_to_denv  Ω  )  w ->
      ((exists A B,  w  = work_sub A B) -> False)  ->
     d_wf_twl Ω ->
     d_wf_twl (dworklist_cons_work Ω w).

Inductive d_wf_wl : dworklist -> Prop :=
 | d_wf_wl__twl : forall (Ω:dworklist),
     d_wf_twl Ω ->
     d_wf_wl Ω
 | d_wf_wl__consstvar : forall (Ω:dworklist) (X:typvar),
      ( X   `notin` dom (  ( dwl_to_denv  Ω  )  ))  ->
     d_wf_wl Ω ->
     d_wf_wl (dworklist_cons_var Ω X dbind_stvar_empty)
 | d_wf_wl__conswork_sub : forall (Ω:dworklist) (A B:typ),
     d_wf_typ  ( dwl_to_denv  Ω  )  A ->
     d_wf_typ  ( dwl_to_denv  Ω  )  B ->
     d_wf_wl Ω ->
     d_wf_wl (dworklist_cons_work Ω (work_sub A B)).

Inductive a_wneq_all : aenv -> typ -> Prop :=
 | a_wneq_all__unit : forall (Σ:aenv),
     a_wneq_all Σ typ_unit
 | a_wneq_all__top : forall (Σ:aenv),
     a_wneq_all Σ typ_top
 | a_wneq_all__tvar : forall (Σ:aenv) (X:typvar),
      binds ( X )  ( abind_tvar_empty ) ( Σ )  ->
     a_wneq_all Σ (typ_var_f X)
 | a_wneq_all__etvar : forall (Σ:aenv) (X:typvar),
      binds ( X )  ( abind_etvar_empty ) ( Σ )  ->
     a_wneq_all Σ (typ_var_f X)
 | a_wneq_all__arrow : forall (Σ:aenv) (A1 A2:typ),
     lc_typ A1 ->
     lc_typ A2 ->
     a_wneq_all Σ (typ_arrow A1 A2)
 | a_wneq_all__union1 : forall (Σ:aenv) (A1 A2:typ),
     lc_typ A2 ->
     a_wneq_all Σ A1 ->
     a_wneq_all Σ (typ_union A1 A2)
 | a_wneq_all__union2 : forall (Σ:aenv) (A1 A2:typ),
     lc_typ A1 ->
     a_wneq_all Σ A2 ->
     a_wneq_all Σ (typ_union A1 A2)
 | a_wneq_all__intersection2 : forall (Σ:aenv) (A1 A2:typ),
     a_wneq_all Σ A1 ->
     a_wneq_all Σ A2 ->
     a_wneq_all Σ (typ_intersection A1 A2).

Inductive a_wf_typ : aenv -> typ -> Prop :=
 | a_wf_typ__unit : forall (Σ:aenv),
     a_wf_typ Σ typ_unit
 | a_wf_typ__bot : forall (Σ:aenv),
     a_wf_typ Σ typ_bot
 | a_wf_typ__top : forall (Σ:aenv),
     a_wf_typ Σ typ_top
 | a_wf_typ__tvar : forall (Σ:aenv) (X:typvar),
      binds ( X )  ( abind_tvar_empty ) ( Σ )  ->
     a_wf_typ Σ (typ_var_f X)
 | a_wf_typ__stvar : forall (Σ:aenv) (X:typvar),
      binds ( X )  ( abind_stvar_empty ) ( Σ )  ->
     a_wf_typ Σ (typ_var_f X)
 | a_wf_typ__etvar : forall (Σ:aenv) (X:typvar),
      binds ( X )  ( abind_etvar_empty ) ( Σ )  ->
     a_wf_typ Σ (typ_var_f X)
 | a_wf_typ__arrow : forall (Σ:aenv) (A1 A2:typ),
     a_wf_typ Σ A1 ->
     a_wf_typ Σ A2 ->
     a_wf_typ Σ (typ_arrow A1 A2)
 | a_wf_typ__all : forall (L:vars) (Σ:aenv) (A:typ),
      ( forall X , X \notin  L  -> s_in X  ( open_typ_wrt_typ A (typ_var_f X) )  )  ->
      ( forall X , X \notin  L  -> a_wf_typ  ( X ~ abind_tvar_empty  ++  Σ )   ( open_typ_wrt_typ A (typ_var_f X) )  )  ->
     a_wf_typ Σ (typ_all A)
 | a_wf_typ__union : forall (Σ:aenv) (A1 A2:typ),
     a_wf_typ Σ A1 ->
     a_wf_typ Σ A2 ->
     a_wf_typ Σ (typ_union A1 A2)
 | a_wf_typ__intersection : forall (Σ:aenv) (A1 A2:typ),
     a_wf_typ Σ A1 ->
     a_wf_typ Σ A2 ->
     a_wf_typ Σ (typ_intersection A1 A2).

Inductive a_mono_typ : aenv -> typ -> Prop :=
 | a_mono_typ__unit : forall (Σ:aenv),
     a_mono_typ Σ typ_unit
 | a_mono_typ__tvar : forall (Σ:aenv) (X:typvar),
      binds ( X )  ( abind_tvar_empty ) ( Σ )  ->
     a_mono_typ Σ (typ_var_f X)
 | a_mono_typ__etvar : forall (Σ:aenv) (X:typvar),
      binds ( X )  ( abind_etvar_empty ) ( Σ )  ->
     a_mono_typ Σ (typ_var_f X)
 | a_mono_typ__arrow : forall (Σ:aenv) (A1 A2:typ),
     a_mono_typ Σ A1 ->
     a_mono_typ Σ A2 ->
     a_mono_typ Σ (typ_arrow A1 A2).

Inductive a_wf_exp : aenv -> exp -> Prop :=
 | a_wf_exp__unit : forall (Σ:aenv),
     a_wf_exp Σ exp_unit
 | a_wf_exp__var : forall (Σ:aenv) (x:expvar) (A:typ),
      binds ( x )  ( (abind_var_typ A) ) ( Σ )  ->
     a_wf_exp Σ (exp_var_f x)
 | a_wf_exp__abs : forall (L:vars) (Σ:aenv) (e:exp) (T:typ),
     a_wf_typ Σ T ->
      ( forall x , x \notin  L  -> a_wf_exp  ( x ~ (abind_var_typ T)  ++  Σ )   ( open_exp_wrt_exp e (exp_var_f x) )  )  ->
     a_wf_exp Σ (exp_abs e)
 | a_wf_exp__app : forall (Σ:aenv) (e1 e2:exp),
     a_wf_exp Σ e1 ->
     a_wf_exp Σ e2 ->
     a_wf_exp Σ (exp_app e1 e2)
 | a_wf_exp__tabs : forall (L:vars) (Σ:aenv) (e:exp) (A:typ),
      ( forall X , X \notin  L  -> s_in X  ( open_typ_wrt_typ A (typ_var_f X) )  )  ->
      ( forall X , X \notin  L  -> a_wf_exp  ( X ~ abind_tvar_empty  ++  Σ )  (exp_anno  ( open_exp_wrt_typ e (typ_var_f X) )   ( open_typ_wrt_typ A (typ_var_f X) ) ) )  ->
     a_wf_exp Σ (exp_tabs  ( (exp_anno e A) ) )
 | a_wf_exp__tapp : forall (Σ:aenv) (e:exp) (A:typ),
     a_wf_typ Σ A ->
     a_wf_exp Σ e ->
     a_wf_exp Σ (exp_tapp e A)
 | a_wf_exp__anno : forall (Σ:aenv) (e:exp) (A:typ),
     a_wf_typ Σ A ->
     a_wf_exp Σ e ->
     a_wf_exp Σ (exp_anno e A).

Inductive a_wf_conts : aenv -> conts -> Prop :=
 | a_wf_conts__infabs : forall (Σ:aenv) (cd:contd),
     a_wf_contd Σ cd ->
     a_wf_conts Σ (conts_infabs cd)
 | a_wf_conts__inftapp : forall (Σ:aenv) (A:typ) (cs:conts),
     a_wf_typ Σ A ->
     a_wf_conts Σ cs ->
     a_wf_conts Σ (conts_inftapp A cs)
 | a_wf_conts__inftappunion : forall (Σ:aenv) (A1 A2:typ) (cs:conts),
     a_wf_typ Σ A1 ->
     a_wf_typ Σ A2 ->
     a_wf_conts Σ cs ->
     a_wf_conts Σ (conts_inftappunion A1 A2 cs)
 | a_wf_conts__unioninftapp : forall (Σ:aenv) (A:typ) (cs:conts),
     a_wf_typ Σ A ->
     a_wf_conts Σ cs ->
     a_wf_conts Σ (conts_unioninftapp A cs)
 | a_wf_conts__sub : forall (Σ:aenv) (A:typ),
     a_wf_typ Σ A ->
     a_wf_conts Σ (conts_sub A)
with a_wf_contd : aenv -> contd -> Prop :=
 | a_wf_contd__infabsunion : forall (Σ:aenv) (A:typ) (cd:contd),
     a_wf_typ Σ A ->
     a_wf_contd Σ cd ->
     a_wf_contd Σ (contd_infabsunion A cd)
 | a_wf_contd__infapp : forall (Σ:aenv) (e:exp) (cs:conts),
     a_wf_exp Σ e ->
     a_wf_conts Σ cs ->
     a_wf_contd Σ (contd_infapp e cs)
 | a_wf_contd__unioninfabs : forall (Σ:aenv) (A B:typ) (cd:contd),
     a_wf_typ Σ (typ_arrow A B) ->
     a_wf_contd Σ cd ->
     a_wf_contd Σ (contd_unioninfabs A B cd).

Inductive a_wf_work : aenv -> work -> Prop :=
 | a_wf_work__infer : forall (Σ:aenv) (e:exp) (cs:conts),
     a_wf_exp Σ e ->
     a_wf_conts Σ cs ->
     a_wf_work Σ (work_infer e cs)
 | a_wf_work__check : forall (Σ:aenv) (e:exp) (A:typ),
     a_wf_exp Σ e ->
     a_wf_typ Σ A ->
     a_wf_work Σ (work_check e A)
 | a_wf_work__infabs : forall (Σ:aenv) (A:typ) (cd:contd),
     a_wf_typ Σ A ->
     a_wf_contd Σ cd ->
     a_wf_work Σ (work_infabs A cd)
 | a_wf_work__infabsunion : forall (Σ:aenv) (A1 B1 A2:typ) (cd:contd),
     a_wf_typ Σ (typ_arrow A1 B1) ->
     a_wf_typ Σ A2 ->
     a_wf_contd Σ cd ->
     a_wf_work Σ (work_infabsunion A1 B1 A2 cd)
 | a_wf_work__infapp : forall (Σ:aenv) (A B:typ) (e:exp) (cs:conts),
     a_wf_typ Σ (typ_arrow A B) ->
     a_wf_exp Σ e ->
     a_wf_conts Σ cs ->
     a_wf_work Σ (work_infapp A B e cs)
 | a_wf_work__inftapp : forall (Σ:aenv) (A1 A2:typ) (cs:conts),
     a_wf_typ Σ A1 ->
     a_wf_typ Σ A2 ->
     a_wf_conts Σ cs ->
     a_wf_work Σ (work_inftapp A1 A2 cs)
 | a_wf_work__inftappunion : forall (Σ:aenv) (A1 A2 B:typ) (cs:conts),
     a_wf_typ Σ A1 ->
     a_wf_typ Σ A2 ->
     a_wf_typ Σ B ->
     a_wf_conts Σ cs ->
     a_wf_work Σ (work_inftappunion A1 A2 B cs)
 | a_wf_work__unioninftapp : forall (Σ:aenv) (A1 A2:typ) (cs:conts),
     a_wf_typ Σ A1 ->
     a_wf_typ Σ A2 ->
     a_wf_conts Σ cs ->
     a_wf_work Σ (work_unioninftapp A1 A2 cs)
 | a_wf_work__unioninfabs : forall (Σ:aenv) (A1 B1 A2 B2:typ) (cd:contd),
     a_wf_typ Σ (typ_arrow A1 B1) ->
     a_wf_typ Σ (typ_arrow A2 B2) ->
     a_wf_contd Σ cd ->
     a_wf_work Σ (work_unioninfabs A1 B1 A2 B2 cd)
 | a_wf_work__sub : forall (Σ:aenv) (A B:typ),
     a_wf_typ Σ A ->
     a_wf_typ Σ B ->
     a_wf_work Σ (work_sub A B)
 | a_wf_work__apply : forall (Σ:aenv) (cs:conts) (A:typ),
     a_wf_typ Σ A ->
     a_wf_conts Σ cs ->
     a_wf_work Σ (work_applys cs A)
 | a_wf_work__apply2 : forall (Σ:aenv) (cd:contd) (A B:typ),
     a_wf_typ Σ A ->
     a_wf_typ Σ B ->
     a_wf_contd Σ cd ->
     a_wf_work Σ (work_applyd cd A B).

Inductive a_wf_wwl : aworklist -> Prop :=
 | a_wf_wwl__empty :
     a_wf_wwl aworklist_empty
 | a_wf_wwl__consvar : forall (Γ:aworklist) (x:expvar) (A:typ),
      ( x   `notin` dom (  ( awl_to_aenv  Γ  )  ))  ->
     a_wf_typ  ( awl_to_aenv  Γ  )  A ->
     a_wf_wwl Γ ->
     a_wf_wwl  ( aworklist_cons_var  Γ   x   (abind_var_typ A)  )
 | a_wf_wwl__constvar : forall (Γ:aworklist) (X:typvar),
      ( X   `notin` dom (  ( awl_to_aenv  Γ  )  ))  ->
     a_wf_wwl Γ ->
     a_wf_wwl (aworklist_cons_var Γ X abind_tvar_empty)
 | a_wf_wwl__consstvar : forall (Γ:aworklist) (X:typvar),
      ( X   `notin` dom (  ( awl_to_aenv  Γ  )  ))  ->
     a_wf_wwl Γ ->
     a_wf_wwl (aworklist_cons_var Γ X abind_stvar_empty)
 | a_wf_wwl__consetvar : forall (Γ:aworklist) (X:typvar),
      ( X   `notin` dom (  ( awl_to_aenv  Γ  )  ))  ->
     a_wf_wwl Γ ->
     a_wf_wwl (aworklist_cons_var Γ X abind_etvar_empty)
 | a_wf_wwl__conswork : forall (Γ:aworklist) (w:work),
     a_wf_work  ( awl_to_aenv  Γ  )  w ->
     a_wf_wwl Γ ->
     a_wf_wwl (aworklist_cons_work Γ w).

Inductive a_wf_twl : aworklist -> Prop :=
 | a_wf_twl__empty :
     a_wf_twl aworklist_empty
 | a_wf_twl__consvar : forall (Γ:aworklist) (x:expvar) (A:typ),
      ( x   `notin` dom (  ( awl_to_aenv  Γ  )  ))  ->
     a_wf_typ  ( awl_to_aenv  Γ  )  A ->
     a_wf_twl Γ ->
     a_wf_twl  ( aworklist_cons_var  Γ   x   (abind_var_typ A)  )
 | a_wf_twl__constvar : forall (Γ:aworklist) (X:typvar),
      ( X   `notin` dom (  ( awl_to_aenv  Γ  )  ))  ->
     a_wf_twl Γ ->
     a_wf_twl (aworklist_cons_var Γ X abind_tvar_empty)
 | a_wf_twl__consetvar : forall (Γ:aworklist) (X:typvar),
      ( X   `notin` dom (  ( awl_to_aenv  Γ  )  ))  ->
     a_wf_twl Γ ->
     a_wf_twl (aworklist_cons_var Γ X abind_etvar_empty)
 | a_wf_twl__conswork : forall (Γ:aworklist) (w:work),
     a_wf_work  ( awl_to_aenv  Γ  )  w ->
      ((exists A B,  w  = work_sub A B) -> False)  ->
     a_wf_twl Γ ->
     a_wf_twl (aworklist_cons_work Γ w).

Inductive a_wf_wl : aworklist -> Prop :=
 | a_wf_wl__twl : forall (Γ:aworklist),
     a_wf_twl Γ ->
     a_wf_wl Γ
 | a_wf_wl__consstvar : forall (Γ:aworklist) (X:typvar),
      ( X   `notin` dom (  ( awl_to_aenv  Γ  )  ))  ->
     a_wf_wl Γ ->
     a_wf_wl (aworklist_cons_var Γ X abind_stvar_empty)
 | a_wf_wl__consetvar : forall (Γ:aworklist) (X:typvar),
      ( X   `notin` dom (  ( awl_to_aenv  Γ  )  ))  ->
     a_wf_wl Γ ->
     a_wf_wl (aworklist_cons_var Γ X abind_etvar_empty)
 | a_wf_wl__conswork_sub : forall (Γ:aworklist) (A B:typ),
     a_wf_typ  ( awl_to_aenv  Γ  )  A ->
     a_wf_typ  ( awl_to_aenv  Γ  )  B ->
     a_wf_wl Γ ->
     a_wf_wl (aworklist_cons_work Γ (work_sub A B)).

Inductive a_wf_env : aenv -> Prop :=
 | a_wf_env__empty :
     a_wf_env  nil
 | a_wf_env__tvar : forall (Σ:aenv) (X:typvar),
     a_wf_env Σ ->
      ( X   `notin` dom ( Σ ))  ->
     a_wf_env  ( X ~ abind_tvar_empty  ++  Σ )
 | a_wf_env__stvar : forall (Σ:aenv) (X:typvar),
     a_wf_env Σ ->
      ( X   `notin` dom ( Σ ))  ->
     a_wf_env  ( X ~ abind_stvar_empty  ++  Σ )
 | a_wf_env__etvar : forall (Σ:aenv) (X:typvar),
     a_wf_env Σ ->
      ( X   `notin` dom ( Σ ))  ->
     a_wf_env  ( X ~ abind_etvar_empty  ++  Σ )
 | a_wf_env__typ : forall (Σ:aenv) (x:expvar) (A:typ),
     a_wf_env Σ ->
     a_wf_typ Σ A ->
      ( x   `notin` dom ( Σ ))  ->
     a_wf_env  ( x ~ (abind_var_typ A)  ++  Σ ) .
