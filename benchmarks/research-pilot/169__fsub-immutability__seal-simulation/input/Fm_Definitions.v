(* Based on the System F-sub development by Brian Aydemir and Arthur
   Charguéraud, with Aaron Bohannon, Jeffrey Vaughan, and Dimitrios Vytiniotis. *)

Require Export Fsub.FmMeta.Metatheory.

Require Export String.

Require Export Fsub.Label.

Require Export Fsub.Signatures.

Require Export Fsub.LabelMap.

Require Export Coq.Program.Equality.


Inductive mut : Set :=
  | mut_readonly : mut
.

Inductive typ : Set :=
  | typ_top : typ
  | typ_bvar : nat -> typ
  | typ_fvar : atom -> typ
  | typ_arrow : typ -> typ -> typ
  | typ_all : typ -> typ -> typ

  | typ_box : typ -> typ

  | typ_mut : mut -> typ -> typ

  | typ_int : typ -> typ -> typ

  | typ_record : atom -> typ -> typ
.

Inductive exp : Set :=
  | exp_bvar : nat -> exp
  | exp_fvar : atom -> exp
  | exp_abs : typ -> exp -> exp
  | exp_app : exp -> exp -> exp
  | exp_tabs : typ -> exp -> exp
  | exp_tapp : exp -> typ -> exp
  | exp_let : exp -> exp -> exp

  | exp_box : exp -> exp
  | exp_unbox : exp -> exp
  | exp_set_box : exp -> exp -> exp
  | exp_ref : label -> exp

  | exp_seal : exp -> exp

  | exp_record : rec_comp -> exp
  | exp_record_read : exp -> atom -> exp
  | exp_record_write: exp -> atom -> exp -> exp
with rec_comp : Set :=


  | rec_empty : rec_comp
  | rec_exp : atom -> exp -> rec_comp -> rec_comp
  | rec_ref : atom -> label -> rec_comp -> rec_comp
.

Coercion typ_bvar : nat >-> typ.

Coercion typ_fvar : atom >-> typ.

Coercion exp_bvar : nat >-> exp.

Coercion exp_fvar : atom >-> exp.

Fixpoint open_tt_rec (K : nat) (U : typ) (T : typ)  {struct T} : typ :=
  match T with
  | typ_top => typ_top
  | typ_bvar J => if K == J then U else (typ_bvar J)
  | typ_fvar X => typ_fvar X
  | typ_arrow T1 T2 => typ_arrow (open_tt_rec K U T1) (open_tt_rec K U T2)
  | typ_all T1 T2 => typ_all (open_tt_rec K U T1) (open_tt_rec (S K) U T2)
  | typ_box T => typ_box (open_tt_rec K U T)
  | typ_mut M T => typ_mut M (open_tt_rec K U T)
  | typ_int T1 T2 => typ_int (open_tt_rec K U T1) (open_tt_rec K U T2)
  | typ_record a T1 => typ_record a (open_tt_rec K U T1)
  end.

Fixpoint open_te_rec (K : nat) (U : typ) (e : exp) {struct e} : exp :=
  match e with
  | exp_bvar i => exp_bvar i
  | exp_fvar x => exp_fvar x
  | exp_abs V e1 => exp_abs  (open_tt_rec K U V)  (open_te_rec K U e1)
  | exp_app e1 e2 => exp_app  (open_te_rec K U e1) (open_te_rec K U e2)
  | exp_tabs V e1 => exp_tabs (open_tt_rec K U V)  (open_te_rec (S K) U e1)
  | exp_tapp e1 V => exp_tapp (open_te_rec K U e1) (open_tt_rec K U V)
  | exp_let e1 e2 => exp_let (open_te_rec K U e1) (open_te_rec K U e2)
  | exp_box e => exp_box (open_te_rec K U e)
  | exp_unbox e => exp_unbox (open_te_rec K U e)
  | exp_set_box b e => exp_set_box (open_te_rec K U b) (open_te_rec K U e)
  | exp_ref l => exp_ref l
  | exp_seal e => exp_seal (open_te_rec K U e)
  | exp_record r => exp_record (open_te_record_rec K U r)
  | exp_record_read e a => exp_record_read (open_te_rec K U e) a
  | exp_record_write e1 a e2 => exp_record_write (open_te_rec K U e1) a (open_te_rec K U e2)
  end
with
  open_te_record_rec (K : nat) (U : typ) (r : rec_comp) {struct r} : rec_comp :=
  match r with
  | rec_empty => rec_empty
  | rec_exp a e r => rec_exp a (open_te_rec K U e) (open_te_record_rec K U r)
  | rec_ref a l r => rec_ref a l (open_te_record_rec K U r)
  end.

Fixpoint open_ee_rec (k : nat) (f : exp) (e : exp)  {struct e} : exp :=
  match e with
  | exp_bvar i => if k == i then f else (exp_bvar i)
  | exp_fvar x => exp_fvar x
  | exp_abs V e1 => exp_abs V (open_ee_rec (S k) f e1)
  | exp_app e1 e2 => exp_app (open_ee_rec k f e1) (open_ee_rec k f e2)
  | exp_tabs V e1 => exp_tabs V (open_ee_rec k f e1)
  | exp_tapp e1 V => exp_tapp (open_ee_rec k f e1) V
  | exp_let e1 e2 => exp_let (open_ee_rec k f e1) (open_ee_rec (S k) f e2)
  | exp_box e => exp_box (open_ee_rec k f e)
  | exp_unbox e => exp_unbox (open_ee_rec k f  e)
  | exp_set_box b e => exp_set_box (open_ee_rec k f b) (open_ee_rec k f e)
  | exp_ref l => exp_ref l
  | exp_seal e => exp_seal (open_ee_rec k f e)
  | exp_record r => exp_record (open_ee_record_rec k f r)
  | exp_record_read e a => exp_record_read (open_ee_rec k f e) a
  | exp_record_write e1 a e2 => exp_record_write (open_ee_rec k f e1) a (open_ee_rec k f e2)
  end
with
  open_ee_record_rec (k : nat) (f : exp) (r : rec_comp)  {struct r} : rec_comp :=
  match r with
  | rec_empty => rec_empty
  | rec_exp a e r => rec_exp a (open_ee_rec k f e) (open_ee_record_rec k f r)
  | rec_ref a l r => rec_ref a l (open_ee_record_rec k f r)
  end.

Definition open_tt T U := open_tt_rec 0 U T.

Definition open_te e U := open_te_rec 0 U e.

Definition open_ee e1 e2 := open_ee_rec 0 e2 e1.

Inductive type : typ -> Prop :=
  | type_top :
      type typ_top
  | type_var : forall X,
      type (typ_fvar X)
  | type_arrow : forall T1 T2,
      type T1 ->
      type T2 ->
      type (typ_arrow T1 T2)
  | type_all : forall L T1 T2,
      type T1 ->
      (forall X : atom, X `notin` L -> type (open_tt T2 X)) ->
      type (typ_all T1 T2)
  | type_box : forall T,
      type T ->
      type (typ_box T)
  | type_readonly : forall T,
      type T ->
      type (typ_mut mut_readonly T)
  | type_intersect : forall T1 T2,
      type T1 ->
      type T2 ->
      type (typ_int T1 T2)
  | type_record : forall a T1,
      type T1 ->
      type (typ_record a T1)
.

Inductive expr : exp -> Prop :=
  | expr_var : forall x,
      expr (exp_fvar x)
  | expr_abs : forall L T e1,
      type T ->
      (forall x : atom, x `notin` L -> expr (open_ee e1 x)) ->
      expr (exp_abs T e1)
  | expr_app : forall e1 e2,
      expr e1 ->
      expr e2 ->
      expr (exp_app e1 e2)
  | expr_tabs : forall L T e1,
      type T ->
      (forall X : atom, X `notin` L -> expr (open_te e1 X)) ->
      expr (exp_tabs T e1)
  | expr_tapp : forall e1 V,
      expr e1 ->
      type V ->
      expr (exp_tapp e1 V)
  | expr_let : forall L e1 e2,
      expr e1 ->
      (forall x : atom, x `notin` L -> expr (open_ee e2 x)) ->
      expr (exp_let e1 e2)
  | expr_box : forall e,
      expr e ->
      expr (exp_box e)
  | expr_unbox : forall e,
      expr e ->
      expr (exp_unbox e)
  | expr_set_box : forall e1 e2,
      expr e1 ->
      expr e2 ->
      expr (exp_set_box e1 e2)
  | expr_ref : forall l,
      expr (exp_ref l)
  | expr_seal : forall e,
      expr e ->
      expr (exp_seal e)
  | expr_record : forall r,
      record_comp r ->
      expr (exp_record r)
  | expr_record_read : forall e a,
      expr e ->
      expr (exp_record_read e a)
  | expr_record_write : forall e1 a e2,
      expr e1 ->
      expr e2 ->
      expr (exp_record_write e1 a e2)
with record_comp : rec_comp -> Prop :=
  | record_comp_empty :
      record_comp (rec_empty)
  | record_comp_exp : forall a e r,
      expr e ->
      record_comp r ->
      record_comp (rec_exp a e r)
  | record_comp_ref : forall a e r,
      record_comp r ->
      record_comp (rec_ref a e r)
.

Definition body_e (e : exp) :=
  exists L, forall x : atom, x `notin` L -> expr (open_ee e x).

Inductive binding : Set :=
  | bind_sub : typ -> binding
  | bind_typ : typ -> binding.

Inductive signature : Set :=
  | bind_sig : typ -> signature.

Notation env := (list (atom * binding)).

Notation empty := (@nil (atom * binding)).

Notation sig := (list (label * signature)).

Notation sempty := (@nil (label * signature)).

Inductive wf_typ : env -> typ -> Prop :=
  | wf_typ_top : forall E,
      wf_typ E typ_top
  | wf_typ_var : forall U E (X : atom),
      binds X (bind_sub U) E ->
      wf_typ E (typ_fvar X)
  | wf_typ_arrow : forall E T1 T2,
      wf_typ E T1 ->
      wf_typ E T2 ->
      wf_typ E (typ_arrow T1 T2)
  | wf_typ_all : forall L E T1 T2,
      wf_typ E T1 ->
      (forall X : atom, X `notin` L ->
        wf_typ (X ~ bind_sub T1 ++ E) (open_tt T2 X)) ->
      wf_typ E (typ_all T1 T2)
  | wf_typ_box : forall E T,
      wf_typ E T ->
      wf_typ E (typ_box T)
  | wf_typ_readonly : forall E T,
      wf_typ E T ->
      wf_typ E (typ_mut mut_readonly T)
  | wf_typ_intersect : forall E T1 T2,
      wf_typ E T1 ->
      wf_typ E T2 ->
      wf_typ E (typ_int T1 T2)
  | wf_typ_record : forall E a T1,
      wf_typ E T1 ->
      wf_typ E (typ_record a T1)
.

Inductive wf_env : env -> Prop :=
  | wf_env_empty :
      wf_env empty
  | wf_env_sub : forall (E : env) (X : atom) (T : typ),
      wf_env E ->
      wf_typ E T ->
      X `notin` dom E ->
      wf_env (X ~ bind_sub T ++ E)
  | wf_env_typ : forall (E : env) (x : atom) (T : typ),
      wf_env E ->
      wf_typ E T ->
      x `notin` dom E ->
      wf_env (x ~ bind_typ T ++ E).

Inductive wf_sig : env -> sig -> Prop :=
    | wf_sig_empty : forall E,
        wf_env E ->
        wf_sig E sempty
    | wf_sig_typ : forall (E : env) (R : sig) (l : label) (T : typ),
        wf_sig E R ->
        wf_typ E T ->
        LabelSetImpl.notin l (Signatures.dom R) ->
        wf_sig E (l ~ bind_sig T ++ R).

Fixpoint merge_mutability (T : typ) (m : mut) {struct T} :=
    match T with



    | typ_bvar J => (typ_mut m T)
    | typ_fvar X => (typ_mut m (typ_fvar X))
    | typ_box T => (typ_mut m (typ_box T))
    | typ_record a T => (typ_mut m (typ_record a T))

    | typ_int T1 T2 => (typ_int (merge_mutability T1 m) (merge_mutability T2 m))

    | _ => T
    end.

Fixpoint normal_form_typing (T : typ) {struct T} :=
    match T with
    | typ_top => typ_top
    | typ_bvar J => typ_bvar J
    | typ_fvar X => typ_fvar X
    | typ_arrow T1 T2 => typ_arrow (normal_form_typing T1) (normal_form_typing T2)
    | typ_all T1 T2 => typ_all (normal_form_typing T1) (normal_form_typing T2)
    | typ_box T => typ_box (normal_form_typing T)
    | typ_int T1 T2 => typ_int (normal_form_typing T1) (normal_form_typing T2)
    | typ_mut M T =>
        (merge_mutability (normal_form_typing T) M)
    | typ_record a T => typ_record a (normal_form_typing T)
    end.

Arguments merge_mutability T m /.

Arguments normal_form_typing T /.

Inductive in_normal_form : typ -> Prop :=
  | top_in_normal_form :
    in_normal_form typ_top
  | fvar_in_normal_form : forall (X : atom),
    in_normal_form X
  | readonly_fvar_in_normal_form : forall (X : atom) m,
    in_normal_form (typ_mut m X)
  | arrow_in_normal_form : forall T1 T2,
    in_normal_form T1 ->
    in_normal_form T2 ->
    in_normal_form (typ_arrow T1 T2)
  | all_in_normal_form : forall L T1 T2,
    in_normal_form T1 ->
    (forall X : atom, X `notin` L -> in_normal_form (open_tt T2 X)) ->
    in_normal_form (typ_all T1 T2)
  | box_in_normal_form : forall T,
    in_normal_form T ->
    in_normal_form (typ_box T)
  | readonly_box_in_normal_form : forall T m,
    in_normal_form T ->
    in_normal_form (typ_mut m (typ_box T))
  | int_in_normal_form : forall T1 T2,
    in_normal_form T1 ->
    in_normal_form T2 ->
    in_normal_form (typ_int T1 T2)
  | record_in_normal_form : forall a T1,
    in_normal_form T1 ->
    in_normal_form (typ_record a T1)
  | readonly_record_in_normal_form : forall T a m,
    in_normal_form T ->
    in_normal_form (typ_mut m (typ_record a T))
.

Inductive in_intersection : typ -> typ -> Prop :=
  | actually_equal : forall S T,
    S = T ->
    in_intersection S T
  | in_intersection_left : forall S L R,
    in_intersection S L ->
    in_intersection S (typ_int L R)
  | in_intersection_right : forall S L R,
    in_intersection S R ->
    in_intersection S (typ_int L R).

Definition in_intersection_component (S T : typ) :=
    (~ exists L R, S = typ_int L R) /\
    (in_intersection S T).

Inductive sub : env -> typ -> typ -> Prop :=
  | sub_top : forall E S,
      wf_env E ->
      wf_typ E S ->
      sub E S typ_top
  | sub_refl_tvar : forall E X,
      wf_env E ->
      wf_typ E (typ_fvar X) ->
      sub E (typ_fvar X) (typ_fvar X)
  | sub_trans_tvar : forall U E T X,
      binds X (bind_sub U) E ->
      sub E U T ->
      sub E (typ_fvar X) T
  | sub_arrow : forall E S1 S2 T1 T2,
      sub E T1 S1 ->
      sub E S2 T2 ->
      sub E (typ_arrow S1 S2) (typ_arrow T1 T2)
  | sub_all : forall L E S1 S2 T1 T2,
      sub E T1 S1 ->
      (forall X : atom, X `notin` L ->
          sub (X ~ bind_sub T1 ++ E) (open_tt S2 X) (open_tt T2 X)) ->
      sub E (typ_all S1 S2) (typ_all T1 T2)
  | sub_box : forall E T1 T2,
      sub E T1 T2 ->
      sub E T2 T1 ->
      sub E (typ_box T1) (typ_box T2)

  | sub_readonly : forall E T1 T2,
      sub E T1 T2 ->
      sub E (typ_mut mut_readonly T1) (typ_mut mut_readonly T2)

  | sub_readonly_mutable : forall E T1 T2,
      sub E T1 T2 ->
      sub E T1 (typ_mut mut_readonly T2)
  | sub_trans : forall E T1 T2 T3,
      sub E T1 T2 ->
      sub E T2 T3 ->
      sub E T1 T3
  | sub_inter_left : forall E T1 T2,
      wf_env E ->
      wf_typ E T1 ->
      wf_typ E T2 ->
      sub E (typ_int T1 T2) T1
  | sub_inter_right : forall E T1 T2,
      wf_env E ->
      wf_typ E T1 ->
      wf_typ E T2 ->
      sub E (typ_int T1 T2) T2
  | sub_inter : forall E T1 T2 T3,
      sub E T1 T2 ->
      sub E T1 T3 ->
      sub E T1 (typ_int T2 T3)
  | sub_record : forall E a T1 T2,
      sub E T1 T2 ->
      sub E T2 T1 ->
      sub E (typ_record a T1) (typ_record a T2)

  | sub_readonly_record : forall E a T1 T2,
      sub E T1 T2 ->
      sub E (typ_mut mut_readonly (typ_record a T1)) (typ_mut mut_readonly (typ_record a T2))

  | sub_denormalize : forall E T1 T2,
      wf_typ E T1 ->
      wf_typ E T2 ->
      sub E (normal_form_typing T1) (normal_form_typing T2) ->
      sub E T1 T2
.

Notation "E |-s S <: T" := (sub E S T) (at level 70).

Fixpoint record_dom (r : rec_comp)  {struct r} : atoms :=
    match r with
    | rec_empty => {}
    | rec_exp a e r => {{ a }} `union` record_dom r
    | rec_ref a l r => {{ a }} `union` record_dom r
    end.

Inductive typing : env -> sig -> exp -> typ -> Prop :=
  | typing_var : forall E R x T,
      wf_env E ->
      wf_sig E R ->
      binds x (bind_typ T) E ->
      typing E R (exp_fvar x) T
  | typing_abs : forall L E R V e1 T1,
      wf_sig E R ->
      (forall x : atom, x `notin` L ->
        typing (x ~ bind_typ V ++ E) R (open_ee e1 x) T1) ->
      typing E R (exp_abs V e1) (typ_arrow V T1)
  | typing_app : forall T1 E R e1 e2 T2,
      wf_sig E R ->
      typing E R e1 (typ_arrow T1 T2) ->
      typing E R e2 T1 ->
      typing E R (exp_app e1 e2) T2
  | typing_tabs : forall L E R V e1 T1,
      wf_sig E R ->
      (forall X : atom, X `notin` L ->
        typing (X ~ bind_sub V ++ E) R (open_te e1 X) (open_tt T1 X)) ->
      typing E R (exp_tabs V e1) (typ_all V T1)
  | typing_tapp : forall T1 E R e1 T T2,
      wf_sig E R ->
      typing E R e1 (typ_all T1 T2) ->
      sub E T T1 ->
      typing E R (exp_tapp e1 T) (open_tt T2 T)
  | typing_sub : forall S E R e T,
      wf_sig E R ->
      typing E R e S ->
      sub E S T ->
      typing E R e T
  | typing_let : forall L T1 T2 e1 e2 E R,
      wf_sig E R ->
      typing E R e1 T1 ->
      (forall x : atom, x `notin` L ->
        typing (x ~ bind_typ T1 ++ E) R (open_ee e2 x) T2) ->
      typing E R (exp_let e1 e2) T2
  | typing_box : forall E R e T,
      wf_sig E R ->
      typing E R e T ->
      typing E R (exp_box e) (typ_box T)
  | typing_unbox : forall E R e T,
      wf_sig E R ->
      typing E R e (typ_box T) ->
      typing E R (exp_unbox e) T

  | typing_set_box : forall E R e1 e2 T,
      wf_sig E R ->
      typing E R e1 (typ_box T) ->
      typing E R e2 T ->
      typing E R (exp_set_box e1 e2) T
  | typing_ref : forall E R l T,
      wf_env E ->
      wf_sig E R ->
      Signatures.binds l (bind_sig T) R ->
      typing E R (exp_ref l) (typ_box T)

  | typing_seal : forall E R e T,
      typing E R e T ->
      typing E R (exp_seal e) (typ_mut mut_readonly T)

  | typing_unbox_readonly : forall E R e T,
      typing E R e (typ_mut mut_readonly (typ_box T)) ->
      typing E R (exp_unbox e) (typ_mut mut_readonly T)
  | typing_record : forall E R r T,
      typing_record_comp E R r T ->
      typing E R (exp_record r) T

  | typing_record_read : forall E R e a T,
      typing E R e (typ_record a T) ->
      typing E R (exp_record_read e a) T
  | typing_record_read_readonly : forall E R e a T,
      typing E R e (typ_mut mut_readonly (typ_record a T)) ->
      typing E R (exp_record_read e a) (typ_mut mut_readonly T)

  | typing_record_write : forall E R e1 a e2 T,
      typing E R e1 (typ_record a T) ->
      typing E R e2 T ->
      typing E R (exp_record_write e1 a e2) T
with typing_record_comp : env -> sig -> rec_comp -> typ -> Prop :=
  | typing_record_empty : forall E R,
      wf_env E ->
      wf_sig E R ->
      typing_record_comp E R rec_empty typ_top
  | typing_record_exp : forall E R a e r T Tr,
      a `notin` record_dom r ->
      typing_record_comp E R r Tr ->
      typing E R e T ->
      typing_record_comp E R (rec_exp a e r) (typ_int (typ_record a T) Tr)
  | typing_record_ref : forall E R a l r T Tr,
      a `notin` record_dom r ->
      typing_record_comp E R r Tr ->
      Signatures.binds l (bind_sig T) R ->
      typing_record_comp E R (rec_ref a l r) (typ_int (typ_record a T) Tr)
.

Notation "E @ R |- e T" := (typing E R e T) (at level 70).

Notation "E @ R |-r r T" := (typing_record_comp E R r T) (at level 70).

Inductive value : exp -> Prop :=
  | value_abs : forall T e1,
      expr (exp_abs T e1) ->
      value (exp_abs T e1)
  | value_tabs : forall T e1,
      expr (exp_tabs T e1) ->
      value (exp_tabs T e1)
  | value_ref : forall l,
      value (exp_ref l)
  | value_sealed_ref : forall l,
      value (exp_seal (exp_ref l))
  | value_record : forall r,
      value_record_comp r ->
      value (exp_record r)
  | value_sealed_record : forall r,
      value_record_comp r ->
      value (exp_seal (exp_record r))
with value_record_comp : rec_comp -> Prop :=
  | value_rec_empty :
      value_record_comp rec_empty
  | value_rec_ref : forall a l r,
      value_record_comp r ->
      value_record_comp (rec_ref a l r)
.

Notation store := (LabelMap exp).

Notation empty_store := (LabelMapImpl.empty store).

Definition well_formed_store (s : store) :=
  forall l v, LabelMapImpl.MapsTo l v s -> value v.

(* The original dependent pair uses this same witness. *)
Definition fresh_label_for_store (s : store) :=
  Label.fresh (List.map fst (LabelMapImpl.elements s)).

Definition typing_store (E: env) (R : sig) (s : store) :=
  forall l,
    (forall T, Signatures.binds l (bind_sig T) R ->
        exists v,
            (LabelMapImpl.MapsTo l v s) /\
            typing E R v T /\ value v)
    /\
    (forall v, (LabelMapImpl.MapsTo l v s) ->
        exists T, (value v /\ typing E R v T /\ Signatures.binds l (bind_sig T) R)).

Notation "E |-st s @ R" := (typing_store E R s) (at level 70).

Fixpoint record_lookup_ref (a : atom) (r : rec_comp) : option label :=
    match r with
    | rec_ref a' l r => if (a === a') then Some l else record_lookup_ref a r
    | _ => None
    end.

Notation "r # a" := (record_lookup_ref a r) (at level 70).

Inductive red : exp -> store -> exp -> store -> Prop :=
  | red_app_1 : forall e1 e1' s1 s1' e2,
      expr e2 ->
      red e1 s1 e1' s1' ->
      red (exp_app e1 e2) s1 (exp_app e1' e2) s1'
  | red_app_2 : forall e1 e2 s2 e2' s2',
      value e1 ->
      red e2 s2 e2' s2' ->
      red (exp_app e1 e2) s2 (exp_app e1 e2') s2'
  | red_tapp : forall e1 e1' s1 s1' V,
      type V ->
      red e1 s1 e1' s1' ->
      red (exp_tapp e1 V) s1 (exp_tapp e1' V) s1'
  | red_abs : forall T e1 s1 v2,
      well_formed_store s1 ->
      expr (exp_abs T e1) ->
      value v2 ->
      red (exp_app (exp_abs T e1) v2) s1 (open_ee e1 v2) s1
  | red_tabs : forall T1 e1 s1 T2,
      well_formed_store s1 ->
      expr (exp_tabs T1 e1) ->
      type T2 ->
      red (exp_tapp (exp_tabs T1 e1) T2) s1 (open_te e1 T2) s1
  | red_let_1 : forall e1 e1' s1 s1' e2,
      red e1 s1 e1' s1' ->
      body_e e2 ->
      red (exp_let e1 e2) s1 (exp_let e1' e2) s1'
  | red_let : forall v1 e2 s2,
      well_formed_store s2 ->
      value v1 ->
      body_e e2 ->
      red (exp_let v1 e2) s2 (open_ee e2 v1) s2
  | red_box_1 : forall e1 e1' s1 s1',
      red e1 s1 e1' s1' ->
      red (exp_box e1) s1 (exp_box e1') s1'
  | red_box_ref : forall v1 l s1,
      well_formed_store s1 ->
      value v1 ->
      l = fresh_label_for_store s1 ->
      red (exp_box v1) s1 (exp_ref l) (LabelMapImpl.add l v1 s1)
  | red_unbox_1 : forall e1 e1' s1 s1',
      red e1 s1 e1' s1' ->
      red (exp_unbox e1) s1 (exp_unbox e1') s1'
  | red_unbox_ref : forall l v1 s1,
      well_formed_store s1 ->
      value v1 ->
      LabelMapImpl.MapsTo l v1 s1 ->
      red (exp_unbox (exp_ref l)) s1 v1 s1
  | red_unbox_sealed_ref : forall l v1 s1,
      well_formed_store s1 ->
      value v1 ->
      LabelMapImpl.MapsTo l v1 s1 ->
      red (exp_unbox (exp_seal (exp_ref l))) s1 (exp_seal v1) s1
  | red_set_box_1 : forall e1 s1 e1' s1' e2,
      expr e2 ->
      red e1 s1 e1' s1' ->
      red (exp_set_box e1 e2) s1 (exp_set_box e1' e2) s1'
  | red_set_box_2 : forall v1 e2 s2 e2' s2',
      value v1 ->
      red e2 s2 e2' s2' ->
      red (exp_set_box v1 e2) s2 (exp_set_box v1 e2') s2'
  | red_set_box_ref : forall l v1 v2 s1,
      well_formed_store s1 ->
      value v1 ->
      value v2 ->
      LabelMapImpl.MapsTo l v1 s1 ->
      red (exp_set_box (exp_ref l) v2) s1 v1 (LabelMapImpl.add l v2 s1)
  | red_seal_1 : forall e1 s1 e1' s1',
      red e1 s1 e1' s1' ->
      red (exp_seal e1) s1 (exp_seal e1') s1'
  | red_seal_abs : forall T e1 s1,
      well_formed_store s1 ->
      expr (exp_abs T e1) ->
      red (exp_seal (exp_abs T e1)) s1 (exp_abs T e1) s1
  | red_seal_tabs : forall T e1 s1,
      well_formed_store s1 ->
      expr (exp_tabs T e1) ->
      red (exp_seal (exp_tabs T e1)) s1 (exp_tabs T e1) s1
  | red_seal_sealed_ref: forall l s1,
      well_formed_store s1 ->
      red (exp_seal (exp_seal (exp_ref l))) s1 (exp_seal (exp_ref l)) s1
  | red_seal_sealed_record : forall r s1,
      well_formed_store s1 ->
      value_record_comp r ->
      red (exp_seal (exp_seal (exp_record r))) s1 (exp_seal (exp_record r)) s1
  | red_record : forall r1 s1 r1' s1',
      red_record_comp r1 s1 r1' s1' ->
      red (exp_record r1) s1 (exp_record r1') s1'
  | red_record_read_1 : forall a e1 e1' s1 s1',
      red e1 s1 e1' s1' ->
      red (exp_record_read e1 a) s1 (exp_record_read e1' a) s1'
  | red_record_read_ref : forall r a l v1 s1,
      well_formed_store s1 ->
      value_record_comp r ->
      record_lookup_ref a r = Some l ->
      value v1 ->
      LabelMapImpl.MapsTo l v1 s1 ->
      red (exp_record_read (exp_record r) a) s1 v1 s1
  | red_sealed_record_read_ref : forall r a l v1 s1,
      well_formed_store s1 ->
      value_record_comp r ->
      record_lookup_ref a r = Some l ->
      value v1 ->
      LabelMapImpl.MapsTo l v1 s1 ->
      red (exp_record_read (exp_seal (exp_record r)) a) s1 (exp_seal v1) s1
  | red_record_write_1 : forall a e1 s1 e1' s1' e2,
      expr e2 ->
      red e1 s1 e1' s1' ->
      red (exp_record_write e1 a e2) s1 (exp_record_write e1' a e2) s1'
  | red_record_write_2 : forall a v1 e2 s2 e2' s2',
      value v1 ->
      red e2 s2 e2' s2' ->
      red (exp_record_write v1 a e2) s2 (exp_record_write v1 a e2') s2'
  | red_record_write_ref : forall a l r v1 v2 s1,
      well_formed_store s1 ->
      value_record_comp r ->
      record_lookup_ref a r = Some l ->
      value v1 ->
      value v2 ->
      LabelMapImpl.MapsTo l v1 s1 ->
      red (exp_record_write (exp_record r) a v2) s1 v1 (LabelMapImpl.add l v2 s1)
with red_record_comp : rec_comp -> store -> rec_comp -> store -> Prop :=
  | red_record_exp_1 : forall a e1 s1 e1' s1' r1,
      record_comp r1 ->
      red e1 s1 e1' s1' ->
      red_record_comp (rec_exp a e1 r1) s1 (rec_exp a e1' r1) s1'
  | red_record_exp_2 : forall a v r1 s1 l,
      well_formed_store s1 ->
      record_comp r1 ->
      value v ->
      l = fresh_label_for_store s1 ->
      red_record_comp (rec_exp a v r1) s1 (rec_ref a l r1) (LabelMapImpl.add l v s1)
  | red_record_ref : forall a l r1 s1 r1' s1',
      red_record_comp r1 s1 r1' s1' ->
      red_record_comp (rec_ref a l r1) s1 (rec_ref a l r1') s1'
.

Notation "< e1 | s1 > --> < e1' | s1' >" := (red e1 s1 e1' s1') (at level 69).

Notation "< r1 | s1 > -->r < r1' | s1' >" := (red_record_comp r1 s1 r1' s1') (at level 69).

Inductive redm : exp -> store -> exp -> store -> Prop :=
  | redm_eq : forall e s e' s',
    e = e' -> s = s' -> redm e s e' s'
  | redm_step : forall e s e'' s'' e' s',
    red e s e'' s'' ->
    redm e'' s'' e' s' ->
    redm e s e' s'.

Notation "< e1 | s1 > -->* < e1' | s1' >" := (redm e1 s1 e1' s1') (at level 69).

Inductive sealcomp : exp -> exp -> Prop :=
  | sealcomp_fvar : forall (x : atom),
      sealcomp x x
  | sealcomp_bvar : forall (n : nat),
      sealcomp n n
  | sealcomp_abs : forall T e1 e2,
      sealcomp e1 e2 ->
      sealcomp (exp_abs T e1) (exp_abs T e2)
  | sealcomp_app : forall e1 e2 f1 f2,
      sealcomp e1 f1 ->
      sealcomp e2 f2 ->
      sealcomp (exp_app e1 e2) (exp_app f1 f2)
  | sealcomp_tabs : forall T e1 e2,
      sealcomp e1 e2 ->
      sealcomp (exp_tabs T e1) (exp_tabs T e2)
  | sealcomp_tapp : forall T e1 e2,
      sealcomp e1 e2 ->
      sealcomp (exp_tapp e1 T) (exp_tapp e2 T)
  | sealcomp_let : forall e1 e2 f1 f2,
      sealcomp e1 f1 ->
      sealcomp e2 f2 ->
      sealcomp (exp_let e1 e2) (exp_let f1 f2)
  | sealcomp_box : forall e1 e2,
      sealcomp e1 e2 ->
      sealcomp (exp_box e1) (exp_box e2)
  | sealcomp_unbox : forall e1 e2,
      sealcomp e1 e2 ->
      sealcomp (exp_unbox e1) (exp_unbox e2)
  | sealcomp_set_box : forall e1 e2 f1 f2,
      sealcomp e1 f1 ->
      sealcomp e2 f2 ->
      sealcomp (exp_set_box e1 e2) (exp_set_box f1 f2)
  | sealcomp_ref : forall l,
      sealcomp (exp_ref l) (exp_ref l)
  | sealcomp_seal : forall e1 e2,
      sealcomp e1 e2 ->
      sealcomp (exp_seal e1) (exp_seal e2)
  | sealcomp_record : forall r1 r2,
      sealcomp_rec_comp r1 r2 ->
      sealcomp (exp_record r1) (exp_record r2)
  | sealcomp_record_read : forall e1 e2 x,
      sealcomp e1 e2 ->
      sealcomp (exp_record_read e1 x) (exp_record_read e2 x)
  | sealcomp_record_write : forall e1 f1 x e2 f2,
      sealcomp e1 f1 ->
      sealcomp e2 f2 ->
      sealcomp (exp_record_write e1 x e2) (exp_record_write f1 x f2)
  | sealcomp_multiple_seal : forall e1 e2,
      sealcomp e1 e2 ->
      sealcomp e1 (exp_seal e2)
with sealcomp_rec_comp : rec_comp -> rec_comp -> Prop :=
  | sealcomp_rec_empty :
      sealcomp_rec_comp (rec_empty) (rec_empty)
  | sealcomp_rec_exp : forall a e1 e2 r1 r2,
      sealcomp_rec_comp r1 r2 ->
      sealcomp e1 e2 ->
      sealcomp_rec_comp (rec_exp a e1 r1) (rec_exp a e2 r2)
  | sealcomp_rec_ref : forall a l r1 r2,
      sealcomp_rec_comp r1 r2 ->
      sealcomp_rec_comp (rec_ref a l r1) (rec_ref a l r2)
.

Definition sealcomp_store (s1 : store) (s2 : store) :=
  (forall l v, (LabelMapImpl.MapsTo l v s1) ->
      exists v', (LabelMapImpl.MapsTo l v' s2) /\ sealcomp v v') /\
  (forall l v', (LabelMapImpl.MapsTo l v' s2) ->
      exists v, (LabelMapImpl.MapsTo l v s1) /\ sealcomp v v').

Notation "e1 <e= e2" := (sealcomp e1 e2) (at level 60).

Notation "r1 <r= r2" := (sealcomp_rec_comp r1 r2) (at level 60).

Notation "s1 <s= s2" := (sealcomp_store s1 s2) (at level 60).

Fixpoint seal_count (e : exp)  {struct e} : nat :=
  match e with
  | exp_bvar i => 0
  | exp_fvar x => 0
  | exp_abs V e1 => (seal_count e1)
  | exp_app e1 e2 => (seal_count e1) + (seal_count e2)
  | exp_tabs V e1 => (seal_count e1)
  | exp_tapp e1 V => (seal_count e1)
  | exp_let e1 e2 => (seal_count e1) + (seal_count e2)
  | exp_box e => (seal_count e)
  | exp_unbox e => (seal_count e)
  | exp_set_box b e => (seal_count b) + (seal_count e)
  | exp_ref l => 0
  | exp_seal e => (S (seal_count e))
  | exp_record r => (seal_count_record r)
  | exp_record_read e a => (seal_count e)
  | exp_record_write e1 a e2 => (seal_count e1) + (seal_count e2)
  end
with
  seal_count_record (r : rec_comp)  {struct r} : nat :=
  match r with
  | rec_empty => 0
  | rec_exp a e r => (seal_count e) + (seal_count_record r)
  | rec_ref a l r => (seal_count_record r)
  end.

Arguments seal_count e /.

Arguments seal_count_record r /.

Notation "| f |" := (seal_count f) (at level 69).
