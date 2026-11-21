Require Export Metalib.Metatheory.

Inductive typ : Set :=
  | t_int : typ
  | t_arrow : typ -> typ -> typ
  | t_dyn : typ
  | t_bvar  : nat -> typ
  | t_fvar  : var -> typ
  | t_all   : typ -> typ
  | t_ref   : typ -> typ
  | t_unit  : typ
.

Inductive exp : Set :=
  | e_bvar   : nat -> exp
  | e_fvar   : var -> exp
  | e_lit    : nat -> exp
  | e_unit   : exp
  | e_anno   : exp -> typ -> exp
  | e_app    : exp -> exp -> exp
  | e_abs    : typ -> exp -> typ -> exp
  | e_tabs   : exp -> typ -> exp
  | e_tapp   : exp -> typ -> exp
  | e_loc    : nat -> exp
  | e_ref    : exp -> exp
  | e_get    : exp -> exp
  | e_set    : exp -> exp -> exp
.

Coercion t_bvar : nat >-> typ.

Coercion t_fvar : atom >-> typ.

Coercion e_bvar : nat >-> exp.

Coercion e_fvar : atom >-> exp.

Inductive dirflag : Set :=
 | Inf : dirflag
 | Chk : dirflag.

Fixpoint open_tt_rec (K : nat) (U : typ) (T : typ) {struct T} : typ :=
  match T with
  | t_int         => t_int
  | t_dyn     => t_dyn
  | t_bvar J      => if K == J then U else (t_bvar J)
  | t_fvar X      => t_fvar X
  | t_arrow T1 T2 => t_arrow (open_tt_rec K U T1) (open_tt_rec K U T2)
  | t_all T       => t_all (open_tt_rec (S K) U T)
  | t_ref T1      => t_ref (open_tt_rec K U T1)
  | t_unit        => t_unit
  end.

Fixpoint open_te_rec (k : nat) (f : typ) (e : exp) {struct e} : exp :=
  match e with
  | e_bvar i       => e_bvar i
  | e_fvar x       => e_fvar x
  | e_lit i        => e_lit i
  | e_unit        => e_unit
  | e_loc x      => e_loc x
  | e_app e1 e2    => e_app (open_te_rec k f e1) (open_te_rec k f e2)
  | e_abs A e1 B   => e_abs (open_tt_rec k f A) (open_te_rec k f e1) (open_tt_rec k f B)
  | e_anno e1 A    => e_anno (open_te_rec k f e1) (open_tt_rec k f A)
  | e_tabs e1 A     => e_tabs (open_te_rec (S k) f e1)  (open_tt_rec (S k) f A)
  | e_tapp e1 A     => e_tapp (open_te_rec k f e1) (open_tt_rec k f A)
  | e_ref e1     => e_ref (open_te_rec k f e1)
  | e_get e1     => e_get (open_te_rec k f e1)
  | e_set e1 e2     => e_set (open_te_rec k f e1) (open_te_rec k f e2)
  end.

Fixpoint open_ee_rec (k : nat) (f : exp) (e : exp) {struct e} : exp :=
  match e with
  | e_bvar i       => if k == i then f else (e_bvar i)
  | e_fvar x       => e_fvar x
  | e_loc x      => e_loc x
  | e_lit i        => e_lit i
  | e_unit        => e_unit
  | e_app e1 e2    => e_app (open_ee_rec k f e1) (open_ee_rec k f e2)
  | e_abs A e1 B   => e_abs A (open_ee_rec (S k) f e1) B
  | e_anno e1 A    => e_anno (open_ee_rec k f e1) A
  | e_tabs e1 A     => e_tabs (open_ee_rec k f e1) A
  | e_tapp e1 A     => e_tapp (open_ee_rec k f e1) A
  | e_ref e1     => e_ref (open_ee_rec k f e1)
  | e_get e1     => e_get (open_ee_rec k f e1)
  | e_set e1 e2     => e_set (open_ee_rec k f e1) (open_ee_rec k f e2)
  end.

Definition open_tt T U := open_tt_rec 0 U T.

Definition open_te e T := open_te_rec 0 T e.

Definition open_ee e1 e2 := open_ee_rec 0 e2 e1.

Notation "T 'open_tt_var' X" := (open_tt T (t_fvar X)) (at level 67).

Notation "t 'open_ee_var' x" := (open_ee t (e_fvar x)) (at level 67).

Notation "t 'open_te_var' a" := (open_te t (t_fvar a)) (at level 67).

Inductive type : typ -> Prop :=
  | type_lit :
      type t_int
  | type_dyn :
      type t_dyn
  | type_unit :
      type t_unit
  | type_var : forall X,
      type (t_fvar X)
  | type_arrow : forall T1 T2,
      type T1 ->
      type T2 ->
      type (t_arrow T1 T2)
  | type_all : forall L T2,
      (forall X, X \notin L -> type (T2 open_tt_var X)) ->
      type (t_all T2)
  | type_ref : forall T,
      type T ->
      type (t_ref T)
.

Inductive expr : exp -> Prop :=
  | expr_var : forall x,
      expr (e_fvar x)
  | expr_nat : forall i,
      expr (e_lit i)
  | expr_unit :
      expr e_unit
  | expr_abs : forall L e1 A B,
      type A ->
      type B ->
      (forall x, x \notin L -> expr (e1 open_ee_var x)) ->
      expr (e_abs A e1 B)
  | expr_app : forall e1 e2,
      expr e1 ->
      expr e2 ->
      expr (e_app e1 e2)
  | expr_tabs : forall L e A,
      (forall x, x \notin L -> expr (e open_te_var x)) ->
      (forall X, X \notin L -> type (A open_tt_var X)) ->
      expr (e_tabs e A)
  | expr_tapp : forall e A,
      expr e ->
      type A ->
      expr (e_tapp e A)
  | expr_anno : forall e A,
      expr e ->
      type A ->
      expr (e_anno e A)
  | expr_loc : forall l,
      expr (e_loc l)
  | expr_ref : forall e,
      expr e ->
      expr (e_ref e)
  | expr_get : forall e,
      expr e ->
      expr (e_get e)
  | expr_set : forall e1 e2,
      expr e1 ->
      expr e2 ->
      expr (e_set e1 e2)
.

Inductive binding : Set :=
  | bind_tvar : binding
  | bind_typ : typ -> binding
.

Notation env := (list (atom * binding)).

Notation empty := (@nil (atom * binding)).

Definition sto := list exp.

Definition phi := list typ.

Notation "x ~tvar" := (x ~ bind_tvar)
  (at level 23, left associativity) : env_scope.

Notation "x ~: T" := (x ~ bind_typ T)
  (at level 23, left associativity) : env_scope.

Inductive wf_typ : env -> typ -> Prop :=
  | wf_typ_int : forall E,
      wf_typ E t_int
  | wf_typ_unit : forall E,
      wf_typ E t_unit
  | wf_typ_dyn : forall E,
      wf_typ E t_dyn
  | wf_typ_var : forall E x,
      binds x bind_tvar E ->
      wf_typ E (t_fvar x)
  | wf_typ_arrow : forall E A1 A2,
      wf_typ E A1 ->
      wf_typ E A2 ->
      wf_typ E (t_arrow A1 A2)
  | wf_typ_all : forall L E A,
      (forall X, X \notin L ->
            wf_typ (X ~tvar ++ E) (A open_tt_var X)) ->
      wf_typ E (t_all A)
  | wf_typ_ref : forall E A,
      wf_typ E A ->
      wf_typ E (t_ref A)
.

Inductive wf_env : env -> Prop :=
  | wf_env_empty :
      wf_env empty
  | wf_env_tvar : forall E x,
      wf_env E ->
      x `notin` dom E ->
      wf_env (x ~tvar ++ E)
  | wf_env_typ : forall E x A,
      wf_env E ->
      wf_typ E A ->
      x `notin` dom E ->
      wf_env (x ~: A ++ E)
.

Inductive consist: env -> typ -> typ -> Prop :=
  | consist_int : forall E,
      wf_env E ->
      consist E t_int t_int
  | consist_unit : forall E,
      wf_env E ->
      consist E t_unit t_unit
  | consist_var : forall E x,
      wf_env E ->
      wf_typ E (t_fvar x) ->
      consist E (t_fvar x) (t_fvar x)
  | consist_dyn_l : forall E A,
      wf_env E ->
      wf_typ E A ->
      consist E t_dyn A
  | consist_dyn_r : forall E A,
      wf_env E ->
      wf_typ E A ->
      consist E A t_dyn
  | consist_fun : forall E A1 A2 B1 B2,
      consist E B1 A1 ->
      consist E A2 B2 ->
      consist E (t_arrow A1 A2) (t_arrow B1 B2)
  | consist_all: forall L E A B ,
      (forall x, x \notin L ->
      consist (x ~tvar ++ E) (A open_tt_var x) (B open_tt_var x)) ->
      consist E (t_all A) (t_all B)
  | consist_ref : forall E A B,
      consist E A B ->
      consist E (t_ref A) (t_ref B)
.

Definition store_Tlookup (n:nat) (ST: phi) :=
  nth n ST t_unit.

Inductive pattern_abs : typ -> typ -> Prop :=
 | pas_abs : forall A B,
   pattern_abs (t_arrow A B) (t_arrow A B)
 | pas_dyn :
   pattern_abs t_dyn (t_arrow t_dyn t_dyn).

Inductive pattern_ref : typ -> typ -> Prop :=
 | pre_ref : forall A,
   pattern_ref (t_ref A) (t_ref A)
 | pre_dyn :
   pattern_ref t_dyn (t_ref t_dyn).

Inductive pattern_all : typ -> typ -> Prop :=
 | pal_ref : forall B,
   pattern_all (t_all B) (t_all B)
 | pal_dyn :
   pattern_all t_dyn (t_all t_dyn).

Inductive typing : env -> phi -> exp -> dirflag -> typ -> Prop :=
  | typ_var : forall E P x T,
      wf_env E ->
      binds x (bind_typ T) E ->
      typing E P (e_fvar x) Inf T
  | typ_nat : forall E P i,
      wf_env E ->
      typing E P (e_lit i) Inf (t_int)
  | typ_unit : forall E P,
      wf_env E ->
      typing E P e_unit Inf t_unit
  | typ_loc : forall E P l,
       wf_env E ->
      l < length P ->
      wf_typ E (store_Tlookup l P) ->
      typing E P (e_loc l) Inf (t_ref (store_Tlookup l P))
  | typ_app : forall E P e1 e2 A1 A B,
      pattern_abs A1 (t_arrow A B) ->
      typing E P e1 Inf A1 ->
      typing E P e2 Chk A ->
      typing E P (e_app e1 e2) Inf B
  | typ_abs : forall L E P A B e,
      (forall x, x \notin L ->
            typing (x ~ bind_typ A ++ E) P (e open_ee_var x) Chk B) ->
      typing E P (e_abs A e B) Inf (t_arrow A B)
  | typ_anno : forall E P e A,
     typing E P e Chk A ->
     typing E P (e_anno e A) Inf A
  | typ_tabs : forall E P e A L,
      ( forall a , a \notin  L  ->
      typing  ( a ~tvar ++ E) P ( e open_te_var a )  Chk  ( A open_tt_var a )  )  ->
     typing E P (e_tabs e A) Inf (t_all A)
  | typ_tapp : forall E P e A A1 B,
      wf_typ E A ->
     pattern_all A1 (t_all B) ->
     typing E P e Inf A1 ->
     typing E P (e_tapp e A) Inf  (open_tt B A )
  | typ_consist : forall E P e B A,
     consist E A B ->
     typing E P e Inf A ->
     typing E P e Chk B
  | typ_ref : forall E P e A,
     typing E P e Inf A ->
     typing E P (e_ref e) Inf (t_ref A)
  | typ_get : forall E P e A A1,
     pattern_ref A (t_ref A1) ->
     typing E P e Inf A ->
     typing E P (e_get e) Inf A1
  | typ_set : forall E P e1 e2 A A1,
     pattern_ref A (t_ref A1) ->
     typing E P e1 Inf A ->
     typing E P e2 Chk A1->
     typing E P (e_set e1 e2) Inf t_unit
.

Inductive FL : typ -> Prop :=
 | fl_abs : forall A B,
   FL (t_arrow A B).

Fixpoint principle_type (e : exp) : typ :=
match e with
| (e_anno e A) => A
| _ => t_dyn
end.

Definition store_lookup (n:nat) (st:sto) :=
  nth n st e_unit.

Inductive pvalue : exp -> Prop :=
| pv_unit :
    pvalue e_unit
| pv_int : forall (i5:nat),
    pvalue (e_lit i5)
| pv_arr : forall (A:typ) (e:exp) (B:typ),
    expr (e_abs A e B) ->
    pvalue (e_abs A e B)
| pv_all : forall (e:exp) A,
    expr (e_tabs e A) ->
    pvalue  (e_tabs e A)
| pv_loc : forall l,
    pvalue  (e_loc l).

Inductive value : exp -> Prop :=
| v_anno : forall u A,
    pvalue u ->
    type A ->
    value (e_anno u A).

Inductive sto_ok : sto -> Prop :=
  | sto_ok_empty : sto_ok nil
  | sto_ok_push : forall mu t,
      sto_ok mu -> value t ->
      sto_ok (t :: mu).

Definition sto_typing P mu :=
     sto_ok mu /\
     length P = length mu /\
     (forall l, l < length mu ->
      typing empty P (store_lookup l mu) Inf (store_Tlookup l P)).

Notation "P |== mu" := (sto_typing P mu) (at level 68).

Inductive ptype : sto -> exp -> typ -> Prop :=
| pt_int : forall mu (i5:nat),
    ptype mu (e_lit i5) t_int
| pt_unit : forall mu,
    ptype mu e_unit t_unit
| pt_arr : forall mu (A:typ) (e:exp) (B:typ),
    expr (e_abs A e B) ->
    ptype mu ( (e_abs A e B) )  (t_arrow A B)
| pt_loc : forall l A mu,
    principle_type (store_lookup l mu) = A ->
    ptype mu (e_loc l) (t_ref A)
| pt_anno : forall (u:exp) (A:typ) mu,
    expr u ->
    ptype mu (e_anno u A) A
| pt_all : forall mu (e:exp) (A:typ),
    expr (e_tabs e A) ->
    ptype mu (e_tabs e A)  (t_all A).

Inductive svalue : exp -> Prop :=
| sv_arr : forall (A:typ) (e:exp) (B:typ),
    expr (e_abs A e B) ->
    svalue (e_abs A e B)
.

Inductive ssvalue : exp -> Prop :=
| sv_int : forall (i5:nat),
    ssvalue (e_lit i5)
| sv_all : forall (e:exp) A,
    expr (e_tabs e A) ->
    ssvalue  (e_tabs e A)
| sv_loc : forall l,
    ssvalue  (e_loc l)
| sv_unit :
    ssvalue  (e_unit)
.

Inductive res : Set :=
 | r_e (e:exp)
 | r_blame.

Definition conf := (exp * sto)%type.

Definition confr := (res * sto)%type.

Inductive TypedReduce : conf -> typ -> confr -> Prop :=
 | TReduce_sim : forall mu u A B C,
     pvalue u ->
     ptype mu u C ->
     consist  nil  C B ->
     TypedReduce ((e_anno u A),mu) B ((r_e (e_anno u B)),mu)
 | TReduce_nsim : forall (u:exp) (A B:typ) (C:typ) mu,
      pvalue u ->
     ptype mu u C ->
      not (  consist  nil  C B  )  ->
     TypedReduce ((e_anno u A),mu) B (r_blame,mu)
.

Definition ltyp : Set := list typ.

Inductive TypeLists : conf -> ltyp -> confr -> Prop :=
 | TLists_nil : forall v mu,
     TypeLists (v,mu)  nil ((r_e v),mu)
 | TLists_baseb : forall (v:exp) (AA:ltyp) (A:typ) mu,
     TypedReduce (v,mu) A (r_blame,mu) ->
     TypeLists (v,mu)  (cons  A   AA ) (r_blame,mu)
 | TLists_cons : forall (v:exp) (AA:ltyp) (A:typ) (v':exp) r mu,
     TypedReduce (v,mu) A ((r_e v'),mu) ->
     TypeLists (v',mu) AA (r,mu) ->
     TypeLists (v,mu)  (cons A AA ) (r,mu)
.

Inductive ctx_item : Type :=
  | appCtxL : exp -> ctx_item
  | appCtxR : exp -> ctx_item
  | tappCtx : typ -> ctx_item
  | refCtx :  ctx_item
  | getCtx : ctx_item
  | setCtxL : exp -> ctx_item
  | setCtxR : exp -> ctx_item
.

Inductive wellformed : ctx_item -> Prop :=
     | wf_appCtxL : forall (e : exp),
                    expr e ->
                    wellformed (appCtxL e)
     | wf_appCtxR : forall (v : exp),
                    value v ->
                    wellformed (appCtxR v)
     | wf_tappCtx : forall A,
                    type A ->
                    wellformed (tappCtx A)
     | wf_setCtxL : forall e,
                    expr e ->
                    wellformed (setCtxL e)
     | wf_setCtxR : forall e,
                    value e ->
                    wellformed (setCtxR e)
     | wf_refCtx :
                    wellformed refCtx
     | wf_getCtx :
                    wellformed getCtx
.

Definition fill (E : ctx_item) (e : exp) : exp :=
     match E with
     | appCtxL e2 => e_app e e2
     | appCtxR v1 => e_app v1 e
     | tappCtx A => e_tapp e A
     | setCtxL e2 => e_set e e2
     | setCtxR v1 => e_set v1 e
     | refCtx => e_ref e
     | getCtx => e_get e
     end.

Fixpoint replace {A:Type} (n:nat) (x:A) (l:list A) : list A :=
  match l with
  | nil => nil
  | h :: t =>
    match n with
    | O => x :: t
    | S n' => h :: replace n' x t
    end
  end.

Inductive step : conf -> confr -> Prop :=
 | step_eval : forall mu mu' F e1 e2,
     wellformed F ->
     step (e1, mu) ((r_e e2), mu') ->
     step ((fill F e1), mu) ((r_e (fill F e2)), mu')
  | step_blame : forall F e mu mu',
     wellformed F ->
     step (e, mu) (r_blame, mu') ->
     step ((fill F e), mu) (r_blame, mu')
  | step_annop : forall (e:exp) (A:typ) mu mu',
     step (e, mu) (r_blame, mu') ->
     not(value (e_anno e A)) ->
     step ((e_anno e A), mu)  (r_blame, mu')
  | step_beta : forall A (A1:typ) (e:exp) (B1 A2 B2:typ) (v v':exp) mu,
     sto_ok mu ->
     value v ->
     expr (e_abs A1 e B1) ->
     pattern_abs A  (t_arrow A2 B2) ->
     TypeLists (v, mu)  (cons A2 (cons A1 nil)) ((r_e v'), mu) ->
     step ((e_app  ( (e_anno  ( (e_abs A1 e B1) )  A) )  v), mu) ((r_e (e_anno (e_anno  (open_ee  e v' )  B1) B2)), mu)
 | step_betap : forall (A1:typ) (e:exp) A (B1 A2 B2:typ) (v :exp) mu,
     sto_ok mu ->
     value v ->
     expr (e_abs A1 e B1) ->
     pattern_abs A  (t_arrow A2 B2) ->
     TypeLists (v, mu) (cons A2 (cons A1 nil)) (r_blame, mu) ->
     step ((e_app ((e_anno  ( (e_abs A1 e B1) ) A)) v), mu) (r_blame, mu)
 | step_betadp : forall p (v :exp) mu,
     sto_ok mu ->
     value v ->
     TypedReduce  ((e_anno p t_dyn),mu) (t_arrow t_dyn t_dyn) (r_blame,mu) ->
     pvalue p ->
     step ((e_app ((e_anno p t_dyn)) v), mu) (r_blame, mu)
 | step_u : forall (u:exp) (A:typ) mu,
     sto_ok mu ->
     pvalue u ->
     ptype mu u A ->
     step (u, mu) ((r_e (e_anno u A)), mu)
 | step_anno : forall (e:exp) (A:typ) (e':exp) mu mu',
     not(value (e_anno e A)) ->
     step (e, mu) ((r_e e'), mu') ->
     step ((e_anno e A), mu) ((r_e (e_anno e' A)), mu')
 | step_annov : forall (v:exp) (A:typ) r mu,
     sto_ok mu ->
     value v ->
     TypedReduce (v, mu) A (r, mu) ->
     step ((e_anno v A), mu) (r, mu)
 | step_tap : forall (e:exp) B1 (A B C:typ) mu,
     expr (e_anno  (e_tabs e A) (t_all B)) ->
     pattern_all B1 (t_all B) ->
     step ((e_tapp (e_anno  (e_tabs e A) B1) C),mu) ((r_e (e_anno (e_anno (open_te  e C ) (open_tt  A C )) (open_tt  B C ))),mu)
 | step_tappd : forall (u:exp) B mu,
     type B ->
     pvalue u ->
     TypedReduce ((e_anno u t_dyn),mu) (t_all t_dyn) (r_blame,mu) ->
     step ((e_tapp  (e_anno u t_dyn)  B),mu) (r_blame,mu)
 | step_set : forall l A1 A B v2 v2' mu,
     sto_ok mu ->
     value v2 ->
     principle_type (store_lookup l mu) = B ->
     TypeLists (v2, mu) (cons A (cons B nil)) (r_e v2', mu) ->
     pattern_ref A1 (t_ref A) ->
     step ((e_set (e_anno (e_loc l) A1) v2), mu) ((r_e e_unit), replace l v2' mu)
 | step_setp : forall l A1 A B v2 mu,
     sto_ok mu ->
     value v2 ->
     principle_type (store_lookup l mu) = B ->
     TypeLists (v2, mu) (cons A (cons B nil)) (r_blame, mu) ->
     pattern_ref A1 (t_ref A) ->
     step ((e_set (e_anno (e_loc l) A1) v2), mu) (r_blame, mu)
 | step_setd : forall u v2 mu,
     sto_ok mu ->
     value v2 ->
     pvalue u ->
     TypedReduce ((e_anno u t_dyn),mu) (t_ref t_dyn) (r_blame, mu) ->
     step ((e_set (e_anno u t_dyn) v2), mu) (r_blame, mu)
 | step_new : forall (v:exp) mu,
     sto_ok mu ->
     value v ->
     step ((e_ref v), mu) ((r_e (e_loc (length mu))), (mu ++ v::nil))
 | step_get : forall A1 (A:typ) l mu,
     sto_ok mu ->
     pattern_ref A1 (t_ref A) ->
     step ((e_get (e_anno (e_loc l) A1)), mu) ((r_e (e_anno (store_lookup l mu) A)), mu)
 | step_getd : forall u mu,
     sto_ok mu ->
     pvalue u ->
     TypedReduce ((e_anno u t_dyn),mu) (t_ref t_dyn) (r_blame,mu) ->
     step ((e_get (e_anno u t_dyn)), mu) (r_blame,mu)
.

Inductive extends : phi -> phi -> Prop :=
  | extends_nil : forall ST',
      extends ST' nil
  | extends_cons : forall x ST' ST,
      extends ST' ST ->
      extends (x::ST') (x::ST).
