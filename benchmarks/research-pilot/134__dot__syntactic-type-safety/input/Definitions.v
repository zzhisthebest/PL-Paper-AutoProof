Set Implicit Arguments.

Require Import TLC.LibLN.

Require Import String.

Require Export TLC.LibLN.

Parameter typ_label: Set.

Parameter trm_label: Set.

Inductive avar : Set :=
  | avar_b : nat -> avar
  | avar_f : var -> avar.

Inductive label: Set :=
| label_typ: typ_label -> label
| label_trm: trm_label -> label.

Inductive typ : Set :=
  | typ_top  : typ
  | typ_bot  : typ
  | typ_rcd  : dec -> typ
  | typ_and  : typ -> typ -> typ
  | typ_sel  : avar -> typ_label -> typ
  | typ_bnd  : typ -> typ
  | typ_all  : typ -> typ -> typ



with dec : Set :=
  | dec_typ  : typ_label -> typ -> typ -> dec
  | dec_trm  : trm_label -> typ -> dec.

Inductive trm : Set :=
  | trm_var  : avar -> trm
  | trm_val  : val -> trm
  | trm_sel  : avar -> trm_label -> trm
  | trm_app  : avar -> avar -> trm
  | trm_let  : trm -> trm -> trm







with val : Set :=
  | val_new  : typ -> defs -> val
  | val_lambda : typ -> trm -> val



with def : Set :=
  | def_typ  : typ_label -> typ -> def
  | def_trm  : trm_label -> trm -> def




with defs : Set :=
  | defs_nil : defs
  | defs_cons : defs -> def -> defs.

Definition label_of_def(d: def): label := match d with
| def_typ L _ => label_typ L
| def_trm m _ => label_trm m
end.

Definition label_of_dec(D: dec): label := match D with
| dec_typ L _ _ => label_typ L
| dec_trm m _   => label_trm m
end.

Fixpoint get_def(l: label)(ds: defs): option def :=
match ds with
| defs_nil => None
| defs_cons ds' d => If label_of_def d = l then Some d else get_def l ds'
end.

Definition defs_has(ds: defs)(d: def) := get_def (label_of_def d) ds = Some d.

Definition defs_hasnt(ds: defs)(l: label) := get_def l ds = None.

Definition ctx := env typ.

Definition sta := env val.

Definition open_rec_avar (k: nat) (u: var) (a: avar) : avar :=
  match a with
  | avar_b i => If k = i then avar_f u else avar_b i
  | avar_f x => avar_f x
  end.

Fixpoint open_rec_typ (k: nat) (u: var) (T: typ): typ :=
  match T with
  | typ_top        => typ_top
  | typ_bot        => typ_bot
  | typ_rcd D      => typ_rcd (open_rec_dec k u D)
  | typ_and T1 T2  => typ_and (open_rec_typ k u T1) (open_rec_typ k u T2)
  | typ_sel x L    => typ_sel (open_rec_avar k u x) L
  | typ_bnd T      => typ_bnd (open_rec_typ (S k) u T)
  | typ_all T1 T2  => typ_all (open_rec_typ k u T1) (open_rec_typ (S k) u T2)
  end
with open_rec_dec (k: nat) (u: var) (D: dec): dec :=
  match D with
  | dec_typ L T U => dec_typ L (open_rec_typ k u T) (open_rec_typ k u U)
  | dec_trm m T   => dec_trm m (open_rec_typ k u T)
  end.

Fixpoint open_rec_trm (k: nat) (u: var) (t: trm): trm :=
  match t with
  | trm_var a      => trm_var (open_rec_avar k u a)
  | trm_val v      => trm_val (open_rec_val k u v)
  | trm_sel v m    => trm_sel (open_rec_avar k u v) m
  | trm_app f a    => trm_app (open_rec_avar k u f) (open_rec_avar k u a)
  | trm_let t1 t2  => trm_let (open_rec_trm k u t1) (open_rec_trm (S k) u t2)
  end
with open_rec_val (k: nat) (u: var) (v: val): val :=
  match v with
  | val_new T ds   => val_new (open_rec_typ (S k) u T) (open_rec_defs (S k) u ds)
  | val_lambda T e => val_lambda (open_rec_typ k u T) (open_rec_trm (S k) u e)
  end
with open_rec_def (k: nat) (u: var) (d: def): def :=
  match d with
  | def_typ L T => def_typ L (open_rec_typ k u T)
  | def_trm m e => def_trm m (open_rec_trm k u e)
  end
with open_rec_defs (k: nat) (u: var) (ds: defs): defs :=
  match ds with
  | defs_nil       => defs_nil
  | defs_cons tl d => defs_cons (open_rec_defs k u tl) (open_rec_def k u d)
  end.

Definition open_avar u a := open_rec_avar  0 u a.

Definition open_typ  u T := open_rec_typ   0 u T.

Definition open_dec  u D := open_rec_dec   0 u D.

Definition open_trm  u e := open_rec_trm   0 u e.

Definition open_val  u v := open_rec_val   0 u v.

Definition open_def  u d := open_rec_def   0 u d.

Definition open_defs u l := open_rec_defs  0 u l.

Definition fv_avar (a: avar) : vars :=
  match a with
  | avar_b i => \{}
  | avar_f x => \{x}
  end.

Fixpoint fv_typ (T: typ) : vars :=
  match T with
  | typ_top        => \{}
  | typ_bot        => \{}
  | typ_rcd D      => (fv_dec D)
  | typ_and T U    => (fv_typ T) \u (fv_typ U)
  | typ_sel x L    => (fv_avar x)
  | typ_bnd T      => (fv_typ T)
  | typ_all T1 T2  => (fv_typ T1) \u (fv_typ T2)
  end
with fv_dec (D: dec) : vars :=
  match D with
  | dec_typ L T U => (fv_typ T) \u (fv_typ U)
  | dec_trm m T   => (fv_typ T)
  end.

Fixpoint fv_trm (t: trm) : vars :=
  match t with
  | trm_var a       => (fv_avar a)
  | trm_val v        => (fv_val v)
  | trm_sel x m      => (fv_avar x)
  | trm_app f a      => (fv_avar f) \u (fv_avar a)
  | trm_let t1 t2    => (fv_trm t1) \u (fv_trm t2)
  end
with fv_val (v: val) : vars :=
  match v with
  | val_new T ds    => (fv_typ T) \u (fv_defs ds)
  | val_lambda T e  => (fv_typ T) \u (fv_trm e)
  end
with fv_def (d: def) : vars :=
  match d with
  | def_typ _ T     => (fv_typ T)
  | def_trm _ t     => (fv_trm t)
  end
with fv_defs(ds: defs) : vars :=
  match ds with
  | defs_nil         => \{}
  | defs_cons tl d   => (fv_defs tl) \u (fv_def d)
  end.

Definition fv_ctx_types(G: ctx): vars := (fv_in_values (fun T => fv_typ T) G).

Definition fv_sta_vals(s: sta): vars := (fv_in_values (fun v => fv_val v) s).

Reserved Notation "G '⊢' t ':' T" (at level 40, t at level 59).

Reserved Notation "G '⊢' T '<:' U" (at level 40, T at level 59).

Reserved Notation "G '/-' d : D" (at level 40, d at level 59).

Reserved Notation "G '/-' ds :: D" (at level 40, ds at level 59).

Inductive ty_trm : ctx -> trm -> typ -> Prop :=




| ty_var : forall G x T,
    binds x T G ->
    G ⊢ trm_var (avar_f x) : T





| ty_all_intro : forall L G T t U,
    (forall x, x \notin L ->
      G & x ~ T ⊢ open_trm x t : open_typ x U) ->
    G ⊢ trm_val (val_lambda T t) : typ_all T U





| ty_all_elim : forall G x z S T,
    G ⊢ trm_var (avar_f x) : typ_all S T ->
    G ⊢ trm_var (avar_f z) : S ->
    G ⊢ trm_app (avar_f x) (avar_f z) : open_typ z T





| ty_new_intro : forall L G T ds,
    (forall x, x \notin L ->
      G & (x ~ open_typ x T) /- open_defs x ds :: open_typ x T) ->
    G ⊢ trm_val (val_new T ds) : typ_bnd T




| ty_new_elim : forall G x a T,
    G ⊢ trm_var (avar_f x) : typ_rcd (dec_trm a T) ->
    G ⊢ trm_sel (avar_f x) a : T






| ty_let : forall L G t u T U,
    G ⊢ t : T ->
    (forall x, x \notin L ->
      G & x ~ T ⊢ open_trm x u : U) ->
    G ⊢ trm_let t u : U




| ty_rec_intro : forall G x T,
    G ⊢ trm_var (avar_f x) : open_typ x T ->
    G ⊢ trm_var (avar_f x) : typ_bnd T




| ty_rec_elim : forall G x T,
    G ⊢ trm_var (avar_f x) : typ_bnd T ->
    G ⊢ trm_var (avar_f x) : open_typ x T





| ty_and_intro : forall G x T U,
    G ⊢ trm_var (avar_f x) : T ->
    G ⊢ trm_var (avar_f x) : U ->
    G ⊢ trm_var (avar_f x) : typ_and T U





| ty_sub : forall G t T U,
    G ⊢ t : T ->
    G ⊢ T <: U ->
    G ⊢ t : U
where "G '⊢' t ':' T" := (ty_trm G t T)


with ty_def : ctx -> def -> dec -> Prop :=

| ty_def_typ : forall G A T,
    G /- def_typ A T : dec_typ A T T




| ty_def_trm : forall G a t T,
    G ⊢ t : T ->
    G /- def_trm a t : dec_trm a T
where "G '/-' d ':' D" := (ty_def G d D)


with ty_defs : ctx -> defs -> typ -> Prop :=



| ty_defs_one : forall G d D,
    G /- d : D ->
    G /- defs_cons defs_nil d :: typ_rcd D






| ty_defs_cons : forall G ds d T D,
    G /- ds :: T ->
    G /- d : D ->
    defs_hasnt ds (label_of_def d) ->
    G /- defs_cons ds d :: typ_and T (typ_rcd D)
where "G '/-' ds '::' T" := (ty_defs G ds T)


with subtyp : ctx -> typ -> typ -> Prop :=


| subtyp_top: forall G T,
    G ⊢ T <: typ_top


| subtyp_bot: forall G T,
    G ⊢ typ_bot <: T


| subtyp_refl: forall G T,
    G ⊢ T <: T





| subtyp_trans: forall G S T U,
    G ⊢ S <: T ->
    G ⊢ T <: U ->
    G ⊢ S <: U


| subtyp_and11: forall G T U,
    G ⊢ typ_and T U <: T


| subtyp_and12: forall G T U,
    G ⊢ typ_and T U <: U





| subtyp_and2: forall G S T U,
    G ⊢ S <: T ->
    G ⊢ S <: U ->
    G ⊢ S <: typ_and T U




| subtyp_fld: forall G a T U,
    G ⊢ T <: U ->
    G ⊢ typ_rcd (dec_trm a T) <: typ_rcd (dec_trm a U)





| subtyp_typ: forall G A S1 T1 S2 T2,
    G ⊢ S2 <: S1 ->
    G ⊢ T1 <: T2 ->
    G ⊢ typ_rcd (dec_typ A S1 T1) <: typ_rcd (dec_typ A S2 T2)




| subtyp_sel2: forall G x A S T,
    G ⊢ trm_var (avar_f x) : typ_rcd (dec_typ A S T) ->
    G ⊢ S <: typ_sel (avar_f x) A




| subtyp_sel1: forall G x A S T,
    G ⊢ trm_var (avar_f x) : typ_rcd (dec_typ A S T) ->
    G ⊢ typ_sel (avar_f x) A <: T






| subtyp_all: forall L G S1 T1 S2 T2,
    G ⊢ S2 <: S1 ->
    (forall x, x \notin L ->
       G & x ~ S2 ⊢ open_typ x T1 <: open_typ x T2) ->
    G ⊢ typ_all S1 T1 <: typ_all S2 T2
where "G '⊢' T '<:' U" := (subtyp G T U).

Definition well_typed (G : ctx) (s : sta) : Prop :=
  ok G /\
  ok s /\
  (dom G = dom s) /\
  (forall x T v, binds x T G ->
            binds x v s ->
            G ⊢ trm_val v : T).

Scheme typ_mut := Induction for typ Sort Prop
with   dec_mut := Induction for dec Sort Prop.

Combined Scheme typ_mutind from typ_mut, dec_mut.

Scheme trm_mut  := Induction for trm  Sort Prop
with   val_mut  := Induction for val Sort Prop
with   def_mut  := Induction for def  Sort Prop
with   defs_mut := Induction for defs Sort Prop.

Combined Scheme trm_mutind from trm_mut, val_mut, def_mut, defs_mut.

Scheme ts_ty_trm_mut := Induction for ty_trm Sort Prop
with   ts_subtyp     := Induction for subtyp Sort Prop.

Combined Scheme ts_mutind from ts_ty_trm_mut, ts_subtyp.

Scheme rules_trm_mut    := Induction for ty_trm Sort Prop
with   rules_def_mut    := Induction for ty_def Sort Prop
with   rules_defs_mut   := Induction for ty_defs Sort Prop
with   rules_subtyp     := Induction for subtyp Sort Prop.

Combined Scheme rules_mutind from rules_trm_mut, rules_def_mut, rules_defs_mut, rules_subtyp.

Open Scope string_scope.
