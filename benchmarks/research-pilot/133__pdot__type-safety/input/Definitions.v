Set Implicit Arguments.

Require Export TLC.LibLN.

Require Import TLC.LibOption.

Require Import List String.

Parameter typ_label: Set.

Parameter trm_label: Set.

Inductive avar : Set :=
  | avar_b : nat -> avar
  | avar_f : var -> avar.

Inductive label: Set :=
| label_typ: typ_label -> label
| label_trm: trm_label -> label.

Definition fields := list trm_label.

Inductive path :=
  | p_sel : avar -> fields ->  path.

Inductive typ : Set :=
  | typ_top  : typ
  | typ_bot  : typ
  | typ_rcd  : dec -> typ
  | typ_and  : typ -> typ -> typ
  | typ_path : path -> typ_label -> typ
  | typ_bnd  : typ -> typ
  | typ_all  : typ -> typ -> typ
  | typ_sngl : path -> typ



with dec : Set :=
  | dec_typ  : typ_label -> typ -> typ -> dec
  | dec_trm  : trm_label -> typ -> dec.

Inductive trm : Set :=
  | trm_val  : val -> trm
  | trm_app  : path -> path -> trm
  | trm_let  : trm -> trm -> trm
  | trm_path : path -> trm







with val : Set :=
  | val_new  : typ -> defs -> val
  | val_lambda : typ -> trm -> val



with def : Set :=
  | def_typ  : typ_label -> typ -> def
  | def_trm  : trm_label -> def_rhs -> def




with defs : Set :=
  | defs_nil : defs
  | defs_cons : defs -> def -> defs

with def_rhs : Set :=
  | defp : path -> def_rhs
  | defv : val -> def_rhs.

Notation "'{' a '⦂' T '}'" := (dec_trm a T) (T at level 50).

Notation "'{' A '>:' S '<:' T '}'" := (dec_typ A S T) (S at level 58).

Notation "T '∧' U" := (typ_and T U) (at level 30).

Notation "'∀' '(' T ')' U" := (typ_all T U) (at level 30).

Notation "p '↓' A" := (typ_path p A) (at level 30).

Notation "'μ' T" := (typ_bnd T) (at level 30, T at level 50).

Notation "⊤" := typ_top.

Notation "⊥" := typ_bot.

Notation "'{{' p '}}'" := (typ_sngl p).

Notation "'ν' '(' T ')' ds" := (val_new T ds) (at level 40, T at level 40, ds at level 40).

Notation "'λ' '(' T ')' t" := (val_lambda T t) (at level 50).

Notation "'{' a ':=' t '}'" := (def_trm a t) (t at level 50).

Notation "'{' a ':=p' p '}'" := (def_trm a (defp p)).

Notation "'{' a ':=v' v '}'" := (def_trm a (defv v)).

Notation "'{' A '⦂=' T '}'" := (def_typ A T).

Notation pvar x := (p_sel (avar_f x) nil).

Notation  tvar x := (trm_path (pvar x)).

Definition sel_field (p : path) (b : trm_label) :=
  match p with
  | p_sel x bs => p_sel x (b :: bs)
  end.

Definition sel_fields (p : path) (bs : list trm_label) :=
  match p with
  | p_sel x bs' => p_sel x (bs ++ bs')
  end.

Notation "p '•' a" := (sel_field p a) (at level 5).

Notation "p '••' bs" := (sel_fields p bs) (at level 5).

Definition label_of_def(d: def): label := match d with
| def_typ A _ => label_typ A
| { a := t }  => label_trm a
end.

Definition label_of_dec(D: dec): label := match D with
| { A >: _ <: _ } => label_typ A
| { a ⦂ _ }  => label_trm a
end.

Fixpoint get_def(l: label)(ds: defs): option def :=
match ds with
| defs_nil => None
| defs_cons ds' d => If label_of_def d = l then Some d else get_def l ds'
end.

Definition defs_has(ds: defs)(d: def) := get_def (label_of_def d) ds = Some d.

Definition defs_hasnt(ds: defs)(l: label) := get_def l ds = None.

Definition open_rec_avar (k: nat) (u: var) (a: avar) : avar :=
  match a with
  | avar_b i => If k = i then avar_f u else avar_b i
  | avar_f x => avar_f x
end.

Definition open_rec_path (k: nat) (u: var) (p: path): path :=
  match p with
  | p_sel x bs => p_sel (open_rec_avar k u x) bs
  end.

Fixpoint open_rec_typ (k: nat) (u: var) (T: typ): typ :=
  match T with
  | typ_top        => typ_top
  | typ_bot        => typ_bot
  | typ_rcd D      => typ_rcd (open_rec_dec k u D)
  | T1 ∧ T2        => open_rec_typ k u T1 ∧ open_rec_typ k u T2
  | p ↓ L          => open_rec_path k u p ↓ L
  | μ T            => μ (open_rec_typ (S k) u T)
  | ∀(T1) T2      => ∀(open_rec_typ k u T1) open_rec_typ (S k) u T2
  | {{ p }}        => {{ open_rec_path k u p }}
  end
with open_rec_dec (k: nat) (u: var) (D: dec): dec :=
  match D with
  | { A >: T <: U } => { A >: open_rec_typ k u T <: open_rec_typ k u U }
  | { a ⦂ T } => { a ⦂ open_rec_typ k u T }
  end.

Fixpoint open_rec_trm (k: nat) (u: var) (t: trm): trm :=
  match t with
  | trm_val v      => trm_val (open_rec_val k u v)
  | trm_path p     => trm_path (open_rec_path k u p)
  | trm_app p q    => trm_app (open_rec_path k u p) (open_rec_path k u q)
  | trm_let t1 t2  => trm_let (open_rec_trm k u t1) (open_rec_trm (S k) u t2)
  end
with open_rec_val (k: nat) (u: var) (v: val): val :=
  match v with
  | ν(T)ds   => ν (open_rec_typ (S k) u T) open_rec_defs (S k) u ds
  | λ(T) e  => λ(open_rec_typ k u T) open_rec_trm (S k) u e
  end
with open_rec_def (k: nat) (u: var) (d: def): def :=
  match d with
  | def_typ A T => def_typ A (open_rec_typ k u T)
  | { a := t } => { a := open_rec_defrhs k u t }
  end
with open_rec_defs (k: nat) (u: var) (ds: defs): defs :=
  match ds with
  | defs_nil => defs_nil
  | defs_cons tl d => defs_cons (open_rec_defs k u tl) (open_rec_def k u d)
  end
with open_rec_defrhs (k: nat) (u: var) (drhs: def_rhs) : def_rhs :=
  match drhs with
  | defp p => defp (open_rec_path k u p)
  | defv v => defv (open_rec_val k u v)
  end.

Definition open_avar u a := open_rec_avar  0 u a.

Definition open_typ  u t := open_rec_typ   0 u t.

Definition open_dec  u D := open_rec_dec   0 u D.

Definition open_trm  u e := open_rec_trm   0 u e.

Definition open_val  u v := open_rec_val   0 u v.

Definition open_def  u d := open_rec_def   0 u d.

Definition open_defs u l := open_rec_defs  0 u l.

Definition open_defrhsdd u t := open_rec_defrhs 0 u t.

Definition open_path u p := open_rec_path  0 u p.

Definition open_paths u ps := map (open_path u) ps.

Definition open_rec_avar_p (k: nat) (u: path) (a: avar) : path :=
  match a with
  | avar_b i => If k = i then u else p_sel (avar_b i) nil
  | avar_f x => pvar x
  end.

Definition open_rec_path_p (k: nat) (u: path) (p: path): path :=
  match p, u with
  | p_sel x bs, p_sel y cs=>
    match x with
    | avar_b i => If k = i then p_sel y (bs ++ cs) else p
    | avar_f x => p
    end
  end.

Fixpoint open_rec_typ_p (k: nat) (u: path) (T: typ): typ :=
  match T with
  | typ_top        => typ_top
  | typ_bot        => typ_bot
  | typ_rcd D      => typ_rcd (open_rec_dec_p k u D)
  | T1 ∧ T2        => open_rec_typ_p k u T1 ∧ open_rec_typ_p k u T2
  | p ↓ L          => open_rec_path_p k u p ↓ L
  | μ       T      => μ (open_rec_typ_p (S k) u T)
  | ∀(T1) T2       => ∀(open_rec_typ_p k u T1) open_rec_typ_p (S k) u T2
  | {{ p }}        => {{ open_rec_path_p k u p }}
  end
with open_rec_dec_p (k: nat) (u: path) (D: dec): dec :=
  match D with
  | { A >: T <: U } => { A >: open_rec_typ_p k u T <: open_rec_typ_p k u U }
  | { a ⦂ T } => { a ⦂ open_rec_typ_p k u T }
  end.

Fixpoint open_rec_trm_p (k: nat) (u: path) (t: trm): trm :=
  match t with
  | trm_val v      => trm_val (open_rec_val_p k u v)
  | trm_path p     => trm_path (open_rec_path_p k u p)
  | trm_app p q    => trm_app (open_rec_path_p k u p) (open_rec_path_p k u q)
  | trm_let t1 t2  => trm_let (open_rec_trm_p k u t1) (open_rec_trm_p (S k) u t2)
  end
with open_rec_val_p (k: nat) (u: path) (v: val): val :=
  match v with
  | ν(T) ds => ν(open_rec_typ_p (S k) u T) open_rec_defs_p (S k) u ds
  | λ(T) e  => λ(open_rec_typ_p k u T) open_rec_trm_p (S k) u e
  end
with open_rec_def_p (k: nat) (u: path) (d: def): def :=
  match d with
  | def_typ L T => def_typ L (open_rec_typ_p k u T)
  | { a := t } => { a := open_rec_defrhs_p k u t }
  end
with open_rec_defs_p (k: nat) (u: path) (ds: defs): defs :=
  match ds with
  | defs_nil => defs_nil
  | defs_cons tl d => defs_cons (open_rec_defs_p k u tl) (open_rec_def_p k u d)
  end
with open_rec_defrhs_p (k: nat) (u: path) (drhs: def_rhs) : def_rhs :=
  match drhs with
  | defp p => defp (open_rec_path_p k u p)
  | defv v => defv (open_rec_val_p k u v)
  end.

Definition open_avar_p u a := open_rec_avar_p  0 u a.

Definition open_typ_p  u t := open_rec_typ_p   0 u t.

Definition open_dec_p  u D := open_rec_dec_p   0 u D.

Definition open_path_p u p := open_rec_path_p  0 u p.

Definition open_trm_p  u t := open_rec_trm_p   0 u t.

Definition open_val_p  u v := open_rec_val_p   0 u v.

Definition open_def_p  u d := open_rec_def_p   0 u d.

Definition open_defs_p u l := open_rec_defs_p 0 u l.

Definition open_defrhs_p u t := open_rec_defrhs_p 0 u t.

Inductive repl_typ : path -> path -> typ -> typ -> Prop :=
| rrcd: forall p q D1 D2,
    repl_dec p q D1 D2 ->
    repl_typ p q (typ_rcd D1) (typ_rcd D2)
| rand1: forall p q T1 T2 U,
    repl_typ p q T1 T2 ->
    repl_typ p q (T1 ∧ U) (T2 ∧ U)
| rand2: forall p q T1 T2 U,
    repl_typ p q T1 T2 ->
    repl_typ p q (U ∧ T1) (U ∧ T2)
| rpath: forall p q bs A,
    repl_typ p q (p••bs ↓ A) (q••bs ↓ A)
| rbnd: forall p q T1 T2,
    repl_typ p q T1 T2 ->
    repl_typ p q (μ T1) (μ T2)
| rall1: forall p q T1 T2 U,
    repl_typ p q T1 T2 ->
    repl_typ p q (∀(T1) U) (∀(T2) U)
| rall2: forall p q T1 T2 U,
    repl_typ p q T1 T2 ->
    repl_typ p q (∀(U) T1) (∀(U) T2)
| rsngl: forall p q bs,
    repl_typ p q {{ p••bs }} {{ q••bs }}
with repl_dec : path -> path -> dec -> dec -> Prop :=
| rdtyp1: forall p q T1 T2 A U,
    repl_typ p q T1 T2 ->
    repl_dec p q {A >: T1 <: U} {A >: T2 <: U}
| rdtyp2: forall p q T1 T2 A U,
    repl_typ p q T1 T2 ->
    repl_dec p q {A >: U <: T1} {A >: U <: T2}
| rdtrm: forall p q T1 T2 a,
    repl_typ p q T1 T2 ->
    repl_dec p q {a ⦂ T1} {a ⦂ T2}.

Definition fv_avar (a: avar) : vars :=
  match a with
  | avar_b i => \{}
  | avar_f x => \{x}
  end.

Fixpoint fv_path (p: path) : vars :=
  match p with
  | p_sel x bs => fv_avar x
  end.

Fixpoint fv_typ (T: typ) : vars :=
  match T with
  | typ_top        => \{}
  | typ_bot        => \{}
  | typ_rcd D      => fv_dec D
  | T ∧ U          => (fv_typ T) \u (fv_typ U)
  | p ↓ L          => fv_path p
  | μ T            => fv_typ T
  | ∀(T1) T2       => (fv_typ T1) \u (fv_typ T2)
  | {{ p }}        => fv_path p
  end
with fv_dec (D: dec) : vars :=
  match D with
  | { A >: T <: U } => (fv_typ T) \u (fv_typ U)
  | { a ⦂ T } => fv_typ T
  end.

Fixpoint fv_trm (t: trm) : vars :=
  match t with
  | trm_val v        => (fv_val v)
  | trm_path p       => (fv_path p)
  | trm_app p q      => (fv_path p) \u (fv_path q)
  | trm_let t1 t2    => (fv_trm t1) \u (fv_trm t2)
  end
with fv_val (v: val) : vars :=
  match v with
  | ν(T) ds    => (fv_typ T) \u (fv_defs ds)
  | λ(T)t      => (fv_typ T) \u (fv_trm t)
  end
with fv_def (d: def) : vars :=
  match d with
  | def_typ _ T => (fv_typ T)
  | { _ := t }  => (fv_defrhs t)
  end
with fv_defs(ds: defs) : vars :=
  match ds with
  | defs_nil         => \{}
  | defs_cons tl d   => (fv_defs tl) \u (fv_def d)
  end
with fv_defrhs(drhs: def_rhs) : vars :=
  match drhs with
  | defp p => fv_path p
  | defv v => fv_val v
  end.

Definition ctx := env typ.

Definition sta := env val.

Definition fv_ctx_types(G: ctx): vars :=
  (fv_in_values (fun T => fv_typ T) G).

Definition fv_sta_vals(s: sta): vars := (fv_in_values (fun v => fv_val v) s).

Inductive record_dec : dec -> Prop :=
| rd_typ : forall A T, record_dec { A >: T <: T }
| rd_trm : forall a T, inert_typ T -> record_dec { a ⦂ T }
| rd_trm_sngl : forall a p, record_dec { a ⦂ {{ p }} }





with record_typ : typ -> fset label -> Prop :=
| rt_one : forall D l,
  record_dec D ->
  l = label_of_dec D ->
  record_typ (typ_rcd D) \{l}
| rt_cons: forall T ls D l,
  record_typ T ls ->
  record_dec D ->
  l = label_of_dec D ->
  l \notin ls ->
  record_typ (T ∧ typ_rcd D) (union ls \{l})















with inert_typ : typ -> Prop :=
  | inert_typ_all : forall S T, inert_typ (∀(S) T)
  | inert_typ_bnd : forall T ls,
      record_typ T ls ->
      inert_typ (μ T).

Inductive record_has: typ -> dec -> Prop :=
| rh_one : forall D,
    record_has (typ_rcd D) D
| rh_andl : forall T U D,
    record_has T D ->
    record_has (T ∧ U) D
| rh_andr : forall T U D,
    record_has U D ->
    record_has (T ∧ U) D.

Definition record_type T := exists ls, record_typ T ls.

Inductive inert : ctx -> Prop :=
  | inert_empty : inert empty
  | inert_push : forall G x T,
      inert G ->
      inert_typ T ->
      x # G ->
      inert (G & x ~ T).

Fixpoint tight_bounds T :=
  match T with
  | typ_rcd D => tight_bounds_dec D
  | U ∧ V     => tight_bounds U /\ tight_bounds V
  | typ_bnd U => tight_bounds U
  | _         => True
  end
with tight_bounds_dec D :=
  match D with
  | { a ⦂ T }       => tight_bounds T
  | { A >: T <: U } => T = U
  end.

Reserved Notation "G '⊢' t ':' T" (at level 40, t at level 59).

Reserved Notation "G '⊢' T '<:' U" (at level 40, T at level 59).

Reserved Notation "x ';' bs ';' G '⊢' d ':' D"
         (at level 40, bs at level 39, G at level 39, d at level 59).

Reserved Notation "x ';' bs ';' G '⊢' ds '::' D"
         (at level 40, bs at level 39, G at level 39, ds at level 59).

Inductive ty_trm : ctx -> trm -> typ -> Prop :=







| ty_var : forall x T G,
    binds x T G ->
    G ⊢ tvar x : T








| ty_all_intro : forall L G T t U,
    (forall z, z \notin L ->
      G & z ~ T ⊢ open_trm z t : open_typ z U) ->
    G ⊢ trm_val (λ(T) t) : ∀(T) U








| ty_all_elim : forall G p q S T,
    G ⊢ trm_path p : ∀(S) T ->
    G ⊢ trm_path q : S ->
    G ⊢ trm_app p q : open_typ_p q T








| ty_new_intro : forall L G T ds,
    (forall z, z \notin L ->
      z; nil; G & (z ~ open_typ z T) ⊢ open_defs z ds :: open_typ z T) ->
    G ⊢ trm_val (ν(T) ds) : μ T







| ty_new_elim : forall G p a T,
    G ⊢ trm_path p : typ_rcd { a ⦂ T } ->
    G ⊢ trm_path p•a : T







| ty_rcd_intro : forall G p a T,
    G ⊢ trm_path p•a : T ->
    G ⊢ trm_path p : typ_rcd { a ⦂ T }









| ty_let : forall L G t u T U,
    G ⊢ t : T ->
    (forall x, x \notin L ->
      G & x ~ T ⊢ open_trm x u : U) ->
    G ⊢ trm_let t u : U








| ty_sngl : forall G p q T,
    G ⊢ trm_path p : {{ q }} ->
    G ⊢ trm_path q : T ->
    G ⊢ trm_path p : T








| ty_path_elim : forall G p q a T,
    G ⊢ trm_path p : {{ q }} ->
    G ⊢ trm_path q•a : T ->
    G ⊢ trm_path p•a : {{ q•a }}







| ty_rec_intro : forall G p T,
    G ⊢ trm_path p : open_typ_p p T ->
    G ⊢ trm_path p : μ T







| ty_rec_elim : forall G p T,
    G ⊢ trm_path p : μ T ->
    G ⊢ trm_path p : open_typ_p p T








| ty_and_intro : forall G p T U,
    G ⊢ trm_path p : T ->
    G ⊢ trm_path p : U ->
    G ⊢ trm_path p : T ∧ U








| ty_sub : forall G t T U,
    G ⊢ t : T ->
    G ⊢ T <: U ->
    G ⊢ t : U
where "G '⊢' t ':' T" := (ty_trm G t T)





with ty_def : var -> fields -> ctx -> def -> dec -> Prop :=

| ty_def_typ : forall x bs G A T,
    x; bs; G ⊢ def_typ A T : { A >: T <: T }







 | ty_def_all : forall x bs G T t b U V,
    G ⊢ trm_val (λ(T) t) : ∀(U) V ->
    x; bs; G ⊢ { b :=v λ(T) t } : { b ⦂ ∀(U) V }







 | ty_def_new : forall x bs b G ds T p,
     p = p_sel (avar_f x) bs ->
     tight_bounds (μ T) ->
     x; (b :: bs); G ⊢ open_defs_p p•b ds :: open_typ_p p•b T ->
     x; bs; G ⊢ { b :=v ν(T) ds } : { b ⦂ μ T }







 | ty_def_path : forall x bs G q b T,
    G ⊢ trm_path q: T ->
    x; bs; G ⊢ { b :=p q } : { b ⦂ {{ q }} }

where "x ';' bs ';' G '⊢' d ':' D" := (ty_def x bs G d D)





with ty_defs : var -> fields -> ctx -> defs -> typ -> Prop :=






| ty_defs_one : forall x bs G d D,
    x; bs; G ⊢ d : D ->
    x; bs; G ⊢ defs_cons defs_nil d :: typ_rcd D









| ty_defs_cons : forall x bs G d ds D T,
    x; bs; G ⊢ ds :: T ->
    x; bs; G ⊢ d : D ->
    defs_hasnt ds (label_of_def d) ->
    x; bs; G ⊢ defs_cons ds d :: T ∧ typ_rcd D
where "x ';' bs ';' G '⊢' ds '::' T" := (ty_defs x bs G ds T)


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
    G ⊢ T ∧ U <: T


| subtyp_and12: forall G T U,
    G ⊢ T ∧ U <: U








| subtyp_and2: forall G S T U,
    G ⊢ S <: T ->
    G ⊢ S <: U ->
    G ⊢ S <: T ∧ U







| subtyp_fld: forall G T U a,
    G ⊢ T <: U ->
    G ⊢ typ_rcd { a ⦂ T } <: typ_rcd { a ⦂ U }








| subtyp_typ: forall G S1 S2 T1 T2 A,
    G ⊢ S2 <: S1 ->
    G ⊢ T1 <: T2 ->
    G ⊢ typ_rcd { A >: S1 <: T1 } <: typ_rcd { A >: S2 <: T2 }








| subtyp_sngl_pq : forall G p q T T' U,
    G ⊢ trm_path p : {{ q }} ->
    G ⊢ trm_path q : U ->
    repl_typ p q T T' ->
    G ⊢ T <: T'








| subtyp_sngl_qp : forall G p q T T' U,
    G ⊢ trm_path p : {{ q }} ->
    G ⊢ trm_path q : U ->
    repl_typ q p T T' ->
    G ⊢ T <: T'







| subtyp_sel2: forall G p A S T,
    G ⊢ trm_path p : typ_rcd { A >: S <: T } ->
    G ⊢ S <: (p ↓ A)







| subtyp_sel1: forall G p A S T,
    G ⊢ trm_path p : typ_rcd  { A >: S <: T } ->
    G ⊢ p ↓ A <: T









| subtyp_all : forall (L : fset var) (G : ctx) (S1 T1 S2 T2 : typ),
    G ⊢ S2 <: S1 ->
    (forall x : var, x \notin L -> G & x ~ S2 ⊢ open_typ x T1 <: open_typ x T2) ->
      G ⊢ ∀(S1) T1 <: ∀(S2) T2
where "G '⊢' T '<:' U" := (subtyp G T U).

Reserved Notation "γ '⫶' G" (at level 40).

Inductive well_typed: ctx -> sta -> Prop :=
| well_typed_empty: empty ⫶ empty
| well_typed_push: forall G γ x T v,
    γ ⫶ G ->
    x # G ->
    x # γ ->
    G ⊢ trm_val v : T ->
    γ & x ~ v ⫶ G & x ~ T
where "γ ⫶ G" := (well_typed G γ).

Scheme typ_mut := Induction for typ Sort Prop
  with   dec_mut := Induction for dec Sort Prop.

Combined Scheme typ_mutind from typ_mut, dec_mut.

Scheme trm_mut  := Induction for trm  Sort Prop
  with   val_mut  := Induction for val Sort Prop
  with   def_mut  := Induction for def  Sort Prop
  with   defs_mut := Induction for defs Sort Prop
  with   defrhs_mut := Induction for def_rhs Sort Prop.

Combined Scheme trm_mutind from trm_mut, val_mut, def_mut, defs_mut, defrhs_mut.

Scheme ty_trm_mut    := Induction for ty_trm    Sort Prop
  with   ty_def_mut    := Induction for ty_def    Sort Prop
  with   ty_defs_mut   := Induction for ty_defs   Sort Prop.

Combined Scheme ty_mutind from ty_trm_mut, ty_def_mut, ty_defs_mut.

Scheme tds_ty_trm_mut  := Induction for ty_trm    Sort Prop
  with   tds_ty_def_mut  := Induction for ty_def    Sort Prop
  with   tds_ty_defs_mut := Induction for ty_defs   Sort Prop
  with   tds_subtyp      := Induction for subtyp    Sort Prop.

Combined Scheme tds_mutind from tds_ty_trm_mut, tds_ty_def_mut, tds_ty_defs_mut, tds_subtyp.

Scheme ts_ty_trm_mut  := Induction for ty_trm    Sort Prop
  with   ts_subtyp      := Induction for subtyp    Sort Prop.

Combined Scheme ts_mutind from ts_ty_trm_mut, ts_subtyp.

Scheme rules_trm_mut    := Induction for ty_trm    Sort Prop
  with   rules_def_mut    := Induction for ty_def    Sort Prop
  with   rules_defs_mut   := Induction for ty_defs   Sort Prop
  with   rules_subtyp     := Induction for subtyp    Sort Prop.

Combined Scheme rules_mutind from rules_trm_mut, rules_def_mut, rules_defs_mut, rules_subtyp.

Scheme rcd_dec_mut := Induction for record_dec Sort Prop
  with rcd_typ_mut := Induction for record_typ Sort Prop
  with inert_mut   := Induction for inert_typ Sort Prop.

Combined Scheme rcd_mutind from rcd_dec_mut, rcd_typ_mut, inert_mut.

Scheme repl_typ_mut := Induction for repl_typ Sort Prop
  with repl_dec_mut := Induction for repl_dec Sort Prop.

Combined Scheme repl_mutind from repl_typ_mut, repl_dec_mut.

Scheme ty_def_mut' := Induction for ty_def Sort Prop
  with ty_defs_mut' := Induction for ty_defs Sort Prop.

Combined Scheme ty_def_mutind from ty_def_mut', ty_defs_mut'.

Open Scope string_scope.
