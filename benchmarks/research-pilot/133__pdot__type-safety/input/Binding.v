Set Implicit Arguments.

Require Import Coq.Program.Equality List String.

Require Import Definitions.

Close Scope string_scope.

Definition subst_var (z: var) (y: var) (x: var): var :=
  If x = z then y else x.

Definition subst_var_p (z: var) (p: path) (x: var): path :=
  If x = z then p else (pvar x).

Definition subst_avar (z: var) (p: path) (x: avar) : path :=
  match x with
  | avar_b i => p_sel (avar_b i) nil
  | avar_f y => subst_var_p z p y
  end.

Definition subst_path (z: var) (q: path) (p: path) : path :=
  match p with
  | p_sel x bs => sel_fields (subst_avar z q x) bs
  end.

Fixpoint subst_typ (z: var) (p: path) (T: typ) { struct T } : typ :=
  match T with
  | ⊤        => ⊤
  | ⊥        => ⊥
  | typ_rcd D      => typ_rcd (subst_dec z p D)
  | T1 ∧ T2        => subst_typ z p T1 ∧ subst_typ z p T2
  | q ↓ L          => subst_path z p q ↓ L
  | μ T            => μ (subst_typ z p T)
  | ∀(T) U         => ∀ (subst_typ z p T) subst_typ z p U
  | {{ q }}        => {{ subst_path z p q }}
  end
with subst_dec (z: var) (p: path) (D: dec) { struct D } : dec :=
  match D with
  | {A >: T <: U} => {A >: subst_typ z p T <: subst_typ z p U}
  | {a ⦂ U}        => {a ⦂ subst_typ z p U }
  end.

Fixpoint subst_trm (z: var) (u: path) (t: trm) : trm :=
  match t with
  | trm_val v        => trm_val (subst_val z u v)
  | trm_path p       => trm_path (subst_path z u p)
  | trm_app x1 x2    => trm_app (subst_path z u x1) (subst_path z u x2)
  | trm_let t1 t2    => trm_let (subst_trm z u t1) (subst_trm z u t2)
  end
with subst_val (z: var) (u: path) (v: val) : val :=
  match v with
  | ν(T) ds  => ν(subst_typ z u T) subst_defs z u ds
  | λ(T) t   => λ(subst_typ z u T) subst_trm z u t
  end
with subst_def (z: var) (u: path) (d: def) : def :=
  match d with
  | def_typ L T => def_typ L (subst_typ z u T)
  | { a := t }  => { a := subst_defrhs z u t }
  end
with subst_defs (z: var) (u: path) (ds: defs) : defs :=
  match ds with
  | defs_nil => defs_nil
  | defs_cons rest d => defs_cons (subst_defs z u rest) (subst_def z u d)
  end
with subst_defrhs (z: var) (u: path) (drhs: def_rhs) : def_rhs :=
  match drhs with
  | defp p => defp (subst_path z u p)
  | defv v => defv (subst_val z u v)
  end.

Definition subst_ctx (z: var) (p: path) (G: ctx) : ctx :=
  map (subst_typ z p) G.

Definition named_path p := exists x bs, p = p_sel (avar_f x) bs.
