Require Export Metalib.Metatheory.

Require Export SystemF_inf.

Require Export Fii_inf.

Require Export TypeSystems.

Coercion ty_var_b : nat >-> ty.

Coercion ty_var_f : typvar >-> ty.

Coercion exp_var_b : nat >-> exp.

Coercion exp_var_f : expvar >-> exp.

Notation "'|' A '|'" := (sty2ty A) (at level 60).

Notation "'∥' Γ '∥'" := (map sty2ty Γ) (at level 60).

Inductive same_stctx {a b} : list (atom * a) -> list (atom * b) -> Prop :=
| same_empty : same_stctx nil nil
| same_cons : forall X A B s1 s2,
    same_stctx s1 s2 ->  same_stctx ([(X , A)] ++ s1) ([(X , B)] ++ s2).

Definition exp_relation := exp -> exp -> Prop.

Definition getR (p : list (atom * (sty * sty * exp_relation))) : list (atom * exp_relation) :=
  map (fun t => match t with | (a, b, R) => R end) p.

Definition getOne (p : list (atom * (sty * sty * exp_relation))) : list (atom * sty) :=
  map (fun t => match t with | (a, b, R) => a end) p.

Definition getTwo (p : list (atom * (sty * sty * exp_relation))) : list (atom * sty) :=
  map (fun t => match t with | (a, b, R) => b end) p.

Definition mtsubst_in_sty (s : list (atom * sty)) (ty : sty) : sty :=
  fold_left (fun acc p => subst_sty_in_sty (snd p) (fst p) acc) s ty.

Definition mtsubst_in_exp (s : list (atom * sty)) (e : exp) : exp :=
  fold_left (fun acc p => subst_ty_in_exp (| snd p |) (fst p)  acc) s e.

Definition msubst_in_exp (s : list (atom * exp)) (t : exp) : exp :=
  fold_left (fun acc p => subst_exp_in_exp (snd p) (fst p) acc) s t.

Inductive all_value : list (atom * exp) -> Prop :=
| all_empty : all_value nil
| all_cons : forall x v T g,
    value v ->
    typ nil nil v T ->
    all_value g ->
    all_value ([(x , v)] ++ g).

Inductive rel_d : stctx -> sctx -> Prop :=
| rel_d_empty : rel_d nil nil
| rel_d_cons : forall X Δ t B p,
    X `notin` dom Δ ->
    rel_d Δ p ->
    swft nil t ->
    mono t ->
    disjoint nil t (mtsubst_in_sty p B) ->
    rel_d ([(X, B)] ++ Δ) ([(X, t)] ++ p).
