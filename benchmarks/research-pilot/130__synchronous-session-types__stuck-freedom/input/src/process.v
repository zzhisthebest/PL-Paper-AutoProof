From mathcomp Require Import ssreflect.seq all_ssreflect.

Require Import List String Coq.Arith.PeanoNat Relations ZArith Datatypes Setoid Morphisms Coq.Logic.Decidable Coq.Program.Basics Coq.Init.Datatypes.

Import ListNotations.

Open Scope list_scope.

From Paco Require Import paco.

Import ListNotations.

From SST Require Import src.header src.sim src.expr.

Section process.

Inductive process : Type :=
  | p_send : part -> label -> expr -> process -> process
  | p_recv : part -> list(option process) -> process
  | p_ite : expr -> process -> process -> process
  | p_rec : process -> process
  | p_var : nat -> process
  | p_inact : process.

Section process_ind_ref.

Variable P : process -> Prop.

End process_ind_ref.

Inductive wtyped : process -> Prop :=
  | wp_var : forall n, wtyped (p_var n)
  | wp_inact : wtyped p_inact
  | wp_send: forall pt lb ex pr, wtyped pr -> wtyped (p_send pt lb ex pr)
  | wp_recv : forall pt llp, SList llp -> List.Forall (fun u => (u = None) \/ (exists k, u = Some k /\ wtyped k)) llp -> wtyped (p_recv pt llp)
  | wp_ite : forall e P1 P2, wtyped P1 -> wtyped P2 -> wtyped (p_ite e P1 P2)
  | wp_rec : forall pr, wtyped pr -> wtyped (p_rec pr).

Section substitution.

Fixpoint incr_freeE (fv m : fin) (e : expr) :=
  match e with
    | e_var n    => e_var (if fv <= n then (n + m)%coq_nat else n)
    | e_val v    => e_val v
    | e_succ n   => e_succ (incr_freeE fv m n)
    | e_neg n    => e_neg (incr_freeE fv m n)
    | e_not n    => e_not (incr_freeE fv m n)
    | e_gt u v   => e_gt (incr_freeE fv m u) (incr_freeE fv m v)
    | e_plus u v => e_plus (incr_freeE fv m u) (incr_freeE fv m v)
    | e_det u v  => e_det (incr_freeE fv m u) (incr_freeE fv m v)
  end.

Fixpoint incr_free (fvP fvE m k : fin) (P : process) : process :=
  match P with
    | p_var n          => p_var (if fvP <= n then ((n + m)%coq_nat) else n)
    | p_inact          => p_inact
    | p_send p l e P'  => p_send p l (incr_freeE fvE k e) (incr_free fvP fvE m k P')
    | p_recv p llp     => p_recv p (List.map (
        fun u => match u with
          | Some p' => Some (incr_free fvP (S fvE) m k p')
          | None    => None
        end) llp)
    | p_ite e P1 P2    => p_ite (incr_freeE fvE k e) (incr_free fvP fvE m k P1) (incr_free fvP fvE m k P2)
    | p_rec P'         => p_rec (incr_free (S fvP) fvE m k P')
  end.

Definition subst_relation (A : Type) : Type := fin -> fin -> fin -> A -> A -> A -> Prop.

Inductive substitutionP : subst_relation process :=
  | sub_var_is   : forall P x m n,              substitutionP x m n P (p_var x) (incr_free 0 0 m n P)
  | sub_var_notz : forall P x m n, x <> 0 ->    substitutionP x m n P (p_var 0) (p_var 0)
  | sub_var_not1 : forall P x y m n, x <> S y -> x <= y -> substitutionP x m n P (p_var (S y)) (p_var y)
  | sub_var_not2 : forall P x y m n, x <> S y -> y < x  -> substitutionP x m n P (p_var (S y)) (p_var (S y))
  | sub_inact    : forall P x m n,              substitutionP x m n P (p_inact) (p_inact)
  | sub_send     : forall P x m n pt l e P' Q', substitutionP x m n P P' Q' -> substitutionP x m n P (p_send pt l e P') (p_send pt l e Q')
  | sub_recv     : forall P x m n pt xs ys,
  List.Forall2 (fun u v =>
    (u = None /\ v = None) \/
    (exists k l, u = Some k /\ v = Some l /\ substitutionP x m (S n) P k l)
  ) xs ys -> substitutionP x m n P (p_recv pt xs) (p_recv pt ys)
  | sub_ite       : forall P x m n e P1 P2 Q1 Q2, substitutionP x m n P P1 Q1 -> substitutionP x m n P P2 Q2 -> substitutionP x m n P (p_ite e P1 P2) (p_ite e Q1 Q2)
  | sub_rec       : forall P x m n P' Q', substitutionP (S x) (S m) n P P' Q' -> substitutionP x m n P (p_rec P') (p_rec Q').

End substitution.

Inductive peq_w : process -> process -> Prop :=
  | peq_var : forall n, peq_w (p_var n) (p_var n)
  | peq_inact : peq_w p_inact p_inact
  | peq_send : forall pt lb e e' p1 p2, peq_w p1 p2 -> peq_w (p_send pt lb e p1) (p_send pt lb e' p2)
  | peq_recv : forall pt xs ys, Forall2 (fun u v => (u = None /\ v = None) \/ (exists p p', u = Some p /\ v = Some p' /\ peq_w p p')) xs ys -> peq_w (p_recv pt xs) (p_recv pt ys)
  | peq_ite  : forall e1 p1 q1 e2 p2 q2, peq_w p1 p2 -> peq_w q1 q2 -> peq_w (p_ite e1 p1 q1) (p_ite e2 p2 q2)
  | peq_rec : forall p1 p2, peq_w p1 p2 -> peq_w (p_rec p1) (p_rec p2).

Fixpoint subst_expr (n d : fin) (e : expr) (e1 : expr) : expr :=
  match e1 with
    | e_var 0     => if Nat.eqb n 0 then (incr_freeE 0 d e) else e_var 0
    | e_var (S m) => if Nat.eqb (S m) n then (incr_freeE 0 d e) else
                     if Nat.ltb (S m) n then e_var (S m) else e_var m
    | e_succ e' => e_succ (subst_expr n d e e')
    | e_neg e' => e_neg (subst_expr n d e e')
    | e_not e' => e_not (subst_expr n d e e')
    | e_gt e' e'' => e_gt (subst_expr n d e e') (subst_expr n d e e'')
    | e_plus e' e'' => e_plus (subst_expr n d e e') (subst_expr n d e e'')
    | e_det e' e'' => e_det (subst_expr n d e e') (subst_expr n d e e'')
    | _ => e1
  end.

Fixpoint subst_expr_proc (p : process) (e : expr) (n d : fin) : process :=
  match p with
    | p_send pt l e' P => p_send pt l (subst_expr n d e e') (subst_expr_proc P e n d)
    | p_ite e' P Q     => p_ite (subst_expr n d e e') (subst_expr_proc P e n d) (subst_expr_proc Q e n d)
    | p_recv pt lst    => p_recv pt (map (fun x => match x with
                                                | None => None
                                                | Some y => Some (subst_expr_proc y e (S n) (S d))
                                               end) lst)
    | p_rec P          => p_rec (subst_expr_proc P e n d)
    | _ => p
  end.

Inductive guardP : fin -> fin -> process -> Prop :=
  | gp_nil : forall m G, guardP 0 m G
  | gp_inact : forall n m, guardP n m p_inact
  | gp_send : forall n m pt l e g, guardP n m g -> guardP (S n) m (p_send pt l e g)
  | gp_recv : forall n m p lis, List.Forall (fun u => u = None \/ (exists g, u = Some g /\ guardP n m g)) lis -> guardP (S n) m (p_recv p lis)
  | gp_ite : forall n m P Q e, guardP n m P -> guardP n m Q -> guardP n (S m) (p_ite e P Q)
  | gp_rec : forall n m g Q, substitutionP 0 0 0 (p_rec g) g Q -> guardP n m Q -> guardP n (S m) (p_rec g).

Inductive betaPr : relation process :=
  | betaPr_sin : forall P Q, substitutionP 0 0 0 (p_rec P) P Q -> betaPr (p_rec P) Q.

End process.
