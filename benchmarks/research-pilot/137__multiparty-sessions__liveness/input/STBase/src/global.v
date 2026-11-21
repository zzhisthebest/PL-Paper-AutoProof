From mathcomp Require Import all_ssreflect.

Require Import List String Coq.Arith.PeanoNat Relations ZArith Datatypes Setoid Morphisms Coq.Logic.Decidable Coq.Program.Basics Coq.Init.Datatypes.

Import ListNotations.

Open Scope list_scope.

From Paco Require Import paco.

Import ListNotations.

From live_mpst.STBase Require Import src.header src.sim src.expr.

Section gtt.

CoInductive gtt: Type :=
  | gtt_end    : gtt
  | gtt_send   : part -> part -> list (option (sort*gtt)) -> gtt.

Definition gtt_id (s: gtt): gtt :=
  match s with
    | gtt_end        => gtt_end
    | gtt_send p q l => gtt_send p q l
  end.

Inductive global  : Type :=
  | g_var : fin -> global
  | g_end : global
  | g_send : part -> part -> list (option (sort * global)) -> global
  | g_rec : global -> global.

Section global_ind_ref.

Variable P : global -> Prop.

End global_ind_ref.

Fixpoint incr_freeG (fv m : fin) (G : global) :=
  match G with
    | g_var n        => g_var (if fv <= n then (n + m) else n)
    | g_end          => g_end
    | g_send p q lis => g_send p q (map (fun u =>
          match u with
            | Some (s, g) => Some (s, incr_freeG fv m g)
            | None        => None
          end) lis)
    | g_rec g        => g_rec (incr_freeG (S fv) m g)
  end.

Inductive subst_global : fin -> fin -> global -> global -> global -> Prop :=
  | subg_var_is   : forall G t m,                            subst_global t m G (g_var t) (incr_freeG 0 m G)
  | subg_var_notz : forall G t m, t <> 0 ->                  subst_global t m G (g_var 0) (g_var 0)
  | subg_var_not1 : forall G t t' m, t <> S t' -> t <= t' -> subst_global t m G (g_var (S t')) (g_var (t'))
  | subg_var_not2 : forall G t t' m, t <> S t' -> t' < t  -> subst_global t m G (g_var (S t')) (g_var (S t'))
  | subg_end      : forall G t m,                            subst_global t m G g_end g_end
  | subg_send     : forall G t m p q xs ys, List.Forall2 (fun u v =>
                           (u = None /\ v = None) \/
                           (exists s g g', u = Some(s, g) /\ v = Some(s, g') /\ subst_global t m G g g')
                                                  ) xs ys -> subst_global t m G (g_send p q xs) (g_send p q ys)
  | subg_rec      : forall G t m P Q, subst_global (S t) (S m) G P Q -> subst_global t m G (g_rec P) (g_rec Q).

Inductive betaG : relation global :=
  | gttS : forall G G', subst_global 0 0 (g_rec G) G G' -> betaG (g_rec G) G'.

Inductive gttT (R : global -> gtt -> Prop) : global -> gtt -> Prop :=
  | gttT_end  : gttT R g_end gtt_end
  | gttT_send : forall p q xs ys, List.Forall2 (fun u v => (u = None /\ v = None) \/ (exists s g g', u = Some(s, g) /\ v = Some(s, g') /\ R g g')) xs ys -> gttT R (g_send p q xs) (gtt_send p q ys)
  | gttT_rec  : forall G Q G', subst_global 0 0 (g_rec G) G Q -> R Q G' -> gttT R (g_rec G) G'.

Definition gttTC G G' := paco2 gttT bot2 G G'.

Inductive wfG : global -> Prop :=
  | wfg_var : forall n, wfG (g_var n)
  | wfg_end : wfG g_end
  | wfg_send : forall p q lis, SList lis -> p <> q -> List.Forall (fun u => u = None \/ (exists s g, u = Some(s, g) /\ wfG g)) lis -> wfG (g_send p q lis)
  | wfg_rec : forall g, wfG g -> wfG (g_rec g).

Inductive guardG : fin -> fin -> global -> Prop :=
  | gg_nil : forall m G, guardG 0 m G
  | gg_end : forall n m, guardG n m g_end
  | gg_send : forall n m p q lis, List.Forall (fun u => u = None \/ (exists s g, u = Some(s, g) /\ guardG n m g)) lis -> guardG (S n) m (g_send p q lis)
  | gg_rec : forall n m g Q, subst_global 0 0 (g_rec g) g Q -> guardG n m Q -> guardG n (S m) (g_rec g).

End gtt.
