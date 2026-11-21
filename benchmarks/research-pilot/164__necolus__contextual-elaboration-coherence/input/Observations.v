Require Import Metalib.Metatheory Infrastructure target_inf.

Definition kleene_equiv t1 t2 :=
  exists k, t1 ->* (trm_lit k) /\ t2 ->* (trm_lit k).

Fixpoint appctx (ctx : cc) (t : exp) : exp :=
  match ctx with
  | cc_Empty => t
  | cc_Lam x c => trm_abs (close_exp_wrt_exp x (appctx c t))
  | cc_AppL c t2 => trm_app (appctx c t) t2
  | cc_AppR t1 c => trm_app t1 (appctx c t)
  | cc_PairL c t2 => trm_pair (appctx c t) t2
  | cc_PairR t1 c => trm_pair t1 (appctx c t)
  | cc_Co co c => trm_capp co (appctx c t)
  | cc_Rcd l c => trm_rcd l (appctx c t)
  | cc_Proj c l => trm_proj (appctx c t) l
  end.
