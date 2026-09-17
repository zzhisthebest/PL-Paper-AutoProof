Require Import AutoProof.SystemRF.SystemRF.BasicDefinitions.
Require Import AutoProof.SystemRF.SystemRF.Names.

(** Because the underyling System F types have type variables, we need a concept
  *   of well-formedness that works for the System F types and the System F
  *   binding environments containing System F types in the bindings. *)

(*-----------------------------------------------------------------------------
----- | JUDGEMENTS : WELL-FORMEDNESS of System F TYPES and ENVIRONMENTS
-----------------------------------------------------------------------------*)

  (* --- Well-Formedness of (System) F types *)

Inductive WFFT : fenv -> ftype -> kind -> Prop :=
    | WFFTBasic : forall (g : fenv) (b : basic),
           isConcreteBasic b  ->  WFFT g (FTBasic b) Base
    | WFFTFV    : forall (g : fenv) (a : var_name) (k : kind), 
          tv_bound_inF a k g -> WFFT g (FTBasic (FTV a)) k
    | WFFTFunc  : forall (g : fenv) (t1 : ftype) (k1 : kind) (t2 : ftype) (k2 : kind),
          WFFT g t1 k1 -> WFFT g t2 k2 -> WFFT g (FTFunc t1 t2) Star
    | WFFTPoly  : forall (g : fenv) (k : kind) (t : ftype) (k_t : kind) (nms : names),
          ( forall (a:var_name), ~ In a nms -> WFFT (FConsT a k g) (unbindFT a t) k_t )
              -> WFFT g (FTPoly k t) Star
    | WFFTKind  : forall (g : fenv) (t : ftype),
          WFFT g t Base -> WFFT g t Star.

Inductive WFFE : fenv -> Prop := 
    | WFFEmpty : WFFE FEmpty
    | WFFBind  : forall (g : fenv) (x : var_name) (t : ftype) (k : kind),
          WFFE g -> ~ (in_envF x g) -> WFFT g t k -> WFFE (FCons x t g)
    | WFFBindT : forall (g : fenv) (a : var_name)             (k : kind),
          WFFE g -> ~ (in_envF a g)               -> WFFE (FConsT a k g).

Lemma wffe_uniqueF : forall (g : fenv),
    WFFE g -> uniqueF g.
Proof. intros g p_g; induction p_g; simpl; trivial; split; assumption. Qed.