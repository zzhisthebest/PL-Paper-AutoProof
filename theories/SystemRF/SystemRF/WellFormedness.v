Require Import AutoProof.SystemRF.SystemRF.BasicDefinitions.
Require Import AutoProof.SystemRF.SystemRF.Names.
Require Import AutoProof.SystemRF.SystemRF.SystemFTyping.

(*-----------------------------------------------------------------------------
----- | JUDGEMENTS : WELL-FORMEDNESS of TYPES and ENVIRONMENTS
-----------------------------------------------------------------------------*)

  (* --- Well-Formedness of types *)
(* WFtype g ty k表示：
  SystemRF 类型 ty 在环境 g 中是合法的，并且它的 kind 是 k。 *)
Inductive WFtype : env -> type -> kind -> Prop :=
    | WFBase : forall (g : env) (b : basic),
          isConcreteBasic b -> WFtype g (TRefn b PEmpty) Base
    (* 如果基础类型 b 合法，并且假设 y : b 后，ps 中的每个
       predicate 都具有 Bool 类型，那么 {y : b | ps} 是合法的 Base 类型。
       例：检查 {y : Int | y > 0} 时，内部的 y 原本表示为 BV 0。
       unbindP y ps 将 BV 0 打开成 y；在环境中加入 y : Int 后，
       PredicatesHaveBoolType 检查 y > 0 的类型确实是 Bool。 *)
    | WFRefn : forall (g : env) (b : basic) (ps : preds) (nms : names),
          WFtype g (TRefn b PEmpty) Base 
          -> ps <> PEmpty (* ps为空的情形已经在WFBase里 *)
          -> ( forall (y:var_name), ~ In y nms 
                  -> PredicatesHaveBoolType (FCons y (FTBasic b) (erase_env g)) (unbindP y ps) )
          -> WFtype g (TRefn b ps) Base
    | WFVar : forall (g : env) (a : var_name) (k : kind),
          tv_bound_in a k g -> WFtype g (TRefn (FTV a) PEmpty) k
    | WFFunc : forall (g : env) (t_x : type) (k_x : kind) (t : type) (k : kind) (nms : names),
          WFtype g t_x k_x
              -> (forall (y:var_name), ~ In y nms -> WFtype (Cons y t_x g) (unbindT y t) k )
              -> WFtype g (TFunc t_x t) Star
    | WFExis : forall (g : env) (t_x : type) (k_x : kind) (t : type) (k : kind) (nms : names), 
          WFtype g t_x k_x
              -> (forall (y:var_name), ~ In y nms -> WFtype (Cons y t_x g) (unbindT y t) k )
              -> WFtype g (TExists t_x t) k
    | WFPoly : forall (g : env) (k : kind) (t : type) (k_t : kind) (nms : names),
          (forall (a':var_name), ~ In a' nms -> WFtype (ConsT a' k g) (unbind_tvT a' t) k_t )
              -> WFtype g (TPoly k t) Star
    | WFKind : forall (g : env) (t : type), WFtype g t Base -> WFtype g t Star.

  (* --- Well-formedness of Environments *)

Inductive WFEnv : env -> Prop :=
    | WFEEmpty : WFEnv Empty
    | WFEBind  : forall (g : env) (x : var_name) (t : type) (k : kind),
          WFEnv g -> ~ (in_env x g) -> WFtype g t k -> WFEnv (Cons x t g)
    | WFEBindT : forall (g : env) (a : var_name) (k : kind),
          WFEnv g -> ~ (in_env a g)                 -> WFEnv (ConsT a k g).

Lemma wfenv_unique : forall (g : env),
    WFEnv g -> unique g.
Proof. intros g p_g; induction p_g; simpl; trivial; split; assumption. Qed.
