Require Import Arith.
Require Import ZArith.

Require Import AutoProof.SystemRF.SystemRF.BasicDefinitions.
Require Import AutoProof.SystemRF.SystemRF.Names. 
Require Import AutoProof.SystemRF.SystemRF.LocalClosure.
Require Import AutoProof.SystemRF.SystemRF.Semantics.
Require Import AutoProof.SystemRF.SystemRF.SystemFTyping.
Require Import AutoProof.SystemRF.SystemRF.WellFormedness.
Require Import AutoProof.SystemRF.SystemRF.BasicPropsSubstitution.
Require Import AutoProof.SystemRF.SystemRF.BasicPropsEnvironments.

(*-----------------------------------------------------------------------------
----- | JUDGEMENTS : the Typing Relation and the Subtyping Relation
-----------------------------------------------------------------------------*)
(* eqlPred b e 构造一个 Bool 类型的 equality predicate：bvar 0 = e。
   b 是两边值的基础类型；
   BV 0 是 refinement type 当前描述的值；
   e 是要与它比较的程序。
   Eql 被实例化为没有 predicate 的基础类型 TRefn b PEmpty。*)
Definition eqlPred (b : basic) (e : expr) : expr :=
  <{ Eql [$(TRefn b PEmpty)] $(e) (bvar 0) }>.

Lemma lem_eqlPred_islc_at : forall (b : basic) (e : expr),
    isLCT (TRefn b PEmpty) -> isLC e -> isLC_at 1 0 (eqlPred b e).
Proof. intros; simpl; intuition; 
  try destruct b; simpl in H; try contradiction;
  try apply lem_islc_at_weaken with 0 0; intuition. Qed.

Lemma lem_unbind_eqlPred : forall (y : var_name) (b : basic) (e : expr),
    isLC e -> unbind y (eqlPred b e) 
                   = App (App (AppT (Prim Eql) (TRefn b PEmpty)) e) (FV y).
Proof. intros; unfold unbind; simpl; rewrite lem_unbind_lc; trivial. Qed.

Lemma lem_tsubFTV_eqlPred : forall (a:var_name) (t_a:type) (b:basic) (e:expr),
    noExists t_a  -> ~ (b = FTV a) -> ~ In a (ftv e)
                  -> subFTV a t_a (eqlPred b e) = eqlPred b e.
Proof. intros; destruct b eqn:B; simpl; try destruct (a =? a0) eqn:A;
  try (apply Nat.eqb_eq in A; subst a0; contradiction);
  unfold eqlPred; repeat f_equal; apply lem_subFTV_notin; apply H1. Qed.

(* self T e k 根据 kind k，把原类型 T 加强为精确描述程序 e 的类型。
   例：T = {x : Int | x > 0}、e = 3、k = Base 时，结果是
   {x : Int | x = 3 并且 x > 0}。 *)
Fixpoint self (T : type) (e : expr) (k : kind) : type :=
    match k with 
    | Base => match T with
              | (TRefn b ps)      =>  TRefn b (PCons  (eqlPred b e)  ps)
              | (TFunc    T1 T2)  =>  TFunc   T1 T2
              | (TExists  T1 T2)  =>  TExists T1 (self T2 e Base)
              | (TPoly    k_a T1) =>  TPoly   k_a T1
              end
    | Star => T
    end.  (* { t':type | Set_sub (free t') (Set_cup (free t) (fv e)) &&
                  (isTRefn t => isTRefn t') && (noExists t => noExists t' )*)
Lemma self_trefn_is_push : forall (b : basic) (ps : preds) (e : expr), 
    self (TRefn b ps) e Base = push (PCons (eqlPred b e) PEmpty) (TRefn b ps).
Proof. intros; simpl; reflexivity. Qed.

Lemma lem_self_islct_at : forall (t:type) (e:expr) (k:kind) (j:index),
    isLCT_at j 0 t -> isLC e -> isLCT_at j 0 (self t e k).
Proof. induction t; intros; destruct k0 || destruct k; unfold self; try assumption.
  - (* TRefn b ps, Base *) destruct b eqn:B; simpl in H;
    (* no BTV *) try (destruct H; unfold lt in H; apply Nat.le_0_r in H; discriminate);
    simpl; repeat split; try apply H; 
    try apply lem_islc_at_weaken with 0 0; auto with *.
  - (* TExists, Base *) fold self; simpl; simpl in H; intuition. Qed.

Lemma lem_self_islct : forall (t : type) (e : expr) (k : kind),
    isLCT t -> isLC e -> isLCT (self t e k).
Proof. intros t e k; apply lem_self_islct_at. Qed. 

Lemma lem_openT_at_self : forall (j:index) (y:var_name) (t:type) (e:expr) (k:kind),
    isLC e ->  openT_at j y (self t e k) = self (openT_at j y t) e k.
Proof. intros j y t; generalize dependent j; induction t; intros.
  - (* TRefn *) destruct k; simpl; unfold eqlPred;
    pose proof lem_open_at_lc_at; destruct H0;
    try rewrite (e0 e (j+1) 0 y); try destruct (j + 1 =? 0) eqn:J; 
    rewrite Nat.add_comm in J; simpl in J; try discriminate J;
    try apply lem_islc_at_weaken with 0 0; auto with *.
  - (* TFunc *) destruct k; simpl; reflexivity.
  - (* TExis *) destruct k; simpl; try rewrite IHt2; trivial.
  - (* TPoly *) destruct k0; simpl; reflexivity.
  Qed.

Lemma lem_unbindT_self : forall (y:var_name) (t:type) (e:expr) (k:kind),
    isLC e ->  unbindT y (self t e k) = self (unbindT y t) e k.
Proof. intros; unfold unbindT; apply lem_openT_at_self; apply H. Qed. 

Lemma lem_tsubFV_self : forall (z:var_name) (v_z:expr) (t:type) (e:expr) (k:kind),
    tsubFV z v_z (self t e k) = self (tsubFV z v_z t) (subFV z v_z e) k.
Proof. intros; induction t; destruct k; simpl; f_equal.
  - (* TExis *) apply IHt2. Qed.

Lemma lem_tsubBV_at_self : forall (j:index) (v_z:expr) (t:type) (e:expr) (k:kind),
    isValue v_z -> isLC e -> tsubBV_at j v_z (self t e k) = self (tsubBV_at j v_z t) e k.
Proof. intros j v_z t; generalize dependent j; induction t; intros.
  - (* TRefn *) destruct k; simpl; pose proof lem_subBV_at_lc_at; destruct H1;
    try rewrite e0 with e (j+1) v_z 0 0; try destruct (j + 1 =? 0) eqn:J;
    rewrite Nat.add_comm in J; simpl in J; try discriminate J; auto with *.
  - (* TFunc *) destruct k; simpl; reflexivity.
  - (* TExis *) destruct k; simpl; try rewrite IHt2; trivial.
  - (* TPoly *) destruct k0; simpl; reflexivity.
  Qed.
  
Lemma lem_tsubBV_self : forall (v_z:expr) (t:type) (e:expr) (k:kind),
    isValue v_z -> isLC e -> tsubBV v_z (self t e k) = self (tsubBV v_z t) e k.
Proof. intros; apply lem_tsubBV_at_self; apply H || apply H0. Qed.

Lemma lem_erase_self : forall (t:type) (e:expr) (k:kind),
    erase (self t e k) = erase t.
Proof. intros; destruct k; induction t; simpl; try apply IHt2; reflexivity. Qed.

Lemma lem_self_star : forall (t:type) (e:expr), self t e Star = t.
Proof. intros; destruct t; reflexivity. Qed.

(*------------------------------------------------------------------------------
----- | TYPING & SUBTYPING JUDGMENTS and UNINTERPRETED IMPLICATION 
------------------------------------------------------------------------------*)
(* typing rules *)
Inductive Hastype : env -> expr -> type -> Prop :=
    | T_BC   : forall (g:env) (b:bool), Hastype g (Bool_constant b) (tybc b) 
    | T_IC   : forall (g:env) (m:Z),  Hastype g (Int_constant m) (tyic m) 
    (* 给x加上精确类型 *)
    (* 若环境 g 中记录了变量 x 的类型是 Int，那么FV x 不仅具有
     Int 类型，还具有更精确的 self type {v : Int | v = x}，表示 FV x
     的求值结果就是环境中的变量 x 所代表的值。 *)
    | T_Var  : forall (g:env) (x:var_name) (T:type) (k:kind),
          bound_in x T g -> WFtype g T k -> Hastype g (FV x) (self T (FV x) k)
    
    | T_Prm  : forall (g:env) (c:prim), Hastype g (Prim c) (primitive_type c)
    (* 看到这里了 *)
    | T_Abs  : forall (g:env) (T1:type) (k:kind) (t:expr) (T2:type) (nms:names),
          WFtype g T1 k
              -> (forall (y:var_name), ~ In y nms -> Hastype (Cons y T1 g) (unbind y t) (unbindT y T2)) 
              -> Hastype g (Lambda t) (TFunc T1 T2) 
    | T_App  : forall (g:env) (t1:expr) (T1:type) (T2:type) (t2:expr),
          Hastype g t1 (TFunc T1 T2) -> Hastype g t2 T1 -> Hastype g (App t1 t2) (TExists T1 T2)
    | T_AbsT : forall (g:env) (k:kind) (t:expr) (T:type) (nms:names),
          (forall (a':var_name), ~ In a' nms 
                           -> Hastype (ConsT a' k g) (unbind_tv a' t) (unbind_tvT a' T))
              -> Hastype g (LambdaT k t) (TPoly k T)
    | T_AppT : forall (g:env) (t:expr) (k:kind) (T1:type) (T2:type),
          Hastype g t (TPoly k T1) -> isMono T2 -> noExists T2 -> WFtype g T2 k
              -> Hastype g (AppT t T2) (tsubBTV T2 T1)
    | T_Let  : forall (g:env) (t1:expr) (T1:type) (t2:expr) (T2:type) (k:kind) (nms:names),
          WFtype g T2 k -> Hastype g t1 T1
              -> (forall (y:var_name), ~ In y nms 
                          -> Hastype (Cons y T1 g) (unbind y t2) (unbindT y T2)) 
              -> Hastype g (Let t1 t2) T2 
    | T_Ann  : forall (g:env) (t:expr) (T:type), 
          noExists T -> Hastype g t T -> Hastype g (Annot t T) T
    | T_If   : forall (g:env) (t1 t2 t3 : expr) (ps: preds) (T:type) (k:kind) (nms:names),
          Hastype g t1 (TRefn TBool ps) -> WFtype  g T k 
            -> (forall (y:var_name), ~ In y nms
                  -> Hastype (Cons y (self (TRefn TBool ps) (Bool_constant true)  Base) g) t2 T )
            -> (forall (y:var_name), ~ In y nms
                  -> Hastype (Cons y (self (TRefn TBool ps) (Bool_constant false) Base) g) t3 T )
            -> Hastype g (If t1 t2 t3) T
    | T_Sub  : forall (g:env) (t:expr) (T1:type) (T2:type) (k:kind),
          Hastype g t T1 -> WFtype g T2 k -> Subtype g T1 T2 -> Hastype g t T2

with Subtype : env -> type -> type -> Prop :=
    | SBase : forall (g:env) (b:basic) (p1:preds) (p2:preds) (nms:names),
          (forall (y:var_name), ~ In y nms
                          -> Implies (Cons y (TRefn b PEmpty) g) (unbindP y p1) (unbindP y p2)) 
              -> Subtype g (TRefn b p1) (TRefn b p2) 
    | SFunc : forall (g:env) (s1:type) (s2:type) (t1:type) (t2:type) (nms:names),
          Subtype g s2 s1
              -> (forall (y:var_name), ~ In y nms
                          -> Subtype (Cons y s2 g) (unbindT y t1) (unbindT y t2)) 
              -> Subtype g (TFunc s1 t1) (TFunc s2 t2) 
    | SWitn : forall (g:env) (v_x:expr) (t_x:type) (t:type) (t':type) ,
          isValue v_x -> Hastype g v_x t_x -> Subtype g t (tsubBV v_x t')
              -> Subtype g t (TExists t_x t')
    | SBind : forall (g:env) (t_x:type) (t:type) (t':type) (nms:names),
          isLCT t' -> (forall (y:var_name), ~ In y nms -> Subtype (Cons y t_x g) (unbindT y t) t') 
              -> Subtype g (TExists t_x t) t' 
    | SPoly : forall (g:env) (k:kind) (t1:type) (t2:type) (nms:names),
              (forall (a:var_name), ~ In a nms 
                          -> Subtype (ConsT a k g) (unbind_tvT a t1) (unbind_tvT a t2)) 
                  -> Subtype g (TPoly k t1) (TPoly k t2)

with Implies : env -> preds -> preds -> Prop := 
    | IRefl   : forall (g:env) (ps:preds), Implies g ps ps
    | ITrans  : forall (g:env) (ps:preds) (qs:preds) (rs:preds),
          Implies g ps qs -> Implies g qs rs -> Implies g ps rs
    | IFaith  : forall (g:env) (ps:preds), Implies g ps PEmpty
    | IConj   : forall (g:env) (ps:preds) (qs:preds) (rs:preds),
          Implies g ps qs -> Implies g ps rs -> Implies g ps (strengthen qs rs)
    | ICons1  : forall (g:env) (p:expr) (ps:preds), Implies g (PCons p ps) (PCons p PEmpty)
    | ICons2  : forall (g:env) (p:expr) (ps:preds), Implies g (PCons p ps) ps
    | IRepeat : forall (g:env) (p:expr) (ps:preds), Implies g (PCons p ps) (PCons p (PCons p ps))
    | INarrow : forall (g:env) (g':env) (x:var_name) (s_x t_x:type) (k_sx k_tx:kind) (ps qs:preds),
          intersect (binds g) (binds g') = empty -> unique g -> unique g'
              -> ~ in_env x g -> ~ in_env x g' -> WFEnv g
              -> WFtype g s_x k_sx -> WFtype g t_x k_tx -> Subtype g s_x t_x
              -> Implies (concatE (Cons x t_x g) g') ps qs
              -> Implies (concatE (Cons x s_x g) g') ps qs 
    | IWeak   : forall (g:env) (g':env) (ps:preds) (qs:preds) (x:var_name) (t_x:type),
          intersect (binds g) (binds g') = empty -> unique g -> unique g' 
              -> ~ in_env x g -> ~ in_env x g' -> WFEnv (concatE g g')
              -> ~ In x (fvP ps) -> ~ In x (ftvP ps) 
              -> ~ In x (fvP qs) -> ~ In x (ftvP qs)
              -> Implies (concatE g g') ps qs 
              -> Implies (concatE (Cons x t_x g) g') ps qs
    | IWeakTV : forall (g:env) (g':env) (ps:preds) (qs:preds) (a:var_name) (k_a:kind),
          intersect (binds g) (binds g') = empty -> unique g -> unique g' 
              -> ~ in_env a g -> ~ in_env a g' -> WFEnv (concatE g g')
              -> ~ In a (fvP ps) -> ~ In a (ftvP ps) 
              -> ~ In a (fvP qs) -> ~ In a (ftvP qs)
              -> Implies (concatE g g') ps qs 
              -> Implies (concatE (ConsT a k_a g) g') ps qs
    | ISub    : forall (g:env) (g':env) (x:var_name) (v_x:expr) (t_x:type) (ps:preds) (qs:preds),
          intersect (binds g) (binds g') = empty -> unique g -> unique g' 
              -> ~ in_env x g -> ~ in_env x g' -> WFEnv g
              -> isValue v_x -> Hastype g v_x t_x
              -> Implies (concatE (Cons x t_x g) g') ps qs
              -> Implies (concatE g (esubFV x v_x g')) (psubFV x v_x ps) (psubFV x v_x qs)
    | ISubTV  : forall (g:env) (g':env) (a:var_name) (t_a:type) (k_a:kind) (ps:preds) (qs:preds),
          intersect (binds g) (binds g') = empty -> unique g -> unique g' 
              -> ~ in_env a g -> ~ in_env a g' -> WFEnv g
              -> isMono t_a -> noExists t_a -> WFtype g t_a k_a
              -> Implies (concatE (ConsT a k_a g) g') ps qs
              -> Implies (concatE g (esubFTV a t_a g')) (psubFTV a t_a ps) (psubFTV a t_a qs)
    | IEqlSub : forall (g:env) (b:basic) (y:var_name) (e:expr) (ps:preds),
          Implies g (PCons (App (App (AppT (Prim Eql) (TRefn b PEmpty)) e) (FV y)) PEmpty)
                    (PCons (App (App (AppT (Prim Eql) (TRefn b ps    )) e) (FV y)) PEmpty) 
    | IStren  : forall (y:var_name) (b':basic) (qs:preds) (g:env) (p1s:preds) (p2s:preds),
          ~ in_env y g -> ~ In y (fvP qs)
              -> Implies (Cons y (TRefn b' qs)     g) p1s p2s
              -> Implies (Cons y (TRefn b' PEmpty) g) 
                         (strengthen p1s (unbindP y qs)) (strengthen p2s (unbindP y qs))
    | IEvals  : forall (g:env) (p p':expr) (ps:preds),
          multistep p p' -> Implies g (PCons p ps) (PCons p' ps)
    | IEvals2 : forall (g:env) (p p':expr) (ps:preds),
          multistep p' p -> Implies g (PCons p ps) (PCons p' ps).

Scheme Hastype_mutind  := Induction for Hastype  Sort Prop
with   Subtype_mutind  := Induction for Subtype  Sort Prop.
Combined Scheme judgments_mutind from Hastype_mutind, Subtype_mutind.    

Scheme Hastype_mutind3 := Induction for Hastype  Sort Prop
with   Subtype_mutind3 := Induction for Subtype  Sort Prop
with   Implies_mutind3 := Induction for Implies  Sort Prop.
Combined Scheme judgments_mutind3 
    from Hastype_mutind3, Subtype_mutind3, Implies_mutind3.
